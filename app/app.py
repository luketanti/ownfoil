import os
import sys

APP_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(APP_DIR)
if PROJECT_DIR not in sys.path:
    sys.path.insert(0, PROJECT_DIR)

from flask import Flask, render_template, request, redirect, url_for, jsonify, send_from_directory, Response, has_app_context, has_request_context, g
from flask_login import LoginManager, current_user
from werkzeug.utils import secure_filename
from werkzeug.security import check_password_hash
from werkzeug.exceptions import RequestEntityTooLarge
from sqlalchemy import func, and_, or_, case, literal
from sqlalchemy import inspect
from app.scheduler import init_scheduler
from functools import wraps
from app.file_watcher import Watcher
import threading
import logging
import copy
import hashlib
import flask.cli
from datetime import timedelta, datetime
flask.cli.show_server_banner = lambda *args: None
from app.constants import *
from app.settings import *
from app.downloads import ProwlarrClient, filter_results, test_download_client, get_supported_download_clients, get_download_client_capabilities, get_download_client_diagnostics, run_downloads_job, manual_search_update, queue_download_url, search_update_options, check_completed_downloads, get_downloads_state, get_active_downloads, get_download_ui_visibility, filter_download_search_results, sort_download_search_results, remove_pending_download, remove_duplicate_download, dismiss_duplicate_download
from app.library import organize_library, delete_older_updates, delete_duplicates, delete_library_content, delete_orphaned_addons
from app.db import *
from app.shop import *
from app.auth import *
from app.auth import _effective_client_ip, _is_private_ip, _get_auth_protection_config, _is_permanently_blocked_ip
from app import titles
from app.utils import *
from app.library import *
from app.library import _get_nsz_runner, _ensure_unique_path
from app import titledb
from app import cheats
from app.title_requests import create_title_request, list_requests
import requests
import re
import unicodedata
import threading
import time
import uuid
import re
import secrets
import gc
import ctypes
import zipfile
import tempfile
from urllib.parse import quote

from app import compressed_stream

from app.db import add_access_event, get_access_events

try:
    from waitress import serve as waitress_serve
except Exception:
    waitress_serve = None

try:
    from PIL import Image, ImageOps
except Exception:
    Image = None
    ImageOps = None

# In-process media cache index.
# Avoids repeated os.listdir() and TitleDB lookups for icons/banners that are already cached.
_media_cache_lock = threading.Lock()
_media_cache_index = {
    'icon': {},   # title_id -> filename
    'banner': {}, # title_id -> filename
}
_media_cache_last_reset = 0

_media_resize_lock = threading.Lock()

_ICON_SIZE = (300, 300)
_BANNER_SIZE = (920, 520)
_WEB_ICON_SIZE = (300, 300)
_WEB_BANNER_SIZE = (640, 360)
try:
    _libc = ctypes.CDLL("libc.so.6")
    _malloc_trim = getattr(_libc, "malloc_trim", None)
    if _malloc_trim is not None:
        _malloc_trim.argtypes = [ctypes.c_size_t]
        _malloc_trim.restype = ctypes.c_int
except Exception:
    _malloc_trim = None

def _release_process_memory():
    try:
        gc.collect()
    except Exception:
        pass
    if _malloc_trim is not None:
        try:
            _malloc_trim(0)
        except Exception:
            pass


def _safe_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _app_has_deletable_files(app):
    if app is None or getattr(app, 'id', None) is None:
        return False

    for file_entry in list(getattr(app, 'files', []) or []):
        if file_entry is None:
            continue
        filepath = str(getattr(file_entry, 'filepath', '') or '').strip()
        if not filepath:
            continue
        linked_apps = [linked for linked in list(getattr(file_entry, 'apps', []) or []) if linked is not None]
        foreign_apps = [linked for linked in linked_apps if getattr(linked, 'id', None) != getattr(app, 'id', None)]
        if not foreign_apps:
            return True
    return False


def _build_deletable_version_map(apps):
    deletable = {}
    for app in apps or []:
        key = (
            str(getattr(app, 'app_id', '') or '').strip().upper(),
            str(getattr(app, 'app_type', '') or '').strip().upper(),
            str(getattr(app, 'app_version', '') or '').strip(),
        )
        if not all(key):
            continue
        deletable[key] = bool(deletable.get(key)) or (
            bool(getattr(app, 'owned', False)) and _app_has_deletable_files(app)
        )
    return deletable

def _media_variant_dirname(media_kind, size_override=None):
    if media_kind == 'icon':
        size = size_override or _ICON_SIZE
        return f"icons_{size[0]}x{size[1]}"
    size = size_override or _BANNER_SIZE
    return f"banners_{size[0]}x{size[1]}"

def _is_jpeg_name(filename):
    return str(filename).lower().endswith(('.jpg', '.jpeg'))

def _resize_image_to_path(src_path, dest_path, size, quality=85):
    if not Image or not ImageOps:
        return False

    try:
        with Image.open(src_path) as im:
            # Normalize orientation if EXIF is present.
            im = ImageOps.exif_transpose(im)
            fitted = ImageOps.fit(im, size, method=Image.Resampling.LANCZOS)

            os.makedirs(os.path.dirname(dest_path), exist_ok=True)

            if _is_jpeg_name(dest_path):
                if fitted.mode not in ('RGB',):
                    fitted = fitted.convert('RGB')
                fitted.save(dest_path, format='JPEG', quality=quality, optimize=True, progressive=True)
            else:
                # PNG etc.
                fitted.save(dest_path, optimize=True)
        return True
    except Exception as e:
        logger.error(f"Failed to resize image from {src_path} to {dest_path}: {e}")
        return False

def _get_variant_path(cache_dir, cached_name, media_kind, size_override=None):
    if not cached_name:
        return None
    size = size_override or (_ICON_SIZE if media_kind == 'icon' else _BANNER_SIZE)
    variant_dir = os.path.join(CACHE_DIR, _media_variant_dirname(media_kind, size_override=size_override))
    variant_path = os.path.join(variant_dir, cached_name)
    return size, variant_dir, variant_path

def _get_web_media_size(media_kind):
    size_key = (request.args.get('size') or '').lower().strip()
    if size_key not in ('web', 'small'):
        return None
    return _WEB_ICON_SIZE if media_kind == 'icon' else _WEB_BANNER_SIZE

def _maybe_expire_media_cache_index(now=None):
    if MEDIA_INDEX_TTL_S is None:
        return
    if MEDIA_INDEX_TTL_S <= 0:
        with _media_cache_lock:
            _media_cache_index['icon'].clear()
            _media_cache_index['banner'].clear()
        return
    now = now or time.time()
    global _media_cache_last_reset
    with _media_cache_lock:
        if _media_cache_last_reset and (now - _media_cache_last_reset) < MEDIA_INDEX_TTL_S:
            return
        _media_cache_index['icon'].clear()
        _media_cache_index['banner'].clear()
        _media_cache_last_reset = now

def _get_cached_media_filename(cache_dir, title_id, media_kind='icon'):
    """Return cached filename for title_id if present on disk."""
    _maybe_expire_media_cache_index()
    title_id = (title_id or '').upper()
    if not title_id:
        return None
    cache_enabled = MEDIA_INDEX_TTL_S is None or MEDIA_INDEX_TTL_S > 0
    if cache_enabled:
        with _media_cache_lock:
            cached_name = _media_cache_index.get(media_kind, {}).get(title_id)
        if cached_name:
            path = os.path.join(cache_dir, cached_name)
            if os.path.exists(path):
                return cached_name
            with _media_cache_lock:
                _media_cache_index.get(media_kind, {}).pop(title_id, None)

    try:
        for name in os.listdir(cache_dir):
            if name.startswith(f"{title_id}."):
                if cache_enabled:
                    with _media_cache_lock:
                        _media_cache_index.setdefault(media_kind, {})[title_id] = name
                return name
    except Exception:
        return None
    return None

def _remember_cached_media_filename(title_id, filename, media_kind='icon'):
    title_id = (title_id or '').upper()
    if not title_id or not filename:
        return
    _maybe_expire_media_cache_index()
    if MEDIA_INDEX_TTL_S is not None and MEDIA_INDEX_TTL_S <= 0:
        return
    with _media_cache_lock:
        _media_cache_index.setdefault(media_kind, {})[title_id] = filename

def _ensure_cached_media_file(cache_dir, title_id, remote_url):
    """Compute local cache name/path from remote_url."""
    if not remote_url:
        return None, None
    url = remote_url
    if url.startswith('//'):
        url = 'https:' + url
    clean_url = url.split('?', 1)[0]
    _, ext = os.path.splitext(clean_url)
    if not ext:
        ext = '.jpg'
    cache_name = f"{title_id.upper()}{ext}"
    cache_path = os.path.join(cache_dir, cache_name)
    return cache_name, cache_path
import json

def init():
    global watcher
    global watcher_thread
    # Create and start the file watcher
    logger.info('Initializing File Watcher...')
    watcher = Watcher(on_library_change)
    watcher_thread = threading.Thread(target=watcher.run)
    watcher_thread.daemon = True
    watcher_thread.start()

    # Load initial configuration
    logger.info('Loading initial configuration...')
    reload_conf()

    # init libraries
    library_paths = app_settings['library']['paths']
    init_libraries(app, watcher, library_paths)

    # Initialize job scheduler
    logger.info('Initializing Scheduler...')
    init_scheduler(app)

    def downloads_job():
        run_downloads_job(scan_cb=scan_library, post_cb=post_library_change)

    def downloads_pending_job():
        check_completed_downloads(scan_cb=scan_library, post_cb=post_library_change)

    def maintenance_job():
        run_library_maintenance()

    # Automatic update downloader job
    app.scheduler.add_job(
        job_id='downloads_update_job',
        func=downloads_job,
        interval=timedelta(minutes=5)
    )

    # Fast completion monitor: only does work while AeroFoil has pending downloads.
    app.scheduler.add_job(
        job_id='downloads_pending_monitor_job',
        func=downloads_pending_job,
        interval=timedelta(seconds=30),
        log_level='debug'
    )
    maintenance_interval_minutes = _get_maintenance_interval_minutes(app_settings)
    app.scheduler.add_job(
        job_id=LIBRARY_MAINTENANCE_JOB_ID,
        func=maintenance_job,
        interval=timedelta(minutes=maintenance_interval_minutes),
        run_first=True
    )
    
    # Define update_titledb_job
    def update_titledb_job():
        global is_titledb_update_running
        with titledb_update_lock:
            is_titledb_update_running = True
        logger.info("Starting TitleDB update job...")
        try:
            current_settings = load_settings()
            titledb.update_titledb(current_settings)
            logger.info("TitleDB update job completed.")
        except Exception as e:
            logger.error(f"Error during TitleDB update job: {e}")
        finally:
            with titledb_update_lock:
                is_titledb_update_running = False
        
    # Define scan_library_job
    def scan_library_job():
        global is_titledb_update_running
        with titledb_update_lock:
            if is_titledb_update_running:
                logger.info("Skipping scheduled library scan: update_titledb job is currently in progress. Rescheduling in 5 minutes.")
                # Reschedule the job for 5 minutes later
                app.scheduler.add_job(
                    job_id=f'scan_library_rescheduled_{datetime.now().timestamp()}', # Unique ID
                    func=scan_library_job,
                    run_once=True,
                    start_date=datetime.now().replace(microsecond=0) + timedelta(minutes=5)
                )
                return
        if _is_conversion_running():
            logger.info("Skipping scheduled library scan: conversion job is running. Rescheduling in 5 minutes.")
            app.scheduler.add_job(
                job_id=f'scan_library_rescheduled_{datetime.now().timestamp()}',
                func=scan_library_job,
                run_once=True,
                start_date=datetime.now().replace(microsecond=0) + timedelta(minutes=5)
            )
            return
        logger.info("Starting scheduled library scan job...")
        global scan_in_progress
        with scan_lock:
            if scan_in_progress:
                logger.info(f'Skipping scheduled library scan: scan already in progress.')
                return # Skip the scan if already in progress
            scan_in_progress = True
        try:
            scan_library()
            post_library_change()
            logger.info("Scheduled library scan job completed.")
        except Exception as e:
            logger.error(f"Error during scheduled library scan job: {e}")
        finally:
            with scan_lock:
                scan_in_progress = False

    # Update job: run update_titledb then scan_library once on startup
    def update_db_and_scan_job():
        logger.info("Running update job (TitleDB update and library scan)...")
        update_titledb_job() # This will set/reset the flag
        scan_library_job() # This will check the flag and run if update_titledb_job is done
        logger.info("Update job completed.")

    # Schedule the update job to run immediately and only once
    app.scheduler.add_job(
        job_id='update_db_and_scan',
        func=update_db_and_scan_job,
        interval=timedelta(hours=2),
        run_first=True
    )

os.makedirs(CONFIG_DIR, exist_ok=True)
os.makedirs(DATA_DIR, exist_ok=True)

LIBRARY_MAINTENANCE_JOB_ID = 'library_maintenance_job'

def _get_maintenance_interval_minutes(settings):
    interval = settings.get('library', {}).get('maintenance_interval_minutes', 720)
    try:
        interval = int(interval)
    except Exception:
        interval = 720
    return max(30, interval)

def run_library_maintenance():
    try:
        if _is_conversion_running():
            logger.info("Skipping scheduled library maintenance: conversion job is running.")
            return
        current_settings = load_settings()
        library_cfg = current_settings.get('library', {})
        if not library_cfg.get('auto_maintenance', False):
            return
        logger.info("Starting scheduled library maintenance job...")
        results = organize_library(dry_run=False, verbose=False)
        if library_cfg.get('maintenance_delete_updates', True):
            delete_results = delete_older_updates(dry_run=False, verbose=False)
            if not delete_results.get('success'):
                logger.warning("Delete updates reported errors: %s", delete_results.get('errors'))
        if results.get('success'):
            post_library_change()
            logger.info("Library maintenance completed.")
        else:
            logger.warning("Library maintenance reported errors: %s", results.get('errors'))
    except Exception as e:
        logger.error("Error during library maintenance job: %s", e)
    finally:
        _release_process_memory()

def _reschedule_library_maintenance(app):
    try:
        interval_minutes = _get_maintenance_interval_minutes(app_settings)
        interval = timedelta(minutes=interval_minutes)
        import datetime as dt
        scheduler = getattr(app, 'scheduler', None)
        if not scheduler:
            return False
        lock = getattr(scheduler, '_lock', None)
        jobs = getattr(scheduler, 'scheduled_jobs', None)
        if lock is None or jobs is None:
            return False
        with lock:
            job = jobs.get(LIBRARY_MAINTENANCE_JOB_ID)
            if job:
                job['interval'] = interval
                job['cron'] = None
                job['run_once'] = False
                job['next_run'] = dt.datetime.now().replace(microsecond=0) + interval
                return True
        scheduler.add_job(
            job_id=LIBRARY_MAINTENANCE_JOB_ID,
            func=run_library_maintenance,
            interval=interval,
            run_first=False
        )
        return True
    except Exception as e:
        logger.warning("Failed to reschedule maintenance job: %s", e)
        return False

## Global variables
app_settings = {}
# Create a global variable and lock for scan_in_progress
scan_in_progress = False
scan_lock = threading.Lock()
# Global flag for titledb update status
is_titledb_update_running = False
titledb_update_lock = threading.Lock()
conversion_jobs = {}
conversion_jobs_lock = threading.Lock()
conversion_job_limit = 50
upload_jobs = {}
upload_jobs_lock = threading.Lock()
upload_job_limit = 200
library_rebuild_status = {
    'in_progress': False,
    'started_at': 0,
    'updated_at': 0
}
library_rebuild_lock = threading.Lock()
shop_sections_cache = {
    'limit': None,
    'timestamp': 0,
    'state_token': None,
    'payload': None,
    'encrypted': {},
}
shop_sections_cache_lock = threading.Lock()
shop_sections_refresh_lock = threading.Lock()
shop_sections_refresh_running = False
shop_root_cache_lock = threading.Lock()
shop_root_cache = {
    'state_token': None,
    'files': None,
    'files_enriched': None,
    'encrypted': {},
}
_SHOP_ROOT_ENCRYPTED_CACHE_LIMIT = 8
_SHOP_SECTIONS_ENCRYPTED_CACHE_LIMIT = 8
_TITLES_METADATA_CACHE_VERSION = 4
titles_metadata_cache_lock = threading.Lock()
titles_metadata_cache = {
    'version': _TITLES_METADATA_CACHE_VERSION,
    'state_token': None,
    'genres': [],
    'title_name_map': {},
    'genre_title_ids': {},
    'unrecognized_title_ids': set(),
    'rating_by_title_id': {},
}
titles_total_cache_lock = threading.Lock()
titles_total_cache = {}
library_size_cache_lock = threading.Lock()
library_size_cache = {
    'state_token': None,
    'total_bytes': 0,
    'updated_at': 0.0,
}
request_settings_sync_lock = threading.Lock()
request_settings_last_sync_ts = 0.0
missing_files_sweep_lock = threading.Lock()
missing_files_last_run_ts = 0.0
_title_request_users_table_exists_cache = None


def _has_title_request_users_table():
    global _title_request_users_table_exists_cache
    if _title_request_users_table_exists_cache is not None:
        return bool(_title_request_users_table_exists_cache)
    try:
        _title_request_users_table_exists_cache = bool(inspect(db.engine).has_table('title_request_users'))
    except Exception:
        _title_request_users_table_exists_cache = False
    return bool(_title_request_users_table_exists_cache)


def _resolve_motd_username():
    try:
        if current_user.is_authenticated:
            return str(getattr(current_user, 'user', '') or '').strip()
    except Exception:
        pass
    try:
        auth = request.authorization
        if auth and auth.username:
            return str(auth.username).strip()
    except Exception:
        pass
    return ''


def _render_motd_template(raw_motd):
    text = str(raw_motd or '')
    if not text:
        return ''
    now_ts = time.time()
    now_struct = time.localtime(now_ts)
    username = _resolve_motd_username()
    user_id = ''
    is_admin = 'false'
    shop_access = 'false'
    backup_access = 'false'
    frozen = 'false'
    client_uid = ''
    try:
        if current_user.is_authenticated:
            user_id = str(getattr(current_user, 'id', '') or '')
            is_admin = 'true' if bool(getattr(current_user, 'is_admin', False)) else 'false'
            shop_access = 'true' if bool(getattr(current_user, 'shop_access', False)) else 'false'
            backup_access = 'true' if bool(getattr(current_user, 'backup_access', False)) else 'false'
            frozen = 'true' if bool(getattr(current_user, 'frozen', False)) else 'false'
            client_uid = str(getattr(current_user, 'client_uid', '') or '').strip()
    except Exception:
        pass
    values = {
        'username': username,
        'user_id': user_id,
        'is_admin': is_admin,
        'shop_access': shop_access,
        'backup_access': backup_access,
        'frozen': frozen,
        'client_uid': client_uid,
        'remote_addr': _effective_remote_addr(),
        'user_agent': str(request.user_agent.string or ''),
        'host': str(request.host or ''),
        'path': str(request.path or ''),
        'date': time.strftime('%Y-%m-%d', now_struct),
        'time': time.strftime('%H:%M:%S', now_struct),
        'datetime': time.strftime('%Y-%m-%d %H:%M:%S', now_struct),
        'timestamp': str(int(now_ts)),
    }
    values.update(_resolve_motd_api_variables())
    return re.sub(r"\{([a-z_][a-z0-9_]*)\}", lambda m: str(values.get(m.group(1), m.group(0))), text)


def _resolve_motd_api_variables():
    shop_settings = app_settings.get('shop', {}) if isinstance(app_settings, dict) else {}
    custom_url = str((shop_settings or {}).get('motd_api_url') or '').strip()
    out = {'api_text': ''}
    if not custom_url:
        return out
    try:
        resp = requests.get(custom_url, timeout=3, headers={'User-Agent': 'AeroFoil-MOTD/1.0'})
        if resp.status_code >= 400:
            logger.warning('MOTD API returned HTTP %s for %s; API MOTD variables will be empty.', resp.status_code, custom_url)
            return out
        content_type = str(resp.headers.get('Content-Type') or '').lower()
        text_body = str(resp.text or '').strip()[:4096]
        out['api_text'] = text_body
        if 'application/json' in content_type:
            try:
                payload = resp.json()
                if isinstance(payload, dict):
                    for key, value in payload.items():
                        key_norm = re.sub(r'[^a-z0-9_]+', '_', str(key or '').strip().lower()).strip('_')
                        if not key_norm:
                            continue
                        out[f'api_{key_norm}'] = str(value if value is not None else '')
            except Exception:
                pass
        return out
    except Exception as exc:
        logger.warning('MOTD API request failed for %s: %s; API MOTD variables will be empty.', custom_url, exc)
        return out


def _prune_upload_jobs_unlocked(now_ts=None):
    now = float(now_ts if now_ts is not None else time.time())
    stale_cutoff = now - 3600.0
    stale_ids = [
        job_id for job_id, job in upload_jobs.items()
        if float(job.get('updated_at') or 0.0) < stale_cutoff
    ]
    for job_id in stale_ids:
        upload_jobs.pop(job_id, None)
    while len(upload_jobs) > upload_job_limit:
        oldest_id = min(upload_jobs, key=lambda key: float((upload_jobs.get(key) or {}).get('updated_at') or 0.0))
        upload_jobs.pop(oldest_id, None)


def _set_upload_job_stage(upload_id, stage, message=None, status=None, extra=None):
    if not upload_id:
        return
    now = time.time()
    with upload_jobs_lock:
        _prune_upload_jobs_unlocked(now)
        job = upload_jobs.get(upload_id)
        if job is None:
            job = {
                'id': upload_id,
                'status': 'running',
                'stage': 'starting',
                'message': 'Starting upload...',
                'created_at': now,
                'updated_at': now,
            }
            upload_jobs[upload_id] = job
        job['stage'] = str(stage or job.get('stage') or 'running')
        if message is not None:
            job['message'] = str(message)
        if status:
            job['status'] = str(status)
        if isinstance(extra, dict):
            for key, value in extra.items():
                job[key] = value
        job['updated_at'] = now


def _is_conversion_running():
    with conversion_jobs_lock:
        for job in conversion_jobs.values():
            kind = str(job.get('kind') or '')
            status = str(job.get('status') or '')
            if kind.startswith('convert') and status == 'running':
                return True
    return False

def _read_cache_ttl(env_key, default_value):
    raw = os.environ.get(env_key)
    if raw is None:
        return default_value
    raw = str(raw).strip()
    if not raw:
        return default_value
    lowered = raw.lower()
    if lowered in ('none', 'null', 'off'):
        return None
    try:
        return int(lowered)
    except ValueError:
        return default_value

def _read_int_env(env_key, default_value, minimum=None, maximum=None):
    raw = os.environ.get(env_key)
    if raw is None:
        return default_value
    raw = str(raw).strip()
    if not raw:
        return default_value
    try:
        value = int(raw)
    except ValueError:
        return default_value
    if minimum is not None:
        value = max(int(minimum), value)
    if maximum is not None:
        value = min(int(maximum), value)
    return value

def _invalidate_shop_root_cache():
    with shop_root_cache_lock:
        shop_root_cache['state_token'] = None
        shop_root_cache['files'] = None
        shop_root_cache['files_enriched'] = None
        shop_root_cache['encrypted'] = {}

def _get_titledb_aware_state_token():
    library_token = str(get_library_cache_state_token() or '')
    try:
        titledb_token = str(titles.get_titledb_cache_token() or 'missing')
    except Exception:
        titledb_token = 'missing'
    return f"{library_token}::{titledb_token}::{cheats.cheat_state_token()}"


def _get_cached_titles_total(cache_key):
    if TITLES_TOTAL_CACHE_TTL_S == 0:
        return None
    now = time.time()
    with titles_total_cache_lock:
        cached = titles_total_cache.get(cache_key)
        if not isinstance(cached, dict):
            return None
        if TITLES_TOTAL_CACHE_TTL_S is not None:
            age = now - float(cached.get('timestamp') or 0.0)
            if age > float(TITLES_TOTAL_CACHE_TTL_S):
                titles_total_cache.pop(cache_key, None)
                return None
        try:
            return int(cached.get('total') or 0)
        except Exception:
            return None


def _store_titles_total(cache_key, total):
    if TITLES_TOTAL_CACHE_TTL_S == 0:
        return
    with titles_total_cache_lock:
        titles_total_cache[cache_key] = {
            'total': int(total or 0),
            'timestamp': time.time(),
        }
        if len(titles_total_cache) > TITLES_TOTAL_CACHE_MAX_ENTRIES:
            ordered = sorted(
                titles_total_cache.items(),
                key=lambda kv: float((kv[1] or {}).get('timestamp') or 0.0),
                reverse=True,
            )[:TITLES_TOTAL_CACHE_MAX_ENTRIES]
            titles_total_cache.clear()
            for key, value in ordered:
                titles_total_cache[key] = value

def _build_enriched_shop_files():
    """Build the shop file list annotated with each file's ESRB rating.

    `rating` is the max known rating among the file's titles (most restrictive),
    or None. `unrated` is True when any associated title is unrated or the file
    is unidentified (no title). Used to apply the per-user age filter.
    """
    rows = (
        db.session.query(
            Files.id.label('file_id'),
            Files.filename.label('filename'),
            Files.size.label('size'),
            Titles.title_id.label('title_id'),
        )
        .select_from(Files)
        .outerjoin(app_files, app_files.c.file_id == Files.id)
        .outerjoin(Apps, Apps.id == app_files.c.app_id)
        .outerjoin(Titles, Titles.id == Apps.title_id)
        .all()
    )

    files = {}
    order = []
    for row in rows:
        fid = row.file_id
        meta = files.get(fid)
        if meta is None:
            meta = {'filename': row.filename, 'size': int(row.size or 0), 'title_ids': set()}
            files[fid] = meta
            order.append(fid)
        tid = (row.title_id or '').strip().upper()
        if tid:
            meta['title_ids'].add(tid)

    rating_cache = {}
    enriched = []
    with titles.titledb_session() as titledb_loaded:
        def _rating(tid):
            if not titledb_loaded:
                return None
            if tid not in rating_cache:
                info = titles.get_game_info(tid) or {}
                rating_cache[tid] = _coerce_rating_value(info.get('rating'))
            return rating_cache[tid]

        for fid in order:
            meta = files[fid]
            tids = meta['title_ids']
            if not tids:
                file_rating = None
                unrated = True
            else:
                ratings = [_rating(t) for t in tids]
                unrated = any(r is None for r in ratings)
                known = [r for r in ratings if r is not None]
                file_rating = max(known) if known else None
            enriched.append({
                'url': f"/api/get_game/{fid}#{meta['filename']}",
                'size': meta['size'],
                'rating': file_rating,
                'unrated': unrated,
            })
    return enriched


def _enriched_file_allowed(entry, cap, block_unrated):
    if cap is None:
        return True
    if entry.get('unrated') and block_unrated:
        return False
    rating = entry.get('rating')
    if rating is None:
        return True
    return rating <= cap


def _get_cached_shop_files(cap=None, block_unrated=True, virtualize_compressed=False):
    state_token = get_library_cache_state_token()
    with shop_root_cache_lock:
        cached = shop_root_cache.get('files_enriched')
        if shop_root_cache.get('state_token') == state_token and isinstance(cached, list):
            enriched = cached
        else:
            enriched = None

    if enriched is None:
        enriched = _build_enriched_shop_files()
        with shop_root_cache_lock:
            shop_root_cache['state_token'] = state_token
            shop_root_cache['files_enriched'] = enriched
            shop_root_cache['encrypted'] = {}

    visible = enriched if cap is None else [
        {"url": e["url"], "size": e["size"]}
        for e in enriched
        if _enriched_file_allowed(e, cap, block_unrated)
    ]
    if cap is None:
        visible = [{"url": e["url"], "size": e["size"]} for e in enriched]
    if not virtualize_compressed:
        return visible

    virtual_files = []
    for entry in visible:
        virtual_entry = dict(entry)
        url, marker, listed_filename = str(entry['url']).partition('#')
        if marker and compressed_stream.supports_virtual_stream(listed_filename):
            virtual_entry['url'] = f'{url}#{compressed_stream.virtual_filename(listed_filename)}'
        virtual_files.append(virtual_entry)
    return virtual_files

def _get_cached_encrypted_shop_payload(shop_payload, public_key, verified_host, filter_token=None):
    state_token = get_library_cache_state_token()
    motd = str(shop_payload.get("success") or "")
    referrer = str(shop_payload.get("referrer") or verified_host or "")
    cache_key = (state_token, motd, str(public_key or ''), referrer, filter_token)

    with shop_root_cache_lock:
        encrypted_cache = shop_root_cache.setdefault('encrypted', {})
        cached = encrypted_cache.get(cache_key)
        if isinstance(cached, (bytes, bytearray)):
            return bytes(cached)

    payload = encrypt_shop(shop_payload, public_key_pem=public_key, compression_level=6)
    with shop_root_cache_lock:
        encrypted_cache = shop_root_cache.setdefault('encrypted', {})
        encrypted_cache[cache_key] = payload
        if len(encrypted_cache) > _SHOP_ROOT_ENCRYPTED_CACHE_LIMIT:
            ordered_keys = list(encrypted_cache.keys())[-_SHOP_ROOT_ENCRYPTED_CACHE_LIMIT:]
            shop_root_cache['encrypted'] = {k: encrypted_cache[k] for k in ordered_keys}
    return payload


def _filter_sections_payload(payload, cap, block_unrated):
    """Return a copy of a sections payload with items above the age cap removed.

    Each item carries a `rating` (base-title ESRB age, or None when unrated).
    Applied per-request at the response edge so the global section caches stay
    user-agnostic.
    """
    if cap is None or not isinstance(payload, dict):
        return payload
    sections = payload.get('sections')
    if not isinstance(sections, list):
        return payload

    filtered_sections = []
    for section in sections:
        items = section.get('items') if isinstance(section, dict) else None
        if not isinstance(items, list):
            filtered_sections.append(section)
            continue
        kept = [
            item for item in items
            if _title_allowed(cap, _coerce_rating_value((item or {}).get('rating')), block_unrated)
        ]
        new_section = dict(section)
        new_section['items'] = kept
        filtered_sections.append(new_section)

    new_payload = dict(payload)
    new_payload['sections'] = filtered_sections
    return new_payload


def _get_cached_encrypted_shop_sections_payload(shop_payload, public_key, cache_limit, full_catalog=False, filter_token=None):
    state_token = _get_titledb_aware_state_token()
    cache_key = (state_token, int(cache_limit), bool(full_catalog), str(public_key or ''), filter_token)

    with shop_sections_cache_lock:
        encrypted_cache = shop_sections_cache.setdefault('encrypted', {})
        cached = encrypted_cache.get(cache_key)
        if isinstance(cached, (bytes, bytearray)):
            return bytes(cached)

    payload = encrypt_shop(shop_payload, public_key_pem=public_key, compression_level=6)
    with shop_sections_cache_lock:
        encrypted_cache = shop_sections_cache.setdefault('encrypted', {})
        encrypted_cache[cache_key] = payload
        if len(encrypted_cache) > _SHOP_SECTIONS_ENCRYPTED_CACHE_LIMIT:
            ordered_keys = list(encrypted_cache.keys())[-_SHOP_SECTIONS_ENCRYPTED_CACHE_LIMIT:]
            shop_sections_cache['encrypted'] = {k: encrypted_cache[k] for k in ordered_keys}
    return payload


def _respond_with_shop_payload(payload, verified_host=None, cache_kind=None, cache_limit=None, full_catalog=False, filter_token=None):
    response_payload = payload
    if verified_host is not None and not response_payload.get('referrer'):
        response_payload = dict(response_payload)
        response_payload['referrer'] = f"https://{verified_host}"

    if app_settings['shop']['encrypt']:
        public_key = app_settings['shop'].get('public_key')
        if cache_kind == 'root':
            encrypted = _get_cached_encrypted_shop_payload(
                response_payload,
                public_key=public_key,
                verified_host=verified_host,
                filter_token=filter_token,
            )
        elif cache_kind == 'sections':
            encrypted = _get_cached_encrypted_shop_sections_payload(
                response_payload,
                public_key=public_key,
                cache_limit=cache_limit,
                full_catalog=full_catalog,
                filter_token=filter_token,
            )
        else:
            encrypted = encrypt_shop(response_payload, public_key_pem=public_key, compression_level=6)
        return Response(encrypted, mimetype='application/octet-stream')

    return jsonify(response_payload)

def _is_titledb_unrecognized(info):
    try:
        name_value = str((info or {}).get('name') or '').strip().lower()
        id_value = str((info or {}).get('id') or '').strip().lower()
        return name_value == 'unrecognized' or 'not found in titledb' in id_value
    except Exception:
        return True

def _split_genres_value(raw):
    parts = []
    for segment in str(raw or '').split(','):
        cleaned = re.sub(r'^[\s\[\]\'"`]+|[\s\[\]\'"`]+$', '', str(segment or '').strip()).strip()
        if cleaned:
            parts.append(cleaned)
    seen = set()
    out = []
    for part in parts:
        key = part.lower()
        if key in seen:
            continue
        seen.add(key)
        out.append(part)
    return out

def _normalize_library_search_text(text):
    value = str(text or '')
    try:
        # Keep Unicode letters (e.g. CJK), but normalize width/compat forms.
        value = unicodedata.normalize('NFKC', value)
        # Fold accents for Latin-like scripts while keeping non-Latin letters.
        value = ''.join(
            ch for ch in unicodedata.normalize('NFKD', value)
            if unicodedata.category(ch) != 'Mn'
        )
    except Exception:
        pass
    value = value.casefold()
    value = re.sub(r"_+", " ", value)
    value = re.sub(r"[^\w\s]+", " ", value, flags=re.UNICODE)
    return re.sub(r"\s+", " ", value).strip()

def _search_matches_normalized_text(query_normalized, field_value):
    hay = _normalize_library_search_text(field_value)
    if not hay:
        return False
    if query_normalized in hay:
        return True

    # Handle spacing/symbol differences (e.g. "you update" vs "youupdate").
    query_compact = query_normalized.replace(' ', '')
    hay_compact = hay.replace(' ', '')
    if query_compact and query_compact in hay_compact:
        return True

    # Token-aware fallback so all query terms must be present.
    terms = [t for t in query_normalized.split(' ') if t]
    if terms and all(term in hay for term in terms):
        return True
    return False

def _build_titles_metadata_cache():
    genres_map = {}
    genre_title_ids = {}
    title_name_map = {}
    unrecognized_title_ids = set()
    rating_by_title_id = {}

    with titles.titledb_session() as titledb_loaded:
        if not titledb_loaded:
            return {
                'genres': [],
                'title_name_map': {},
                'genre_title_ids': {},
                'unrecognized_title_ids': set(),
                'rating_by_title_id': {},
            }

        title_ids = [row.title_id for row in db.session.query(Titles.title_id).all() if row.title_id]
        for tid in title_ids:
            normalized_tid = str(tid or '').strip().upper()
            if not normalized_tid:
                continue
            info = titles.get_game_info(normalized_tid) or {}
            name = str(info.get('name') or '').strip()
            title_name_map[normalized_tid] = _normalize_library_search_text(name)
            rating_by_title_id[normalized_tid] = _coerce_rating_value(info.get('rating'))
            if _is_titledb_unrecognized(info):
                unrecognized_title_ids.add(normalized_tid)
            for genre in _split_genres_value(info.get('category') or ''):
                lowered = genre.lower()
                if lowered not in genres_map:
                    genres_map[lowered] = genre
                genre_title_ids.setdefault(lowered, set()).add(normalized_tid)

    genres = sorted(genres_map.values(), key=lambda item: str(item).lower())
    return {
        'genres': genres,
        'title_name_map': title_name_map,
        'genre_title_ids': genre_title_ids,
        'unrecognized_title_ids': unrecognized_title_ids,
        'rating_by_title_id': rating_by_title_id,
    }

def _get_cached_titles_metadata():
    state_token = _get_titledb_aware_state_token()
    with titles_metadata_cache_lock:
        if (
            titles_metadata_cache.get('state_token') == state_token
            and int(titles_metadata_cache.get('version') or 0) == _TITLES_METADATA_CACHE_VERSION
        ):
            return {
                'genres': list(titles_metadata_cache.get('genres') or []),
                'title_name_map': dict(titles_metadata_cache.get('title_name_map') or {}),
                'genre_title_ids': {
                    str(k): set(v or set())
                    for k, v in (titles_metadata_cache.get('genre_title_ids') or {}).items()
                },
                'unrecognized_title_ids': set(titles_metadata_cache.get('unrecognized_title_ids') or set()),
                'rating_by_title_id': dict(titles_metadata_cache.get('rating_by_title_id') or {}),
            }

    fresh = _build_titles_metadata_cache()
    with titles_metadata_cache_lock:
        titles_metadata_cache['version'] = _TITLES_METADATA_CACHE_VERSION
        titles_metadata_cache['state_token'] = state_token
        titles_metadata_cache['genres'] = list(fresh.get('genres') or [])
        titles_metadata_cache['title_name_map'] = dict(fresh.get('title_name_map') or {})
        titles_metadata_cache['genre_title_ids'] = {
            str(k): set(v or set())
            for k, v in (fresh.get('genre_title_ids') or {}).items()
        }
        titles_metadata_cache['unrecognized_title_ids'] = set(fresh.get('unrecognized_title_ids') or set())
        titles_metadata_cache['rating_by_title_id'] = dict(fresh.get('rating_by_title_id') or {})
    return fresh

def _get_cached_library_genres():
    metadata = _get_cached_titles_metadata()
    return list(metadata.get('genres') or [])


def _sort_library_rows_by_title_name(rows, title_name_map, descending=False):
    title_name_map = title_name_map or {}

    def _sort_key(row):
        title_id = str(getattr(row, 'title_id', '') or '').strip().upper()
        app_id = str(getattr(row, 'app_id', '') or '').strip().upper()
        normalized_name = str(title_name_map.get(title_id) or '').strip()
        fallback_name = _normalize_library_search_text(title_id or app_id)
        return (
            normalized_name or fallback_name,
            title_id,
            app_id,
        )

    return sorted(rows, key=_sort_key, reverse=bool(descending))

def _get_discovery_sections(limit=12):
    try:
        limit = max(1, int(limit))
    except Exception:
        limit = 12

    now = time.time()
    state_token = _get_titledb_aware_state_token()
    payload = None
    with shop_sections_cache_lock:
        cache_enabled = SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0
        cache_valid = True
        if SHOP_SECTIONS_CACHE_TTL_S is not None:
            cache_valid = (now - float(shop_sections_cache.get('timestamp') or 0)) <= SHOP_SECTIONS_CACHE_TTL_S
        cache_hit = (
            cache_enabled
            and shop_sections_cache['payload'] is not None
            and shop_sections_cache.get('state_token') == state_token
            and cache_valid
        )
        if cache_hit:
            payload = shop_sections_cache['payload']

    if payload is None:
        if SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0:
            disk_cache = _load_shop_sections_cache_from_disk()
            if (
                disk_cache
                and disk_cache.get('limit') == max(limit, 50)
                and str(disk_cache.get('state_token') or '') == state_token
            ):
                disk_payload = disk_cache.get('payload')
                disk_ts = float(disk_cache.get('timestamp') or 0)
                disk_ok = True
                if SHOP_SECTIONS_CACHE_TTL_S is not None:
                    disk_ok = (now - disk_ts) <= SHOP_SECTIONS_CACHE_TTL_S
                if disk_payload and disk_ok:
                    payload = disk_payload
                    _store_shop_sections_cache(payload, max(limit, 50), disk_ts, state_token, persist_disk=False)

    if payload is None:
        payload = _build_shop_sections_payload(max(limit, 50))
        if SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0:
            _store_shop_sections_cache(payload, max(limit, 50), now, state_token, persist_disk=True)

    sections = payload.get('sections') if isinstance(payload, dict) else []
    newest = []
    recommended = []
    for section in sections or []:
        if section.get('id') == 'new':
            newest = list(section.get('items') or [])[:limit]
        elif section.get('id') == 'recommended':
            recommended = list(section.get('items') or [])[:limit]
    return newest, recommended

# ===== CACHE TTLs (seconds) =====
# Make these short if you want the Web UI caches to free memory frequently.
# Set to 0 to disable in-memory caching entirely.
# Set to None to disable expiry (cache refreshes on library rebuild).
SHOP_SECTIONS_CACHE_TTL_S = _read_cache_ttl('SHOP_SECTIONS_CACHE_TTL_S', None)
SHOP_SECTIONS_ALL_ITEMS_CAP = _read_cache_ttl('SHOP_SECTIONS_ALL_ITEMS_CAP', None)
SHOP_SECTIONS_ALL_ITEMS_CAP_NO_TITLEDB = _read_cache_ttl('SHOP_SECTIONS_ALL_ITEMS_CAP_NO_TITLEDB', 120)
SHOP_SECTIONS_MAX_IN_MEMORY_BYTES = _read_cache_ttl('SHOP_SECTIONS_MAX_IN_MEMORY_BYTES', 4 * 1024 * 1024)
MEDIA_INDEX_TTL_S = _read_cache_ttl('MEDIA_INDEX_TTL_S', None)
REQUEST_SETTINGS_SYNC_INTERVAL_S = _read_cache_ttl('REQUEST_SETTINGS_SYNC_INTERVAL_S', 5)
MISSING_FILES_SWEEP_INTERVAL_S = _read_cache_ttl('MISSING_FILES_SWEEP_INTERVAL_S', 21600)
TITLES_TOTAL_CACHE_TTL_S = _read_cache_ttl('AEROFOIL_TITLES_TOTAL_CACHE_TTL_S', 300)
TITLES_TOTAL_CACHE_TTL_S = _read_cache_ttl('OWNFOIL_TITLES_TOTAL_CACHE_TTL_S', TITLES_TOTAL_CACHE_TTL_S)
TITLES_TOTAL_CACHE_MAX_ENTRIES = _read_int_env('AEROFOIL_TITLES_TOTAL_CACHE_MAX_ENTRIES', 256, minimum=16, maximum=4096)
TITLES_TOTAL_CACHE_MAX_ENTRIES = _read_int_env('OWNFOIL_TITLES_TOTAL_CACHE_MAX_ENTRIES', TITLES_TOTAL_CACHE_MAX_ENTRIES, minimum=16, maximum=4096)
# ===============================

def _load_shop_sections_cache_from_disk():
    cache_path = SHOP_SECTIONS_CACHE_FILE
    if not os.path.exists(cache_path):
        return None
    try:
        with open(cache_path, 'r', encoding='utf-8') as handle:
            data = json.load(handle)
    except Exception:
        return None
    if not isinstance(data, dict):
        return None
    if 'payload' not in data or 'timestamp' not in data or 'limit' not in data:
        return None
    return data

def _save_shop_sections_cache_to_disk(payload, limit, timestamp, state_token=None):
    cache_path = SHOP_SECTIONS_CACHE_FILE
    os.makedirs(os.path.dirname(cache_path), exist_ok=True)
    data = {
        'payload': payload,
        'limit': limit,
        'timestamp': timestamp,
        'state_token': state_token,
    }
    try:
        with open(cache_path, 'w', encoding='utf-8') as handle:
            json.dump(data, handle)
    except Exception:
        pass

def _estimate_json_size_bytes(payload):
    try:
        return len(json.dumps(payload, separators=(',', ':')).encode('utf-8'))
    except Exception:
        return None

def _store_shop_sections_cache(payload, limit, timestamp, state_token, persist_disk=True):
    cache_payload = payload
    if '::missing' in str(state_token or ''):
        # Keep cold-boot payload on disk only; avoid retaining large placeholder payloads in RAM.
        cache_payload = None

    max_bytes = SHOP_SECTIONS_MAX_IN_MEMORY_BYTES
    if cache_payload is not None and max_bytes is not None:
        try:
            max_bytes = max(0, int(max_bytes))
            payload_size = _estimate_json_size_bytes(cache_payload)
            if payload_size is not None and payload_size > max_bytes:
                logger.info(
                    "Skipping in-memory shop sections cache (%s bytes > %s bytes); using disk cache only.",
                    payload_size,
                    max_bytes
                )
                cache_payload = None
        except Exception:
            pass

    with shop_sections_cache_lock:
        if cache_payload is None:
            shop_sections_cache['payload'] = None
            shop_sections_cache['limit'] = None
            shop_sections_cache['timestamp'] = 0
            shop_sections_cache['state_token'] = None
            shop_sections_cache['encrypted'] = {}
        else:
            shop_sections_cache['payload'] = cache_payload
            shop_sections_cache['limit'] = limit
            shop_sections_cache['timestamp'] = timestamp
            shop_sections_cache['state_token'] = state_token
            shop_sections_cache['encrypted'] = {}

    if persist_disk:
        _save_shop_sections_cache_to_disk(payload, limit, timestamp, state_token=state_token)

def _summarize_shop_sections_payload(payload):
    summary = {
        'valid': isinstance(payload, dict),
        'size_bytes': _estimate_json_size_bytes(payload),
        'sections': []
    }
    if not isinstance(payload, dict):
        return summary
    sections = payload.get('sections')
    if not isinstance(sections, list):
        return summary
    for section in sections:
        if not isinstance(section, dict):
            continue
        items = section.get('items') or []
        total = section.get('total')
        try:
            total = int(total) if total is not None else len(items)
        except Exception:
            total = len(items)
        summary['sections'].append({
            'id': section.get('id'),
            'title': section.get('title'),
            'items': len(items) if isinstance(items, list) else 0,
            'total': total,
            'truncated': bool(section.get('truncated'))
        })
    return summary

def _read_proc_meminfo_bytes():
    values = {}
    try:
        with open('/proc/self/status', 'r', encoding='utf-8') as fh:
            for line in fh:
                if line.startswith('VmRSS:') or line.startswith('VmSize:'):
                    parts = line.split()
                    if len(parts) >= 2:
                        key = parts[0].rstrip(':')
                        values[key] = int(parts[1]) * 1024
    except Exception:
        pass
    return {
        'rss_bytes': values.get('VmRSS'),
        'vms_bytes': values.get('VmSize')
    }

def _build_shop_sections_payload(limit, full_catalog=False):
    try:
        limit = int(limit or 50)
    except (TypeError, ValueError):
        limit = 50
    limit = max(1, limit)
    ranked_files = (
        db.session.query(
            app_files.c.app_id.label('app_pk'),
            Files.id.label('file_id'),
            Files.filename.label('filename'),
            func.coalesce(Files.size, 0).label('size'),
            func.coalesce(Files.download_count, 0).label('download_count'),
            func.row_number().over(
                partition_by=app_files.c.app_id,
                order_by=(Files.size.desc(), Files.id.desc())
            ).label('row_rank')
        )
        .join(Files, Files.id == app_files.c.file_id)
        .subquery()
    )
    best_files = (
        db.session.query(
            ranked_files.c.app_pk,
            ranked_files.c.file_id,
            ranked_files.c.filename,
            ranked_files.c.size,
            ranked_files.c.download_count,
        )
        .filter(ranked_files.c.row_rank == 1)
        .subquery()
    )
    rows = (
        db.session.query(
            Apps.id.label('app_pk'),
            Apps.app_id.label('app_id'),
            Apps.app_version.label('app_version'),
            Apps.app_type.label('app_type'),
            Titles.title_id.label('title_id'),
            best_files.c.file_id.label('file_id'),
            best_files.c.filename.label('filename'),
            best_files.c.size.label('size'),
            best_files.c.download_count.label('download_count'),
        )
        .outerjoin(Titles, Apps.title_id == Titles.id)
        .outerjoin(best_files, best_files.c.app_pk == Apps.id)
        .filter(Apps.owned.is_(True))
        .filter(best_files.c.file_id.isnot(None))
        .all()
    )

    info_cache = {}

    with titles.titledb_session() as titledb_loaded:
        def _get_info(lookup_id):
            if not titledb_loaded:
                return {}
            key = (lookup_id or '').strip().upper()
            if not key:
                return {}
            if key not in info_cache:
                info_cache[key] = titles.get_game_info(key) or {}
            return info_cache[key]

        def _build_item(row):
            title_id = (row.title_id or '').strip().upper() or None
            app_id = str(row.app_id or '').strip().upper()
            if not app_id:
                return None

            base_info = _get_info(title_id) if title_id else {}
            app_info = base_info
            if row.app_type == APP_TYPE_DLC:
                app_info = _get_info(app_id) or base_info

            if titledb_loaded:
                name = (app_info or {}).get('name') or app_id
                title_name = (base_info or {}).get('name') or name
                category = (base_info or {}).get('category', '')
            else:
                name = title_id or app_id
                title_name = title_id or name
                category = ''
            icon_url = f'/api/shop/icon/{title_id}' if title_id else ((app_info or {}).get('iconUrl') or '')
            # Base-title rating governs the whole title (updates/DLC inherit it).
            rating = _coerce_rating_value((base_info or {}).get('rating'))

            return {
                'name': name,
                'title_name': title_name,
                'title_id': title_id,
                'app_id': app_id,
                'app_version': row.app_version,
                'app_type': row.app_type,
                'category': category,
                'rating': rating,
                'icon_url': icon_url,
                'iconUrl': icon_url,
                'url': f"/api/get_game/{int(row.file_id)}#{row.filename}",
                'size': int(row.size or 0),
                'file_id': int(row.file_id),
                'filename': row.filename,
                'download_count': int(row.download_count or 0)
            }

        base_items = [
            item for item in (_build_item(row) for row in rows if row.app_type == APP_TYPE_BASE)
            if item
        ]
        base_items.sort(key=lambda item: item['file_id'], reverse=True)
        discovery_limit = 40
        new_items = base_items[:discovery_limit]

        recommended_items = sorted(base_items, key=lambda item: item['download_count'], reverse=True)[:discovery_limit]
        if not any(item['download_count'] for item in recommended_items):
            recommended_items = new_items[:discovery_limit]

        all_limit = None
        updates_dlc_limit = None
        if not full_catalog:
            if SHOP_SECTIONS_ALL_ITEMS_CAP is not None:
                cap_value = int(SHOP_SECTIONS_ALL_ITEMS_CAP)
                if not titledb_loaded and SHOP_SECTIONS_ALL_ITEMS_CAP_NO_TITLEDB is not None:
                    cap_value = min(cap_value, int(SHOP_SECTIONS_ALL_ITEMS_CAP_NO_TITLEDB))
                all_limit = max(limit, cap_value)
            updates_dlc_limit = all_limit if all_limit is not None else limit

        latest_update_by_title_id = {}
        for row in rows:
            if row.app_type != APP_TYPE_UPD:
                continue
            title_id = (row.title_id or '').strip().upper()
            if not title_id:
                continue
            version = _safe_int(row.app_version)
            current = latest_update_by_title_id.get(title_id)
            if not current or version > current['version']:
                latest_update_by_title_id[title_id] = {'version': version, 'row': row}

        update_items_full = [
            item
            for item in (_build_item(entry['row']) for entry in latest_update_by_title_id.values())
            if item
        ]
        update_items_full.sort(key=lambda item: _safe_int(item['app_version']), reverse=True)
        if updates_dlc_limit is None:
            update_items = update_items_full
        else:
            update_items = update_items_full[:updates_dlc_limit]

        latest_dlc_by_app_id = {}
        for row in rows:
            if row.app_type != APP_TYPE_DLC:
                continue
            app_id = str(row.app_id or '').strip().upper()
            if not app_id:
                continue
            version = _safe_int(row.app_version)
            current = latest_dlc_by_app_id.get(app_id)
            if not current or version > current['version']:
                latest_dlc_by_app_id[app_id] = {'version': version, 'row': row}

        dlc_items_full = [
            item
            for item in (_build_item(entry['row']) for entry in latest_dlc_by_app_id.values())
            if item
        ]
        dlc_items_full.sort(key=lambda item: _safe_int(item['app_version']), reverse=True)
        if updates_dlc_limit is None:
            dlc_items = dlc_items_full
        else:
            dlc_items = dlc_items_full[:updates_dlc_limit]

        all_total = len(base_items) + len(update_items_full) + len(dlc_items_full)
        all_items = sorted(
            base_items + update_items_full + dlc_items_full,
            key=lambda item: str(item.get('name') or '').lower()
        )
        if all_limit is not None:
            all_items = all_items[:all_limit]

        sections = [
            {'id': 'new', 'title': 'New', 'items': new_items},
            {'id': 'recommended', 'title': 'Recommended', 'items': recommended_items},
            {'id': 'updates', 'title': 'Updates', 'items': update_items},
            {'id': 'dlc', 'title': 'DLC', 'items': dlc_items},
            {
                'id': 'all',
                'title': 'All',
                'items': all_items,
                'total': all_total,
                'truncated': len(all_items) < all_total
            }
        ]
        if full_catalog and bool((app_settings.get('cheats') or {}).get('enabled', True)):
            cheat_items = _build_cyberfoil_cheat_items()
            sections.append({
                'id': 'cheats',
                'title': 'Cheats',
                'items': cheat_items,
                'total': len(cheat_items),
                'truncated': False,
            })
        return {
            'sections': sections
        }


def _build_cyberfoil_cheat_items():
    """Return versioned cheat entries for the CyberFoil catalogue.

    Entries deliberately carry a normal URL/size pair, making them browseable by
    current clients while providing the title/build metadata newer clients need to
    place a file in Atmosphere's cheats directory.
    """
    owned_title_ids = {
        str(row[0] or '').upper()
        for row in (
            db.session.query(Titles.title_id)
            .join(Apps, Apps.title_id == Titles.id)
            .filter(Apps.owned.is_(True), Apps.app_type == APP_TYPE_BASE)
            .distinct()
            .all()
        )
    }
    items = []
    with titles.titledb_session() as titledb_loaded:
        for cheat in cheats.list_cheats():
            title_id = cheat['title_id']
            if title_id not in owned_title_ids:
                continue
            info = titles.get_game_info(title_id) if titledb_loaded else {}
            name = str((info or {}).get('name') or title_id)
            build_id = cheat['build_id']
            icon_url = f'/api/shop/icon/{title_id}'
            items.append({
                'name': f'{name} — {build_id}',
                'title_name': name,
                'title_id': title_id,
                'build_id': build_id,
                'app_type': 'CHEAT',
                'category': 'Cheats',
                'icon_url': icon_url,
                'iconUrl': icon_url,
                'url': f'/api/cheats/{title_id}/{build_id}',
                'size': int(cheat['size']),
                'filename': f'{build_id}.txt',
                'note': str(cheat.get('note') or ''),
            })
    return sorted(items, key=lambda item: (item['title_name'].lower(), item['build_id']))

def _refresh_shop_sections_cache(limit):
    global shop_sections_refresh_running
    with shop_sections_refresh_lock:
        if shop_sections_refresh_running:
            return
        shop_sections_refresh_running = True

    def _run():
        global shop_sections_refresh_running
        try:
            with app.app_context():
                now = time.time()
                state_token = _get_titledb_aware_state_token()
                payload = _build_shop_sections_payload(limit)
                _store_shop_sections_cache(payload, limit, now, state_token, persist_disk=True)
        finally:
            with shop_sections_refresh_lock:
                shop_sections_refresh_running = False

    thread = threading.Thread(target=_run, daemon=True)
    thread.start()

# Configure logging
# Get log level from environment variable, default to INFO
log_level_str = os.environ.get('LOG_LEVEL', 'INFO').upper()
log_level_map = {
    'DEBUG': logging.DEBUG,
    'INFO': logging.INFO,
    'WARNING': logging.WARNING,
    'ERROR': logging.ERROR,
    'CRITICAL': logging.CRITICAL,
}
log_level = log_level_map.get(log_level_str, logging.INFO)

formatter = ColoredFormatter(
    '[%(asctime)s.%(msecs)03d] %(levelname)s (%(module)s) %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S',
)
handler = logging.StreamHandler(sys.stdout)
handler.setFormatter(formatter)

logging.basicConfig(
    level=log_level,
    handlers=[handler]
)

# Create main logger
logger = logging.getLogger('main')
logger.setLevel(log_level)

# Apply filter to hide date from http access logs
logging.getLogger('werkzeug').addFilter(FilterRemoveDateFromWerkzeugLogs())

# Suppress specific Alembic INFO logs
logging.getLogger('alembic.runtime.migration').setLevel(logging.WARNING)

def _configure_upload_tempdir():
    configured = (
        os.environ.get('AEROFOIL_UPLOAD_TMP_DIR')
        or os.environ.get('OWNFOIL_UPLOAD_TMP_DIR')
        or os.path.join(DATA_DIR, 'tmp', 'uploads')
    )
    upload_tmp_dir = str(configured).strip()
    if not upload_tmp_dir:
        return
    try:
        os.makedirs(upload_tmp_dir, exist_ok=True)
        tempfile.tempdir = upload_tmp_dir
        # Keep environment hints aligned for subprocesses/libs that inspect these.
        os.environ['TMPDIR'] = upload_tmp_dir
        os.environ['TMP'] = upload_tmp_dir
        os.environ['TEMP'] = upload_tmp_dir
        logger.info('Using upload temp directory: %s', upload_tmp_dir)
    except Exception:
        logger.exception('Failed to configure upload temp directory: %s', upload_tmp_dir)

_configure_upload_tempdir()

# API response helper functions for consistent error handling
def api_error(message, status_code=400, error_code=None):
    """Return a standardized error response."""
    response = {'success': False, 'message': message}
    if error_code:
        response['error_code'] = error_code
    return jsonify(response), status_code

def api_success(data=None, message=None):
    """Return a standardized success response."""
    response = {'success': True}
    if data:
        response.update(data)
    if message:
        response['message'] = message
    return jsonify(response)

# Input validation constants and helpers
MAX_UPLOAD_SIZE = 100 * 1024 * 1024  # 100MB for keys.txt files
MAX_LIBRARY_UPLOAD_SIZE = 64 * 1024 * 1024 * 1024  # 64GB for game files
MAX_SAVE_UPLOAD_SIZE = 4 * 1024 * 1024 * 1024  # 4GB for save archives
# Leave room for multipart form overhead beyond the file payload itself.
DEFAULT_WSGI_MAX_REQUEST_BODY_SIZE = MAX_LIBRARY_UPLOAD_SIZE + (128 * 1024 * 1024)
ACTIVITY_API_MAX_LIMIT = _read_int_env(
    'AEROFOIL_ACTIVITY_API_MAX_LIMIT',
    _read_int_env('OWNFOIL_ACTIVITY_API_MAX_LIMIT', 10000, minimum=100, maximum=200000),
    minimum=100,
    maximum=200000,
)
CLIENTS_HISTORY_API_MAX_LIMIT = _read_int_env(
    'AEROFOIL_CLIENTS_HISTORY_API_MAX_LIMIT',
    _read_int_env('OWNFOIL_CLIENTS_HISTORY_API_MAX_LIMIT', 20000, minimum=100, maximum=200000),
    minimum=100,
    maximum=200000,
)
CLIENTS_HISTORY_CSV_MAX_LIMIT = _read_int_env(
    'AEROFOIL_CLIENTS_HISTORY_CSV_MAX_LIMIT',
    _read_int_env('OWNFOIL_CLIENTS_HISTORY_CSV_MAX_LIMIT', 50000, minimum=100, maximum=200000),
    minimum=100,
    maximum=200000,
)
SAVE_SYNC_DIR = os.path.join(DATA_DIR, 'saves')
MAX_TITLE_ID_LENGTH = 16
MAX_SAVE_NOTE_LENGTH = 120
MAX_SAVE_ID_LENGTH = 96
SAVE_ID_RE = re.compile(r'^[A-Za-z0-9._-]+$')

def validate_title_id(title_id):
    """Validate title_id format (should be 16 hex characters)."""
    if not title_id:
        return False, "Title ID is required"
    title_id = title_id.strip().upper()
    if len(title_id) != MAX_TITLE_ID_LENGTH:
        return False, f"Title ID must be {MAX_TITLE_ID_LENGTH} characters"
    if not all(c in '0123456789ABCDEF' for c in title_id):
        return False, "Title ID must contain only hexadecimal characters"
    return True, title_id

def validate_file_size(file_size):
    """Validate file size against maximum upload limit (for keys.txt files)."""
    if file_size is None:
        return False, "File size is unknown"
    if file_size > MAX_UPLOAD_SIZE:
        return False, f"File size exceeds maximum limit of {MAX_UPLOAD_SIZE // (1024*1024)}MB"
    return True, None

def validate_library_file_size(file_size):
    """Validate file size against maximum library upload limit (for game files)."""
    if file_size is None:
        return False, "File size is unknown"
    if file_size > MAX_LIBRARY_UPLOAD_SIZE:
        return False, f"File size exceeds maximum limit of {MAX_LIBRARY_UPLOAD_SIZE // (1024*1024*1024)}GB"
    return True, None


def _normalize_save_title_id(raw_title_id):
    title_id = str(raw_title_id or '').strip().upper()
    if title_id.startswith('0X'):
        title_id = title_id[2:]
    if title_id.endswith('.ZIP'):
        title_id = title_id[:-4]
    if len(title_id) != MAX_TITLE_ID_LENGTH:
        return None
    if not all(c in '0123456789ABCDEF' for c in title_id):
        return None
    return title_id


def _resolve_save_sync_user():
    user = None
    try:
        if current_user.is_authenticated:
            user = current_user
    except Exception:
        user = None

    if user is None:
        auth = request.authorization
        if not auth or not auth.username or not auth.password:
            return None, 'Save sync requires username/password authentication.', 401

        user = User.query.filter_by(user=auth.username).first()
        if user is None or not check_password_hash(user.password, auth.password):
            return None, 'Invalid save sync credentials.', 401

    if bool(getattr(user, 'frozen', False)):
        message = (getattr(user, 'frozen_message', None) or '').strip() or 'Account is frozen.'
        return None, message, 403

    if not user.has_shop_access():
        username = str(getattr(user, 'user', '') or '').strip() or 'unknown'
        return None, f'User "{username}" does not have access to the shop.', 403

    if not bool(getattr(user, 'backup_access', False)):
        return None, 'Backup access is required for save sync.', 403

    return user, None, None


def _save_sync_user_dir(user):
    user_name = str(getattr(user, 'user', '') or '').strip()
    user_key = secure_filename(user_name)
    user_id = getattr(user, 'id', None)
    if not user_key and user_id is not None:
        user_key = secure_filename(str(user_id))
    if not user_key:
        user_key = 'unknown'

    return os.path.join(SAVE_SYNC_DIR, user_key)


def _normalize_save_id(raw_save_id):
    save_id = secure_filename(str(raw_save_id or '').strip())
    if save_id.lower().endswith('.zip'):
        save_id = save_id[:-4]
    if not save_id or len(save_id) > MAX_SAVE_ID_LENGTH:
        return None
    if not SAVE_ID_RE.match(save_id):
        return None
    return save_id


def _normalize_save_note(raw_note):
    note = ' '.join(str(raw_note or '').split()).strip()
    if len(note) > MAX_SAVE_NOTE_LENGTH:
        note = note[:MAX_SAVE_NOTE_LENGTH].rstrip()
    return note


def _save_sync_resolve_note():
    for key in ('note', 'save_note', 'saveNote'):
        value = request.form.get(key)
        if value is not None:
            return _normalize_save_note(value)
    return ''


def _save_sync_title_dir(user, title_id):
    return os.path.join(_save_sync_user_dir(user), title_id)


def _save_sync_latest_dir(user, title_id):
    return os.path.join(_save_sync_title_dir(user, title_id), 'latest')


def _save_sync_latest_archive_path(user, title_id):
    return os.path.join(_save_sync_title_dir(user, title_id), '_latest.zip')


def _save_sync_archive_path(user, title_id, save_id=None):
    if save_id:
        return os.path.join(_save_sync_title_dir(user, title_id), f'{save_id}.zip')
    # Legacy single-save path.
    return os.path.join(_save_sync_user_dir(user), f'{title_id}.zip')


def _save_sync_metadata_path(user, title_id, save_id):
    return os.path.join(_save_sync_title_dir(user, title_id), f'{save_id}.json')


def _save_sync_format_created_at(created_ts):
    try:
        ts = int(created_ts or 0)
    except Exception:
        ts = 0
    if ts <= 0:
        ts = int(time.time())
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(ts))


def _save_sync_parse_created_ts(raw_value):
    if raw_value is None:
        return 0
    try:
        import datetime as dt_mod

        if isinstance(raw_value, (int, float)):
            value = int(raw_value)
            return value if value > 0 else 0
        text = str(raw_value).strip()
        if not text:
            return 0
        if text.isdigit():
            value = int(text)
            return value if value > 0 else 0
        if text.endswith('Z'):
            dt = dt_mod.datetime.strptime(text, '%Y-%m-%dT%H:%M:%SZ')
            return int(dt.timestamp())
        dt = dt_mod.datetime.fromisoformat(text)
        return int(dt.timestamp())
    except Exception:
        return 0


def _save_sync_generate_save_id(note=''):
    timestamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    nonce = secrets.token_hex(3)
    note_token = secure_filename(note or '').strip('._-')
    if note_token:
        note_token = note_token[:32]
        return f'{timestamp}_{nonce}_{note_token}'
    return f'{timestamp}_{nonce}'


def _save_sync_read_metadata(path):
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            data = json.load(handle)
            if isinstance(data, dict):
                return data
    except Exception:
        pass
    return {}


def _save_sync_write_metadata(path, data):
    temp_path = path + '.tmp'
    with open(temp_path, 'w', encoding='utf-8') as handle:
        json.dump(data, handle, ensure_ascii=False, separators=(',', ':'))
    os.replace(temp_path, path)


def _save_sync_safe_extract_zip(archive_path, dest_dir):
    with zipfile.ZipFile(archive_path, 'r') as archive:
        names = archive.namelist()
        if not names:
            raise ValueError('Save archive is empty.')
        os.makedirs(dest_dir, exist_ok=True)
        dest_root = os.path.abspath(dest_dir)
        for member in archive.infolist():
            member_name = str(member.filename or '')
            if not member_name or member_name.endswith('/'):
                continue
            normalized = member_name.replace('\\', '/')
            target_path = os.path.abspath(os.path.normpath(os.path.join(dest_root, normalized)))
            if not (target_path == dest_root or target_path.startswith(dest_root + os.sep)):
                raise ValueError('Save archive contains invalid path traversal entry.')
            parent_dir = os.path.dirname(target_path)
            os.makedirs(parent_dir, exist_ok=True)
            with archive.open(member, 'r') as src, open(target_path, 'wb') as dst:
                shutil.copyfileobj(src, dst)


def _save_sync_clear_directory(path):
    if not os.path.isdir(path):
        return
    for entry in os.listdir(path):
        entry_path = os.path.join(path, entry)
        try:
            if os.path.isdir(entry_path):
                shutil.rmtree(entry_path)
            else:
                os.remove(entry_path)
        except Exception:
            continue


def _save_sync_refresh_latest_from_archive(user, title_id, archive_path):
    latest_dir = _save_sync_latest_dir(user, title_id)
    os.makedirs(latest_dir, exist_ok=True)
    temp_dir = os.path.join(_save_sync_title_dir(user, title_id), '.latest_tmp')
    if os.path.isdir(temp_dir):
        shutil.rmtree(temp_dir, ignore_errors=True)
    os.makedirs(temp_dir, exist_ok=True)
    try:
        _save_sync_safe_extract_zip(archive_path, temp_dir)
        _save_sync_clear_directory(latest_dir)
        for entry in os.listdir(temp_dir):
            src = os.path.join(temp_dir, entry)
            dst = os.path.join(latest_dir, entry)
            os.replace(src, dst)
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def _save_sync_build_archive_from_directory(source_dir, archive_path):
    if not os.path.isdir(source_dir):
        raise ValueError('Latest save directory does not exist.')

    started_at = time.time()
    temp_archive = archive_path + '.tmp'
    if os.path.exists(temp_archive):
        os.remove(temp_archive)

    try:
        with zipfile.ZipFile(temp_archive, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
            has_files = False
            file_count = 0
            for root, _dirs, files in os.walk(source_dir):
                for filename in files:
                    abs_path = os.path.join(root, filename)
                    rel_path = os.path.relpath(abs_path, source_dir)
                    archive.write(abs_path, arcname=rel_path)
                    has_files = True
                    file_count += 1
            if not has_files:
                raise ValueError('Latest save directory is empty.')
        os.replace(temp_archive, archive_path)
        elapsed_ms = int((time.time() - started_at) * 1000)
        archive_size = 0
        try:
            archive_size = int(os.path.getsize(archive_path))
        except Exception:
            archive_size = 0
        logger.info(
            'Save latest archive generated source=%s archive=%s files=%s bytes=%s elapsed_ms=%s',
            source_dir,
            archive_path,
            file_count,
            archive_size,
            elapsed_ms,
        )
    except Exception:
        try:
            if os.path.exists(temp_archive):
                os.remove(temp_archive)
        except Exception:
            pass
        raise


def _save_sync_refresh_latest_for_title(user, title_id):
    versions = _save_sync_collect_versions_for_title(user, title_id)
    latest_archive = None
    for version in versions:
        archive_path = str(version.get('archive_path') or '')
        if archive_path and os.path.isfile(archive_path):
            latest_archive = archive_path
            break
    latest_dir = _save_sync_latest_dir(user, title_id)
    latest_archive_path = _save_sync_latest_archive_path(user, title_id)
    if not latest_archive:
        _save_sync_clear_directory(latest_dir)
        try:
            if os.path.isfile(latest_archive_path):
                os.remove(latest_archive_path)
        except Exception:
            pass
        return
    _save_sync_refresh_latest_from_archive(user, title_id, latest_archive)


def _save_sync_collect_versions_for_title(user, title_id):
    versions = []
    title_dir = _save_sync_title_dir(user, title_id)
    if os.path.isdir(title_dir):
        try:
            for filename in sorted(os.listdir(title_dir)):
                if not filename.lower().endswith('.zip'):
                    continue
                if filename == '_latest.zip':
                    continue
                save_id = _normalize_save_id(filename[:-4])
                if not save_id:
                    continue
                archive_path = os.path.join(title_dir, filename)
                if not os.path.isfile(archive_path):
                    continue

                try:
                    size = int(os.path.getsize(archive_path))
                except Exception:
                    size = 0

                meta = _save_sync_read_metadata(_save_sync_metadata_path(user, title_id, save_id))
                created_ts = _save_sync_parse_created_ts(meta.get('created_ts'))
                if created_ts <= 0:
                    created_ts = _save_sync_parse_created_ts(meta.get('createdAt'))
                if created_ts <= 0:
                    created_ts = _save_sync_parse_created_ts(meta.get('created_at'))
                if created_ts <= 0:
                    try:
                        created_ts = int(os.path.getmtime(archive_path))
                    except Exception:
                        created_ts = int(time.time())

                created_at = str(meta.get('created_at') or meta.get('createdAt') or '').strip()
                if not created_at:
                    created_at = _save_sync_format_created_at(created_ts)

                note = _normalize_save_note(meta.get('note'))
                versions.append({
                    'title_id': title_id,
                    'save_id': save_id,
                    'size': size,
                    'note': note,
                    'created_ts': int(created_ts),
                    'created_at': created_at,
                    'download_url': f'/api/saves/download/{title_id}/{save_id}.zip',
                    'delete_url': f'/api/saves/delete/{title_id}/{save_id}',
                    'archive_path': archive_path,
                    'legacy': False,
                })
        except Exception as e:
            logger.warning('Failed listing versioned saves for title %s: %s', title_id, e)

    legacy_archive = _save_sync_archive_path(user, title_id)
    if os.path.isfile(legacy_archive):
        try:
            legacy_size = int(os.path.getsize(legacy_archive))
        except Exception:
            legacy_size = 0
        try:
            legacy_created_ts = int(os.path.getmtime(legacy_archive))
        except Exception:
            legacy_created_ts = int(time.time())
        versions.append({
            'title_id': title_id,
            'save_id': 'legacy',
            'size': legacy_size,
            'note': '',
            'created_ts': legacy_created_ts,
            'created_at': _save_sync_format_created_at(legacy_created_ts),
            'download_url': f'/api/saves/download/{title_id}.zip',
            'delete_url': f'/api/saves/delete/{title_id}',
            'archive_path': legacy_archive,
            'legacy': True,
        })

    versions.sort(key=lambda item: (-(int(item.get('created_ts') or 0)), str(item.get('save_id') or '')))
    return versions


def _save_sync_collect_versions(user):
    user_dir = _save_sync_user_dir(user)
    os.makedirs(user_dir, exist_ok=True)

    title_ids = set()
    try:
        for name in os.listdir(user_dir):
            title_id = _normalize_save_title_id(name)
            if not title_id:
                continue
            path = os.path.join(user_dir, name)
            if os.path.isdir(path) or (os.path.isfile(path) and name.lower().endswith('.zip')):
                title_ids.add(title_id)
    except Exception as e:
        logger.warning('Failed reading save sync directory for user %s: %s', getattr(user, 'user', '?'), e)

    saves = []
    for title_id in sorted(title_ids):
        saves.extend(_save_sync_collect_versions_for_title(user, title_id))

    saves.sort(key=lambda item: (str(item.get('title_id') or ''), -(int(item.get('created_ts') or 0)), str(item.get('save_id') or '')))
    return saves


def _save_sync_resolve_download_archive(user, title_id, save_id=None):
    latest_archive_path = _save_sync_latest_archive_path(user, title_id)
    wants_generated_latest = (save_id is None) or (str(save_id).strip().lower() == 'latest')
    if wants_generated_latest:
        latest_dir = _save_sync_latest_dir(user, title_id)
        if os.path.isdir(latest_dir):
            try:
                _save_sync_build_archive_from_directory(latest_dir, latest_archive_path)
            except Exception as e:
                logger.warning(
                    'Failed generating latest save archive for user %s title %s from latest directory: %s',
                    getattr(user, 'user', '?'),
                    title_id,
                    e,
                )
    if wants_generated_latest and os.path.isfile(latest_archive_path):
        latest_size = 0
        latest_created_ts = int(time.time())
        try:
            latest_size = int(os.path.getsize(latest_archive_path))
        except Exception:
            latest_size = 0
        try:
            latest_created_ts = int(os.path.getmtime(latest_archive_path))
        except Exception:
            latest_created_ts = int(time.time())
        return {
            'title_id': title_id,
            'save_id': 'latest',
            'size': latest_size,
            'note': 'latest',
            'created_ts': latest_created_ts,
            'created_at': _save_sync_format_created_at(latest_created_ts),
            'download_url': f'/api/saves/download/{title_id}.zip',
            'delete_url': '',
            'archive_path': latest_archive_path,
            'legacy': False,
            'generated_latest': True,
        }, None

    versions = _save_sync_collect_versions_for_title(user, title_id)
    if not versions:
        return None, 'Save archive not found.'
    if save_id:
        normalized_save_id = _normalize_save_id(save_id)
        if not normalized_save_id:
            return None, 'Invalid save_id for save download.'
        for version in versions:
            if str(version.get('save_id') or '') == normalized_save_id:
                return version, None
        return None, 'Save archive not found.'
    return versions[0], None


def _save_sync_delete_archive(user, title_id, save_id=None):
    selected_archive, resolve_error = _save_sync_resolve_download_archive(user, title_id, save_id=save_id)
    if selected_archive is None:
        return None, resolve_error or 'Save archive not found.'

    archive_path = str(selected_archive.get('archive_path') or '')
    if not archive_path or not os.path.isfile(archive_path):
        return None, 'Save archive not found.'

    selected_save_id = str(selected_archive.get('save_id') or '').strip()
    is_legacy = bool(selected_archive.get('legacy'))
    try:
        os.remove(archive_path)
    except FileNotFoundError:
        return None, 'Save archive not found.'
    except Exception as e:
        logger.error('Failed deleting save archive for user %s title %s save %s: %s', getattr(user, 'user', '?'), title_id, selected_save_id or '-', e)
        return None, 'Failed to delete save archive.'

    if not is_legacy and selected_save_id:
        try:
            metadata_path = _save_sync_metadata_path(user, title_id, selected_save_id)
            if os.path.isfile(metadata_path):
                os.remove(metadata_path)
        except Exception as e:
            logger.warning('Failed deleting save metadata for user %s title %s save %s: %s', getattr(user, 'user', '?'), title_id, selected_save_id, e)

        title_dir = _save_sync_title_dir(user, title_id)
        try:
            if os.path.isdir(title_dir) and not os.listdir(title_dir):
                os.rmdir(title_dir)
        except Exception:
            pass

    return {
        'title_id': title_id,
        'save_id': selected_save_id or '',
        'legacy': is_legacy,
    }, None


def _save_sync_resolve_title_id(route_title_id=None):
    route_value = _normalize_save_title_id(route_title_id)
    if route_value:
        return route_value

    form_candidates = [
        request.form.get('title_id'),
        request.form.get('titleId'),
        request.form.get('application_id'),
        request.form.get('app_id'),
    ]
    for candidate in form_candidates:
        normalized = _normalize_save_title_id(candidate)
        if normalized:
            return normalized
    return None


def save_sync_access(f):
    @wraps(f)
    def _save_sync_access(*args, **kwargs):
        user, error, status = _resolve_save_sync_user()
        if user is None:
            return api_error(error or 'Save sync authorization failed.', status or 403)
        g.save_sync_user = user
        return f(*args, **kwargs)
    return _save_sync_access

@login_manager.user_loader
def load_user(user_id):
    # since the user_id is just the primary key of our user table, use it in the query for the user
    return User.query.filter_by(id=user_id).first()

def reload_conf():
    global app_settings
    global watcher
    app_settings = load_settings()

def _maybe_sync_request_settings():
    global app_settings
    global request_settings_last_sync_ts

    interval = REQUEST_SETTINGS_SYNC_INTERVAL_S
    if interval is None:
        return

    now = time.time()
    if interval > 0 and (now - float(request_settings_last_sync_ts or 0.0)) < interval:
        return

    with request_settings_sync_lock:
        now = time.time()
        if interval > 0 and (now - float(request_settings_last_sync_ts or 0.0)) < interval:
            return
        app_settings = load_settings()
        request_settings_last_sync_ts = now

def _maybe_remove_missing_files_from_db(force=False):
    global missing_files_last_run_ts
    interval = MISSING_FILES_SWEEP_INTERVAL_S
    if interval is None and not force:
        return

    now = time.time()
    if (not force) and interval and interval > 0:
        if (now - float(missing_files_last_run_ts or 0.0)) < float(interval):
            return

    if not missing_files_sweep_lock.acquire(blocking=False):
        return
    try:
        now = time.time()
        if (not force) and interval and interval > 0:
            if (now - float(missing_files_last_run_ts or 0.0)) < float(interval):
                return
        remove_missing_files_from_db()
        missing_files_last_run_ts = time.time()
    finally:
        missing_files_sweep_lock.release()

def on_library_change(events):
    # TODO refactor: group modified and created together
    with app.app_context():
        has_changes = False
        created_events = [e for e in events if e.type == 'created']
        modified_events = [e for e in events if e.type != 'created']

        deleted_paths = []
        for event in modified_events:
            if event.type == 'moved':
                moved_outside_library = not event.dest_path or not event.dest_path.startswith(event.directory)
                if moved_outside_library:
                    deleted_paths.append(event.src_path)
                    continue
                if file_exists_in_db(event.src_path):
                    # update the path
                    update_file_path(event.directory, event.src_path, event.dest_path)
                    has_changes = True
                else:
                    # add to the database
                    event.src_path = event.dest_path
                    created_events.append(event)

            elif event.type == 'deleted':
                deleted_paths.append(event.src_path)

            elif event.type == 'modified':
                # can happen if file copy has started before the app was running
                if file_exists_in_db(event.src_path):
                    continue
                add_files_to_library(event.directory, [event.src_path])
                has_changes = True

        if deleted_paths:
            # One transaction for the whole event batch: per-event deletes paid
            # an existence query plus a commit (and fsync) per file, which made
            # mass deletions crawl through the watcher one file at a time.
            unique_deleted = list(dict.fromkeys(deleted_paths))
            try:
                deleted_count, apps_updated = delete_files_by_filepaths_batch(unique_deleted, commit=True)
            except Exception as e:
                # Keep the watcher thread alive; the periodic scan reconciles
                # anything this batch failed to remove.
                db.session.rollback()
                logger.error(f"Failed to remove deleted files from the database: {e}")
                deleted_count, apps_updated = 0, 0
            if deleted_count > 0:
                has_changes = True
                logger.info(
                    f"Removed {deleted_count} deleted files from the database "
                    f"({apps_updated} app references updated)."
                )

        if created_events:
            directories = list(set(e.directory for e in created_events))
            for library_path in directories:
                new_files = [e.src_path for e in created_events if e.directory == library_path]
                add_files_to_library(library_path, new_files)
                if new_files:
                    has_changes = True

    if has_changes:
        post_library_change()

def create_app():
    app = Flask(__name__)
    app.config["SQLALCHEMY_DATABASE_URI"] = AEROFOIL_DB
    static_max_age = _read_int_env('AEROFOIL_STATIC_MAX_AGE_S', 3600, minimum=0, maximum=31536000)
    static_max_age = _read_int_env('OWNFOIL_STATIC_MAX_AGE_S', static_max_age, minimum=0, maximum=31536000)
    app.config['SEND_FILE_MAX_AGE_DEFAULT'] = int(static_max_age)
    # Generate secret key from environment variable or create random one
    secret_key = os.getenv('AEROFOIL_SECRET_KEY') or os.getenv('OWNFOIL_SECRET_KEY')
    if not secret_key:
        secret_key = secrets.token_hex(32)
        logger.warning('SECRET_KEY not set in environment. Generated random key. Set AEROFOIL_SECRET_KEY for production.')
    app.config['SECRET_KEY'] = secret_key
    app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False

    db.init_app(app)
    migrate.init_app(app, db)
    login_manager.init_app(app)

    app.register_blueprint(auth_blueprint)

    return app


# Create app
app = create_app()


@app.context_processor
def inject_static_asset_version():
    """Make template assets refresh after an in-place application update."""
    try:
        version = os.stat(os.path.join(app.static_folder, 'style.css')).st_mtime_ns
    except OSError:
        version = None
    return {'static_asset_version': version}


@app.errorhandler(RequestEntityTooLarge)
def handle_request_entity_too_large(_error):
    return api_error(
        f"Upload too large. Maximum allowed is {MAX_LIBRARY_UPLOAD_SIZE // (1024 * 1024 * 1024)}GB per file.",
        413
    )


@app.before_request
def _block_permanent_blacklist_requests():
    try:
        settings = {}
        try:
            settings = load_settings()
        except Exception:
            settings = {}
        auth_config = _get_auth_protection_config(settings)
        client_ip = _effective_client_ip(settings)
        geo = {}
        if client_ip and not _is_private_ip(client_ip):
            try:
                geo = lookup_geoip(client_ip) or {}
            except Exception:
                geo = {}

        if _is_permanently_blocked_ip(client_ip, auth_config):
            try:
                _log_access_dedup(
                    kind='permanent_ip_blocked',
                    dedupe_key=f"{client_ip}|{request.path}",
                    ok=False,
                    status_code=404,
                    filename=request.path,
                    remote_addr=client_ip,
                    user_agent=request.headers.get('User-Agent'),
                    country=geo.get('country'),
                    country_code=geo.get('country_code'),
                    region=geo.get('region'),
                    city=geo.get('city'),
                    latitude=geo.get('latitude'),
                    longitude=geo.get('longitude'),
                )
            except Exception:
                pass
            return Response(status=404)

        blocked_country_codes = {
            str(code or '').strip().upper()
            for code in ((settings.get('security') or {}).get('auth_blocked_country_codes') or [])
            if str(code or '').strip()
        }
        allowed_country_codes = {
            str(code or '').strip().upper()
            for code in ((settings.get('security') or {}).get('auth_allowed_country_codes') or [])
            if str(code or '').strip()
        }
        country_code = str(geo.get('country_code') or '').strip().upper()
        if blocked_country_codes and country_code and country_code in blocked_country_codes:
            try:
                _log_access_dedup(
                    kind='country_blocked',
                    dedupe_key=f"{client_ip}|{request.path}|{country_code}",
                    ok=False,
                    status_code=404,
                    filename=request.path,
                    remote_addr=client_ip,
                    user_agent=request.headers.get('User-Agent'),
                    country=geo.get('country'),
                    country_code=country_code,
                    region=geo.get('region'),
                    city=geo.get('city'),
                    latitude=geo.get('latitude'),
                    longitude=geo.get('longitude'),
                )
            except Exception:
                pass
            return Response(status=404)
        if allowed_country_codes and country_code and country_code not in allowed_country_codes:
            try:
                _log_access_dedup(
                    kind='country_not_whitelisted',
                    dedupe_key=f"{client_ip}|{request.path}|{country_code}|allow",
                    ok=False,
                    status_code=404,
                    filename=request.path,
                    remote_addr=client_ip,
                    user_agent=request.headers.get('User-Agent'),
                    country=geo.get('country'),
                    country_code=country_code,
                    region=geo.get('region'),
                    city=geo.get('city'),
                    latitude=geo.get('latitude'),
                    longitude=geo.get('longitude'),
                )
            except Exception:
                pass
            return Response(status=404)
    except Exception:
        return None
    return None


@app.before_request
def _block_frozen_web_ui():
    """Frozen accounts should only see the MOTD page in the web UI."""
    try:
        # Let Tinfoil/Cyberfoil flows be handled by tinfoil_access.
        if _is_shop_client_request():
            return None

        if not current_user.is_authenticated:
            return None

        if not bool(getattr(current_user, 'frozen', False)):
            return None

        path = request.path or '/'
        if path.startswith('/static/'):
            return None
        if path in ('/login', '/logout'):
            return None

        message = (getattr(current_user, 'frozen_message', None) or '').strip() or 'Account is frozen.'
        if path.startswith('/api/'):
            return jsonify({'success': False, 'error': message}), 403
        return render_template('frozen.html', title='Library', message=message)
    except Exception:
        return None


_active_transfers_lock = threading.Lock()
_active_transfers = {}

_connected_clients_lock = threading.Lock()
_connected_clients = {}

_recent_access_lock = threading.Lock()
_recent_access = {}

_CLIENT_SEEN_META_PREFIX = 'client_meta:'

_transfer_sessions_lock = threading.Lock()
_transfer_sessions = {}

_transfer_finalize_timers_lock = threading.Lock()
_transfer_finalize_timers = {}

_TRANSFER_FINALIZE_GRACE_S = 30
_ACTIVE_TRANSFER_STALE_S = 300


def _get_request_user():
    try:
        if current_user.is_authenticated:
            return current_user.user
    except Exception:
        return None
    auth = request.authorization
    if auth and auth.username:
        return auth.username
    return None


# --- ESRB / age content filter ---------------------------------------------

def _content_filter_block_unrated():
    try:
        settings = load_settings()
        return bool((settings or {}).get('content_filter', {}).get('block_unrated', True))
    except Exception:
        return True


def _coerce_rating_value(rating):
    """Coerce a rating to a non-negative int age, or None if unknown/unrated."""
    if rating is None:
        return None
    try:
        value = int(rating)
    except (TypeError, ValueError):
        return None
    return value if value >= 0 else None


def _title_rating(title_id):
    """Return the ESRB minimum-age int for a title_id, or None if unknown.

    Opens its own TitleDB session; intended for single-title checks (e.g. the
    download gate). List builders should reuse an open session instead.
    """
    tid = str(title_id or '').strip().upper()
    if not tid:
        return None
    try:
        with titles.titledb_session() as titledb_loaded:
            if not titledb_loaded:
                return None
            info = titles.get_game_info(tid) or {}
    except Exception:
        return None
    return _coerce_rating_value(info.get('rating'))


def _title_allowed(cap, rating, block_unrated):
    """Whether a title is visible/downloadable under an age cap.

    cap is None        -> unrestricted (always allowed)
    rating is None      -> allowed only when not block_unrated (fail-closed)
    otherwise           -> allowed when rating <= cap
    """
    if cap is None:
        return True
    if rating is None:
        return not bool(block_unrated)
    try:
        return int(rating) <= int(cap)
    except (TypeError, ValueError):
        return not bool(block_unrated)


def _user_rating_cap(username=None):
    """Resolve (cap, block_unrated) for the requesting (or named) user.

    cap is the user's max_rating int, or None when unrestricted/unknown user.
    """
    block_unrated = _content_filter_block_unrated()
    user = None
    try:
        if username is None:
            try:
                if current_user.is_authenticated:
                    user = current_user
            except Exception:
                user = None
            if user is None:
                username = _get_request_user()
        if user is None and username:
            user = User.query.filter_by(user=username).first()
        cap = getattr(user, 'max_rating', None) if user is not None else None
    except Exception:
        cap = None
    try:
        cap = int(cap) if cap is not None else None
    except (TypeError, ValueError):
        cap = None
    return cap, block_unrated


def _file_title_ids(file_id):
    """All distinct title_ids associated with a file (multicontent-safe)."""
    rows = (
        db.session.query(Titles.title_id)
        .select_from(Files)
        .outerjoin(app_files, app_files.c.file_id == Files.id)
        .outerjoin(Apps, Apps.id == app_files.c.app_id)
        .outerjoin(Titles, Titles.id == Apps.title_id)
        .filter(Files.id == file_id)
        .all()
    )
    seen = []
    for row in rows:
        tid = (row[0] or '').strip().upper()
        if tid and tid not in seen:
            seen.append(tid)
    return seen


def _file_blocked_by_cap(file_id, cap, block_unrated):
    """True if a file must be hidden/blocked for the given age cap.

    Gates on the most restrictive associated title (fail-closed): an unidentified
    file, or any title that is unrated/over-cap, blocks the whole file.
    """
    if cap is None:
        return False
    title_ids = _file_title_ids(file_id)
    if not title_ids:
        return bool(block_unrated)
    with titles.titledb_session() as titledb_loaded:
        for tid in title_ids:
            rating = None
            if titledb_loaded:
                info = titles.get_game_info(tid) or {}
                rating = _coerce_rating_value(info.get('rating'))
            if not _title_allowed(cap, rating, block_unrated):
                return True
    return False


def _blocked_title_ids_for_cap(cap, block_unrated):
    """Set of library title_ids that must be hidden for the given age cap.

    Backed by the per-state-token titles metadata cache (rating_by_title_id),
    so this is cheap to call per request.
    """
    if cap is None:
        return set()
    metadata = _get_cached_titles_metadata()
    rating_by_title_id = metadata.get('rating_by_title_id') or {}
    blocked = set()
    for tid, rating in rating_by_title_id.items():
        if not _title_allowed(cap, _coerce_rating_value(rating), block_unrated):
            blocked.add(tid)
    return blocked


def _allowed_title_ids_for_cap(cap):
    """Return TitleDB-rated library title IDs at or below ``cap``.

    Used for fail-closed browse filtering: titles absent from the metadata cache
    are unrated and therefore must not be shown to capped users.
    """
    if cap is None:
        return set()
    metadata = _get_cached_titles_metadata()
    rating_by_title_id = metadata.get('rating_by_title_id') or {}
    return {
        tid for tid, rating in rating_by_title_id.items()
        if _title_allowed(cap, _coerce_rating_value(rating), block_unrated=True)
    }


def _effective_remote_addr():
    # Use trusted proxy config to resolve the true client IP.
    # Cache in `g` so multiple log calls per request are consistent and cheap.
    try:
        if has_request_context() and hasattr(g, '_aerofoil_effective_remote_addr'):
            return g._aerofoil_effective_remote_addr
        if has_request_context() and hasattr(g, '_ownfoil_effective_remote_addr'):
            return g._ownfoil_effective_remote_addr
    except Exception:
        pass

    try:
        settings = load_settings()
    except Exception:
        settings = {}

    try:
        remote = _effective_client_ip(settings)
    except Exception:
        remote = (request.remote_addr or '').strip()

    remote = (remote or (request.remote_addr or '-') or '-').strip()
    try:
        if has_request_context():
            g._aerofoil_effective_remote_addr = remote
    except Exception:
        pass
    return remote


def _client_key():
    user = _get_request_user() or '-'
    remote = _effective_remote_addr() or '-'
    ua = request.headers.get('User-Agent') or '-'
    uid = ''
    try:
        if _is_shop_client_request():
            uid = (request.headers.get('Uid') or '').strip()
    except Exception:
        uid = ''
    return f"{user}|{remote}|{ua}|{uid}"[:512]


def _extract_tinfoil_client_meta():
    try:
        if not _is_shop_client_request():
            return {}
    except Exception:
        return {}

    def _val(name, max_len=256):
        try:
            return str(request.headers.get(name) or '').strip()[:max_len]
        except Exception:
            return ''

    out = {
        'theme': _val('Theme', 128),
        'uid': _val('Uid', 128),
        'version': _val('Version', 64),
        'revision': _val('Revision', 64),
        'language': _val('Language', 64),
        'hauth': _val('Hauth', 256),
        'uauth': _val('Uauth', 256),
    }
    return {k: v for k, v in out.items() if v}


def _encode_client_seen_meta(meta):
    if not isinstance(meta, dict) or not meta:
        return None
    payload = {}
    for key in ('theme', 'uid', 'version', 'revision', 'language', 'hauth', 'uauth'):
        try:
            value = str(meta.get(key) or '').strip()
        except Exception:
            value = ''
        if value:
            payload[key] = value[:256]
    if not payload:
        return None
    try:
        return _CLIENT_SEEN_META_PREFIX + json.dumps(payload, separators=(',', ':'))
    except Exception:
        return None


def _decode_client_seen_meta(raw):
    try:
        text = str(raw or '')
    except Exception:
        return {}
    if not text.startswith(_CLIENT_SEEN_META_PREFIX):
        return {}
    try:
        data = json.loads(text[len(_CLIENT_SEEN_META_PREFIX):])
    except Exception:
        return {}
    if not isinstance(data, dict):
        return {}

    out = {}
    for key in ('theme', 'uid', 'version', 'revision', 'language', 'hauth', 'uauth'):
        try:
            value = str(data.get(key) or '').strip()
        except Exception:
            value = ''
        if value:
            out[key] = value[:256]
    return out


def _attach_client_meta(items):
    for item in (items or []):
        if not isinstance(item, dict):
            continue

        decoded = _decode_client_seen_meta(item.get('filename'))
        for key in ('theme', 'uid', 'version', 'revision', 'language', 'hauth', 'uauth'):
            value = item.get(key)
            if value in (None, ''):
                value = decoded.get(key)
            if value in (None, ''):
                value = ''
            item[key] = value
    return items


def _touch_client():
    path = request.path or '/'
    if path.startswith('/static/'):
        return
    if path in ('/favicon.ico',):
        return

    now = time.time()
    remote = _effective_remote_addr()
    meta = {
        'last_seen_at': now,
        'user': _get_request_user(),
        'remote_addr': remote,
        'user_agent': request.headers.get('User-Agent'),
    }
    tinfoil_meta = _extract_tinfoil_client_meta()
    if tinfoil_meta:
        meta.update(tinfoil_meta)
    key = _client_key()
    with _connected_clients_lock:
        existing = _connected_clients.get(key) or {}
        existing.update(meta)
        _connected_clients[key] = existing

    # Persist a low-noise log of connected clients for auditing.
    # Use dedupe so polling/static bursts don't spam the database.
    try:
        _log_access_dedup(
            kind='client_seen',
            dedupe_key=key,
            window_s=300,
            user=meta.get('user'),
            remote_addr=meta.get('remote_addr'),
            user_agent=meta.get('user_agent'),
            filename=_encode_client_seen_meta(tinfoil_meta),
            ok=True,
            status_code=200,
        )
    except Exception:
        pass

    try:
        try:
            is_shop_client = _is_shop_client_request()
        except Exception:
            is_shop_client = False
        if not is_shop_client:
            return
        username = meta.get('user')
        if not username:
            return
        user = User.query.filter_by(user=username).first()
        if user is None:
            return
        uid_value = (tinfoil_meta.get('uid') or '').strip() if tinfoil_meta else ''
        remote = (meta.get('remote_addr') or '').strip()
        geo = {}
        if remote:
            try:
                if not _is_private_ip(remote):
                    geo = lookup_geoip(remote) or {}
            except Exception:
                geo = {}
        updated = False
        if uid_value and uid_value != (user.client_uid or ''):
            user.client_uid = uid_value
            updated = True
        user.last_login_at = utc_now()
        user.last_login_ip = remote or user.last_login_ip
        user.last_login_country = geo.get('country') or user.last_login_country
        user.last_login_country_code = geo.get('country_code') or user.last_login_country_code
        updated = True
        if updated:
            db.session.commit()
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass

    try:
        if tinfoil_meta and (tinfoil_meta.get('uid') or '').strip():
            username = meta.get('user')
            if username:
                user = User.query.filter_by(user=username).first()
                if user is not None:
                    uid_value = (tinfoil_meta.get('uid') or '').strip()
                    updated = False
                    if uid_value and uid_value != (user.client_uid or ''):
                        user.client_uid = uid_value
                        updated = True
                    if updated:
                        db.session.commit()
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass


def _is_cyberfoil_request():
    ua = request.headers.get('User-Agent') or ''
    return 'cyberfoil' in ua.lower()


def _is_tinfoil_request():
    ua = request.headers.get('User-Agent') or ''
    return 'tinfoil' in ua.lower()


def _has_tinfoil_header_set():
    return all(header in request.headers for header in TINFOIL_HEADERS)


def _is_shop_client_allowed_for_external():
    return _is_tinfoil_request() or _is_cyberfoil_request()


def _is_shop_client_request():
    # Primary detection for shop protocol traffic.
    return _has_tinfoil_header_set() or _is_shop_client_allowed_for_external()


def _request_has_cheat_access():
    """Resolve the current shop user's cheat permission without changing auth flow."""
    try:
        if current_user.is_authenticated:
            return bool(current_user.has_access('cheats'))
    except Exception:
        pass
    username = _get_request_user()
    if username:
        user = User.query.filter_by(user=username).first()
        return bool(user and user.has_access('cheats'))
    # A public shop has no per-user identity to apply a user permission to.
    return bool((app_settings.get('shop') or {}).get('public', False))


def _filter_cheat_section(payload, allowed):
    if allowed:
        return payload
    sections = (payload or {}).get('sections')
    if not isinstance(sections, list):
        return payload
    filtered = [section for section in sections if str((section or {}).get('id') or '') != 'cheats']
    if len(filtered) == len(sections):
        return payload
    result = dict(payload)
    result['sections'] = filtered
    return result


def _log_access(
    kind,
    title_id=None,
    file_id=None,
    filename=None,
    ok=True,
    status_code=200,
    duration_ms=None,
    bytes_sent=None,
    user=None,
    remote_addr=None,
    user_agent=None,
    country=None,
    country_code=None,
    region=None,
    city=None,
    latitude=None,
    longitude=None,
):
    if has_request_context():
        if user is None:
            user = _get_request_user()
        if remote_addr is None:
            remote_addr = _effective_remote_addr()
        if user_agent is None:
            user_agent = request.headers.get('User-Agent')
        if country is None:
            try:
                from app.auth import _is_private_ip
                if remote_addr and not _is_private_ip(remote_addr):
                    geo = lookup_geoip(remote_addr) or {}
                    country = geo.get('country')
                    country_code = geo.get('country_code')
                    region = geo.get('region')
                    city = geo.get('city')
                    latitude = geo.get('latitude')
                    longitude = geo.get('longitude')
            except Exception:
                pass

    def _do_write():
        add_access_event(
            kind=kind,
            user=user,
            remote_addr=remote_addr,
            user_agent=user_agent,
            country=country,
            country_code=country_code,
            region=region,
            city=city,
            latitude=latitude,
            longitude=longitude,
            title_id=title_id,
            file_id=file_id,
            filename=filename,
            bytes_sent=bytes_sent,
            ok=ok,
            status_code=status_code,
            duration_ms=duration_ms,
        )

    try:
        if has_app_context():
            _do_write()
        else:
            # Streaming responses may call this outside request/app context.
            with app.app_context():
                _do_write()
    except Exception:
        try:
            logger.exception('Failed to log access event')
        except Exception:
            pass


def _log_access_dedup(kind, dedupe_key, window_s=15, **kwargs):
    now = time.time()
    key = f"{kind}|{dedupe_key}"[:512]

    with _recent_access_lock:
        last = _recent_access.get(key) or 0
        if now - last < float(window_s):
            return False
        _recent_access[key] = now
        if len(_recent_access) > 5000:
            ordered = sorted(_recent_access.items(), key=lambda kv: kv[1], reverse=True)
            _recent_access.clear()
            for k, ts in ordered[:2000]:
                _recent_access[k] = ts

    _log_access(kind=kind, **kwargs)
    return True


def _dedupe_history(items, window_s=3):
    out = []
    last_seen = {}
    for item in (items or []):
        at = item.get('at') or 0
        key = (
            item.get('kind'),
            item.get('user'),
            item.get('remote_addr'),
            item.get('title_id'),
            item.get('file_id'),
            item.get('filename'),
        )
        prev = last_seen.get(key)
        if prev is not None and abs(prev - at) <= window_s:
            continue
        last_seen[key] = at
        out.append(item)
    return out


def _transfer_session_key(user, remote_addr, user_agent, file_id):
    user = user or '-'
    remote = remote_addr or '-'
    ua = user_agent or '-'
    return f"{user}|{remote}|{ua}|{file_id}"[:512]


def _transfer_session_start(user, remote_addr, user_agent, title_id, file_id, filename, resp_status_code=None):
    now = time.time()
    key = _transfer_session_key(user, remote_addr, user_agent, file_id)
    created = False

    # If we had a pending finalize timer for this session, cancel it (resume / next range request).
    with _transfer_finalize_timers_lock:
        t = _transfer_finalize_timers.pop(key, None)
        if t:
            try:
                t.cancel()
            except Exception:
                pass

    with _transfer_sessions_lock:
        sess = _transfer_sessions.get(key)
        if not sess:
            sess = {
                'started_at': now,
                'last_seen_at': now,
                'open_streams': 0,
                'bytes_sent': 0,
                'bytes_sent_total': 0,
                'bytes_total': 0,
                'ok': True,
                'status_code': None,
                'user': user,
                'remote_addr': remote_addr,
                'user_agent': user_agent,
                'title_id': title_id,
                'file_id': file_id,
                'filename': filename,
            }
            _transfer_sessions[key] = sess
            created = True

        sess['last_seen_at'] = now
        sess['open_streams'] = int(sess.get('open_streams') or 0) + 1
        if title_id and not sess.get('title_id'):
            sess['title_id'] = title_id
        if filename and not sess.get('filename'):
            sess['filename'] = filename

        # Bound memory.
        if len(_transfer_sessions) > 2000:
            ordered = sorted(_transfer_sessions.items(), key=lambda kv: (kv[1] or {}).get('last_seen_at', 0), reverse=True)
            _transfer_sessions.clear()
            for k, v in ordered[:1000]:
                _transfer_sessions[k] = v

    if created:
        _log_access(
            kind='transfer_start',
            title_id=title_id,
            file_id=file_id,
            filename=filename,
            bytes_sent=0,
            ok=True,
            status_code=int(resp_status_code) if resp_status_code is not None else 200,
            duration_ms=0,
            user=user,
            remote_addr=remote_addr,
            user_agent=user_agent,
        )

    return key


def _transfer_session_progress(key, bytes_sent):
    now = time.time()
    with _transfer_sessions_lock:
        sess = _transfer_sessions.get(key)
        if not sess:
            return
        sess['last_seen_at'] = now
        if bytes_sent is not None:
            try:
                sess['bytes_sent'] = max(int(sess.get('bytes_sent') or 0), int(bytes_sent))
            except Exception:
                pass


def _transfer_session_finalize(key):
    # Timer callback; only finalize if no streams reopened during grace.
    sess = None
    with _transfer_sessions_lock:
        sess = _transfer_sessions.get(key)
        if not sess or int(sess.get('open_streams') or 0) != 0:
            return
        sess = _transfer_sessions.pop(key, sess)

    if not sess:
        return

    started_at = float(sess.get('started_at') or time.time())
    duration_ms = int((time.time() - started_at) * 1000)
    code = sess.get('status_code')
    try:
        code = int(code) if code is not None else None
    except Exception:
        code = None

    bytes_total = sess.get('bytes_sent_total')
    if bytes_total is None:
        bytes_total = sess.get('bytes_sent')
    try:
        bytes_total = int(bytes_total) if bytes_total is not None else None
    except Exception:
        bytes_total = None

    ok = bool(sess.get('ok'))
    _log_access(
        kind='transfer',
        title_id=sess.get('title_id'),
        file_id=sess.get('file_id'),
        filename=sess.get('filename'),
        bytes_sent=bytes_total,
        ok=ok if code is None else (ok and code < 400),
        status_code=code if code is not None else 0,
        duration_ms=duration_ms,
        user=sess.get('user'),
        remote_addr=sess.get('remote_addr'),
        user_agent=sess.get('user_agent'),
    )


def _transfer_session_finish(key, ok, status_code, bytes_sent):
    now = time.time()
    with _transfer_sessions_lock:
        sess = _transfer_sessions.get(key)
        if not sess:
            return
        sess['last_seen_at'] = now

        try:
            if bytes_sent is not None:
                bs = int(bytes_sent)
                # Sum response body sizes across sequential range requests.
                sess['bytes_sent_total'] = int(sess.get('bytes_sent_total') or 0) + bs
                # Keep per-response max for debugging / safety.
                sess['bytes_sent'] = max(int(sess.get('bytes_sent') or 0), bs)
        except Exception:
            pass

        try:
            sess['ok'] = bool(sess.get('ok')) and bool(ok)
        except Exception:
            pass

        if status_code is not None:
            try:
                sess['status_code'] = int(status_code)
            except Exception:
                pass

        sess['open_streams'] = max(0, int(sess.get('open_streams') or 0) - 1)
        if sess['open_streams'] != 0:
            return

    # Schedule finalize after grace to merge sequential range requests.
    timer = threading.Timer(_TRANSFER_FINALIZE_GRACE_S, _transfer_session_finalize, args=(key,))
    timer.daemon = True
    with _transfer_finalize_timers_lock:
        prev = _transfer_finalize_timers.pop(key, None)
        if prev:
            try:
                prev.cancel()
            except Exception:
                pass
        _transfer_finalize_timers[key] = timer
    timer.start()


def _prune_stale_active_transfers(now=None, stale_after_s=None):
    current_ts = float(now if now is not None else time.time())
    stale_s = float(stale_after_s if stale_after_s is not None else _ACTIVE_TRANSFER_STALE_S)
    removed = []
    with _active_transfers_lock:
        for transfer_id, meta in list(_active_transfers.items()):
            if not isinstance(meta, dict):
                _active_transfers.pop(transfer_id, None)
                removed.append(transfer_id)
                continue
            last_seen_at = float(meta.get('last_seen_at') or meta.get('started_at') or 0.0)
            if last_seen_at <= 0:
                _active_transfers.pop(transfer_id, None)
                removed.append(transfer_id)
                continue
            if (current_ts - last_seen_at) > stale_s:
                _active_transfers.pop(transfer_id, None)
                removed.append(transfer_id)
    if removed:
        try:
            logger.warning("Pruned %s stale live transfer entries.", len(removed))
        except Exception:
            pass
    return removed


@app.before_request
def _activity_before_request():
    # Track recent clients in-memory for the admin activity page.
    try:
        _touch_client()
    except Exception:
        pass


def tinfoil_error(error):
    return jsonify({
        'error': error
    })

def _create_job(kind, total=0):
    job_id = uuid.uuid4().hex
    job = {
        'id': job_id,
        'kind': kind,
        'status': 'running',
        'cancelled': False,
        'created_at': time.time(),
        'updated_at': time.time(),
        'progress': {
            'done': 0,
            'total': total,
            'percent': 0,
            'message': ''
        },
        'logs': [],
        'errors': [],
        'summary': None
    }
    with conversion_jobs_lock:
        conversion_jobs[job_id] = job
    return job_id

def _job_log(job_id, message):
    if message is None:
        return
    message = _fix_mojibake(str(message)).strip()
    if not message:
        return
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        if not job:
            return
        suppress_traceback = bool(job.get('_suppress_traceback'))
        if message.startswith('Traceback (most recent call last):'):
            job['_suppress_traceback'] = True
            if not job.get('_traceback_notice_emitted'):
                job['_traceback_notice_emitted'] = True
                job['logs'].append('Converter traceback suppressed. Showing concise error summary.')
            job['updated_at'] = time.time()
            return
        if message.startswith('During handling of the above exception'):
            job['_suppress_traceback'] = True
            job['updated_at'] = time.time()
            return
        if suppress_traceback:
            if re.match(r'^\s*File ".*", line \d+, in .+$', message):
                job['updated_at'] = time.time()
                return
            if re.match(r'^\s*~+.*$', message):
                job['updated_at'] = time.time()
                return
            if re.match(r'^\s*[A-Za-z_][A-Za-z0-9_.]*: .*$', message):
                # Exception summary line; stop traceback suppression after this.
                job['_suppress_traceback'] = False
            elif message.strip() == '':
                job['updated_at'] = time.time()
                return
            else:
                job['updated_at'] = time.time()
                return

        verification_error_match = re.search(
            r'VerificationException:\s*Verification detected hash mismatch',
            message,
            re.IGNORECASE
        )
        permission_32_match = re.search(r'PermissionError:.*WinError\s*32', message, re.IGNORECASE)
        bad_verify_match = re.search(r'^\[BAD VERIFY\]\s+(.+)$', message)
        delete_failed_output_match = re.search(r'^\[DELETE NSZ\]\s+(.+)$', message)
        compress_error_match = re.search(r'^Error while compressing file:\s+(.+)$', message)

        if verification_error_match:
            message = 'Verification failed: hash mismatch detected. Source file is likely bad or corrupted.'
        elif permission_32_match:
            message = 'Cleanup warning: failed output file is in use (WinError 32), so automatic delete failed.'
        elif bad_verify_match:
            bad_path = str(bad_verify_match.group(1) or '').strip()
            bad_name = os.path.basename(bad_path) if bad_path else bad_path
            message = f"Verification failed for output: {bad_name or bad_path}."
        elif delete_failed_output_match:
            out_path = str(delete_failed_output_match.group(1) or '').strip()
            out_name = os.path.basename(out_path) if out_path else out_path
            message = f"Removing failed output: {out_name or out_path}."
        elif compress_error_match:
            in_path = str(compress_error_match.group(1) or '').strip()
            in_name = os.path.basename(in_path) if in_path else in_path
            message = f"Conversion failed for input: {in_name or in_path}."

        percent_match = re.search(r'Compressed\s+([0-9.]+)%', message)
        minimal_progress_match = re.search(r'^\s*(?:[^0-9]{1,4}\s*)?([0-9]{1,3}(?:\.[0-9]+)?)%\s*(.*)$', message)
        numeric_match = re.fullmatch(r'\d{1,3}', message)
        convert_match = re.search(r'^\[CONVERT\]\s+(.+?)\s+->\s+(.+)$', message)
        verify_match = re.search(r'^\[VERIFY\]\s+(.+)$', message)

        if numeric_match:
            try:
                percent_value = int(numeric_match.group(0))
                if 0 <= percent_value <= 100:
                    job['progress']['percent'] = float(percent_value)
                    stage = job['progress'].get('stage') or 'converting'
                    label = 'Verifying' if stage == 'verifying' else 'Converting'
                    file_name = (job['progress'].get('file') or '').strip()
                    file_suffix = f" ({file_name})" if file_name else ''
                    job['progress']['message'] = f"{label}: {percent_value}%{file_suffix}"
                    job['updated_at'] = time.time()
                    return
            except ValueError:
                pass
        if minimal_progress_match:
            try:
                percent_value = float(minimal_progress_match.group(1))
                if 0 <= percent_value <= 100:
                    status_hint = (minimal_progress_match.group(2) or '').strip()
                    status_hint_lower = status_hint.lower()
                    stage = job['progress'].get('stage') or 'converting'
                    if 'verif' in status_hint_lower:
                        stage = 'verifying'
                    elif 'compress' in status_hint_lower or 'convert' in status_hint_lower:
                        stage = 'converting'
                    job['progress']['stage'] = stage
                    file_match = re.search(r'([^\s].*\.(?:nsp|nsz|xci|xcz|nca|ncz))', status_hint, re.IGNORECASE)
                    if file_match:
                        status_file = os.path.basename(file_match.group(1).strip())
                        if status_file:
                            job['progress']['file'] = status_file
                    job['progress']['percent'] = percent_value
                    label = 'Verifying' if stage == 'verifying' else 'Converting'
                    file_name = (job['progress'].get('file') or '').strip()
                    file_suffix = f" ({file_name})" if file_name else ''
                    suffix = f" - {status_hint}" if status_hint else ''
                    job['progress']['message'] = f"{label}: {percent_value:.0f}%{file_suffix}{suffix}"
                    job['updated_at'] = time.time()
                    return
            except ValueError:
                pass
        if percent_match:
            try:
                job['progress']['percent'] = float(percent_match.group(1))
                stage = job['progress'].get('stage') or 'converting'
                label = 'Verifying' if stage == 'verifying' else 'Converting'
                file_name = (job['progress'].get('file') or '').strip()
                file_suffix = f" ({file_name})" if file_name else ''
                job['progress']['message'] = f"{label}: {job['progress']['percent']:.0f}%{file_suffix}"
                job['updated_at'] = time.time()
                return
            except ValueError:
                pass

        if convert_match:
            input_path = convert_match.group(1)
            display_name = os.path.basename(input_path)
            message = f"Converting {display_name}..."
            job['progress']['stage'] = 'converting'
            job['progress']['file'] = display_name
            job['progress']['message'] = message
        elif verify_match:
            input_path = verify_match.group(1)
            display_name = os.path.basename(input_path)
            message = f"Verifying {display_name}..."
            job['progress']['stage'] = 'verifying'
            job['progress']['file'] = display_name
            job['progress']['message'] = message
        elif message.startswith("Running:"):
            message = "Starting converter..."
            job['progress']['stage'] = 'converting'
            job['progress']['message'] = message

        if message:
            job['logs'].append(message)
        if len(job['logs']) > 500:
            job['logs'] = job['logs'][-500:]
        job['updated_at'] = time.time()

def _fix_mojibake(text):
    if not text:
        return text
    if "Ã" not in text and "â" not in text:
        return text
    try:
        fixed = text.encode("latin-1").decode("utf-8")
        return fixed if fixed else text
    except (UnicodeEncodeError, UnicodeDecodeError):
        return text

def _job_progress(job_id, done, total):
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        if not job:
            return
        job['progress']['done'] = done
        job['progress']['total'] = total
        job['updated_at'] = time.time()

def _job_finish(job_id, results):
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        if not job:
            return
        if job.get('cancelled'):
            job['status'] = 'cancelled'
        else:
            job['status'] = 'failed' if results.get('errors') else 'success'
        job['errors'] = results.get('errors', [])
        job['summary'] = {
            'converted': results.get('converted', 0),
            'skipped': results.get('skipped', 0),
            'deleted': results.get('deleted', 0),
            'moved': results.get('moved', 0)
        }
        progress = job.setdefault('progress', {})
        kind = str(job.get('kind') or '')
        total = int(progress.get('total') or 0)
        if kind == 'convert-single':
            total = max(total, 1)
            progress['total'] = total
            progress['done'] = total
        else:
            if total > 0:
                progress['done'] = total
            else:
                estimated_total = int(job['summary'].get('converted', 0) or 0) + int(job['summary'].get('skipped', 0) or 0)
                if estimated_total > 0:
                    progress['total'] = estimated_total
                    progress['done'] = estimated_total
        final_total = int(progress.get('total') or 0)
        final_done = int(progress.get('done') or 0)
        if final_total > 0 and final_done >= final_total:
            progress['percent'] = 100.0
        if job['status'] == 'success':
            progress['message'] = 'Conversion complete.'
            progress['stage'] = 'completed'
        elif job['status'] == 'cancelled':
            progress['message'] = 'Conversion cancelled.'
            progress['stage'] = 'cancelled'
        else:
            progress['message'] = 'Conversion failed.'
            progress['stage'] = 'failed'
        job['updated_at'] = time.time()
        if len(conversion_jobs) > conversion_job_limit:
            oldest = sorted(conversion_jobs.values(), key=lambda item: item['created_at'])[:len(conversion_jobs) - conversion_job_limit]
            for item in oldest:
                conversion_jobs.pop(item['id'], None)

def _job_is_cancelled(job_id):
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        return bool(job and job.get('cancelled'))

def tinfoil_access(f):
    @wraps(f)
    def _tinfoil_access(*args, **kwargs):
        _maybe_sync_request_settings()
        hauth_success = None
        auth_success = None
        auth_error = None
        request.verified_host = None
        is_shop_client = _is_shop_client_request()
        # Host verification to prevent hotlinking
        #Tinfoil doesn't send Hauth for file grabs, only directories, so ignore get_game endpoints.
        host_verification = (
            is_shop_client
            and "/api/get_game" not in request.path
            and (request.is_secure or request.headers.get("X-Forwarded-Proto") == "https")
        )
        if host_verification:
            request_host = request.host
            request_hauth = request.headers.get('Hauth')
            logger.info(f"Secure Tinfoil request from remote host {request_host}, proceeding with host verification.")
            shop_host = app_settings["shop"].get("host")
            shop_hauth = app_settings["shop"].get("hauth")
            if not shop_host:
                logger.error("Missing shop host configuration, Host verification is disabled.")

            elif request_host != shop_host:
                logger.warning(f"Incorrect URL referrer detected: {request_host}.")
                error = f"Incorrect URL `{request_host}`."
                hauth_success = False

            elif not shop_hauth:
                # Try authentication, if an admin user is logging in then set the hauth
                auth_success, auth_error, auth_is_admin =  basic_auth(request)
                if auth_success and auth_is_admin:
                    shop_settings = app_settings['shop']
                    shop_settings['hauth'] = request_hauth
                    set_shop_settings(shop_settings)
                    logger.info(f"Successfully set Hauth value for host {request_host}.")
                    hauth_success = True
                else:
                    logger.warning(f"Hauth value not set for host {request_host}, Host verification is disabled. Connect to the shop from Tinfoil with an admin account to set it.")

            elif request_hauth != shop_hauth:
                logger.warning(f"Incorrect Hauth detected for host: {request_host}.")
                error = f"Incorrect Hauth for URL `{request_host}`."
                hauth_success = False

            else:
                hauth_success = True
                request.verified_host = shop_host

            if hauth_success is False:
                return tinfoil_error(error)
        
        # Now checking auth if shop is private
        if not app_settings['shop']['public']:
            # Shop is private
            if auth_success is None:
                if current_user.is_authenticated and current_user.has_access('shop'):
                    auth_success = True
                else:
                    auth_success, auth_error, _ = basic_auth(request)
            if not auth_success:
                # If the account is frozen, return safe empty responses so clients can display the MOTD.
                try:
                    if is_shop_client and request.path in ('/', '/api/shop/sections', '/api/frozen/notice'):
                        username = _get_request_user()
                        frozen_user = User.query.filter_by(user=username).first() if username else None
                        if frozen_user is not None and bool(getattr(frozen_user, 'frozen', False)):
                            message = (getattr(frozen_user, 'frozen_message', None) or '').strip() or 'Account is frozen.'
                            if request.path == '/api/shop/sections':
                                placeholder_item = {
                                    'name': 'Account frozen',
                                    'title_name': 'Account frozen',
                                    'title_id': '0000000000000000',
                                    'app_id': '0000000000000000',
                                    'app_version': '0',
                                    'app_type': APP_TYPE_BASE,
                                    'category': '',
                                    'icon_url': '',
                                    'url': '/api/frozen/notice#frozen.txt',
                                    'size': 1,
                                    'file_id': 0,
                                    'filename': 'frozen.txt',
                                    'download_count': 0,
                                }
                                empty_sections = {
                                    'sections': [
                                        {'id': 'new', 'title': 'New', 'items': [placeholder_item]},
                                        {'id': 'recommended', 'title': 'Recommended', 'items': [placeholder_item]},
                                        {'id': 'updates', 'title': 'Updates', 'items': [placeholder_item]},
                                        {'id': 'dlc', 'title': 'DLC', 'items': [placeholder_item]},
                                        {'id': 'all', 'title': 'All', 'items': [placeholder_item]},
                                    ]
                                }
                                return _respond_with_shop_payload(empty_sections)

                            placeholder = {"url": "/api/frozen/notice#frozen.txt", "size": 1}
                            shop = {"error": message, "files": [placeholder]}
                            return _respond_with_shop_payload(shop, verified_host=request.verified_host)
                except Exception:
                    pass
                return tinfoil_error(auth_error)

        # External-client restriction: allow authenticated get_game requests even when
        # the client omits Tinfoil/CyberFoil markers on file-transfer requests.
        if bool(app_settings.get('shop', {}).get('external_tinfoil_only', False)):
            remote = _effective_remote_addr()
            if remote and not _is_private_ip(remote) and not is_shop_client:
                allow_via_auth_for_get_game = False
                if request.path.startswith('/api/get_game/'):
                    if auth_success is None:
                        auth_success, auth_error, _ = basic_auth(request)
                    allow_via_auth_for_get_game = bool(auth_success)
                if not allow_via_auth_for_get_game:
                    return jsonify({'error': 'External access is restricted to Tinfoil/CyberFoil clients.'}), 403

        # Auth success: block frozen accounts from accessing the library.
        try:
            frozen_user = None
            if current_user.is_authenticated:
                frozen_user = current_user
            else:
                username = _get_request_user()
                frozen_user = User.query.filter_by(user=username).first() if username else None
            if frozen_user is not None and bool(getattr(frozen_user, 'frozen', False)):
                message = (getattr(frozen_user, 'frozen_message', None) or '').strip() or 'Account is frozen.'

                # Allow safe empty responses for the shop root + sections.
                if is_shop_client and request.path in ('/', '/api/shop/sections', '/api/frozen/notice'):
                    if request.path == '/api/shop/sections':
                        placeholder_item = {
                            'name': 'Account frozen',
                            'title_name': 'Account frozen',
                            'title_id': '0000000000000000',
                            'app_id': '0000000000000000',
                            'app_version': '0',
                            'app_type': APP_TYPE_BASE,
                            'category': '',
                            'icon_url': '',
                            'url': '/api/frozen/notice#frozen.txt',
                            'size': 1,
                            'file_id': 0,
                            'filename': 'frozen.txt',
                            'download_count': 0,
                        }
                        empty_sections = {
                            'sections': [
                                {'id': 'new', 'title': 'New', 'items': [placeholder_item]},
                                {'id': 'recommended', 'title': 'Recommended', 'items': [placeholder_item]},
                                {'id': 'updates', 'title': 'Updates', 'items': [placeholder_item]},
                                {'id': 'dlc', 'title': 'DLC', 'items': [placeholder_item]},
                                {'id': 'all', 'title': 'All', 'items': [placeholder_item]},
                            ]
                        }
                        return _respond_with_shop_payload(empty_sections)

                    placeholder = {"url": "/api/frozen/notice#frozen.txt", "size": 1}
                    shop = {"error": message, "files": [placeholder]}
                    return _respond_with_shop_payload(shop, verified_host=request.verified_host)

                return tinfoil_error(message)
        except Exception:
            pass

        # Auth success
        return f(*args, **kwargs)
    return _tinfoil_access


@app.get('/api/frozen/notice')
def frozen_notice_api():
    # Minimal endpoint used to provide a harmless placeholder file
    # for frozen accounts so clients don't reject an empty shop.
    return Response(b' ', mimetype='application/octet-stream')

def access_shop():
    static_asset_version = os.stat(os.path.join(app.static_folder, 'style.css')).st_mtime_ns
    return render_template(
        'index.html',
        title='Library',
        admin_account_created=admin_account_created(),
        valid_keys=app_settings['titles']['valid_keys'],
        identification_disabled=not app_settings['titles']['valid_keys'],
        download_ui_visibility=_get_download_template_visibility(),
        static_asset_version=static_asset_version,
    )

@access_required('shop')
def access_shop_auth():
    return access_shop()

@app.route('/')
def index():
    is_shop_client = _is_shop_client_request()
    is_allowed_external_client = _is_shop_client_request()
    tinfoil_only_mode = bool((app_settings.get('shop') or {}).get('tinfoil_only_mode', False))
    prefers_html = bool(request.accept_mimetypes.accept_html)
    if bool(app_settings.get('shop', {}).get('external_tinfoil_only', False)):
        remote = _effective_remote_addr()
        if remote and not _is_private_ip(remote) and not is_allowed_external_client:
            return 'Forbidden', 403

    @tinfoil_access
    def access_tinfoil_shop():
        start_ts = time.time()
        motd_text = ''
        try:
            if bool(app_settings.get('shop', {}).get('motd_enabled', True)):
                motd_text = _render_motd_template(app_settings['shop']['motd'])
        except Exception:
            motd_text = ''
        cap, block_unrated = _user_rating_cap()
        shop = {
            "success": motd_text
        }
        is_cyberfoil = _is_cyberfoil_request()
        virtual_compressed_stream = bool(
            (app_settings.get('shop') or {}).get('cyberfoil_virtual_compressed_stream', True)
        )
        shop["files"] = _get_cached_shop_files(
            cap=cap,
            block_unrated=block_unrated,
            virtualize_compressed=is_cyberfoil and virtual_compressed_stream,
        )

        if is_cyberfoil:
            _log_access(
                kind='shop',
                filename=request.full_path if request.query_string else request.path,
                ok=True,
                status_code=200,
                duration_ms=int((time.time() - start_ts) * 1000),
            )

        return _respond_with_shop_payload(
            shop,
            verified_host=request.verified_host,
            cache_kind='root',
            filter_token=(cap, block_unrated, is_cyberfoil, virtual_compressed_stream),
        )
    
    if is_shop_client or (tinfoil_only_mode and not prefers_html):
        logger.info(
            "Serving shop protocol response from %s (client_detected=%s, tinfoil_only_mode=%s, prefers_html=%s)",
            request.remote_addr,
            bool(is_shop_client),
            bool(tinfoil_only_mode),
            bool(prefers_html),
        )
        return access_tinfoil_shop()

    # Frozen accounts: web UI should only show the MOTD message.
    try:
        frozen_user = None
        if current_user.is_authenticated:
            frozen_user = current_user
        else:
            auth = request.authorization
            username = auth.username if auth and auth.username else None
            frozen_user = User.query.filter_by(user=username).first() if username else None

        if frozen_user is not None and bool(getattr(frozen_user, 'frozen', False)):
            message = (getattr(frozen_user, 'frozen_message', None) or '').strip() or 'Account is frozen.'
            return render_template('frozen.html', title='Library', message=message)
    except Exception:
        pass
     
    if not app_settings['shop']['public']:
        return access_shop_auth()
    return access_shop()

@app.route('/settings')
@access_required('admin')
def settings_page():
    languages_file = os.path.join(TITLEDB_DIR, 'languages.json')
    if os.path.exists(languages_file):
        with open(languages_file) as f:
            languages = json.load(f)
            languages = dict(sorted(languages.items()))
    else:
        languages = {}
    return render_template(
        'settings.html',
        title='Settings',
        languages_from_titledb=languages,
        admin_account_created=admin_account_created(),
        valid_keys=app_settings['titles']['valid_keys'],
        identification_disabled=not app_settings['titles']['valid_keys'],
        app_version=get_app_version(APP_VERSION))

@app.route('/manage')
@access_required('admin')
def manage_page():
    return render_template(
        'manage.html',
        title='Manage',
        admin_account_created=admin_account_created())

@app.route('/downloads')
@access_required('admin')
def downloads_page():
    return render_template(
        'downloads.html',
        title='Downloads',
        admin_account_created=admin_account_created(),
        download_ui_visibility=_get_download_template_visibility())

@app.route('/upload')
@access_required('admin')
def upload_page():
    return render_template(
        'upload.html',
        title='Upload',
        admin_account_created=admin_account_created())


@app.route('/cheats')
@access_required('admin')
def cheats_page():
    return render_template(
        'cheats.html',
        title='Cheats',
        admin_account_created=admin_account_created())


@app.route('/activity')
@access_required('admin')
def activity_page():
    return render_template(
        'activity.html',
        title='Activity',
        admin_account_created=admin_account_created())


@app.route('/users')
@access_required('admin')
def users_page():
    return render_template(
        'users.html',
        title='Users',
        admin_account_created=admin_account_created())


@app.route('/requests')
@access_required('shop')
def requests_page():
    return render_template(
        'requests.html',
        title='Requests',
        admin_account_created=admin_account_created(),
        download_ui_visibility=_get_download_template_visibility())


@app.route('/saves')
@access_required('backup')
def saves_page():
    return render_template(
        'saves.html',
        title='Save Data Backups',
        admin_account_created=admin_account_created())


@app.post('/api/requests')
@access_required('shop')
def create_title_request_api():
    data = request.json or {}
    title_id_raw = data.get('title_id', '').strip()
    title_name = (data.get('title_name') or '').strip() or None

    # Validate title_id format
    is_valid, title_id_result = validate_title_id(title_id_raw)
    if not is_valid:
        return api_error(title_id_result, 400)
    
    title_id = title_id_result
    ok, message, req = create_title_request(current_user.id, title_id, title_name=title_name)
    if ok:
        return jsonify({'success': True, 'message': message, 'request_id': req.id if req else None})
    return jsonify({'success': False, 'message': message})


@app.get('/api/requests')
@access_required('shop')
def list_requests_api():
    include_all = request.args.get('all', '0') == '1'
    if include_all:
        if not current_user.is_admin:
            return jsonify({'success': False, 'message': 'Forbidden'}), 403

    items = list_requests(user_id=current_user.id, include_all=include_all, limit=500)

    # Auto-close open requests whose titles are now in the library.
    # This keeps the requests list actionable without requiring manual admin cleanup.
    try:
        open_requests = [
            r for r in (items or [])
            if getattr(r, 'status', None) == 'open' and getattr(r, 'title_id', None)
        ]
        if open_requests:
            open_ids = [r.id for r in open_requests if r.id is not None]
            open_title_ids = sorted({
                str(getattr(r, 'title_id', '') or '').strip().upper()
                for r in open_requests
            })
            open_title_ids = [tid for tid in open_title_ids if tid]
            if open_ids and open_title_ids:
                existing_title_ids = {
                    row.title_id
                    for row in (
                        db.session.query(Titles.title_id)
                        .filter(Titles.title_id.in_(open_title_ids))
                        .all()
                    )
                    if row.title_id
                }
                if existing_title_ids:
                    changed = (
                        db.session.query(TitleRequests)
                        .filter(TitleRequests.id.in_(open_ids))
                        .filter(TitleRequests.status == 'open')
                        .filter(TitleRequests.title_id.in_(existing_title_ids))
                        .update({TitleRequests.status: 'closed'}, synchronize_session=False)
                    )
                    if changed:
                        db.session.commit()
                        for r in open_requests:
                            if str(getattr(r, 'title_id', '') or '').strip().upper() in existing_title_ids:
                                r.status = 'closed'
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass

    relation_table_available = _has_title_request_users_table()
    out = []
    for r in items:
        request_users = []
        requester_count = 0
        if relation_table_available:
            try:
                request_users = list(getattr(r, 'request_users', []) or [])
                requester_count = len(request_users)
            except Exception:
                request_users = []
                requester_count = 0
        primary_user = getattr(r, 'user', None)
        if primary_user is None and request_users:
            primary_user = getattr(request_users[0], 'user', None)
        out.append({
            'id': r.id,
            'created_at': int(r.created_at.timestamp()) if r.created_at else None,
            'status': r.status,
            'user_status': r.status,
            'title_id': r.title_id,
            'title_name': r.title_name,
            'user': {
                'id': primary_user.id if primary_user else None,
                'user': primary_user.user if primary_user else None,
            } if include_all else None,
            'requesters': [
                {
                    'id': link.user.id if getattr(link, 'user', None) else None,
                    'user': link.user.user if getattr(link, 'user', None) else None,
                }
                for link in request_users
                if getattr(link, 'user', None) is not None
            ] if include_all else None,
            'requester_count': int(requester_count) if include_all else None,
        })
    return jsonify({'success': True, 'requests': out})


@app.get('/api/requests/unseen-count')
@access_required('admin')
def admin_unseen_requests_count_api():
    try:
        count = (
            db.session.query(TitleRequests)
            .outerjoin(
                TitleRequestViews,
                (TitleRequestViews.request_id == TitleRequests.id)
                & (TitleRequestViews.user_id == current_user.id),
            )
            .filter(TitleRequests.status == 'open')
            .filter(TitleRequestViews.id.is_(None))
            .count()
        )
        return jsonify({'success': True, 'count': int(count)})
    except Exception as e:
        logger.error(f"Error in title request endpoint: {e}")
        return api_error('An error occurred processing the request', 500)


@app.post('/api/requests/mark-seen')
@access_required('admin')
def admin_mark_requests_seen_api():
    data = request.json or {}
    ids = data.get('request_ids')
    mark_all_open = not ids

    if mark_all_open:
        ids = []

    try:
        ids = [int(x) for x in (ids or [])]
    except Exception:
        return api_error('Invalid request_ids.', 400)

    ids = list(dict.fromkeys([x for x in ids if x > 0]))
    if not ids and not mark_all_open:
        return jsonify({'success': True, 'message': 'Nothing to mark.', 'marked': 0})

    now = None
    try:
        now = utc_now()
    except Exception:
        now = None

    try:
        ts = now or utc_now()

        if mark_all_open:
            select_stmt = (
                db.session.query(
                    literal(int(current_user.id)).label('user_id'),
                    TitleRequests.id.label('request_id'),
                    literal(ts).label('viewed_at'),
                )
                .outerjoin(
                    TitleRequestViews,
                    (TitleRequestViews.request_id == TitleRequests.id)
                    & (TitleRequestViews.user_id == current_user.id),
                )
                .filter(TitleRequests.status == 'open')
                .filter(TitleRequestViews.id.is_(None))
            )
            stmt = (
                insert(TitleRequestViews)
                .from_select(['user_id', 'request_id', 'viewed_at'], select_stmt)
                .on_conflict_do_nothing(index_elements=['user_id', 'request_id'])
            )
            result = db.session.execute(stmt)
            try:
                marked = int(result.rowcount or 0)
            except Exception:
                marked = 0
            if marked < 0:
                marked = 0
        else:
            existing_ids = {
                row.request_id
                for row in (
                    db.session.query(TitleRequestViews.request_id)
                    .filter(TitleRequestViews.user_id == current_user.id)
                    .filter(TitleRequestViews.request_id.in_(ids))
                    .all()
                )
                if row.request_id is not None
            }
            to_insert = [
                {'user_id': current_user.id, 'request_id': req_id, 'viewed_at': ts}
                for req_id in ids
                if req_id not in existing_ids
            ]
            marked = 0
            if to_insert:
                stmt = (
                    insert(TitleRequestViews)
                    .values(to_insert)
                    .on_conflict_do_nothing(index_elements=['user_id', 'request_id'])
                )
                result = db.session.execute(stmt)
                try:
                    marked = int(result.rowcount or 0)
                except Exception:
                    marked = len(to_insert)
        db.session.commit()
        return jsonify({'success': True, 'message': 'Marked seen.', 'marked': int(marked)})
    except Exception as e:
        db.session.rollback()
        return api_error(str(e), 500)


@app.post('/api/requests/delete')
@access_required('admin')
def admin_delete_request_api():
    data = request.json or {}
    try:
        req_id = int(data.get('request_id'))
    except Exception:
        return api_error('Invalid request_id.', 400)

    try:
        req = TitleRequests.query.filter_by(id=req_id).first()
        if req is None:
            return api_error('Request not found.', 404)

        # Clean up per-admin view markers for this request.
        try:
            TitleRequestViews.query.filter_by(request_id=req_id).delete(synchronize_session=False)
        except Exception:
            pass

        db.session.delete(req)
        db.session.commit()
        return jsonify({'success': True})
    except Exception as e:
        db.session.rollback()
        return api_error(str(e), 500)


@app.post('/api/requests/deny')
@access_required('admin')
def admin_deny_request_api():
    data = request.json or {}
    try:
        req_id = int(data.get('request_id'))
    except Exception:
        return api_error('Invalid request_id.', 400)

    try:
        req = TitleRequests.query.filter_by(id=req_id).first()
        if req is None:
            return api_error('Request not found.', 404)
        if (req.status or '').strip().lower() == 'denied':
            return jsonify({'success': True, 'message': 'Request already denied.'})

        req.status = 'denied'
        db.session.commit()
        return jsonify({'success': True, 'message': 'Request denied.'})
    except Exception as e:
        db.session.rollback()
        return api_error(str(e), 500)


def _apply_download_search_char_replacements(text, downloads_settings):
    out = str(text or '')
    for rule in (downloads_settings or {}).get('search_char_replacements') or []:
        if not isinstance(rule, dict):
            continue
        from_text = str(rule.get('from') or '')
        to_text = str(rule.get('to') or '')
        if not from_text:
            continue
        out = out.replace(from_text, to_text)
    return out


def _normalize_download_search_query(text, downloads_settings=None):
    normalized = _apply_download_search_char_replacements(text, downloads_settings)
    try:
        normalized = unicodedata.normalize('NFKD', normalized)
        normalized = normalized.encode('ascii', 'ignore').decode('ascii')
    except Exception:
        normalized = str(normalized or '')
    normalized = re.sub(r"[^A-Za-z0-9\s]+", " ", normalized)
    return re.sub(r"\s+", " ", normalized).strip()


def _get_download_filter_thresholds(downloads):
    downloads = downloads or {}
    torrent_cfg = downloads.get('torrent_client') or {}
    usenet_cfg = downloads.get('usenet_client') or {}
    try:
        min_seeders = int(torrent_cfg.get('min_seeders') or 0)
    except (TypeError, ValueError):
        min_seeders = 0
    try:
        min_age_minutes = int(usenet_cfg.get('min_age_minutes') or 0)
    except (TypeError, ValueError):
        min_age_minutes = 0
    return max(min_seeders, 0), max(min_age_minutes, 0)


def _get_prowlarr_search_limit(prowlarr_cfg):
    try:
        search_limit = int((prowlarr_cfg or {}).get('search_limit') or 100)
    except (TypeError, ValueError):
        search_limit = 100
    return max(1, min(search_limit, 500))


def _trim_download_search_results(results, limit=50):
    ordered_results = sort_download_search_results(results)
    return [
        {
            'title': r.get('title'),
            'indexer': r.get('indexer'),
            'size': r.get('size'),
            'seeders': r.get('seeders'),
            'leechers': r.get('leechers'),
            'download_url': r.get('download_url'),
            'protocol': r.get('protocol'),
            'age_minutes': r.get('age_minutes'),
            'age_label': r.get('age_label'),
            'published_at': r.get('published_at'),
        }
        for r in ordered_results[:limit]
    ]


def _get_download_template_visibility():
    settings = load_settings()
    downloads = settings.get('downloads', {})
    return get_download_ui_visibility(downloads)


@app.get('/api/requests/search')
@access_required('admin')
def request_prowlarr_search_api():
    title_id = (request.args.get('title_id') or '').strip().upper()
    title_name = (request.args.get('title_name') or '').strip()
    if not title_id and not title_name:
        return api_error('Missing title_id or title_name.', 400)

    settings = load_settings()
    downloads = settings.get('downloads', {})
    prowlarr_cfg = downloads.get('prowlarr', {})
    if not prowlarr_cfg.get('url') or not prowlarr_cfg.get('api_key'):
        return jsonify({'success': False, 'message': 'Prowlarr is not configured.', 'results': []})

    # Prefer TitleDB name if we can resolve it.
    resolved_name = title_name
    if title_id:
        titles.load_titledb()
        try:
            info = titles.get_game_info(title_id) or {}
            resolved_name = (info.get('name') or '').strip() or resolved_name
        finally:
            titles.release_titledb()

    base_query = _normalize_download_search_query(resolved_name or title_id, downloads)
    prefix = _normalize_download_search_query(downloads.get('search_prefix') or '', downloads)
    full_query = base_query
    if prefix and not full_query.lower().startswith(prefix.lower()):
        full_query = f"{prefix} {full_query}".strip()

    try:
        try:
            timeout_seconds = int(prowlarr_cfg.get('timeout_seconds') or 15)
        except (TypeError, ValueError):
            timeout_seconds = 15
        timeout_seconds = max(5, min(timeout_seconds, 180))
        search_limit = _get_prowlarr_search_limit(prowlarr_cfg)
        client = ProwlarrClient(prowlarr_cfg['url'], prowlarr_cfg['api_key'], timeout_seconds=timeout_seconds)
        logger.info(f'Prowlarr search (requests page): "{full_query}" (title {title_id or "-"})')
        results = client.search(
            full_query,
            indexer_ids=prowlarr_cfg.get('indexer_ids') or [],
            categories=prowlarr_cfg.get('categories') or [],
            limit=search_limit,
        )
        results = filter_download_search_results(results, downloads)
        trimmed = _trim_download_search_results(results, limit=50)
        return jsonify({'success': True, 'results': trimmed})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e), 'results': []})


@app.get('/api/admin/activity')
@access_required('admin')
def admin_activity_api():
    limit = request.args.get('limit', 100)
    try:
        limit = int(limit)
    except Exception:
        limit = 100
    limit = max(1, min(limit, ACTIVITY_API_MAX_LIMIT))

    _prune_stale_active_transfers()

    # Snapshot active transfers.
    with _active_transfers_lock:
        live = list(_active_transfers.values())

    # Snapshot connected clients (last 2 minutes).
    cutoff = time.time() - 120
    with _connected_clients_lock:
        clients = [v for v in _connected_clients.values() if (v or {}).get('last_seen_at', 0) >= cutoff]

        # Bound memory: drop oldest if we grow too much.
        if len(_connected_clients) > 2000:
            ordered = sorted(_connected_clients.items(), key=lambda kv: (kv[1] or {}).get('last_seen_at', 0), reverse=True)
            _connected_clients.clear()
            for k, v in ordered[:1000]:
                _connected_clients[k] = v

    clients = sorted(clients, key=lambda item: item.get('last_seen_at', 0), reverse=True)[:250]
    _attach_client_meta(clients)

    geo_cache = {}
    def _attach_geo(items):
        for item in (items or []):
            if not isinstance(item, dict):
                continue
            remote = (item.get('remote_addr') or '').strip()
            if not remote:
                continue
            if _is_private_ip(remote):
                continue
            if item.get('country') or item.get('region') or item.get('city'):
                continue
            if remote in geo_cache:
                geo = geo_cache[remote]
            else:
                try:
                    geo = lookup_geoip(remote) or {}
                except Exception:
                    geo = {}
                geo_cache[remote] = geo
            if not geo:
                continue
            item['country'] = geo.get('country')
            item['country_code'] = geo.get('country_code')
            item['region'] = geo.get('region')
            item['city'] = geo.get('city')
            item['latitude'] = geo.get('latitude')
            item['longitude'] = geo.get('longitude')

    _attach_geo(live)
    _attach_geo(clients)

    # Recent access events.
    history_error = None
    try:
        history = get_access_events(limit=limit)
    except Exception as e:
        history = []
        history_error = str(e)

    include_starts = request.args.get('include_starts', '1') != '0'
    if not include_starts:
        history = [h for h in history if h.get('kind') != 'transfer_start']

    include_clients = request.args.get('include_clients', '0') != '0'
    if not include_clients:
        history = [h for h in history if h.get('kind') != 'client_seen']
    history = _dedupe_history(history)

    # Hydrate title_name where possible.
    title_ids = set()
    for item in live:
        if item.get('title_id'):
            title_ids.add(item['title_id'])
    for item in history:
        if item.get('title_id'):
            title_ids.add(item['title_id'])

    title_names = {}
    try:
        with titles.titledb_session() as titledb_loaded:
            if titledb_loaded:
                for tid in title_ids:
                    try:
                        info = titles.get_game_info(tid)
                        if info and info.get('name'):
                            title_names[tid] = info.get('name')
                    except Exception:
                        pass
    except Exception:
        title_names = {}

    for item in live:
        tid = item.get('title_id')
        if tid and tid in title_names:
            item['title_name'] = title_names[tid]
    for item in history:
        tid = item.get('title_id')
        if tid and tid in title_names:
            item['title_name'] = title_names[tid]

    return jsonify({
        'success': True,
        'live_transfers': live,
        'connected_clients': clients,
        'access_history': history,
        'access_history_error': history_error,
    })


@app.get('/api/admin/clients-history')
@access_required('admin')
def admin_clients_history_api():
    limit = request.args.get('limit', 250)
    try:
        limit = int(limit)
    except Exception:
        limit = 250
    limit = max(1, min(limit, CLIENTS_HISTORY_API_MAX_LIMIT))
    try:
        history = get_access_events(limit=limit, kinds=['client_seen'])
        _attach_client_meta(history)
        return jsonify({'success': True, 'history': history})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e), 'history': []}), 500


@app.get('/api/admin/clients-history.csv')
@access_required('admin')
def admin_clients_history_csv_api():
    limit = request.args.get('limit', 2000)
    try:
        limit = int(limit)
    except Exception:
        limit = 2000
    limit = max(1, min(limit, CLIENTS_HISTORY_CSV_MAX_LIMIT))

    try:
        items = get_access_events(limit=limit, kinds=['client_seen'])
        _attach_client_meta(items)
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

    import csv
    import io
    from datetime import datetime

    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator='\n')
    writer.writerow(['at', 'user', 'remote_addr', 'user_agent', 'theme', 'uid', 'version', 'revision', 'language', 'hauth', 'uauth'])
    for item in (items or []):
        at = item.get('at')
        at_iso = ''
        try:
            if at:
                at_iso = datetime.utcfromtimestamp(int(at)).isoformat() + 'Z'
        except Exception:
            at_iso = ''
        writer.writerow([
            at_iso,
            item.get('user') or '',
            item.get('remote_addr') or '',
            item.get('user_agent') or '',
            item.get('theme') or '',
            item.get('uid') or '',
            item.get('version') or '',
            item.get('revision') or '',
            item.get('language') or '',
            item.get('hauth') or '',
            item.get('uauth') or '',
        ])

    csv_text = buf.getvalue()
    resp = Response(csv_text, mimetype='text/csv')
    resp.headers['Content-Disposition'] = 'attachment; filename="clients_history.csv"'
    return resp


@app.post('/api/admin/clients-history/clear')
@access_required('admin')
def admin_clients_history_clear_api():
    try:
        ok = delete_access_events(kinds=['client_seen'])
        if not ok:
            return jsonify({'success': False, 'error': 'Failed to clear client history.'}), 500
        return jsonify({'success': True})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.post('/api/admin/access-history/clear')
@access_required('admin')
def admin_access_history_clear_api():
    data = request.json or {}
    include_clients = bool(data.get('include_clients', False))
    try:
        if include_clients:
            ok = delete_access_events()
        else:
            ok = delete_access_events_excluding(kinds=['client_seen'])

        if not ok:
            return jsonify({'success': False, 'error': 'Failed to clear access history.'}), 500
        return jsonify({'success': True})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.post('/api/admin/blacklist-ip')
@access_required('admin')
def admin_blacklist_ip_api():
    data = request.json or {}
    ip_value = str(data.get('ip') or '').strip()
    if not ip_value:
        return jsonify({'success': False, 'error': 'Missing IP.'}), 400
    try:
        settings = load_settings(force_reload=True)
        security = settings.get('security') or {}
        existing = security.get('auth_permanent_ip_blacklist') or []
        entries = [str(item).strip() for item in existing if str(item).strip()]
        if ip_value not in entries:
            entries.append(ip_value)
        set_security_settings({'auth_permanent_ip_blacklist': entries})
        reload_conf()
        return jsonify({'success': True, 'blacklist': entries})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.get('/api/settings')
@access_required('admin')
def get_settings_api():
    reload_conf()
    settings = copy.deepcopy(app_settings)
    settings.setdefault('shop', {})
    hauth_value = settings['shop'].get('hauth')
    settings['shop']['hauth_value'] = hauth_value or ''
    settings['shop']['hauth'] = bool(hauth_value)
    settings['shop']['fast_transfer_mode'] = bool(settings['shop'].get('fast_transfer_mode'))
    settings['shop']['cyberfoil_virtual_compressed_stream'] = bool(
        settings['shop'].get('cyberfoil_virtual_compressed_stream', True)
    )

    # Surface the effective public key in the UI even if it isn't in settings.yaml yet.
    settings['shop']['public_key'] = settings['shop'].get('public_key') or TINFOIL_PUBLIC_KEY
    try:
        scheduler = getattr(app, 'scheduler', None)
        if scheduler:
            job = scheduler.scheduled_jobs.get(LIBRARY_MAINTENANCE_JOB_ID)
            last_run = job.get('last_run') if job else None
            settings.setdefault('library', {})
            settings['library']['maintenance_last_run'] = last_run.isoformat() if last_run else None
    except Exception:
        pass
    settings.setdefault('downloads', {})
    settings['downloads']['client_capabilities'] = get_supported_download_clients()
    return jsonify(settings)

@app.post('/api/settings/content-filter')
@access_required('admin')
def set_content_filter_settings_api():
    data = request.json or {}
    block_unrated = bool(data.get('block_unrated'))
    set_content_filter_settings({'block_unrated': block_unrated})
    reload_conf()
    # Encrypted shop payloads vary by filter; drop caches so changes apply now.
    _invalidate_shop_root_cache()
    return jsonify({'success': True, 'errors': []})


@app.post('/api/settings/titles')
@access_required('admin')
def set_titles_settings_api():
    settings = request.json
    region = settings['region']
    language = settings['language']
    prefer_english_metadata = bool(settings.get('prefer_english_metadata'))
    languages_file = os.path.join(TITLEDB_DIR, 'languages.json')
    if os.path.exists(languages_file):
        with open(languages_file) as f:
            languages = json.load(f)
            languages = dict(sorted(languages.items()))
    else:
        resp = {
            'success': False,
            'errors': [{
                    'path': 'titles',
                    'error': "TitleDB has not been initialized yet. Please wait for the initial update to complete or trigger it manually."
                }]
        }
        return jsonify(resp)

    if region not in languages or language not in languages[region]:
        resp = {
            'success': False,
            'errors': [{
                    'path': 'titles',
                    'error': f"The region/language pair {region}/{language} is not available."
                }]
        }
        return jsonify(resp)
    
    set_titles_settings(region, language, prefer_english_metadata=prefer_english_metadata)
    reload_conf()
    titledb.update_titledb(app_settings)
    post_library_change()
    resp = {
        'success': True,
        'errors': []
    } 
    return jsonify(resp)

@app.post('/api/settings/shop')
@access_required('admin')
def set_shop_settings_api():
    data = request.json or {}
    security_fields = {
        'auth_ip_lockout_enabled',
        'auth_ip_lockout_threshold',
        'auth_ip_lockout_window_seconds',
        'auth_ip_lockout_duration_seconds',
        'auth_permanent_ip_blacklist',
        'auth_blocked_country_codes',
        'auth_allowed_country_codes',
    }
    shop_data = dict(data)
    security_data = {}
    for key in list(shop_data.keys()):
        if key in security_fields:
            security_data[key] = shop_data.pop(key)

    shop_data.setdefault('host', '')
    current_settings = load_settings(force_reload=True)
    merged_shop = dict(current_settings.get('shop', {}))
    merged_shop.update(shop_data)
    success, errors = verify_settings('shop', merged_shop)
    if not success:
        return jsonify({'success': False, 'errors': errors}), 400
    set_shop_settings(shop_data)
    if security_data:
        set_security_settings(security_data)
    reload_conf()
    _invalidate_shop_root_cache()
    resp = {
        'success': True,
        'errors': []
    } 
    return jsonify(resp)

@app.post('/api/settings/downloads')
@access_required('admin')
def set_download_settings_api():
    data = request.json or {}
    set_download_settings(data)
    reload_conf()
    resp = {
        'success': True,
        'errors': []
    }
    return jsonify(resp)

@app.post('/api/settings/library')
@access_required('admin')
def set_library_settings_api():
    data = request.json or {}
    current_settings = load_settings(force_reload=True)
    merged_library = dict(current_settings.get('library', {}))
    merged_library.update(data)
    merged_library['_validate_paths'] = False
    success, errors = verify_settings('library', merged_library)
    if not success:
        return jsonify({'success': False, 'errors': errors}), 400
    set_library_settings(data)
    reload_conf()
    _reschedule_library_maintenance(app)
    resp = {
        'success': True,
        'errors': []
    }
    return jsonify(resp)


@app.post('/api/settings/media-cache/refresh')
@access_required('admin')
def refresh_media_cache_api():
    data = request.json or {}
    refresh_icons = data.get('icons', True)
    refresh_banners = data.get('banners', True)

    def _clear_cache_dir(dirname):
        cache_dir = os.path.join(CACHE_DIR, dirname)
        if not os.path.isdir(cache_dir):
            return 0
        removed = 0
        for filename in os.listdir(cache_dir):
            path = os.path.join(cache_dir, filename)
            if os.path.isfile(path):
                try:
                    os.remove(path)
                    removed += 1
                except Exception:
                    continue
        return removed

    removed_icons = _clear_cache_dir('icons') if refresh_icons else 0
    removed_banners = _clear_cache_dir('banners') if refresh_banners else 0

    return jsonify({
        'success': True,
        'removed_icons': removed_icons,
        'removed_banners': removed_banners
    })

def _get_media_prefetch_ids():
    title_ids = {
        str(row.title_id or '').strip().upper()
        for row in db.session.query(Titles.title_id).all()
        if row.title_id
    }
    app_ids = {
        str(row.app_id or '').strip().upper()
        for row in (
            db.session.query(Apps.app_id)
            .filter(Apps.owned.is_(True))
            .distinct()
            .all()
        )
        if row.app_id
    }
    all_ids = {value for value in (title_ids | app_ids) if value}
    return sorted(all_ids)


@app.post('/api/settings/media-cache/prefetch-icons')
@access_required('admin')
def prefetch_media_icons_api():
    prefetch_ids = _get_media_prefetch_ids()
    cache_dir = os.path.join(CACHE_DIR, 'icons')
    os.makedirs(cache_dir, exist_ok=True)

    fetched = 0
    skipped = 0
    missing = 0
    failed = 0
    failures = []
    headers = {'User-Agent': 'AeroFoil/1.0'}

    titles.load_titledb()
    try:
        for title_id in prefetch_ids:
            if not title_id:
                missing += 1
                continue
            info = titles.get_game_info(title_id)
            icon_url = (info or {}).get('iconUrl') or ''
            if not icon_url:
                missing += 1
                continue
            if icon_url.startswith('//'):
                icon_url = 'https:' + icon_url
            clean_url = icon_url.split('?', 1)[0]
            _, ext = os.path.splitext(clean_url)
            if not ext:
                ext = '.jpg'
            cache_name = f"{title_id}{ext}"
            cache_path = os.path.join(cache_dir, cache_name)
            if os.path.exists(cache_path):
                skipped += 1
                continue
            try:
                response = requests.get(icon_url, timeout=10, headers=headers)
                if response.status_code == 200:
                    with open(cache_path, 'wb') as handle:
                        handle.write(response.content)
                    # Generate a smaller variant for faster web UI loads.
                    size, variant_dir, variant_path = _get_variant_path(cache_dir, cache_name, media_kind='icon')
                    if variant_path:
                        with _media_resize_lock:
                            _resize_image_to_path(cache_path, variant_path, size=size)
                    fetched += 1
                else:
                    failed += 1
                    if len(failures) < 5:
                        failures.append({
                            'title_id': title_id,
                            'status': response.status_code,
                            'url': icon_url
                        })
            except Exception as e:
                failed += 1
                if len(failures) < 5:
                    failures.append({
                        'title_id': title_id,
                        'status': 'error',
                        'url': icon_url,
                        'message': str(e)
                    })
    finally:
        titles.release_titledb()

    return jsonify({
        'success': True,
        'fetched': fetched,
        'skipped': skipped,
        'missing': missing,
        'failed': failed,
        'failures': failures
    })


@app.post('/api/settings/media-cache/prefetch-banners')
@access_required('admin')
def prefetch_media_banners_api():
    prefetch_ids = _get_media_prefetch_ids()
    cache_dir = os.path.join(CACHE_DIR, 'banners')
    os.makedirs(cache_dir, exist_ok=True)

    fetched = 0
    skipped = 0
    missing = 0
    failed = 0
    failures = []
    headers = {'User-Agent': 'AeroFoil/1.0'}

    titles.load_titledb()
    try:
        for title_id in prefetch_ids:
            if not title_id:
                missing += 1
                continue
            info = titles.get_game_info(title_id)
            banner_url = (info or {}).get('bannerUrl') or ''
            if not banner_url:
                missing += 1
                continue
            if banner_url.startswith('//'):
                banner_url = 'https:' + banner_url
            clean_url = banner_url.split('?', 1)[0]
            _, ext = os.path.splitext(clean_url)
            if not ext:
                ext = '.jpg'
            cache_name = f"{title_id}{ext}"
            cache_path = os.path.join(cache_dir, cache_name)
            if os.path.exists(cache_path):
                skipped += 1
                continue
            try:
                response = requests.get(banner_url, timeout=10, headers=headers)
                if response.status_code == 200:
                    with open(cache_path, 'wb') as handle:
                        handle.write(response.content)
                    # Generate a smaller variant for faster web UI loads.
                    size, variant_dir, variant_path = _get_variant_path(cache_dir, cache_name, media_kind='banner')
                    if variant_path:
                        with _media_resize_lock:
                            _resize_image_to_path(cache_path, variant_path, size=size)
                    fetched += 1
                else:
                    failed += 1
                    if len(failures) < 5:
                        failures.append({
                            'title_id': title_id,
                            'status': response.status_code,
                            'url': banner_url
                        })
            except Exception as e:
                failed += 1
                if len(failures) < 5:
                    failures.append({
                        'title_id': title_id,
                        'status': 'error',
                        'url': banner_url,
                        'message': str(e)
                    })
    finally:
        titles.release_titledb()

    return jsonify({
        'success': True,
        'fetched': fetched,
        'skipped': skipped,
        'missing': missing,
        'failed': failed,
        'failures': failures
    })

@app.post('/api/settings/downloads/test-prowlarr')
@access_required('admin')
def test_downloads_prowlarr_api():
    data = request.json or {}
    url = data.get('url', '')
    api_key = data.get('api_key', '')
    try:
        timeout_seconds = int(data.get('timeout_seconds') or 15)
    except (TypeError, ValueError):
        timeout_seconds = 15
    timeout_seconds = max(5, min(timeout_seconds, 180))
    try:
        client = ProwlarrClient(url, api_key, timeout_seconds=timeout_seconds)
        status = client.system_status()
        indexer_ids = data.get('indexer_ids') or []
        warning = None
        if indexer_ids:
            indexers = client.list_indexers()
            available_ids = {item.get('id') for item in (indexers or [])}
            missing = [idx for idx in indexer_ids if idx not in available_ids]
            if missing:
                warning = f"Missing indexer IDs: {', '.join(str(x) for x in missing)}"
        return jsonify({
            'success': True,
            'message': f"Prowlarr OK ({status.get('version', 'unknown')})",
            'warning': warning
        })
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.post('/api/settings/downloads/test-client')
@access_required('admin')
def test_downloads_client_api():
    data = request.json or {}
    diagnostics = get_download_client_diagnostics(
        '',
        {
            'type': data.get('type', ''),
            'url': data.get('url', ''),
            'username': data.get('username', ''),
            'password': data.get('password', ''),
            'api_key': data.get('api_key', ''),
        }
    ) or {}
    capabilities = diagnostics.get('capabilities') or {}
    ok, message = test_download_client(
        client_type=data.get('type', ''),
        url=data.get('url', ''),
        username=data.get('username', ''),
        password=data.get('password', ''),
        api_key=data.get('api_key', '')
    )
    detail = None
    failure_kind = None
    message_text = str(message or '').strip()
    message_lower = message_text.lower()
    missing_fields = diagnostics.get('missing') if isinstance(diagnostics, dict) else []
    if ok:
        failure_kind = None
    elif isinstance(missing_fields, list) and missing_fields:
        failure_kind = 'missing_credentials'
        detail = f"Missing required fields: {', '.join(str(field) for field in missing_fields)}."
    elif (
        'authentication failed' in message_lower
        or 'login failed' in message_lower
        or 'unauthorized' in message_lower
        or '(401' in message_lower
        or re.search(r'(^|\s|\()401(\b|\)|\.)', message_lower)
    ):
        failure_kind = 'authentication'
        detail = 'Authentication failed. Verify username/password or API key for this client.'
    elif (
        'forbidden' in message_lower
        or '(403' in message_lower
        or re.search(r'(^|\s|\()403(\b|\)|\.)', message_lower)
    ):
        failure_kind = 'authorization'
        detail = 'Client denied access. Check account permissions and client security settings.'
    elif 'timeout' in message_lower or 'timed out' in message_lower:
        failure_kind = 'timeout'
        detail = 'Connection timed out. Verify the URL/port, client availability, and network reachability.'
    elif 'url is required' in message_lower or 'url is invalid' in message_lower:
        failure_kind = 'invalid_url'
        detail = 'Client URL is invalid or missing. Include protocol and port (for example http://host:8080).'
    elif 'connection' in message_lower or 'refused' in message_lower or 'failed to establish a new connection' in message_lower:
        failure_kind = 'connection'
        detail = 'Could not connect to the client. Confirm the host, port, and firewall/network settings.'
    elif 'unsupported' in message_lower:
        failure_kind = 'unsupported_client'
        detail = 'Selected client type is not supported for testing.'
    else:
        failure_kind = 'unknown'
        detail = 'Client test failed. Review URL, credentials, and server logs for more detail.'
    download_path = (data.get('download_path') or '').strip()
    warning = None
    supports_download_path = bool(capabilities.get('supports_download_path'))
    if ok and download_path and supports_download_path:
        if not os.path.isdir(download_path):
            warning = f"Download path not found: {download_path}"
        elif not os.access(download_path, os.W_OK):
            warning = f"Download path not writable: {download_path}"
    return jsonify({
        'success': ok,
        'message': message,
        'detail': detail,
        'failure_kind': failure_kind,
        'warning': warning,
        'diagnostics': diagnostics,
    })

@app.post('/api/downloads/manual')
@access_required('admin')
def manual_download_update():
    data = request.json or {}
    title_id = data.get('title_id')
    version = data.get('version')
    if not title_id or version is None:
        return jsonify({'success': False, 'message': 'Missing title ID or version.'})
    try:
        ok, message = manual_search_update(title_id=title_id, version=version)
        return jsonify({'success': ok, 'message': message})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.post('/api/downloads/manual-search')
@access_required('admin')
def manual_search_update_options():
    data = request.json or {}
    title_id = data.get('title_id')
    version = data.get('version')
    if not title_id or version is None:
        return jsonify({'success': False, 'message': 'Missing title ID or version.', 'results': []})
    try:
        ok, message, results = search_update_options(title_id=title_id, version=version)
        return jsonify({'success': ok, 'message': message, 'results': results})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e), 'results': []})

@app.get('/api/downloads/search')
@access_required('admin')
def downloads_search():
    query = request.args.get('query', '').strip()
    apply_settings = request.args.get('apply_settings', '').strip() in ('1', 'true', 'yes')
    extra_blacklist_terms = []
    for raw_value in request.args.getlist('extra_blacklist'):
        for term in str(raw_value or '').split(','):
            normalized = term.strip()
            if normalized:
                extra_blacklist_terms.append(normalized)
    if not query:
        return jsonify({'success': False, 'message': 'Missing query.'})
    settings = load_settings()
    downloads = settings.get('downloads', {})
    prowlarr_cfg = downloads.get('prowlarr', {})
    if not prowlarr_cfg.get('url') or not prowlarr_cfg.get('api_key'):
        return jsonify({'success': False, 'message': 'Prowlarr is not configured.'})
    try:
        try:
            timeout_seconds = int(prowlarr_cfg.get('timeout_seconds') or 15)
        except (TypeError, ValueError):
            timeout_seconds = 15
        timeout_seconds = max(5, min(timeout_seconds, 180))
        search_limit = _get_prowlarr_search_limit(prowlarr_cfg)
        full_query = _normalize_download_search_query(query, downloads)
        if apply_settings:
            prefix = _normalize_download_search_query(downloads.get('search_prefix') or '', downloads)
            suffix = _normalize_download_search_query(downloads.get('search_suffix') or '', downloads)
            if prefix and not full_query.lower().startswith(prefix.lower()):
                full_query = f"{prefix} {full_query}".strip()
            if suffix and not full_query.lower().endswith(suffix.lower()):
                full_query = f"{full_query} {suffix}".strip()
        client = ProwlarrClient(prowlarr_cfg['url'], prowlarr_cfg['api_key'], timeout_seconds=timeout_seconds)
        logger.info(f'Prowlarr search (manual): "{full_query}"')
        results = client.search(
            full_query,
            indexer_ids=prowlarr_cfg.get('indexer_ids') or [],
            categories=prowlarr_cfg.get('categories') or [],
            limit=search_limit,
        )
        if apply_settings:
            results = filter_download_search_results(
                results,
                downloads,
                blacklist_terms=extra_blacklist_terms,
            )
        trimmed = _trim_download_search_results(results, limit=50)
        return jsonify({'success': True, 'results': trimmed})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.post('/api/downloads/queue')
@access_required('admin')
def downloads_queue():
    data = request.json or {}
    download_url = str(data.get('download_url') or '')
    expected_name = data.get('title')
    title_id = data.get('title_id')
    protocol = data.get('protocol')
    update_only = bool(data.get('update_only', False))
    dlc_only = bool(data.get('dlc_only', False))
    expected_version = data.get('expected_version')
    if not download_url:
        return jsonify({'success': False, 'message': 'Missing download URL.'})
    url_digest = hashlib.sha256(download_url.encode('utf-8', errors='ignore')).hexdigest()[:12]
    logger.debug(
        'Queue download request: url_len=%s url_sha12=%s is_magnet=%s title_id=%s update_only=%s dlc_only=%s',
        len(download_url),
        url_digest,
        download_url.lower().startswith('magnet:?'),
        title_id,
        update_only,
        dlc_only,
    )
    ok, message = queue_download_url(
        download_url,
        expected_name=expected_name,
        update_only=update_only,
        dlc_only=dlc_only,
        expected_version=expected_version,
        title_id=title_id,
        protocol=protocol,
    )
    return jsonify({'success': ok, 'message': message})

@app.post('/api/manage/organize')
@access_required('admin')
def manage_organize_library():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    verbose = bool(data.get('verbose', False))
    results = organize_library(dry_run=dry_run, verbose=verbose)
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.post('/api/manage/delete-updates')
@access_required('admin')
def manage_delete_updates():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    verbose = bool(data.get('verbose', False))
    results = delete_older_updates(dry_run=dry_run, verbose=verbose)
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.post('/api/manage/delete-duplicates')
@access_required('admin')
def manage_delete_duplicates():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    verbose = bool(data.get('verbose', False))
    results = delete_duplicates(dry_run=dry_run, verbose=verbose)
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.post('/api/manage/delete-library-content')
@access_required('admin')
def manage_delete_library_content():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    verbose = bool(data.get('verbose', False))
    scope = str(data.get('scope') or '').strip()
    title_id = data.get('title_id')
    app_id = data.get('app_id')
    app_type = data.get('app_type')
    version = data.get('version')

    results = delete_library_content(
        scope=scope,
        dry_run=dry_run,
        verbose=verbose,
        title_id=title_id,
        app_id=app_id,
        app_type=app_type,
        version=version,
    )
    if not dry_run and results.get('mutated'):
        _run_post_library_change()
    status_code = 200 if results.get('success') else 400
    return jsonify(results), status_code

@app.post('/api/manage/delete-orphaned-addons')
@access_required('admin')
def manage_delete_orphaned_addons():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    verbose = bool(data.get('verbose', False))
    results = delete_orphaned_addons(dry_run=dry_run, verbose=verbose)
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.post('/api/manage/check-downloads')
@access_required('admin')
def manage_check_downloads():
    ok, message = check_completed_downloads(scan_cb=scan_library, post_cb=post_library_change)
    return jsonify({'success': ok, 'message': message})


@app.post('/api/downloads/check-completed')
@access_required('admin')
def downloads_check_completed():
    ok, message = check_completed_downloads(scan_cb=scan_library, post_cb=post_library_change)
    return jsonify({'success': ok, 'message': message})


@app.get('/api/downloads/queue')
@access_required('admin')
def downloads_queue_state():
    state = get_downloads_state()
    return jsonify({'success': True, 'state': state})


@app.post('/api/downloads/queue/delete')
@access_required('admin')
def downloads_queue_delete():
    data = request.json or {}
    ok, message = remove_pending_download(data.get('key'))
    state = get_downloads_state()
    return jsonify({'success': ok, 'message': message, 'state': state})


@app.post('/api/downloads/duplicates/delete')
@access_required('admin')
def downloads_duplicates_delete():
    data = request.json or {}
    ok, message = remove_duplicate_download(data.get('id'))
    state = get_downloads_state()
    return jsonify({'success': ok, 'message': message, 'state': state})


@app.post('/api/downloads/duplicates/dismiss')
@access_required('admin')
def downloads_duplicates_dismiss():
    data = request.json or {}
    ok, message = dismiss_duplicate_download(data.get('id'), fingerprint=data.get('fingerprint'))
    state = get_downloads_state()
    return jsonify({'success': ok, 'message': message, 'state': state})


@app.get('/api/downloads/active')
@access_required('admin')
def downloads_active():
    ok, message, items, summary = get_active_downloads()
    return jsonify({'success': ok, 'message': message, 'items': items, 'summary': summary})


@app.get('/api/manage/downloads-queue')
@access_required('admin')
def manage_downloads_queue():
    state = get_downloads_state()
    return jsonify({'success': True, 'state': state})

@app.post('/api/manage/convert')
@access_required('admin')
def manage_convert_nsz():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    delete_original = bool(data.get('delete_original', True))
    verbose = bool(data.get('verbose', False))
    verify = bool(data.get('verify', True))
    threads = data.get('threads')
    command = data.get('command')
    results = convert_to_nsz(
        command_template=command,
        delete_original=delete_original,
        dry_run=dry_run,
        verbose=verbose,
        threads=threads,
        verify=verify
    )
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.get('/api/manage/convertibles')
@access_required('admin')
def manage_convertible_files():
    library_id = request.args.get('library_id')
    files = list_convertible_files(library_id=int(library_id)) if library_id else list_convertible_files()
    return jsonify({'success': True, 'files': files})

@app.post('/api/manage/convert-single')
@access_required('admin')
def manage_convert_single():
    data = request.json or {}
    file_id = data.get('file_id')
    dry_run = bool(data.get('dry_run', False))
    delete_original = bool(data.get('delete_original', True))
    verbose = bool(data.get('verbose', False))
    verify = bool(data.get('verify', True))
    threads = data.get('threads')
    command = data.get('command')
    if not file_id:
        return jsonify({'success': False, 'errors': ['Missing file id.'], 'converted': 0, 'skipped': 0, 'details': []})
    results = convert_single_to_nsz(
        file_id=int(file_id),
        command_template=command,
        delete_original=delete_original,
        dry_run=dry_run,
        verbose=verbose,
        threads=threads,
        verify=verify
    )
    if not dry_run and results.get('mutated'):
        post_library_change()
    return jsonify(results)

@app.post('/api/manage/convert-job')
@access_required('admin')
def manage_convert_job():
    data = request.json or {}
    dry_run = bool(data.get('dry_run', False))
    delete_original = bool(data.get('delete_original', True))
    verbose = bool(data.get('verbose', False))
    verify = bool(data.get('verify', True))
    threads = data.get('threads')
    library_id = data.get('library_id')
    timeout_seconds = data.get('timeout_seconds')
    command = data.get('command')

    job_id = _create_job('convert')

    def _run_job():
        with app.app_context():
            try:
                results = convert_to_nsz(
                    command_template=command,
                    delete_original=delete_original,
                    dry_run=dry_run,
                    verbose=verbose,
                    log_cb=lambda msg: _job_log(job_id, msg),
                    progress_cb=lambda done, total: _job_progress(job_id, done, total),
                    stream_output=True,
                    threads=threads,
                    verify=verify,
                    library_id=library_id,
                    cancel_cb=lambda: _job_is_cancelled(job_id),
                    timeout_seconds=timeout_seconds,
                    min_size_bytes=200 * 1024 * 1024
                )
            except Exception as e:
                db.session.rollback()
                logger.exception('Unexpected error while running conversion job %s', job_id)
                results = {
                    'success': False,
                    'converted': 0,
                    'skipped': 0,
                    'deleted': 0,
                    'moved': 0,
                    'errors': [f'Unexpected conversion job error: {e}'],
                    'details': []
                }
            _job_finish(job_id, results)
            if not dry_run and results.get('mutated'):
                try:
                    post_library_change()
                except Exception:
                    logger.exception('Conversion job %s succeeded but post_library_change failed', job_id)

    thread = threading.Thread(target=_run_job, daemon=True)
    thread.start()
    return jsonify({'success': True, 'job_id': job_id})

@app.post('/api/manage/convert-single-job')
@access_required('admin')
def manage_convert_single_job():
    data = request.json or {}
    file_id = data.get('file_id')
    dry_run = bool(data.get('dry_run', False))
    delete_original = bool(data.get('delete_original', True))
    verbose = bool(data.get('verbose', False))
    verify = bool(data.get('verify', True))
    threads = data.get('threads')
    timeout_seconds = data.get('timeout_seconds')
    command = data.get('command')
    if not file_id:
        return jsonify({'success': False, 'errors': ['Missing file id.']})

    job_id = _create_job('convert-single', total=1)

    def _run_job():
        with app.app_context():
            try:
                results = convert_single_to_nsz(
                    file_id=int(file_id),
                    command_template=command,
                    delete_original=delete_original,
                    dry_run=dry_run,
                    verbose=verbose,
                    log_cb=lambda msg: _job_log(job_id, msg),
                    progress_cb=lambda done, total: _job_progress(job_id, done, total),
                    stream_output=True,
                    threads=threads,
                    verify=verify,
                    cancel_cb=lambda: _job_is_cancelled(job_id),
                    timeout_seconds=timeout_seconds
                )
            except Exception as e:
                db.session.rollback()
                logger.exception('Unexpected error while running single conversion job %s', job_id)
                results = {
                    'success': False,
                    'converted': 0,
                    'skipped': 0,
                    'deleted': 0,
                    'moved': 0,
                    'errors': [f'Unexpected single conversion job error: {e}'],
                    'details': []
                }
            _job_finish(job_id, results)
            if not dry_run and results.get('mutated'):
                try:
                    post_library_change()
                except Exception:
                    logger.exception('Single conversion job %s succeeded but post_library_change failed', job_id)

    thread = threading.Thread(target=_run_job, daemon=True)
    thread.start()
    return jsonify({'success': True, 'job_id': job_id})

@app.get('/api/manage/convert-job/<job_id>')
@access_required('admin')
def manage_convert_job_status(job_id):
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        if not job:
            return jsonify({'success': False, 'error': 'Job not found.'}), 404
        return jsonify({'success': True, 'job': job})

@app.post('/api/manage/convert-job/<job_id>/cancel')
@access_required('admin')
def manage_convert_job_cancel(job_id):
    with conversion_jobs_lock:
        job = conversion_jobs.get(job_id)
        if not job:
            return jsonify({'success': False, 'error': 'Job not found.'}), 404
        job['cancelled'] = True
        job['status'] = 'cancelled'
        job['updated_at'] = time.time()
    return jsonify({'success': True})

@app.get('/api/manage/jobs')
@access_required('admin')
def manage_jobs_list():
    limit = request.args.get('limit', 20)
    try:
        limit = int(limit)
    except ValueError:
        limit = 20
    with conversion_jobs_lock:
        jobs = sorted(conversion_jobs.values(), key=lambda item: item['created_at'], reverse=True)[:limit]
        return jsonify({'success': True, 'jobs': jobs})

@app.get('/api/manage/health')
@access_required('admin')
def manage_health():
    nsz_path = None
    try:
        nsz_path = _get_nsz_runner()
    except NameError:
        nsz_path = None
    keys_file = KEYS_FILE
    keys_ok = os.path.exists(KEYS_FILE)
    return jsonify({
        'success': True,
        'nsz_exe': nsz_path,
        'nsz_runner': nsz_path,
        'keys_file': keys_file,
        'keys_present': keys_ok
    })

@app.get('/api/manage/diagnostics/memory')
@app.get('/api/diagnostics/memory')
@access_required('admin')
def manage_memory_diagnostics():
    now = time.time()
    with scan_lock:
        scan_busy = bool(scan_in_progress)
    with library_rebuild_lock:
        rebuild_state = dict(library_rebuild_status)
    with shop_sections_cache_lock:
        in_memory_payload = shop_sections_cache.get('payload')
        in_memory_limit = shop_sections_cache.get('limit')
        in_memory_timestamp = float(shop_sections_cache.get('timestamp') or 0)

    disk_cache = _load_shop_sections_cache_from_disk()
    disk_payload = (disk_cache or {}).get('payload')
    disk_ts = float((disk_cache or {}).get('timestamp') or 0)

    sqlalchemy_diag = {
        'current_session_identity_map_size': len(db.session.identity_map),
        'new_count': len(getattr(db.session, 'new', []) or []),
        'dirty_count': len(getattr(db.session, 'dirty', []) or []),
    }

    return jsonify({
        'success': True,
        'timestamp': now,
        'process': _read_proc_meminfo_bytes(),
        'python_gc': {
            'counts': list(gc.get_count()),
        },
        'scan': {
            'scan_in_progress': scan_busy,
            'library_rebuild': rebuild_state,
            'library_memory_diagnostics': get_memory_diagnostics(),
        },
        'sqlalchemy': sqlalchemy_diag,
        'titledb': titles.get_titledb_diagnostics(),
        'shop_sections_cache': {
            'config': {
                'ttl_s': SHOP_SECTIONS_CACHE_TTL_S,
                'all_items_cap': SHOP_SECTIONS_ALL_ITEMS_CAP,
                'max_in_memory_bytes': SHOP_SECTIONS_MAX_IN_MEMORY_BYTES,
            },
            'in_memory': {
                'present': in_memory_payload is not None,
                'limit': in_memory_limit,
                'timestamp': in_memory_timestamp,
                'age_s': max(0.0, now - in_memory_timestamp) if in_memory_timestamp else None,
                'summary': _summarize_shop_sections_payload(in_memory_payload),
            },
            'disk': {
                'present': bool(disk_cache),
                'limit': (disk_cache or {}).get('limit'),
                'timestamp': disk_ts if disk_ts else None,
                'age_s': max(0.0, now - disk_ts) if disk_ts else None,
                'summary': _summarize_shop_sections_payload(disk_payload),
            },
        }
    })

@app.get('/api/manage/libraries')
@access_required('admin')
def manage_libraries_list():
    libraries = get_libraries()
    return jsonify({
        'success': True,
        'libraries': [{'id': lib.id, 'path': lib.path} for lib in libraries]
    })

@app.route('/api/settings/library/paths', methods=['GET', 'POST', 'DELETE'])
@access_required('admin')
def library_paths_api():
    global watcher
    if request.method == 'POST':
        data = request.json
        success, errors = add_library_complete(app, watcher, data['path'])
        if success:
            reload_conf()
            post_library_change()
        resp = {
            'success': success,
            'errors': errors
        }
    elif request.method == 'GET':
        reload_conf()
        resp = {
            'success': True,
            'errors': [],
            'paths': app_settings['library']['paths']
        }    
    elif request.method == 'DELETE':
        data = request.json
        success, errors = remove_library_complete(app, watcher, data['path'])
        if success:
            reload_conf()
            post_library_change()
        resp = {
            'success': success,
            'errors': errors
        }
    return jsonify(resp)


@app.get('/api/titledb/search')
@access_required('shop')
def titledb_search_api():
    query = request.args.get('q', '').strip()
    limit = request.args.get('limit', 20)
    try:
        limit = int(limit)
    except Exception:
        limit = 20

    if not query:
        return jsonify({'success': True, 'results': []})

    titles.load_titledb()
    try:
        results = titles.search_titles(query, limit=limit)
        # mark items already in library
        existing = set((t.title_id or '').upper() for t in Titles.query.with_entities(Titles.title_id).all())
        for r in results:
            r['in_library'] = (r.get('id') or '').upper() in existing
        return jsonify({'success': True, 'results': results})
    finally:
        titles.release_titledb()

@app.post('/api/upload')
@access_required('admin')
def upload_file():
    errors = []
    success = False

    if 'file' not in request.files:
        return api_error('No file provided', 400)
    
    file = request.files['file']
    
    # Validate file size
    file.seek(0, os.SEEK_END)
    file_size = file.tell()
    file.seek(0)
    is_valid_size, size_error = validate_file_size(file_size)
    if not is_valid_size:
        return api_error(size_error, 400)
    if file and allowed_file(file.filename):
        # filename = secure_filename(file.filename)
        file.save(KEYS_FILE + '.tmp')
        logger.info(f'Validating {file.filename}...')
        valid, validation_errors = validate_keys_file(KEYS_FILE + '.tmp')
        if valid:
            os.replace(KEYS_FILE + '.tmp', KEYS_FILE)
            success = True
            logger.info('Successfully saved valid keys.txt')
            reload_conf()
            post_library_change()
        else:
            os.remove(KEYS_FILE + '.tmp')
            logger.error(f'Invalid keys from {file.filename}')
            errors = validation_errors or ['invalid_keys_file']

    resp = {
        'success': success,
        'errors': errors
    } 
    return jsonify(resp)


@app.delete('/api/upload/keys')
@access_required('admin')
def delete_keys_file():
    success = False
    errors = []

    try:
        if os.path.exists(KEYS_FILE):
            os.remove(KEYS_FILE)
            success = True
            logger.info('Deleted keys.txt')
            reload_conf()
            post_library_change()
        else:
            errors.append('keys_file_not_found')
    except Exception as e:
        logger.error(f'Failed to delete keys file {KEYS_FILE}: {e}')
        errors.append(str(e))

    return jsonify({
        'success': success,
        'errors': errors
    })


@app.post('/api/upload/library')
@access_required('admin')
def upload_library_files():
    upload_id = str(request.form.get('upload_id') or '').strip()
    if not upload_id:
        upload_id = str(uuid.uuid4())
    _set_upload_job_stage(upload_id, 'starting', 'Preparing upload request...')
    try:
        files = request.files.getlist('files')
    except RequestEntityTooLarge:
        _set_upload_job_stage(upload_id, 'failed', 'Upload rejected: request too large.', status='failed')
        raise
    except Exception as e:
        logger.exception("Failed to parse upload request")
        parsed_message = str(e).strip() or e.__class__.__name__
        _set_upload_job_stage(upload_id, 'failed', f'Unable to parse upload request: {parsed_message}', status='failed')
        return jsonify({
            'success': False,
            'message': f'Unable to parse upload request: {parsed_message}',
            'uploaded': 0,
            'skipped': 0,
            'errors': [parsed_message],
            'upload_id': upload_id,
        }), 400

    if not files:
        _set_upload_job_stage(upload_id, 'failed', 'No files uploaded.', status='failed')
        return jsonify({'success': False, 'message': 'No files uploaded.', 'uploaded': 0, 'skipped': 0, 'errors': [], 'upload_id': upload_id}), 400

    library_id = request.form.get('library_id')
    library_path = None
    if library_id:
        library_path = get_library_path(library_id)
    if not library_path:
        library_paths = get_libraries_path()
        library_path = library_paths[0] if library_paths else None

    if not library_path:
        _set_upload_job_stage(upload_id, 'failed', 'No library path configured.', status='failed')
        return jsonify({'success': False, 'message': 'No library path configured.', 'uploaded': 0, 'skipped': 0, 'errors': [], 'upload_id': upload_id}), 400

    try:
        os.makedirs(library_path, exist_ok=True)
    except Exception as e:
        logger.error("Unable to create/access library path %s: %s", library_path, e)
        _set_upload_job_stage(upload_id, 'failed', f'Cannot access library path: {library_path}', status='failed')
        return jsonify({
            'success': False,
            'message': f'Cannot access library path: {library_path}',
            'uploaded': 0,
            'skipped': len(files),
            'errors': [str(e)],
            'upload_id': upload_id,
        }), 500

    allowed_exts = {'nsp', 'nsz', 'xci', 'xcz'}
    uploaded = 0
    skipped = 0
    errors = []
    saved_paths = []
    _set_upload_job_stage(upload_id, 'saving', f'Saving {len(files)} file(s)...', extra={'total_files': len(files), 'uploaded': 0, 'skipped': 0})

    for index, file in enumerate(files):
        filename = secure_filename(file.filename or '')
        if not filename:
            errors.append("A file has an invalid or empty filename.")
            skipped += 1
            _set_upload_job_stage(upload_id, 'saving', f"Saving files... ({index + 1}/{len(files)})", extra={'uploaded': uploaded, 'skipped': skipped})
            continue
        
        # Validate file size (use library limit for game files)
        file.seek(0, os.SEEK_END)
        file_size = file.tell()
        file.seek(0)
        is_valid_size, size_error = validate_library_file_size(file_size)
        if not is_valid_size:
            errors.append(f"{filename}: {size_error}")
            skipped += 1
            _set_upload_job_stage(upload_id, 'saving', f"Saving files... ({index + 1}/{len(files)})", extra={'uploaded': uploaded, 'skipped': skipped})
            continue
        
        ext = filename.rsplit('.', 1)[-1].lower() if '.' in filename else ''
        if ext not in allowed_exts:
            errors.append(f"{filename}: unsupported extension '{ext or 'none'}'.")
            skipped += 1
            _set_upload_job_stage(upload_id, 'saving', f"Saving files... ({index + 1}/{len(files)})", extra={'uploaded': uploaded, 'skipped': skipped})
            continue
        dest_path = _ensure_unique_path(os.path.join(library_path, filename))
        try:
            file.save(dest_path)
            uploaded += 1
            saved_paths.append(dest_path)
            _set_upload_job_stage(upload_id, 'saving', f"Saved file {index + 1}/{len(files)}: {filename}", extra={'uploaded': uploaded, 'skipped': skipped})
        except Exception as e:
            logger.error("Failed to save uploaded file %s to %s: %s", filename, library_path, e)
            errors.append(str(e))
            skipped += 1
            _set_upload_job_stage(upload_id, 'saving', f"Saving files... ({index + 1}/{len(files)})", extra={'uploaded': uploaded, 'skipped': skipped})

    if uploaded:
        _set_upload_job_stage(upload_id, 'scanning', 'Scanning library for uploaded files...', extra={'uploaded': uploaded, 'skipped': skipped})
        scan_library_path(library_path)
        _set_upload_job_stage(upload_id, 'queueing', 'Queueing uploaded files for organization...', extra={'uploaded': uploaded, 'skipped': skipped})
        enqueue_organize_paths(saved_paths)
        _set_upload_job_stage(upload_id, 'refreshing', 'Refreshing library metadata...', extra={'uploaded': uploaded, 'skipped': skipped})
        post_library_change()

    success = uploaded > 0
    message = None
    if success:
        message = f"Uploaded {uploaded} file(s)."
        if skipped:
            message += f" Skipped {skipped}."
    else:
        if errors:
            message = errors[0]
        elif skipped:
            message = "All selected files were skipped."
        else:
            message = "Upload failed."

    if success:
        _set_upload_job_stage(upload_id, 'completed', message or 'Upload complete.', status='success', extra={'uploaded': uploaded, 'skipped': skipped})
    else:
        _set_upload_job_stage(upload_id, 'failed', message or 'Upload failed.', status='failed', extra={'uploaded': uploaded, 'skipped': skipped})

    return jsonify({
        'success': success,
        'message': message,
        'uploaded': uploaded,
        'skipped': skipped,
        'errors': errors,
        'upload_id': upload_id,
    }), (200 if success else 400)


@app.get('/api/upload/library/status/<upload_id>')
@access_required('admin')
def upload_library_status(upload_id):
    lookup_id = str(upload_id or '').strip()
    if not lookup_id:
        return jsonify({'success': False, 'message': 'Missing upload id.'}), 400
    with upload_jobs_lock:
        _prune_upload_jobs_unlocked()
        job = upload_jobs.get(lookup_id)
        if not job:
            return jsonify({'success': False, 'message': 'Upload job not found.'}), 404
        payload = dict(job)
    return jsonify({'success': True, 'job': payload})


@app.get('/api/saves/list')
@save_sync_access
def list_saves_api():
    user = getattr(g, 'save_sync_user', None)
    if user is None:
        return api_error('Save sync authorization failed.', 403)

    saves = []
    titledb_loaded = False
    try:
        titledb_loaded = bool(titles.load_titledb())
    except Exception as e:
        logger.warning('Unable to load TitleDB for save metadata: %s', e)

    try:
        is_cyberfoil = _is_cyberfoil_request()
        save_versions = _save_sync_collect_versions(user)
        seen_titles = {
            str(item.get('title_id') or '').strip().upper()
            for item in save_versions
            if str(item.get('title_id') or '').strip()
        }
        for title_id in sorted(seen_titles):
            latest_dir = _save_sync_latest_dir(user, title_id)
            if not os.path.isdir(latest_dir):
                continue
            latest_created_ts = int(time.time())
            try:
                latest_created_ts = int(os.path.getmtime(latest_dir))
            except Exception:
                latest_created_ts = int(time.time())
            save_versions.append({
                'title_id': title_id,
                'save_id': 'latest',
                'size': 0,
                'note': 'latest directory',
                'created_ts': latest_created_ts,
                'created_at': _save_sync_format_created_at(latest_created_ts),
                'download_url': f'/api/saves/download/{title_id}/latest.zip',
                'delete_url': '',
                'archive_path': '',
                'legacy': False,
                'latest_directory': True,
            })
        latest_by_title = {}
        for version in save_versions:
            title_id = str(version.get('title_id') or '').strip().upper()
            if not title_id:
                continue
            created_ts = int(version.get('created_ts') or 0)
            save_id = str(version.get('save_id') or '')
            current = latest_by_title.get(title_id)
            if current is None or created_ts > current.get('created_ts', 0):
                latest_by_title[title_id] = {'created_ts': created_ts, 'save_id': save_id}
        title_metadata = {}
        for version in save_versions:
            title_id = str(version.get('title_id') or '').strip().upper()
            if not title_id:
                continue

            cached_meta = title_metadata.get(title_id)
            if cached_meta is None:
                title_name = title_id
                icon_remote_url = ''
                if titledb_loaded:
                    try:
                        info = titles.get_game_info(title_id) or {}
                        resolved_name = str(info.get('name') or '').strip()
                        if resolved_name and resolved_name.lower() != 'unrecognized':
                            title_name = resolved_name
                        icon_remote_url = str(info.get('iconUrl') or '').strip()
                    except Exception as title_err:
                        logger.debug('Failed title metadata lookup for save %s: %s', title_id, title_err)
                cached_meta = {'title_name': title_name, 'icon_remote_url': icon_remote_url}
                title_metadata[title_id] = cached_meta

            save_id = str(version.get('save_id') or '')
            note = _normalize_save_note(version.get('note'))
            created_ts = int(version.get('created_ts') or 0)
            created_at = str(version.get('created_at') or '').strip() or _save_sync_format_created_at(created_ts)
            size = int(version.get('size') or 0)
            download_url = str(version.get('download_url') or '')
            delete_url = str(version.get('delete_url') or '')
            icon_url = f'/api/shop/icon/{title_id}'
            latest_info = latest_by_title.get(title_id) or {}
            is_latest = (
                int(latest_info.get('created_ts') or 0) == created_ts
                and str(latest_info.get('save_id') or '') == save_id
            )
            latest_note = ' [latest]' if (is_cyberfoil and is_latest) else ''
            note_with_latest = f'{note}{latest_note}'.strip()
            saves.append({
                'title_id': title_id,
                'titleId': title_id,
                'app_id': title_id,
                'name': cached_meta['title_name'],
                'title_name': cached_meta['title_name'],
                'titleName': cached_meta['title_name'],
                'size': size,
                'save_id': save_id,
                'saveId': save_id,
                'note': note_with_latest if is_cyberfoil else note,
                'save_note': note_with_latest if is_cyberfoil else note,
                'saveNote': note_with_latest if is_cyberfoil else note,
                'created_at': created_at,
                'createdAt': created_at,
                'created_ts': created_ts,
                'createdTs': created_ts,
                'latest_directory': bool(version.get('latest_directory')),
                'latestDirectory': bool(version.get('latest_directory')),
                'is_latest': is_latest,
                'isLatest': is_latest,
                'latest_available_save_id': str(latest_info.get('save_id') or ''),
                'latestAvailableSaveId': str(latest_info.get('save_id') or ''),
                'icon_url': icon_url,
                'iconUrl': icon_url,
                'icon_remote_url': cached_meta['icon_remote_url'],
                'iconRemoteUrl': cached_meta['icon_remote_url'],
                'download_url': download_url,
                'downloadUrl': download_url,
                'delete_url': delete_url,
                'deleteUrl': delete_url,
            })
    except Exception as e:
        logger.error('Failed to list saves for user %s: %s', getattr(user, 'user', '?'), e)
        return api_error('Failed to list saves.', 500)
    finally:
        try:
            titles.release_titledb()
        except Exception:
            pass

    return jsonify({'saves': saves})


@app.post('/api/saves/upload/<title_id>')
@save_sync_access
def upload_save_api(title_id):
    user = getattr(g, 'save_sync_user', None)
    if user is None:
        return api_error('Save sync authorization failed.', 403)

    normalized_title_id = _save_sync_resolve_title_id(title_id)
    if not normalized_title_id:
        return api_error('Invalid title_id for save upload.', 400)

    if 'file' not in request.files:
        return api_error('No save archive provided.', 400)

    uploaded_file = request.files.get('file')
    if uploaded_file is None or not uploaded_file.filename:
        return api_error('No save archive provided.', 400)

    uploaded_file.seek(0, os.SEEK_END)
    file_size = uploaded_file.tell()
    uploaded_file.seek(0)

    if file_size is None or file_size <= 0:
        return api_error('Save archive is empty.', 400)
    if file_size > MAX_SAVE_UPLOAD_SIZE:
        limit_gb = MAX_SAVE_UPLOAD_SIZE // (1024 * 1024 * 1024)
        return api_error(f'Save archive exceeds maximum limit of {limit_gb}GB.', 400)

    note = _save_sync_resolve_note()
    save_id = _save_sync_generate_save_id(note)
    title_dir = _save_sync_title_dir(user, normalized_title_id)
    os.makedirs(title_dir, exist_ok=True)
    archive_path = _save_sync_archive_path(user, normalized_title_id, save_id=save_id)
    temp_path = archive_path + '.tmp'

    try:
        uploaded_file.save(temp_path)
        if not zipfile.is_zipfile(temp_path):
            os.remove(temp_path)
            return api_error('Uploaded file is not a valid zip archive.', 400)

        os.replace(temp_path, archive_path)
    except Exception as e:
        try:
            if os.path.exists(temp_path):
                os.remove(temp_path)
        except Exception:
            pass
        logger.error('Failed to save uploaded archive for user %s title %s: %s', getattr(user, 'user', '?'), normalized_title_id, e)
        return api_error('Failed to store save archive.', 500)

    created_ts = int(time.time())
    created_at = _save_sync_format_created_at(created_ts)
    metadata = {
        'title_id': normalized_title_id,
        'save_id': save_id,
        'created_at': created_at,
        'created_ts': created_ts,
        'note': note,
        'uploaded_by': str(getattr(user, 'user', '') or ''),
        'size': int(file_size),
    }
    try:
        _save_sync_write_metadata(_save_sync_metadata_path(user, normalized_title_id, save_id), metadata)
    except Exception as e:
        logger.warning('Failed writing save metadata for user %s title %s save %s: %s', getattr(user, 'user', '?'), normalized_title_id, save_id, e)
    try:
        _save_sync_refresh_latest_from_archive(user, normalized_title_id, archive_path)
    except Exception as e:
        logger.warning(
            'Failed to refresh latest extracted save for user %s title %s save %s: %s',
            getattr(user, 'user', '?'),
            normalized_title_id,
            save_id,
            e,
        )

    return api_success({
        'title_id': normalized_title_id,
        'titleId': normalized_title_id,
        'save_id': save_id,
        'saveId': save_id,
        'created_at': created_at,
        'createdAt': created_at,
        'created_ts': created_ts,
        'createdTs': created_ts,
        'note': note,
        'size': int(file_size),
        'download_url': f'/api/saves/download/{normalized_title_id}/{save_id}.zip',
        'downloadUrl': f'/api/saves/download/{normalized_title_id}/{save_id}.zip',
        'delete_url': f'/api/saves/delete/{normalized_title_id}/{save_id}',
        'deleteUrl': f'/api/saves/delete/{normalized_title_id}/{save_id}',
    }, message='Save uploaded successfully.')


@app.get('/api/saves/download/<title_id>/<save_id>')
@app.get('/api/saves/download/<title_id>/<save_id>.zip')
@app.get('/api/saves/download/<title_id>')
@app.get('/api/saves/download/<title_id>.zip')
@save_sync_access
def download_save_api(title_id, save_id=None):
    user = getattr(g, 'save_sync_user', None)
    if user is None:
        return api_error('Save sync authorization failed.', 403)

    requested_save_id = str(save_id or '').strip()
    client_kind = 'cyberfoil' if _is_cyberfoil_request() else 'other'

    normalized_title_id = _normalize_save_title_id(title_id)
    if not normalized_title_id:
        logger.warning(
            'Save download rejected for user %s: invalid title_id=%s save_id=%s client=%s',
            getattr(user, 'user', '?'),
            title_id,
            requested_save_id or '-',
            client_kind,
        )
        return api_error('Invalid title_id for save download.', 400)

    logger.info(
        'Save download request user=%s title=%s save_id=%s client=%s',
        getattr(user, 'user', '?'),
        normalized_title_id,
        requested_save_id or 'latest',
        client_kind,
    )

    selected_archive, resolve_error = _save_sync_resolve_download_archive(user, normalized_title_id, save_id=save_id)
    if selected_archive is None:
        logger.warning(
            'Save download resolve failed user=%s title=%s save_id=%s client=%s error=%s',
            getattr(user, 'user', '?'),
            normalized_title_id,
            requested_save_id or 'latest',
            client_kind,
            resolve_error or 'not found',
        )
        if resolve_error and str(resolve_error).lower().startswith('invalid'):
            return api_error(resolve_error, 400)
        return api_error(resolve_error or 'Save archive not found.', 404)

    archive_path = str(selected_archive.get('archive_path') or '')
    if not os.path.isfile(archive_path):
        logger.warning(
            'Save download archive missing user=%s title=%s save_id=%s path=%s client=%s',
            getattr(user, 'user', '?'),
            normalized_title_id,
            requested_save_id or 'latest',
            archive_path or '-',
            client_kind,
        )
        return api_error('Save archive not found.', 404)

    selected_save_id = str(selected_archive.get('save_id') or '').strip()
    generated_latest = bool(selected_archive.get('generated_latest'))
    archive_size = 0
    try:
        archive_size = int(os.path.getsize(archive_path))
    except Exception:
        archive_size = 0
    if selected_save_id and selected_save_id != 'legacy':
        download_name = f'{normalized_title_id}_{selected_save_id}.zip'
    else:
        download_name = f'{normalized_title_id}.zip'

    logger.info(
        'Save download serving user=%s title=%s resolved_save_id=%s bytes=%s generated_latest=%s client=%s path=%s',
        getattr(user, 'user', '?'),
        normalized_title_id,
        selected_save_id or 'latest',
        archive_size,
        generated_latest,
        client_kind,
        archive_path,
    )

    return send_from_directory(
        os.path.dirname(archive_path),
        os.path.basename(archive_path),
        as_attachment=True,
        download_name=download_name,
        mimetype='application/zip'
    )


@app.route('/api/saves/delete/<title_id>/<save_id>', methods=['DELETE', 'POST'])
@app.route('/api/saves/delete/<title_id>/<save_id>.zip', methods=['DELETE', 'POST'])
@app.route('/api/saves/delete/<title_id>', methods=['DELETE', 'POST'])
@app.route('/api/saves/delete/<title_id>.zip', methods=['DELETE', 'POST'])
@save_sync_access
def delete_save_api(title_id, save_id=None):
    user = getattr(g, 'save_sync_user', None)
    if user is None:
        return api_error('Save sync authorization failed.', 403)

    normalized_title_id = _normalize_save_title_id(title_id)
    if not normalized_title_id:
        return api_error('Invalid title_id for save delete.', 400)

    selected_save_id = None
    if save_id is not None:
        selected_save_id = _normalize_save_id(save_id)
        if not selected_save_id:
            return api_error('Invalid save_id for save delete.', 400)

    deleted_info, delete_error = _save_sync_delete_archive(user, normalized_title_id, save_id=selected_save_id)
    if deleted_info is None:
        status = 404
        error_text = str(delete_error or '')
        if error_text.lower().startswith('invalid'):
            status = 400
        elif error_text and 'failed to delete' in error_text.lower():
            status = 500
        return api_error(delete_error or 'Save archive not found.', status)

    deleted_save_id = str(deleted_info.get('save_id') or '')
    is_legacy = bool(deleted_info.get('legacy'))
    try:
        _save_sync_refresh_latest_for_title(user, normalized_title_id)
    except Exception as e:
        logger.warning(
            'Failed to refresh latest extracted save after delete for user %s title %s: %s',
            getattr(user, 'user', '?'),
            normalized_title_id,
            e,
        )
    return api_success({
        'title_id': normalized_title_id,
        'titleId': normalized_title_id,
        'save_id': deleted_save_id,
        'saveId': deleted_save_id,
        'legacy': is_legacy,
        'deleted': True,
    }, message='Save backup deleted successfully.')


@app.route('/api/titles', methods=['GET'])
@access_required('shop')
def get_all_titles_api():
    start_ts = time.time()

    page = max(1, request.args.get('page', 1, type=int))
    per_page = max(1, min(request.args.get('per_page', 50, type=int), 10000))
    lite = str(request.args.get('lite', '')).lower() in ('1', 'true', 'yes')
    sort_key = str(request.args.get('sort') or 'title_asc').strip().lower()
    search = (request.args.get('search') or '').strip()
    initial = str(request.args.get('initial') or '').strip().upper()
    types = request.args.get('types')
    owned = request.args.get('owned')
    updates = request.args.get('updates')
    completion = request.args.get('completion')
    genre = (request.args.get('genre') or '').strip()
    recognized = (request.args.get('recognized') or '').strip().lower()
    app_version_num_expr = func.coalesce(Apps.app_version_num, 0)
    titles_metadata = None
    search_normalized = ''
    allowed_types = set()
    # Per-user ESRB age filter for the web browse view.
    cap, block_unrated = _user_rating_cap()

    size_subquery = (
        db.session.query(
            app_files.c.app_id.label('app_pk'),
            func.coalesce(func.sum(Files.size), 0).label('size'),
        )
        .outerjoin(Files, Files.id == app_files.c.file_id)
        .group_by(app_files.c.app_id)
        .subquery()
    )
    base_status_subquery = (
        db.session.query(
            Apps.title_id.label('title_fk'),
            func.max(
                case(
                    (and_(Apps.app_type == APP_TYPE_BASE, Apps.owned.is_(True)), 1),
                    else_=0
                )
            ).label('has_owned_base')
        )
        .group_by(Apps.title_id)
        .subquery()
    )
    update_status_subquery = (
        db.session.query(
            Apps.title_id.label('title_fk'),
            func.max(
                case(
                    (Apps.app_type == APP_TYPE_UPD, app_version_num_expr),
                    else_=0
                )
            ).label('max_update_version'),
            func.max(
                case(
                    (and_(Apps.app_type == APP_TYPE_UPD, Apps.owned.is_(True)), app_version_num_expr),
                    else_=0
                )
            ).label('max_owned_update_version')
        )
        .filter(or_(Apps.app_type != APP_TYPE_UPD, Apps.ignored.is_(False)))
        .group_by(Apps.title_id)
        .subquery()
    )
    dlc_agg_subquery = (
        db.session.query(
            Apps.app_id.label('dlc_app_id'),
            func.max(app_version_num_expr).label('max_version'),
            func.max(
                case(
                    (Apps.owned.is_(True), app_version_num_expr),
                    else_=0
                )
            ).label('max_owned_version')
        )
        .filter(Apps.app_type == APP_TYPE_DLC, Apps.ignored.is_(False))
        .group_by(Apps.app_id)
        .subquery()
    )
    dlc_title_status_subquery = (
        db.session.query(
            Apps.title_id.label('title_fk'),
            Apps.app_id.label('dlc_app_id'),
            func.max(app_version_num_expr).label('max_version'),
            func.max(
                case(
                    (Apps.owned.is_(True), 1),
                    else_=0
                )
            ).label('has_owned'),
            func.max(
                case(
                    (Apps.owned.is_(True), app_version_num_expr),
                    else_=0
                )
            ).label('max_owned_version')
        )
        .filter(Apps.app_type == APP_TYPE_DLC, Apps.ignored.is_(False))
        .group_by(Apps.title_id, Apps.app_id)
        .subquery()
    )
    dlc_completion_subquery = (
        db.session.query(
            dlc_title_status_subquery.c.title_fk.label('title_fk'),
            func.count().label('dlc_count'),
            func.sum(
                case(
                    (
                        and_(
                            dlc_title_status_subquery.c.has_owned == 1,
                            or_(
                                dlc_title_status_subquery.c.max_version <= 0,
                                dlc_title_status_subquery.c.max_owned_version >= dlc_title_status_subquery.c.max_version,
                            ),
                        ),
                        1,
                    ),
                    else_=0
                )
            ).label('complete_dlc_count')
        )
        .group_by(dlc_title_status_subquery.c.title_fk)
        .subquery()
    )

    query = (
        db.session.query(
            Apps.id.label('app_pk'),
            Apps.title_id.label('title_fk'),
            Titles.id.label('title_db_id'),
            Titles.title_id.label('title_id'),
            Apps.app_id.label('app_id'),
            Apps.app_version.label('app_version'),
            Apps.app_type.label('app_type'),
            Apps.owned.label('owned'),
            func.coalesce(size_subquery.c.size, 0).label('size'),
            func.coalesce(base_status_subquery.c.has_owned_base, 0).label('has_owned_base'),
            func.coalesce(update_status_subquery.c.max_update_version, 0).label('max_update_version'),
            func.coalesce(update_status_subquery.c.max_owned_update_version, 0).label('max_owned_update_version'),
            func.coalesce(dlc_agg_subquery.c.max_version, 0).label('dlc_max_version'),
            func.coalesce(dlc_agg_subquery.c.max_owned_version, 0).label('dlc_max_owned_version'),
            func.coalesce(dlc_completion_subquery.c.dlc_count, 0).label('dlc_count'),
            func.coalesce(dlc_completion_subquery.c.complete_dlc_count, 0).label('complete_dlc_count'),
        )
        .join(Titles, Apps.title_id == Titles.id)
        .outerjoin(size_subquery, size_subquery.c.app_pk == Apps.id)
        .outerjoin(base_status_subquery, base_status_subquery.c.title_fk == Titles.id)
        .outerjoin(update_status_subquery, update_status_subquery.c.title_fk == Titles.id)
        .outerjoin(dlc_agg_subquery, dlc_agg_subquery.c.dlc_app_id == Apps.app_id)
        .outerjoin(dlc_completion_subquery, dlc_completion_subquery.c.title_fk == Titles.id)
        .filter(
            or_(
                Apps.app_type == APP_TYPE_BASE,
                and_(
                    Apps.app_type == APP_TYPE_DLC,
                    app_version_num_expr == dlc_agg_subquery.c.max_version
                )
            )
        )
    )

    if types:
        allowed_types = {part.strip().upper() for part in str(types).split(',') if part.strip()}
        if allowed_types:
            query = query.filter(Apps.app_type.in_(allowed_types))
    if owned == 'owned':
        query = query.filter(Apps.owned.is_(True))
    elif owned == 'missing':
        query = query.filter(Apps.owned.is_(False))
    updates_up_to_date_filter = or_(
        and_(
            Apps.app_type == APP_TYPE_BASE,
            base_status_subquery.c.has_owned_base == 1,
            or_(
                update_status_subquery.c.max_update_version.is_(None),
                update_status_subquery.c.max_update_version == 0,
                update_status_subquery.c.max_owned_update_version >= update_status_subquery.c.max_update_version,
            ),
        ),
        and_(Apps.app_type == APP_TYPE_DLC, dlc_agg_subquery.c.max_owned_version >= dlc_agg_subquery.c.max_version),
    )
    updates_outdated_filter = or_(
        and_(
            Apps.app_type == APP_TYPE_BASE,
            or_(
                func.coalesce(base_status_subquery.c.has_owned_base, 0) == 0,
                and_(
                    func.coalesce(update_status_subquery.c.max_update_version, 0) > 0,
                    func.coalesce(update_status_subquery.c.max_owned_update_version, 0) < func.coalesce(update_status_subquery.c.max_update_version, 0),
                ),
            ),
        ),
        and_(Apps.app_type == APP_TYPE_DLC, dlc_agg_subquery.c.max_owned_version < dlc_agg_subquery.c.max_version),
    )
    completion_complete_filter = and_(
        Apps.app_type == APP_TYPE_BASE,
        or_(
            dlc_completion_subquery.c.dlc_count.is_(None),
            dlc_completion_subquery.c.dlc_count == 0,
            dlc_completion_subquery.c.complete_dlc_count >= dlc_completion_subquery.c.dlc_count,
        ),
    )
    completion_missing_dlc_filter = and_(
        Apps.app_type == APP_TYPE_BASE,
        func.coalesce(dlc_completion_subquery.c.dlc_count, 0) > 0,
        func.coalesce(dlc_completion_subquery.c.complete_dlc_count, 0) < func.coalesce(dlc_completion_subquery.c.dlc_count, 0),
    )

    if updates == 'outdated' and completion == 'missing_dlc':
        query = query.filter(or_(updates_outdated_filter, completion_missing_dlc_filter))
    else:
        if updates == 'up_to_date':
            query = query.filter(updates_up_to_date_filter)
        elif updates == 'outdated':
            query = query.filter(updates_outdated_filter)
        if completion == 'complete':
            query = query.filter(completion_complete_filter)
        elif completion == 'missing_dlc':
            query = query.filter(completion_missing_dlc_filter)

    if search:
        search_normalized = _normalize_library_search_text(search)
        if search_normalized:
            search_term = f"%{search_normalized}%"
            titles_metadata = _get_cached_titles_metadata()
            title_ids_from_search = [
                title_id
                for title_id, lowered_name in (titles_metadata.get('title_name_map') or {}).items()
                if _search_matches_normalized_text(search_normalized, lowered_name)
            ]
            search_filters = [
                func.lower(Apps.app_id).like(search_term),
                func.lower(Titles.title_id).like(search_term),
            ]
            if title_ids_from_search:
                search_filters.append(Titles.title_id.in_(title_ids_from_search))
            query = query.filter(or_(*search_filters))

    if initial in {'#', '@'} or (len(initial) == 1 and initial.isalpha()):
        if titles_metadata is None:
            titles_metadata = _get_cached_titles_metadata()
        title_name_map = titles_metadata.get('title_name_map') or {}
        if initial == '#':
            initial_title_ids = [title_id for title_id, name in title_name_map.items() if str(name or '')[:1].isdigit()]
        elif initial == '@':
            initial_title_ids = [title_id for title_id, name in title_name_map.items() if not str(name or '')[:1].isalnum()]
        else:
            initial_title_ids = [title_id for title_id, name in title_name_map.items() if str(name or '').startswith(initial.lower())]
        query = query.filter(Titles.title_id.in_(initial_title_ids) if initial_title_ids else Titles.id == -1)

    if genre or recognized in ('recognized', 'unrecognized'):
        if titles_metadata is None:
            titles_metadata = _get_cached_titles_metadata()
        matched_title_ids = None
        all_title_ids = set((titles_metadata.get('title_name_map') or {}).keys())
        unrecognized_ids = set(titles_metadata.get('unrecognized_title_ids') or set())

        if recognized == 'unrecognized':
            matched_title_ids = set(unrecognized_ids)
        elif recognized == 'recognized':
            matched_title_ids = set(all_title_ids) - set(unrecognized_ids)

        if genre:
            wanted_genre = genre.lower()
            genre_ids = set((titles_metadata.get('genre_title_ids') or {}).get(wanted_genre) or set())
            if matched_title_ids is None:
                matched_title_ids = genre_ids
            else:
                matched_title_ids &= genre_ids

        if matched_title_ids is None:
            matched_title_ids = set(all_title_ids)

        if matched_title_ids:
            query = query.filter(Titles.title_id.in_(matched_title_ids))
        else:
            query = query.filter(Titles.id == -1)

    if cap is not None:
        if block_unrated:
            # Fail closed: only explicitly rated, permitted titles are visible.
            # This also hides titles absent from TitleDB metadata.
            allowed_ids = _allowed_title_ids_for_cap(cap)
            if allowed_ids:
                query = query.filter(Titles.title_id.in_(allowed_ids))
            else:
                query = query.filter(Titles.id == -1)
        else:
            blocked_ids = _blocked_title_ids_for_cap(cap, block_unrated)
            if blocked_ids:
                query = query.filter(Titles.title_id.notin_(blocked_ids))

    use_name_sort = sort_key in ('title_asc', 'title_desc')
    if sort_key == 'newest':
        query = query.order_by(Titles.id.desc(), Apps.id.desc())
    else:
        # Title sorts are applied after metadata lookup so ordering follows display names.
        query = query.order_by(Titles.title_id.asc(), Apps.app_id.asc())

    state_token = _get_titledb_aware_state_token()
    count_cache_key = (
        state_token,
        search_normalized,
        initial,
        ','.join(sorted(allowed_types)),
        str(owned or ''),
        str(updates or ''),
        str(completion or ''),
        str(genre or '').lower(),
        'unrecognized' if recognized == 'unrecognized' else ('recognized' if recognized == 'recognized' else ''),
        ('cap', cap, bool(block_unrated)) if cap is not None else 'nocap',
    )
    total = _get_cached_titles_total(count_cache_key)
    if total is None:
        total = query.order_by(None).count()
        _store_titles_total(count_cache_key, total)
    start = (page - 1) * per_page

    rows = []
    rows_for_sort = []
    base_title_fk_ids = set()
    title_id_by_fk = {}
    dlc_app_ids = set()
    all_lookup_ids = set()
    info_cache = {}
    release_dates_by_title = {}
    if use_name_sort:
        rows_for_sort = query.order_by(None).all()
        total = len(rows_for_sort)
        all_lookup_ids.update([row.title_id for row in rows_for_sort if row.title_id])
        all_lookup_ids.update([row.app_id for row in rows_for_sort if row.app_type == APP_TYPE_DLC and row.app_id])

        with titles.titledb_session() as titledb_loaded:
            if titledb_loaded:
                for lookup_id in all_lookup_ids:
                    info_cache[lookup_id] = titles.get_game_info(lookup_id) or {}

        def _row_sort_key(row):
            title_info_local = info_cache.get(row.title_id) or {}
            app_info_local = title_info_local if row.app_type == APP_TYPE_BASE else (info_cache.get(row.app_id) or title_info_local)
            display_name = (
                app_info_local.get('name')
                or title_info_local.get('name')
                or row.app_id
                or row.title_id
                or ''
            )
            return (
                str(display_name).lower(),
                str(row.title_id or ''),
                str(row.app_id or ''),
            )

        rows_for_sort.sort(key=_row_sort_key, reverse=(sort_key == 'title_desc'))
        rows = rows_for_sort[start:start + per_page]
    else:
        rows = query.offset(start).limit(per_page).all()

    base_title_fk_ids = {row.title_fk for row in rows if row.app_type == APP_TYPE_BASE and row.title_fk is not None}
    title_id_by_fk = {row.title_fk: row.title_id for row in rows if row.title_fk is not None and row.title_id}
    dlc_app_ids = {row.app_id for row in rows if row.app_type == APP_TYPE_DLC and row.app_id}

    update_rows = []
    if base_title_fk_ids:
        update_rows = (
            db.session.query(
                Apps.title_id.label('title_fk'),
                Apps.app_version.label('app_version'),
                Apps.owned.label('owned'),
                func.coalesce(size_subquery.c.size, 0).label('size'),
            )
            .outerjoin(size_subquery, size_subquery.c.app_pk == Apps.id)
            .filter(Apps.app_type == APP_TYPE_UPD, Apps.title_id.in_(base_title_fk_ids))
            .all()
        )
    update_versions_by_title_fk = {}
    for upd in update_rows:
        update_versions_by_title_fk.setdefault(upd.title_fk, []).append({
            'version': int(upd.app_version or 0),
            'owned': bool(upd.owned),
            'size': int(upd.size or 0),
            'release_date': 'Unknown',
        })

    dlc_rows = []
    if dlc_app_ids:
        dlc_rows = (
            db.session.query(
                Apps.app_id.label('app_id'),
                Apps.app_version.label('app_version'),
                Apps.owned.label('owned'),
            )
            .filter(Apps.app_type == APP_TYPE_DLC, Apps.app_id.in_(dlc_app_ids))
            .all()
        )
    dlc_versions_by_app_id = {}
    for dlc in dlc_rows:
        dlc_versions_by_app_id.setdefault(dlc.app_id, []).append({
            'version': int(dlc.app_version or 0),
            'owned': bool(dlc.owned),
            'release_date': 'Unknown',
        })

    if not use_name_sort:
        all_lookup_ids.update([tid for tid in title_id_by_fk.values() if tid])
        all_lookup_ids.update([aid for aid in dlc_app_ids if aid])
        with titles.titledb_session() as titledb_loaded:
            if titledb_loaded:
                for lookup_id in all_lookup_ids:
                    info_cache[lookup_id] = titles.get_game_info(lookup_id) or {}

    with titles.titledb_session() as titledb_loaded:
        if titledb_loaded:
            for title_fk, title_id in title_id_by_fk.items():
                versions = titles.get_all_existing_versions(title_id) or []
                release_dates_by_title[title_fk] = {
                    int(v.get('version') or 0): v.get('release_date') or 'Unknown'
                    for v in versions
                }

    for title_fk, versions in update_versions_by_title_fk.items():
        release_dates = release_dates_by_title.get(title_fk) or {}
        for version in versions:
            version['release_date'] = release_dates.get(version['version'], 'Unknown')
        versions.sort(key=lambda item: item['version'], reverse=True)
    for app_id, versions in dlc_versions_by_app_id.items():
        versions.sort(key=lambda item: item['version'], reverse=True)

    games = []
    for row in rows:
        title_info = info_cache.get(row.title_id) or {}
        app_info = title_info if row.app_type == APP_TYPE_BASE else (info_cache.get(row.app_id) or title_info)
        game = {
            'id': app_info.get('id') or row.app_id,
            'name': app_info.get('name') or row.app_id,
            'bannerUrl': app_info.get('bannerUrl'),
            'iconUrl': app_info.get('iconUrl'),
            'category': app_info.get('category') or '',
            'genre': app_info.get('category') or '',
            'nsuId': app_info.get('nsuId'),
            'description': app_info.get('description'),
            'screenshots': app_info.get('screenshots') or [],
            'title_db_id': row.title_db_id,
            'title_id': row.title_id,
            'title_id_name': (title_info.get('name') or app_info.get('name') or row.title_id or row.app_id),
            'app_id': row.app_id,
            'app_version': row.app_version,
            'app_type': row.app_type,
            'owned': bool(row.owned),
            'size': int(row.size or 0),
        }
        if row.app_type == APP_TYPE_BASE:
            has_base = bool(row.has_owned_base)
            max_update_version = int(row.max_update_version or 0)
            max_owned_update_version = int(row.max_owned_update_version or 0)
            dlc_count = int(row.dlc_count or 0)
            complete_dlc_count = int(row.complete_dlc_count or 0)
            game['has_base'] = has_base
            game['has_latest_version'] = has_base and (max_update_version <= 0 or max_owned_update_version >= max_update_version)
            game['has_all_dlcs'] = (dlc_count <= 0) or (complete_dlc_count >= dlc_count)
            game['version'] = list(update_versions_by_title_fk.get(row.title_fk, []))
        elif row.app_type == APP_TYPE_DLC:
            game['has_latest_version'] = int(row.dlc_max_owned_version or 0) >= int(row.dlc_max_version or 0)
            game['version'] = list(dlc_versions_by_app_id.get(row.app_id, []))
        games.append(game)

    newest, recommended = _get_discovery_sections(limit=12)
    if cap is not None:
        newest = [
            item for item in newest
            if _title_allowed(cap, _coerce_rating_value((item or {}).get('rating')), block_unrated)
        ]
        recommended = [
            item for item in recommended
            if _title_allowed(cap, _coerce_rating_value((item or {}).get('rating')), block_unrated)
        ]

    if lite:
        def _lite(entry):
            slim = dict(entry)
            slim.pop('version', None)
            slim.pop('description', None)
            slim.pop('screenshots', None)
            return slim
        games = [_lite(entry) for entry in games]
        newest = [_lite(entry) for entry in newest]
        recommended = [_lite(entry) for entry in recommended]

    if _is_cyberfoil_request():
        _log_access(
            kind='shop_titles',
            filename=request.full_path if request.query_string else request.path,
            ok=True,
            status_code=200,
            duration_ms=int((time.time() - start_ts) * 1000),
        )

    return jsonify({
        'total': int(total),
        'page': int(page),
        'per_page': int(per_page),
        'games': games,
        'genres': _get_cached_library_genres(),
        'discovery': {
            'newest': newest,
            'recommended': recommended,
        }
    })


def _build_library_download_files(app_entry):
    files = []
    for file_entry in list(getattr(app_entry, 'files', []) or []):
        file_id = getattr(file_entry, 'id', None)
        filepath = str(getattr(file_entry, 'filepath', '') or '').strip()
        if not file_id or not filepath or not os.path.isfile(filepath):
            continue
        files.append({
            'id': int(file_id),
            'filename': str(getattr(file_entry, 'filename', '') or os.path.basename(filepath)),
            'size': int(getattr(file_entry, 'size', 0) or 0),
            'url': f'/api/get_game/{int(file_id)}?download=1',
        })
    return files


@app.get('/api/title-details')
@access_required('shop')
def get_title_details_api():
    app_id = (request.args.get('app_id') or '').strip()
    app_type = (request.args.get('app_type') or '').strip()
    title_id = (request.args.get('title_id') or '').strip()

    if not app_id and not title_id:
        return jsonify({'success': False, 'error': 'missing_identifier'}), 400

    size_subquery = (
        db.session.query(
            app_files.c.app_id.label('app_pk'),
            func.coalesce(func.sum(Files.size), 0).label('size'),
        )
        .outerjoin(Files, Files.id == app_files.c.file_id)
        .group_by(app_files.c.app_id)
        .subquery()
    )

    query = (
        db.session.query(
            Apps.id.label('app_pk'),
            Apps.title_id.label('title_fk'),
            Titles.title_id.label('title_id'),
            Titles.have_base.label('have_base'),
            Titles.up_to_date.label('up_to_date'),
            Titles.complete.label('complete'),
            Apps.app_id.label('app_id'),
            Apps.app_version.label('app_version'),
            Apps.app_type.label('app_type'),
            Apps.owned.label('owned'),
            func.coalesce(size_subquery.c.size, 0).label('size'),
        )
        .join(Titles, Apps.title_id == Titles.id)
        .outerjoin(size_subquery, size_subquery.c.app_pk == Apps.id)
    )
    if app_id and app_type:
        query = query.filter(Apps.app_id == app_id, Apps.app_type == app_type.upper())
    elif app_id:
        query = query.filter(Apps.app_id == app_id)
    else:
        query = query.filter(Titles.title_id == title_id.upper())
    row = query.order_by(Apps.id.desc()).first()

    app_size_subquery = (
        db.session.query(
            app_files.c.app_id.label('app_pk'),
            func.coalesce(func.sum(Files.size), 0).label('size'),
        )
        .outerjoin(Files, Files.id == app_files.c.file_id)
        .group_by(app_files.c.app_id)
        .subquery()
    )

    game = None
    if row:
        title_cheats = []
        if _request_has_cheat_access():
            title_cheats = [
                {
                    'build_id': cheat['build_id'],
                    'size': int(cheat['size']),
                    'note': str(cheat.get('note') or ''),
                    'url': f"/api/cheats/{row.title_id}/{cheat['build_id']}",
                }
                for cheat in cheats.list_cheats()
                if cheat['title_id'] == row.title_id
            ]
        with titles.titledb_session():
            title_info = titles.get_game_info(row.title_id) or {}
            app_info = title_info if row.app_type == APP_TYPE_BASE else (titles.get_game_info(row.app_id) or title_info)
            title_apps = (
                Apps.query
                .filter(Apps.title_id == row.title_fk)
                .all()
            )
            files_by_app_pk = {
                app.id: _build_library_download_files(app)
                for app in title_apps
            }
            current_app_files = files_by_app_pk.get(row.app_pk, [])
            owned_base_count = sum(1 for app in title_apps if app.app_type == APP_TYPE_BASE and bool(app.owned))
            owned_update_count = sum(1 for app in title_apps if app.app_type == APP_TYPE_UPD and bool(app.owned))
            owned_dlc_count = sum(1 for app in title_apps if app.app_type == APP_TYPE_DLC and bool(app.owned))
            has_base = owned_base_count > 0
            deletable_versions = _build_deletable_version_map(title_apps)
            available_update_versions = [
                _safe_int(app.app_version) for app in title_apps
                if app.app_type == APP_TYPE_UPD and not bool(app.ignored)
            ]
            owned_update_versions = [
                _safe_int(app.app_version) for app in title_apps
                if app.app_type == APP_TYPE_UPD and bool(app.owned) and not bool(app.ignored)
            ]
            highest_available_update_version = max(available_update_versions, default=0)
            highest_owned_update_version = max(owned_update_versions, default=0)
            has_latest_version = highest_available_update_version <= 0 or highest_owned_update_version >= highest_available_update_version
            dlc_items, has_all_dlcs = _build_title_details_dlc_items(row.title_fk, row.title_id)
            dlc_files_by_app_id = {}
            for app in title_apps:
                if app.app_type != APP_TYPE_DLC:
                    continue
                app_id = str(app.app_id or '').strip().upper()
                if app_id:
                    dlc_files_by_app_id.setdefault(app_id, []).extend(files_by_app_pk.get(app.id, []))
            for dlc_item in dlc_items:
                dlc_item['files'] = dlc_files_by_app_id.get(
                    str(dlc_item.get('app_id') or '').strip().upper(),
                    [],
                )
            game = {
                'id': app_info.get('id') or row.app_id,
                'name': app_info.get('name') or row.app_id,
                'bannerUrl': app_info.get('bannerUrl'),
                'iconUrl': app_info.get('iconUrl'),
                'category': app_info.get('category') or '',
                'genre': app_info.get('category') or '',
                'nsuId': app_info.get('nsuId'),
                'rating': app_info.get('rating'),
                'description': app_info.get('description'),
                'screenshots': app_info.get('screenshots') or [],
                'title_id': row.title_id,
                'title_id_name': title_info.get('name') or app_info.get('name') or row.title_id,
                'app_id': row.app_id,
                'app_version': row.app_version,
                'app_type': row.app_type,
                'owned': bool(row.owned),
                'size': int(row.size or 0),
                'files': current_app_files,
                'owned_base_count': int(owned_base_count or 0),
                'owned_update_count': int(owned_update_count or 0),
                'owned_dlc_count': int(owned_dlc_count or 0),
                'has_owned_content': bool(owned_base_count or owned_update_count or owned_dlc_count),
                'has_base': has_base,
                'has_latest_version': has_base and has_latest_version,
                'has_all_dlcs': has_all_dlcs,
                'dlc_list': dlc_items,
                'missing_dlcs': [
                    item for item in dlc_items
                    if not item.get('owned') and not item.get('ignored')
                ],
                'cheats': title_cheats,
            }
            if row.app_type == APP_TYPE_BASE:
                versions = []
                for upd in (
                    db.session.query(
                        Apps.id.label('app_pk'),
                        Apps.app_id,
                        Apps.app_version,
                        Apps.owned,
                        Apps.ignored,
                        func.coalesce(app_size_subquery.c.size, 0).label('size'),
                    )
                    .outerjoin(app_size_subquery, app_size_subquery.c.app_pk == Apps.id)
                    .filter(Apps.title_id == row.title_fk, Apps.app_type == APP_TYPE_UPD)
                    .all()
                ):
                    versions.append({
                        'app_id': upd.app_id,
                        'app_type': APP_TYPE_UPD,
                        'version': int(upd.app_version or 0),
                        'owned': bool(upd.owned),
                        'ignored': bool(upd.ignored),
                        'deletable': deletable_versions.get(
                            (str(upd.app_id or '').strip().upper(), APP_TYPE_UPD, str(upd.app_version or '').strip()),
                            False,
                        ),
                        'size': int(upd.size or 0),
                        'files': files_by_app_pk.get(upd.app_pk, []),
                        'release_date': 'Unknown',
                    })
                release_dates = {
                    int(v.get('version') or 0): v.get('release_date') or 'Unknown'
                    for v in (titles.get_all_existing_versions(row.title_id) or [])
                }
                for version in versions:
                    version['release_date'] = release_dates.get(version['version'], 'Unknown')
                versions.sort(key=lambda item: item['version'], reverse=True)
                game['version'] = versions
            elif row.app_type == APP_TYPE_DLC:
                dlc_versions = []
                for dlc in (
                    db.session.query(
                        Apps.id.label('app_pk'),
                        Apps.app_id,
                        Apps.app_version,
                        Apps.owned,
                        Apps.ignored,
                        func.coalesce(app_size_subquery.c.size, 0).label('size'),
                    )
                    .outerjoin(app_size_subquery, app_size_subquery.c.app_pk == Apps.id)
                    .filter(Apps.app_type == APP_TYPE_DLC, Apps.app_id == row.app_id)
                    .all()
                ):
                    dlc_versions.append({
                        'app_id': dlc.app_id,
                        'app_type': APP_TYPE_DLC,
                        'version': int(dlc.app_version or 0),
                        'owned': bool(dlc.owned),
                        'ignored': bool(dlc.ignored),
                        'deletable': deletable_versions.get(
                            (str(dlc.app_id or '').strip().upper(), APP_TYPE_DLC, str(dlc.app_version or '').strip()),
                            False,
                        ),
                        'size': int(dlc.size or 0),
                        'files': files_by_app_pk.get(dlc.app_pk, []),
                        'release_date': 'Unknown',
                    })
                dlc_versions.sort(key=lambda item: item['version'], reverse=True)
                game['version'] = dlc_versions
                latest_available = max([item['version'] for item in dlc_versions if not item['ignored']], default=0)
                latest_owned = max([item['version'] for item in dlc_versions if item['owned']], default=0)
                game['has_latest_version'] = latest_owned >= latest_available

    return jsonify({
        'success': bool(game),
        'game': game,
    })


@app.post('/api/library/ignored-content')
@access_required('admin')
def set_ignored_library_content_api():
    data = request.get_json(silent=True) or {}
    app_id = str(data.get('app_id') or '').strip().upper()
    app_type = str(data.get('app_type') or '').strip().upper()
    ignored = bool(data.get('ignored'))

    if not app_id or app_type not in (APP_TYPE_UPD, APP_TYPE_DLC):
        return jsonify({'success': False, 'error': 'invalid_content'}), 400

    query = Apps.query.filter(Apps.app_id == app_id, Apps.app_type == app_type)
    if app_type == APP_TYPE_UPD:
        try:
            version = int(data.get('version'))
        except (TypeError, ValueError):
            return jsonify({'success': False, 'error': 'invalid_version'}), 400
        query = query.filter(Apps.app_version_num == version)

    updated = query.update({Apps.ignored: ignored}, synchronize_session=False)
    if not updated:
        db.session.rollback()
        return jsonify({'success': False, 'error': 'content_not_found'}), 404

    db.session.commit()
    update_titles()
    invalidate_library_cache_state_token()
    post_library_change()
    return jsonify({'success': True, 'ignored': ignored, 'updated': updated})


@app.post('/api/library/ignored-missing-dlc')
@access_required('admin')
def ignore_missing_library_dlc_api():
    data = request.get_json(silent=True) or {}
    title_id = str(data.get('title_id') or '').strip().upper()
    if not title_id:
        return jsonify({'success': False, 'error': 'missing_title_id'}), 400

    updated = (
        Apps.query
        .filter(
            Apps.title_id.in_(db.session.query(Titles.id).filter(Titles.title_id == title_id)),
            Apps.app_type == APP_TYPE_DLC,
            Apps.owned.is_(False),
            Apps.ignored.is_(False),
        )
        .update({Apps.ignored: True}, synchronize_session=False)
    )
    db.session.commit()
    if updated:
        update_titles()
        invalidate_library_cache_state_token()
        post_library_change()
    return jsonify({'success': True, 'updated': updated})


def _build_title_details_dlc_items(title_fk, title_id):
    dlc_rows = (
        db.session.query(Apps.app_id, Apps.app_version, Apps.owned, Apps.ignored)
        .filter(Apps.title_id == title_fk, Apps.app_type == APP_TYPE_DLC)
        .all()
    )
    dlc_state = {}
    for dlc in dlc_rows:
        app_id = str(dlc.app_id or '').strip().upper()
        if not app_id:
            continue
        entry = dlc_state.setdefault(app_id, {
            'max_version': None,
            'max_owned': None,
            'has_owned': False,
            'ignored': True,
        })
        version_value = int(dlc.app_version or 0)
        if entry['max_version'] is None or version_value > entry['max_version']:
            entry['max_version'] = version_value
        if dlc.owned:
            entry['has_owned'] = True
            if entry['max_owned'] is None or version_value > entry['max_owned']:
                entry['max_owned'] = version_value
        if not bool(getattr(dlc, 'ignored', False)):
            entry['ignored'] = False

    dlc_app_ids = set(dlc_state.keys())
    if not dlc_app_ids:
        dlc_app_ids = {
            str(app_id or '').strip().upper()
            for app_id in (titles.get_all_existing_dlc(title_id) or [])
            if str(app_id or '').strip()
        }

    dlc_items = []
    for app_id in sorted(dlc_app_ids):
        entry = dlc_state.get(app_id) or {
            'max_version': None,
            'max_owned': None,
            'has_owned': False,
            'ignored': False,
        }
        versions_list = titles.get_all_app_existing_versions(app_id) or []
        max_version = None
        if versions_list:
            try:
                max_version = max(int(v or 0) for v in versions_list)
            except Exception:
                max_version = None
        if max_version is None:
            try:
                local_max_version = entry.get('max_version')
                max_version = int(local_max_version) if local_max_version is not None else None
            except Exception:
                max_version = None
        owned_max_raw = entry.get('max_owned')
        owned_max = int(owned_max_raw) if owned_max_raw is not None else None
        dlc_info = titles.get_game_info(app_id) or {}
        dlc_items.append({
            'app_id': app_id,
            'name': dlc_info.get('name') or app_id,
            'latest_version': max_version,
            'owned_version': owned_max,
            'owned': bool(entry.get('has_owned')),
            'ignored': bool(entry.get('ignored')),
        })

    dlc_items.sort(key=lambda item: str(item.get('name') or '').lower())
    has_all_dlcs = all(item.get('owned') or item.get('ignored') for item in dlc_items) if dlc_items else True
    return dlc_items, has_all_dlcs


@app.get('/api/title-info/<title_id>')
@access_required('shop')
def get_title_info_api(title_id):
    title_id = (title_id or '').strip().upper()
    if not title_id:
        return jsonify({'success': False, 'error': 'missing_title_id'}), 400

    titles.load_titledb()
    try:
        info = titles.get_game_info(title_id) or {}
    finally:
        titles.release_titledb()

    return jsonify({
        'success': True,
        'title_id': title_id,
        'name': info.get('name'),
        'iconUrl': info.get('iconUrl'),
        'bannerUrl': info.get('bannerUrl'),
        'description': info.get('description'),
        'category': info.get('category'),
        'nsuId': info.get('nsuId'),
        'rating': info.get('rating'),
        'screenshots': info.get('screenshots') or []
    })

@app.post('/api/title-info/manual')
@access_required('admin')
def set_manual_title_info_api():
    data = request.json or {}
    title_id = str(data.get('title_id') or '').strip().upper()
    if not title_id:
        return jsonify({'success': False, 'error': 'missing_title_id'}), 400

    payload = {
        'name': data.get('name'),
        'description': data.get('description'),
        'iconUrl': data.get('iconUrl'),
        'bannerUrl': data.get('bannerUrl'),
        'category': data.get('category'),
        'nsuId': data.get('nsuId'),
        'rating': data.get('rating'),
        'screenshots': data.get('screenshots') or [],
    }
    ok = set_manual_title_override(title_id, payload)
    if not ok:
        return jsonify({'success': False, 'error': 'invalid_payload'}), 400

    # Refresh in-memory settings and invalidate library/shop caches so UI picks up overrides.
    reload_conf()
    try:
        if os.path.exists(LIBRARY_CACHE_FILE):
            os.remove(LIBRARY_CACHE_FILE)
    except Exception:
        pass
    with shop_sections_cache_lock:
        shop_sections_cache['payload'] = None
        shop_sections_cache['timestamp'] = 0
        shop_sections_cache['limit'] = None
        shop_sections_cache['state_token'] = None
        shop_sections_cache['encrypted'] = {}
    with titles_metadata_cache_lock:
        titles_metadata_cache['version'] = _TITLES_METADATA_CACHE_VERSION
        titles_metadata_cache['state_token'] = None
        titles_metadata_cache['genres'] = []
        titles_metadata_cache['title_name_map'] = {}
        titles_metadata_cache['genre_title_ids'] = {}
        titles_metadata_cache['unrecognized_title_ids'] = set()
    return jsonify({'success': True, 'title_id': title_id})

@app.get('/api/library/size')
@access_required('shop')
def get_library_size_api():
    state_token = get_library_cache_state_token()
    with library_size_cache_lock:
        cached_token = str(library_size_cache.get('state_token') or '')
        if cached_token and cached_token == str(state_token):
            return jsonify({'success': True, 'total_bytes': int(library_size_cache.get('total_bytes') or 0)})

    total = db.session.query(func.sum(Files.size)).scalar() or 0
    with library_size_cache_lock:
        library_size_cache['state_token'] = str(state_token)
        library_size_cache['total_bytes'] = int(total or 0)
        library_size_cache['updated_at'] = time.time()
    return jsonify({'success': True, 'total_bytes': int(total)})

@app.get('/api/library/status')
@access_required('shop')
def get_library_status_api():
    with library_rebuild_lock:
        status = dict(library_rebuild_status)
    with scan_lock:
        scan_active = bool(scan_in_progress)
    with titledb_update_lock:
        titledb_active = bool(is_titledb_update_running)
    status.update({
        'scan_in_progress': scan_active,
        'titledb_updating': titledb_active
    })
    return jsonify({'success': True, 'status': status})

@app.route('/api/get_game/<int:id>')
@tinfoil_access
def serve_game(id):
    start_ts = time.time()
    remote_addr = _effective_remote_addr()
    user_agent = request.headers.get('User-Agent')
    username = _get_request_user()

    file_row = (
        db.session.query(
            Files.filepath.label('filepath'),
            Files.filename.label('filename'),
            Titles.title_id.label('title_id'),
        )
        .select_from(Files)
        .outerjoin(app_files, app_files.c.file_id == Files.id)
        .outerjoin(Apps, Apps.id == app_files.c.app_id)
        .outerjoin(Titles, Titles.id == Apps.title_id)
        .filter(Files.id == id)
        .first()
    )
    if not file_row:
        return Response(status=404)

    # Per-user ESRB age filter: block downloads above the requester's cap.
    cap, block_unrated = _user_rating_cap(username)
    if cap is not None and _file_blocked_by_cap(id, cap, block_unrated):
        logger.info(
            "Blocked download of file id %s for user %r: exceeds age cap %s.",
            id, username, cap,
        )
        return Response(status=403)

    try:
        queue_file_download_increment(id)
    except Exception as e:
        logger.error(f"Failed to queue download count increment for file id {id}: {e}")

    filepath = file_row.filepath
    filename = file_row.filename or os.path.basename(filepath)
    filedir = os.path.dirname(filepath)
    force_download = str(request.args.get('download') or '').strip().lower() in ('1', 'true', 'yes')
    title_id = (file_row.title_id or '').strip().upper() or None
    fast_transfer_mode = bool((app_settings.get('shop') or {}).get('fast_transfer_mode'))
    stream_compressed = (
        _is_cyberfoil_request()
        and bool((app_settings.get('shop') or {}).get('cyberfoil_virtual_compressed_stream', True))
        and compressed_stream.supports_virtual_stream(filepath)
    )

    transfer_id = uuid.uuid4().hex
    meta = {
        'id': transfer_id,
        'started_at': start_ts,
        'last_seen_at': start_ts,
        'user': username,
        'remote_addr': remote_addr,
        'user_agent': user_agent,
        'file_id': id,
        'filename': filename,
        'title_id': title_id,
        'bytes_sent': 0,
        'transfer_mode': 'virtual' if stream_compressed else 'original',
        'virtual_filename': compressed_stream.virtual_filename(filename) if stream_compressed else None,
    }

    with _active_transfers_lock:
        _active_transfers[transfer_id] = meta

    if stream_compressed:
        try:
            stream, output_size = compressed_stream.virtual_stream(filepath)
            output_filename = compressed_stream.virtual_filename(filename)
            byte_range = compressed_stream.parse_single_range(
                request.headers.get('Range'), output_size,
            )
            if request.headers.get('Range') and byte_range is None:
                with _active_transfers_lock:
                    _active_transfers.pop(transfer_id, None)
                return Response(status=416, headers={'Content-Range': f'bytes */{output_size}'})
            if byte_range is not None:
                range_start, range_end = byte_range
                resp = Response(
                    compressed_stream.virtual_range(filepath, range_start, range_end),
                    status=206,
                    mimetype='application/octet-stream',
                )
                resp.headers['Content-Range'] = f'bytes {range_start}-{range_end}/{output_size}'
                resp.headers['Content-Length'] = str(range_end - range_start + 1)
            else:
                resp = Response(stream, mimetype='application/octet-stream')
                resp.headers['Content-Length'] = str(output_size)
            resp.headers['Content-Disposition'] = (
                "attachment; filename*=UTF-8''" + quote(output_filename)
            )
            # Ranges are generated from the virtual stream (single range only).
            resp.headers['Accept-Ranges'] = 'bytes'
            logger.info(
                'CyberFoil virtual stream: %s -> %s (%s bytes, range=%s)',
                filename,
                output_filename,
                output_size,
                request.headers.get('Range') or 'full',
            )
        except Exception:
            logger.exception('Unable to create virtual compressed stream for %s', filepath)
            resp = send_from_directory(filedir, filename, conditional=True, as_attachment=force_download)
    else:
        resp = send_from_directory(filedir, filename, conditional=True, as_attachment=force_download)

    session_key = _transfer_session_start(
        user=username,
        remote_addr=remote_addr,
        user_agent=user_agent,
        title_id=title_id,
        file_id=id,
        filename=filename,
        resp_status_code=getattr(resp, 'status_code', 200),
    )

    # Wrap response iterable to track bytes sent while preserving Range support.
    original_iterable = resp.response
    status_code = getattr(resp, 'status_code', None)

    state = {
        'sent': 0,
        'ok': True,
        'finished': False,
    }
    fast_mode_fallback_sent = 0
    if fast_transfer_mode:
        try:
            fast_mode_fallback_sent = max(0, int(resp.headers.get('Content-Length') or 0))
        except Exception:
            fast_mode_fallback_sent = 0

    _finish_lock = threading.Lock()

    def _finish_once():
        with _finish_lock:
            if state.get('finished'):
                return
            state['finished'] = True

        code = getattr(resp, 'status_code', None) or status_code
        bytes_sent = int(state.get('sent') or 0)
        if fast_transfer_mode and bytes_sent <= 0 and fast_mode_fallback_sent > 0:
            # Fast mode skips per-chunk accounting; use response length as fallback.
            bytes_sent = int(fast_mode_fallback_sent)
        try:
            _transfer_session_finish(
                session_key,
                ok=bool(state.get('ok')),
                status_code=int(code) if code is not None else None,
                bytes_sent=bytes_sent,
            )
        except Exception:
            try:
                logger.exception('Failed to finalize transfer session')
            except Exception:
                pass
        finally:
            with _active_transfers_lock:
                _active_transfers.pop(transfer_id, None)

    def _on_close():
        _finish_once()

    resp.call_on_close(_on_close)

    if fast_transfer_mode:
        return resp

    def _generate_wrapped():
        try:
            for chunk in original_iterable:
                try:
                    state['sent'] = int(state.get('sent') or 0) + len(chunk)
                    if state['sent'] % (1024 * 1024) < len(chunk):
                        _transfer_session_progress(session_key, state['sent'])
                    with _active_transfers_lock:
                        if transfer_id in _active_transfers:
                            _active_transfers[transfer_id]['bytes_sent'] = state['sent']
                            _active_transfers[transfer_id]['last_seen_at'] = time.time()
                except Exception:
                    pass
                yield chunk
        except Exception:
            state['ok'] = False
            raise
        finally:
            # Ensure we close the session even if call_on_close doesn't fire.
            _finish_once()

    resp.response = _generate_wrapped()
    resp.direct_passthrough = False
    return resp


@app.get('/api/shop/sections')
@tinfoil_access
def shop_sections_api():
    start_ts = time.time()
    limit = request.args.get('limit', 50)
    try:
        limit = int(limit)
    except ValueError:
        limit = 50

    is_cyberfoil = _is_cyberfoil_request()
    # Keep CyberFoil payload uncapped so clients can browse the full owned catalog.
    # Use a dedicated cache key so capped web payloads and uncapped CyberFoil payloads
    # do not overwrite each other.
    cache_limit = -1 if is_cyberfoil else limit

    now = time.time()
    state_token = _get_titledb_aware_state_token()
    payload = None
    with shop_sections_cache_lock:
        cache_enabled = SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0
        cache_valid = True
        if SHOP_SECTIONS_CACHE_TTL_S is not None:
            cache_valid = (now - float(shop_sections_cache.get('timestamp') or 0)) <= SHOP_SECTIONS_CACHE_TTL_S
        cache_hit = (
            cache_enabled
            and shop_sections_cache['payload'] is not None
            and shop_sections_cache['limit'] == cache_limit
            and shop_sections_cache.get('state_token') == state_token
            and cache_valid
        )
        if cache_hit:
            payload = shop_sections_cache['payload']
        elif not cache_enabled or shop_sections_cache.get('payload') is not None:
            # Expired in-memory cache.
            shop_sections_cache['payload'] = None
            shop_sections_cache['limit'] = None
            shop_sections_cache['timestamp'] = 0
            shop_sections_cache['state_token'] = None
            shop_sections_cache['encrypted'] = {}

    if payload is None:
        if SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0:
            disk_cache = _load_shop_sections_cache_from_disk()
            if (
                disk_cache
                and disk_cache.get('limit') == cache_limit
                and str(disk_cache.get('state_token') or '') == state_token
            ):
                disk_payload = disk_cache.get('payload')
                disk_ts = float(disk_cache.get('timestamp') or 0)
                disk_ok = True
                if SHOP_SECTIONS_CACHE_TTL_S is not None:
                    disk_ok = (now - disk_ts) <= SHOP_SECTIONS_CACHE_TTL_S
                if disk_payload and disk_ok:
                    payload = disk_payload
                    _store_shop_sections_cache(payload, cache_limit, disk_ts, state_token, persist_disk=False)

    if payload is None:
        payload = _build_shop_sections_payload(limit, full_catalog=is_cyberfoil)
        if SHOP_SECTIONS_CACHE_TTL_S is None or SHOP_SECTIONS_CACHE_TTL_S > 0:
            _store_shop_sections_cache(payload, cache_limit, now, state_token, persist_disk=True)

    if is_cyberfoil:
        _log_access(
            kind='shop_sections',
            filename=request.full_path if request.query_string else request.path,
            ok=True,
            status_code=200,
            duration_ms=int((time.time() - start_ts) * 1000),
        )

    # Per-user ESRB age filter: applied at the response edge so the global
    # section caches above stay user-agnostic.
    cap, block_unrated = _user_rating_cap()
    response_payload = _filter_sections_payload(payload, cap, block_unrated)
    cheat_access = _request_has_cheat_access()
    if is_cyberfoil:
        response_payload = _filter_cheat_section(response_payload, cheat_access)

    return _respond_with_shop_payload(
        response_payload,
        cache_kind='sections',
        cache_limit=cache_limit,
        full_catalog=is_cyberfoil,
        filter_token=(cap, block_unrated, cheat_access),
    )


@app.get('/api/cheats')
@access_required('shop')
def list_cheats_api():
    if not _request_has_cheat_access():
        return jsonify({'success': False, 'error': 'Cheat access is disabled for this account.'}), 403
    return jsonify({'success': True, 'cheats': _build_cyberfoil_cheat_items()})


@app.get('/api/cheats/<title_id>/<build_id>')
@tinfoil_access
def download_cheat_api(title_id, build_id):
    if not _request_has_cheat_access():
        return tinfoil_error('Cheat access is disabled for this account.')
    data = cheats.read_cheat(title_id, build_id)
    if data is None:
        return jsonify({'success': False, 'error': 'cheat_not_found'}), 404
    normalized_build_id = cheats.normalize_build_id(build_id)
    response = Response(data, mimetype='text/plain')
    response.headers['Content-Disposition'] = (
        f'attachment; filename="{normalized_build_id}.txt"'
    )
    return response


@app.post('/api/cheats')
@access_required('admin')
def upload_cheat_api():
    upload = request.files.get('file')
    pasted_content = request.form.get('content')
    note = str(request.form.get('note') or '').strip()
    if len(note) > 1000:
        return jsonify({'success': False, 'error': 'Cheat note must be 1000 characters or less.'}), 400
    if upload is not None and upload.filename:
        cheat_data = upload.read()
    elif pasted_content is not None and pasted_content.strip():
        cheat_data = pasted_content.encode('utf-8')
    else:
        return jsonify({'success': False, 'error': 'Provide a cheat file or paste cheat content.'}), 400
    try:
        cheat = cheats.save_cheat(
            request.form.get('title_id'), request.form.get('build_id'), cheat_data)
        cheat['note'] = cheats.set_cheat_note(
            cheat['title_id'], cheat['build_id'], note)
    except ValueError as exc:
        return jsonify({'success': False, 'error': str(exc)}), 400
    _invalidate_shop_root_cache()
    with shop_sections_cache_lock:
        shop_sections_cache['payload'] = None
        shop_sections_cache['encrypted'] = {}
    return jsonify({'success': True, 'cheat': cheat})


@app.delete('/api/cheats/<title_id>/<build_id>')
@access_required('admin')
def delete_cheat_api(title_id, build_id):
    if not cheats.delete_cheat(title_id, build_id):
        return jsonify({'success': False, 'error': 'cheat_not_found'}), 404
    _invalidate_shop_root_cache()
    with shop_sections_cache_lock:
        shop_sections_cache['payload'] = None
        shop_sections_cache['encrypted'] = {}
    return jsonify({'success': True})


@app.post('/api/cheats/sync')
@access_required('admin')
def sync_cheats_api():
    data = request.get_json(silent=True) or {}
    sync_url = str(data.get('url') or (app_settings.get('cheats') or {}).get('sync_url') or '').strip()
    if not sync_url.lower().startswith(('https://', 'http://')):
        return jsonify({'success': False, 'error': 'Configure an HTTP(S) cheat ZIP URL first.'}), 400
    try:
        response = requests.get(sync_url, timeout=(10, 90))
        response.raise_for_status()
        result = cheats.import_zip(response.content)
    except requests.RequestException as exc:
        return jsonify({'success': False, 'error': f'Cheat sync failed: {exc}'}), 502
    except ValueError as exc:
        return jsonify({'success': False, 'error': str(exc)}), 400
    _invalidate_shop_root_cache()
    with shop_sections_cache_lock:
        shop_sections_cache['payload'] = None
        shop_sections_cache['encrypted'] = {}
    return jsonify({'success': True, **result})


@app.post('/api/settings/cheats')
@access_required('admin')
def set_cheats_settings_api():
    data = request.get_json(silent=True) or {}
    updates = {}
    if 'enabled' in data:
        updates['enabled'] = bool(data.get('enabled'))
    if 'sync_url' in data:
        updates['sync_url'] = str(data.get('sync_url') or '').strip()
    set_cheats_settings(updates)
    reload_conf()
    with shop_sections_cache_lock:
        shop_sections_cache['payload'] = None
        shop_sections_cache['encrypted'] = {}
    return jsonify({'success': True})


@app.get('/api/shop/icon/<title_id>')
@tinfoil_access
def shop_icon_api(title_id):
    start_ts = time.time()
    title_id = (title_id or '').upper()
    if not title_id:
        return Response(status=404)

    cache_dir = os.path.join(CACHE_DIR, 'icons')
    os.makedirs(cache_dir, exist_ok=True)

    # Fast path: serve cached file without TitleDB lookup.
    size_override = _get_web_media_size('icon')
    cached_name = _get_cached_media_filename(cache_dir, title_id, media_kind='icon')
    if cached_name:
        src_path = os.path.join(cache_dir, cached_name)
        size, variant_dir, variant_path = _get_variant_path(cache_dir, cached_name, media_kind='icon', size_override=size_override)
        if variant_path and os.path.exists(variant_path) and os.path.getmtime(variant_path) >= os.path.getmtime(src_path):
            response = send_from_directory(variant_dir, cached_name)
            response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
            if _is_cyberfoil_request():
                _log_access(
                    kind='shop_media',
                    title_id=title_id,
                    filename=f"icon:{cached_name}",
                    ok=True,
                    status_code=getattr(response, 'status_code', 200),
                    duration_ms=int((time.time() - start_ts) * 1000),
                )
            return response
        if variant_path and os.path.exists(src_path):
            with _media_resize_lock:
                if os.path.exists(src_path) and (not os.path.exists(variant_path) or os.path.getmtime(variant_path) < os.path.getmtime(src_path)):
                    _resize_image_to_path(src_path, variant_path, size=size)
            if os.path.exists(variant_path):
                response = send_from_directory(variant_dir, cached_name)
                response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
                if _is_cyberfoil_request():
                    _log_access(
                        kind='shop_media',
                        title_id=title_id,
                        filename=f"icon:{cached_name}",
                        ok=True,
                        status_code=getattr(response, 'status_code', 200),
                        duration_ms=int((time.time() - start_ts) * 1000),
                    )
                return response
        response = send_from_directory(cache_dir, cached_name)
        response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename=f"icon:{cached_name}",
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    titles.load_titledb()
    try:
        info = titles.get_game_info(title_id)
        if (not (info or {}).get('iconUrl')) and hasattr(titles, '_build_local_fallback_info'):
            try:
                titles._build_local_fallback_info(title_id)
            except Exception:
                pass
            info = titles.get_game_info(title_id)
    finally:
        titles.release_titledb()
    icon_url = info.get('iconUrl') if info else ''
    if not icon_url:
        response = send_from_directory(app.static_folder, 'placeholder-icon.svg')
        response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename='icon:placeholder',
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    cache_name, cache_path = _ensure_cached_media_file(cache_dir, title_id, icon_url)
    if not cache_path:
        response = send_from_directory(app.static_folder, 'placeholder-icon.svg')
        response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename='icon:placeholder',
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    if not os.path.exists(cache_path):
        try:
            resp = requests.get(icon_url, timeout=10)
            if resp.status_code == 200:
                with open(cache_path, 'wb') as handle:
                    handle.write(resp.content)
        except Exception:
            cache_path = None

    if cache_path and os.path.exists(cache_path):
        _remember_cached_media_filename(title_id, cache_name, media_kind='icon')
        size, variant_dir, variant_path = _get_variant_path(cache_dir, cache_name, media_kind='icon', size_override=size_override)
        if variant_path:
            with _media_resize_lock:
                if not os.path.exists(variant_path) or os.path.getmtime(variant_path) < os.path.getmtime(cache_path):
                    _resize_image_to_path(cache_path, variant_path, size=size)
            if os.path.exists(variant_path):
                response = send_from_directory(variant_dir, cache_name)
                response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
                if _is_cyberfoil_request():
                    _log_access(
                        kind='shop_media',
                        title_id=title_id,
                        filename=f"icon:{cache_name}",
                        ok=True,
                        status_code=getattr(response, 'status_code', 200),
                        duration_ms=int((time.time() - start_ts) * 1000),
                    )
                return response

        response = send_from_directory(cache_dir, cache_name)
        response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename=f"icon:{cache_name}",
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    response = send_from_directory(app.static_folder, 'placeholder-icon.svg')
    response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
    if _is_cyberfoil_request():
        _log_access(
            kind='shop_media',
            title_id=title_id,
            filename='icon:placeholder',
            ok=True,
            status_code=getattr(response, 'status_code', 200),
            duration_ms=int((time.time() - start_ts) * 1000),
        )
    return response


@app.get('/api/shop/banner/<title_id>')
@tinfoil_access
def shop_banner_api(title_id):
    start_ts = time.time()
    title_id = (title_id or '').upper()
    if not title_id:
        return Response(status=404)

    cache_dir = os.path.join(CACHE_DIR, 'banners')
    os.makedirs(cache_dir, exist_ok=True)

    # Fast path: serve cached file without TitleDB lookup.
    size_override = _get_web_media_size('banner')
    cached_name = _get_cached_media_filename(cache_dir, title_id, media_kind='banner')
    if cached_name:
        src_path = os.path.join(cache_dir, cached_name)
        size, variant_dir, variant_path = _get_variant_path(cache_dir, cached_name, media_kind='banner', size_override=size_override)
        if variant_path and os.path.exists(variant_path) and os.path.getmtime(variant_path) >= os.path.getmtime(src_path):
            response = send_from_directory(variant_dir, cached_name)
            response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
            if _is_cyberfoil_request():
                _log_access(
                    kind='shop_media',
                    title_id=title_id,
                    filename=f"banner:{cached_name}",
                    ok=True,
                    status_code=getattr(response, 'status_code', 200),
                    duration_ms=int((time.time() - start_ts) * 1000),
                )
            return response
        if variant_path and os.path.exists(src_path):
            with _media_resize_lock:
                if os.path.exists(src_path) and (not os.path.exists(variant_path) or os.path.getmtime(variant_path) < os.path.getmtime(src_path)):
                    _resize_image_to_path(src_path, variant_path, size=size)
            if os.path.exists(variant_path):
                response = send_from_directory(variant_dir, cached_name)
                response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
                if _is_cyberfoil_request():
                    _log_access(
                        kind='shop_media',
                        title_id=title_id,
                        filename=f"banner:{cached_name}",
                        ok=True,
                        status_code=getattr(response, 'status_code', 200),
                        duration_ms=int((time.time() - start_ts) * 1000),
                    )
                return response
        response = send_from_directory(cache_dir, cached_name)
        response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename=f"banner:{cached_name}",
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    titles.load_titledb()
    try:
        info = titles.get_game_info(title_id)
        if (not (info or {}).get('bannerUrl')) and hasattr(titles, '_build_local_fallback_info'):
            try:
                titles._build_local_fallback_info(title_id)
            except Exception:
                pass
            info = titles.get_game_info(title_id)
    finally:
        titles.release_titledb()
    banner_url = info.get('bannerUrl') if info else ''
    if not banner_url:
        response = send_from_directory(app.static_folder, 'placeholder-banner.svg')
        response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename='banner:placeholder',
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    cache_name, cache_path = _ensure_cached_media_file(cache_dir, title_id, banner_url)
    if not cache_path:
        response = send_from_directory(app.static_folder, 'placeholder-banner.svg')
        response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename='banner:placeholder',
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    if not os.path.exists(cache_path):
        try:
            resp = requests.get(banner_url, timeout=10)
            if resp.status_code == 200:
                with open(cache_path, 'wb') as handle:
                    handle.write(resp.content)
        except Exception:
            cache_path = None

    if cache_path and os.path.exists(cache_path):
        _remember_cached_media_filename(title_id, cache_name, media_kind='banner')
        size, variant_dir, variant_path = _get_variant_path(cache_dir, cache_name, media_kind='banner', size_override=size_override)
        if variant_path:
            with _media_resize_lock:
                if not os.path.exists(variant_path) or os.path.getmtime(variant_path) < os.path.getmtime(cache_path):
                    _resize_image_to_path(cache_path, variant_path, size=size)
            if os.path.exists(variant_path):
                response = send_from_directory(variant_dir, cache_name)
                response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
                if _is_cyberfoil_request():
                    _log_access(
                        kind='shop_media',
                        title_id=title_id,
                        filename=f"banner:{cache_name}",
                        ok=True,
                        status_code=getattr(response, 'status_code', 200),
                        duration_ms=int((time.time() - start_ts) * 1000),
                    )
                return response

        response = send_from_directory(cache_dir, cache_name)
        response.headers['Cache-Control'] = 'public, max-age=604800, immutable'
        if _is_cyberfoil_request():
            _log_access(
                kind='shop_media',
                title_id=title_id,
                filename=f"banner:{cache_name}",
                ok=True,
                status_code=getattr(response, 'status_code', 200),
                duration_ms=int((time.time() - start_ts) * 1000),
            )
        return response

    response = send_from_directory(app.static_folder, 'placeholder-banner.svg')
    response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
    if _is_cyberfoil_request():
        _log_access(
            kind='shop_media',
            title_id=title_id,
            filename='banner:placeholder',
            ok=True,
            status_code=getattr(response, 'status_code', 200),
            duration_ms=int((time.time() - start_ts) * 1000),
        )
    return response


def _run_post_library_change():
    if _is_conversion_running():
        logger.info("Skipping library rebuild: conversion job is running.")
        return
    with library_rebuild_lock:
        if not library_rebuild_status['in_progress']:
            library_rebuild_status['started_at'] = time.time()
        library_rebuild_status['in_progress'] = True
        library_rebuild_status['updated_at'] = time.time()
    with app.app_context():
        try:
            invalidate_library_cache_state_token()
            titles.load_titledb()
            process_library_identification(app)
            add_missing_apps_to_db()
            update_titles() # Ensure titles are updated after identification
            # Expensive filesystem sweep: run periodically, not on every rebuild.
            _maybe_remove_missing_files_from_db(force=False)
            organize_pending_downloads()
            # Generate the library after organization tasks so cache/UI reflect final file layout.
            generate_library()
            invalidate_library_cache_state_token()
            with shop_sections_cache_lock:
                shop_sections_cache['payload'] = None
                shop_sections_cache['timestamp'] = 0
                shop_sections_cache['limit'] = None
                shop_sections_cache['state_token'] = None
                shop_sections_cache['encrypted'] = {}
            _invalidate_shop_root_cache()
            with titles_metadata_cache_lock:
                titles_metadata_cache['version'] = _TITLES_METADATA_CACHE_VERSION
                titles_metadata_cache['state_token'] = None
                titles_metadata_cache['genres'] = []
                titles_metadata_cache['title_name_map'] = {}
                titles_metadata_cache['genre_title_ids'] = {}
                titles_metadata_cache['unrecognized_title_ids'] = set()

            # Media cache index can be repopulated on demand.
            with _media_cache_lock:
                _media_cache_index['icon'].clear()
                _media_cache_index['banner'].clear()
            state_token = _get_titledb_aware_state_token()
            if '::missing' not in state_token:
                now = time.time()
                payload = _build_shop_sections_payload(50)
                _store_shop_sections_cache(payload, 50, now, state_token, persist_disk=True)
        finally:
            try:
                titles.release_titledb()
            finally:
                try:
                    _release_process_memory()
                finally:
                    with library_rebuild_lock:
                        library_rebuild_status['in_progress'] = False
                        library_rebuild_status['updated_at'] = time.time()

@debounce(10)
def post_library_change():
    _run_post_library_change()

@app.post('/api/library/scan')
@access_required('admin')
def scan_library_api():
    data = request.json or {}
    path = data.get('path')
    success = True
    errors = []

    if _is_conversion_running():
        logger.info('Skipping scan_library_api call: conversion job is running.')
        return jsonify({'success': False, 'errors': ['Conversion in progress. Try again after conversion finishes.']})

    global scan_in_progress
    with scan_lock:
        if scan_in_progress:
            logger.info('Skipping scan_library_api call: Scan already in progress')
            return {'success': False, 'errors': []}
        # Claim the scan while holding the lock.
        scan_in_progress = True

    try:
        if path is None:
            scan_library()
        else:
            scan_library_path(path)
    except Exception as e:
        errors.append(str(e))
        success = False
        logger.error(f"Error during library scan: {e}")
    finally:
        with scan_lock:
            scan_in_progress = False

    post_library_change()
    resp = {
        'success': success,
        'errors': errors
    } 
    return jsonify(resp)

def scan_library():
    logger.info(f'Scanning whole library ...')
    libraries = get_libraries()
    for library in libraries:
        scan_library_path(library.path) # Only scan, identification will be done globally

if __name__ == '__main__':
    logger.info('Starting initialization of AeroFoil...')
    init_db(app)
    init_users(app)
    init()
    logger.info('Initialization steps done, starting server...')
    host = (os.environ.get('AEROFOIL_HOST') or os.environ.get('OWNFOIL_HOST') or '0.0.0.0').strip() or '0.0.0.0'
    port = _read_int_env('AEROFOIL_PORT', _read_int_env('OWNFOIL_PORT', 8465, minimum=1, maximum=65535), minimum=1, maximum=65535)
    use_flask_dev_server = str(os.environ.get('AEROFOIL_USE_FLASK_DEV') or os.environ.get('OWNFOIL_USE_FLASK_DEV') or '').strip().lower() in ('1', 'true', 'yes', 'on')

    try:
        if waitress_serve is not None and not use_flask_dev_server:
            wsgi_threads = _read_int_env('AEROFOIL_WSGI_THREADS', _read_int_env('OWNFOIL_WSGI_THREADS', 32, minimum=1, maximum=512), minimum=1, maximum=512)
            wsgi_connection_limit = _read_int_env('AEROFOIL_WSGI_CONNECTION_LIMIT', _read_int_env('OWNFOIL_WSGI_CONNECTION_LIMIT', 1000, minimum=1, maximum=100000), minimum=1, maximum=100000)
            wsgi_channel_timeout = _read_int_env('AEROFOIL_WSGI_CHANNEL_TIMEOUT_S', _read_int_env('OWNFOIL_WSGI_CHANNEL_TIMEOUT_S', 120, minimum=5, maximum=3600), minimum=5, maximum=3600)
            wsgi_cleanup_interval = _read_int_env('AEROFOIL_WSGI_CLEANUP_INTERVAL_S', _read_int_env('OWNFOIL_WSGI_CLEANUP_INTERVAL_S', 30, minimum=1, maximum=600), minimum=1, maximum=600)
            wsgi_max_request_body_size = _read_int_env(
                'AEROFOIL_WSGI_MAX_REQUEST_BODY_SIZE',
                _read_int_env(
                    'OWNFOIL_WSGI_MAX_REQUEST_BODY_SIZE',
                    DEFAULT_WSGI_MAX_REQUEST_BODY_SIZE,
                    minimum=1024 * 1024,
                    maximum=1024 * 1024 * 1024 * 1024,
                ),
                minimum=1024 * 1024,
                maximum=1024 * 1024 * 1024 * 1024,
            )
            logger.info(
                'Starting Waitress WSGI server on %s:%s (threads=%s, connection_limit=%s, channel_timeout=%ss, max_request_body_size=%s bytes)',
                host,
                port,
                wsgi_threads,
                wsgi_connection_limit,
                wsgi_channel_timeout,
                wsgi_max_request_body_size,
            )
            waitress_serve(
                app,
                host=host,
                port=port,
                threads=wsgi_threads,
                connection_limit=wsgi_connection_limit,
                channel_timeout=wsgi_channel_timeout,
                cleanup_interval=wsgi_cleanup_interval,
                max_request_body_size=wsgi_max_request_body_size,
                # Keep forwarded headers available for AeroFoil's own trusted-proxy checks.
                clear_untrusted_proxy_headers=False,
                ident='AeroFoil'
            )
        else:
            if use_flask_dev_server:
                logger.warning('AEROFOIL_USE_FLASK_DEV enabled: using Flask development server.')
            elif waitress_serve is None:
                logger.warning('Waitress is not available; falling back to Flask development server.')
            # Threaded fallback keeps admin polling responsive during long transfers.
            app.run(debug=False, use_reloader=False, host=host, port=port, threaded=True)
    finally:
        # Shutdown server
        logger.info('Shutting down server...')
        try:
            watcher.stop()
            watcher_thread.join(timeout=5)
            if watcher_thread.is_alive():
                logger.warning('Watcher shutdown still waiting for filesystem I/O; continuing shutdown.')
            else:
                logger.debug('Watcher thread terminated.')
        except Exception:
            logger.exception('Watcher shutdown failed')
        # Shutdown scheduler
        try:
            app.scheduler.shutdown()
            logger.debug('Scheduler terminated.')
        except Exception:
            logger.exception('Scheduler shutdown failed')
