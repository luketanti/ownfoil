import copy
import gc
import hashlib
import os
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
import importlib.util
from sqlalchemy.orm import aliased, joinedload
from app.constants import *
from app.db import *
from app import titles as titles_lib
import datetime
from pathlib import Path
from app.utils import *

_organize_lock = threading.Lock()
_pending_organize_paths = set()
_pending_cleanup_roots = set()
_SCAN_ADD_BATCH_SIZE = 250
_SCAN_DELETE_PROGRESS_INTERVAL = 250
_IDENTIFY_QUERY_BATCH_SIZE = 500
_IDENTIFY_COMMIT_INTERVAL = 50
_ORGANIZE_BATCH_SIZE = 400
_memory_diag_lock = threading.Lock()
_memory_diagnostics = {
    'updated_at': 0,
    'phases': {}
}
_library_state_token_lock = threading.Lock()
_library_state_token_cache = {
    'token': None,
    'updated_at': 0.0,
}
_LIBRARY_STATE_TOKEN_CACHE_TTL_S = 1.0

def _diag_phase_start(phase, **metadata):
    now = time.time()
    with _memory_diag_lock:
        previous = _memory_diagnostics['phases'].get(phase) or {}
        run_count = int(previous.get('run_count') or 0) + 1
        _memory_diagnostics['phases'][phase] = {
            'run_count': run_count,
            'in_progress': True,
            'started_at': now,
            'finished_at': None,
            'duration_s': None,
            'identity_map_last': 0,
            'identity_map_peak': 0,
            'gc_collections': 0,
            'counters': {},
            'metadata': metadata or {},
            'last_error': None,
        }
        _memory_diagnostics['updated_at'] = now

def _diag_phase_update(phase, **counters):
    now = time.time()
    with _memory_diag_lock:
        phase_state = _memory_diagnostics['phases'].get(phase)
        if not phase_state:
            return
        phase_state['counters'].update(counters or {})
        _memory_diagnostics['updated_at'] = now

def _diag_sample_identity_map(phase):
    try:
        size = len(db.session.identity_map)
    except Exception:
        return
    now = time.time()
    with _memory_diag_lock:
        phase_state = _memory_diagnostics['phases'].get(phase)
        if not phase_state:
            return
        phase_state['identity_map_last'] = int(size)
        phase_state['identity_map_peak'] = max(int(phase_state.get('identity_map_peak') or 0), int(size))
        _memory_diagnostics['updated_at'] = now

def _diag_note_gc(phase, collections=1):
    now = time.time()
    with _memory_diag_lock:
        phase_state = _memory_diagnostics['phases'].get(phase)
        if not phase_state:
            return
        phase_state['gc_collections'] = int(phase_state.get('gc_collections') or 0) + int(collections or 1)
        _memory_diagnostics['updated_at'] = now

def _diag_phase_error(phase, error):
    now = time.time()
    with _memory_diag_lock:
        phase_state = _memory_diagnostics['phases'].get(phase)
        if not phase_state:
            return
        phase_state['last_error'] = str(error)
        _memory_diagnostics['updated_at'] = now

def _diag_phase_end(phase, **counters):
    now = time.time()
    with _memory_diag_lock:
        phase_state = _memory_diagnostics['phases'].get(phase)
        if not phase_state:
            return
        if counters:
            phase_state['counters'].update(counters)
        phase_state['in_progress'] = False
        phase_state['finished_at'] = now
        started_at = float(phase_state.get('started_at') or now)
        phase_state['duration_s'] = max(0.0, now - started_at)
        _memory_diagnostics['updated_at'] = now

def get_memory_diagnostics():
    with _memory_diag_lock:
        return copy.deepcopy(_memory_diagnostics)

def _iter_library_files(library_path):
    """Yield supported files under a library path without building a full list in memory."""
    for root, _, filenames in os.walk(library_path):
        for filename in filenames:
            if is_supported_content_path(filename):
                yield os.path.join(root, filename)

def add_library_complete(app, watcher, path):
    """Add a library to settings, database, and watchdog"""
    from app.settings import add_library_path_to_settings
    
    with app.app_context():
        # Add to settings
        success, errors = add_library_path_to_settings(path)
        if not success:
            return success, errors
        
        # Add to database
        add_library(path)
        
        # Add to watchdog
        watcher.add_directory(path)
        
        logger.info(f"Successfully added library: {path}")
        return True, []

def remove_library_complete(app, watcher, path):
    """Remove a library from settings, database, and watchdog with proper cleanup"""
    from app.settings import delete_library_path_from_settings
    
    with app.app_context():
        # Remove from watchdog first
        watcher.remove_directory(path)
        
        # Get library object before deletion
        library = Libraries.query.filter_by(path=path).first()
        if library:
            # Get all file IDs from this library before deletion
            file_ids = [f.id for f in library.files]
            
            # Update Apps table to remove file references and update ownership
            total_apps_updated = 0
            for file_id in file_ids:
                apps_updated = remove_file_from_apps(file_id)
                total_apps_updated += apps_updated
            
            # Remove titles that no longer have any owned apps
            titles_removed = remove_titles_without_owned_apps()
            
            # Delete library (cascade will delete files automatically)
            db.session.delete(library)
            db.session.commit()
            
            logger.info(f"Removed library: {path}")
            if total_apps_updated > 0:
                logger.info(f"Updated {total_apps_updated} app entries to remove library file references.")
            if titles_removed > 0:
                logger.info(f"Removed {titles_removed} titles with no owned apps.")
        
        # Remove from settings
        success, errors = delete_library_path_from_settings(path)
        return success, errors

def init_libraries(app, watcher, paths):
    # watcher.add_directory() does one inotify_add_watch() syscall per directory in the tree -
    # on a large NFS-backed library (thousands of directories) that's minutes of blocking I/O.
    # This function used to run entirely synchronously inside init(), before waitress opened its
    # port, so a slow library meant the app was unreachable (and its startupProbe was fighting
    # the clock) on every single restart. The DB bookkeeping below is cheap (plain inserts), so
    # keep that synchronous - it has to finish before the scheduler's startup scan job runs, or
    # that job finds no registered libraries and does nothing until its next interval. Only the
    # actual watchdog registration is deferred to a background thread.
    with app.app_context():
        # delete non existing libraries
        for library in get_libraries():
            path = library.path
            if not os.path.exists(path):
                logger.warning(f"Library {path} no longer exists, deleting from database.")
                # Use the complete removal function for consistency
                remove_library_complete(app, watcher, path)

        # add libraries to the database
        for path in paths:
            # Check if library already exists in database
            existing_library = Libraries.query.filter_by(path=path).first()
            if not existing_library:
                add_library(path)

    def _register_watchdog_directories():
        for path in paths:
            watcher.add_directory(path)
    threading.Thread(target=_register_watchdog_directories, daemon=True).start()

def add_files_to_library(library, files, check_existing=True):
    nb_to_identify = len(files)
    if isinstance(library, int) or library.isdigit():
        library_id = library
        library_path = get_library_path(library_id)
    else:
        library_path = library
        library_id = get_library_id(library_path)

    library_path = get_library_path(library_id)
    for n, filepath in enumerate(files):
        if check_existing and file_exists_in_db(filepath):
            logger.debug(f'File already in database, skipping: {filepath}')
            continue
        file = filepath.replace(library_path, "")
        logger.info(f'Getting file info ({n+1}/{nb_to_identify}): {file}')

        file_info = titles_lib.get_file_info(filepath)

        if file_info is None:
            logger.error(f'Failed to get info for file: {file} - file will be skipped.')
            # in the future save identification error to be displayed and inspected in the UI
            continue

        new_file = Files(
            filepath = filepath,
            library_id = library_id,
            folder = file_info["filedir"],
            filename = file_info["filename"],
            extension = file_info["extension"],
            size = file_info["size"],
        )
        db.session.add(new_file)

        # Commit every 100 files to avoid excessive memory use
        if (n + 1) % 100 == 0:
            db.session.commit()
            db.session.expunge_all()

    # Final commit
    db.session.commit()
    db.session.expunge_all()

def scan_library_path(library_path):
    phase = 'scan_library_path'
    _diag_phase_start(phase, library_path=library_path)
    library_id = get_library_id(library_path)
    logger.info(f'Scanning library path {library_path} ...')
    if library_id is None:
        _diag_phase_end(phase, reason='library_not_found')
        logger.warning(f'Library path {library_path} is not registered in database.')
        return
    if not os.path.isdir(library_path):
        _diag_phase_end(phase, reason='path_missing', library_id=library_id)
        logger.warning(f'Library path {library_path} does not exists.')
        return

    total_seen = 0
    added = 0
    missing_count = 0
    _diag_sample_identity_map(phase)
    try:
        existing_filepaths = set(iter_library_file_paths(library_id))
        pending_new_files = []
        for filepath in _iter_library_files(library_path):
            total_seen += 1
            if filepath in existing_filepaths:
                existing_filepaths.discard(filepath)
                continue
            pending_new_files.append(filepath)
            if len(pending_new_files) >= _SCAN_ADD_BATCH_SIZE:
                add_files_to_library(library_id, pending_new_files, check_existing=False)
                added += len(pending_new_files)
                pending_new_files.clear()
                db.session.expunge_all()
                _diag_sample_identity_map(phase)

        if pending_new_files:
            add_files_to_library(library_id, pending_new_files, check_existing=False)
            added += len(pending_new_files)
            pending_new_files.clear()
            _diag_sample_identity_map(phase)

        missing_paths = list(existing_filepaths)
        missing_count = len(missing_paths)
        for n in range(0, missing_count, _SCAN_DELETE_PROGRESS_INTERVAL):
            batch_paths = missing_paths[n:n + _SCAN_DELETE_PROGRESS_INTERVAL]
            delete_files_by_filepaths_batch(batch_paths, commit=True)
            if n % _SCAN_DELETE_PROGRESS_INTERVAL == 0:
                removed = min(n + _SCAN_DELETE_PROGRESS_INTERVAL, missing_count)
                logger.info(f"Removed {removed}/{missing_count} missing files from DB for {library_path}.")
                db.session.expunge_all()
                _diag_sample_identity_map(phase)

        logger.info(
            "Finished scan for %s: %s filesystem files, %s new DB entries, %s removed missing DB entries.",
            library_path,
            total_seen,
            added,
            missing_count
        )
        set_library_scan_time(library_id)
    except Exception as e:
        _diag_phase_error(phase, e)
        raise
    finally:
        _diag_phase_end(
            phase,
            library_path=library_path,
            library_id=library_id,
            files_seen=total_seen,
            files_added=added,
            files_removed=missing_count
        )

def _get_identification_file_ids_batch(library_id, include_filename_retry, include_orphaned, last_id, batch_size):
    orphaned_condition = ~db.session.query(app_files.c.file_id).filter(app_files.c.file_id == Files.id).exists()
    query = db.session.query(Files.id).filter(
        Files.library_id == library_id,
        Files.id > last_id
    )
    if include_filename_retry:
        predicates = [Files.identified.is_(False), Files.identification_type == 'filename']
    else:
        predicates = [Files.identified.is_(False)]
    if include_orphaned:
        predicates.append(orphaned_condition)
    query = query.filter(or_(*predicates))
    rows = query.order_by(Files.id).limit(batch_size).all()
    return [row.id for row in rows]

def get_files_to_identify(library_id):
    non_identified_files = get_all_non_identified_files_from_library(library_id)
    if titles_lib.keys_loaded():
        files_to_identify_with_cnmt = get_files_with_identification_from_library(library_id, 'filename')
        non_identified_files = list(set(non_identified_files).union(files_to_identify_with_cnmt))
    return non_identified_files

def identify_library_files(library):
    phase = 'identify_library_files'
    if isinstance(library, int) or library.isdigit():
        library_id = library
        library_path = get_library_path(library_id)
    else:
        library_path = library
        library_id = get_library_id(library_path)
    _diag_phase_start(phase, library_path=library_path, library_id=library_id)
    if library_id is None:
        _diag_phase_end(phase, reason='library_not_found')
        logger.warning(f'Library path {library_path} is not registered in database.')
        return
    include_filename_retry = bool(titles_lib.keys_loaded())
    include_orphaned = True
    nb_to_identify = count_file_ids_for_identification(
        library_id,
        include_filename_retry=include_filename_retry,
        include_orphaned=include_orphaned
    )
    if nb_to_identify <= 0:
        _diag_phase_end(
            phase,
            library_path=library_path,
            library_id=library_id,
            include_filename_retry=include_filename_retry,
            total_candidates=0
        )
        return

    logger.info(
        "Identifying %s file(s) for library %s (include_filename_retry=%s).",
        nb_to_identify,
        library_path,
        include_filename_retry
    )
    title_id_db_cache = {}
    last_id = 0
    processed = 0
    _diag_sample_identity_map(phase)

    try:
        while True:
            batch_ids = _get_identification_file_ids_batch(
            library_id,
            include_filename_retry=include_filename_retry,
            include_orphaned=include_orphaned,
            last_id=last_id,
            batch_size=_IDENTIFY_QUERY_BATCH_SIZE
        )
            if not batch_ids:
                break
            last_id = batch_ids[-1]

            for file_id in batch_ids:
                file = db.session.get(Files, file_id)
                if file is None:
                    continue
                filename = file.filename or file.filepath or str(file.id)
                filepath = file.filepath
                file_deleted = False

                try:
                    if not filepath or not os.path.exists(filepath):
                        logger.warning(
                            f'Identifying file ({processed + 1}/{nb_to_identify}): {filename} no longer exists, deleting from database.'
                        )
                        db.session.delete(file)
                        file_deleted = True
                        continue

                    logger.info(f'Identifying file ({processed + 1}/{nb_to_identify}): {filename}')
                    identification, success, file_contents, error = titles_lib.identify_file(filepath)
                    if success and file_contents and not error:
                        title_ids = list(dict.fromkeys([c['title_id'] for c in file_contents if c.get('title_id')]))
                        for title_id in title_ids:
                            title_db_id = title_id_db_cache.get(title_id)
                            if title_db_id is None:
                                title_obj = Titles.query.filter_by(title_id=title_id).first()
                                if not title_obj:
                                    title_obj = Titles(title_id=title_id)
                                    db.session.add(title_obj)
                                    db.session.flush()
                                title_db_id = title_obj.id
                                title_id_db_cache[title_id] = title_db_id

                        nb_content = 0
                        for file_content in file_contents:
                            logger.info(
                                "Identifying file (%s/%s) - Found content Title ID: %s App ID : %s Title Type: %s Version: %s",
                                processed + 1,
                                nb_to_identify,
                                file_content.get("title_id"),
                                file_content.get("app_id"),
                                file_content.get("type"),
                                file_content.get("version")
                            )
                            title_id_in_db = title_id_db_cache.get(file_content.get("title_id"))
                            if title_id_in_db is None:
                                continue

                            app_id = file_content.get("app_id")
                            app_version = str(file_content.get("version") or "0")
                            existing_app = Apps.query.filter_by(
                                app_id=app_id,
                                app_version=app_version
                            ).first()

                            if existing_app:
                                if file not in existing_app.files:
                                    existing_app.files.append(file)
                                existing_app.owned = True
                            else:
                                new_app = Apps(
                                    app_id=app_id,
                                    app_version=app_version,
                                    app_type=file_content.get("type"),
                                    owned=True,
                                    title_id=title_id_in_db
                                )
                                new_app.files.append(file)
                                db.session.add(new_app)

                            nb_content += 1

                        file.multicontent = nb_content > 1
                        file.nb_content = nb_content
                        file.identified = True
                        file.identification_error = None
                    else:
                        logger.warning(f"Error identifying file {filename}: {error}")
                        file.identification_error = error
                        file.identified = False

                    file.identification_type = identification
                except Exception as e:
                    logger.warning(f"Error identifying file {filename}: {e}")
                    file.identification_error = str(e)
                    file.identified = False
                finally:
                    if not file_deleted:
                        file.identification_attempts = (file.identification_attempts or 0) + 1
                        file.last_attempt = datetime.datetime.now()
                    processed += 1

                    if processed % _IDENTIFY_COMMIT_INTERVAL == 0:
                        db.session.commit()
                        db.session.expunge_all()
                        _diag_sample_identity_map(phase)
                        if processed % (_IDENTIFY_COMMIT_INTERVAL * 10) == 0:
                            gc.collect()
                            _diag_note_gc(phase)

        db.session.commit()
        db.session.expunge_all()
        _diag_sample_identity_map(phase)
        gc.collect()
        _diag_note_gc(phase)
    except Exception as e:
        _diag_phase_error(phase, e)
        raise
    finally:
        _diag_phase_end(
            phase,
            library_path=library_path,
            library_id=library_id,
            include_filename_retry=include_filename_retry,
            include_orphaned=include_orphaned,
            total_candidates=nb_to_identify,
            processed=processed
        )

def add_missing_apps_to_db():
    phase = 'add_missing_apps_to_db'
    _diag_phase_start(phase)
    logger.info('Adding missing apps to database...')
    apps_added = 0
    processed = 0
    last_title_pk = 0
    _diag_sample_identity_map(phase)

    try:
        while True:
            title_rows = (
                db.session.query(Titles.id, Titles.title_id)
                .filter(Titles.id > last_title_pk)
                .order_by(Titles.id)
                .limit(_IDENTIFY_QUERY_BATCH_SIZE)
                .all()
            )
            if not title_rows:
                break
            last_title_pk = title_rows[-1].id
            title_db_ids = [row.id for row in title_rows]

            existing_apps_rows = (
                db.session.query(
                    Apps.title_id,
                    Apps.app_id,
                    Apps.app_version,
                    Apps.app_type,
                )
                .filter(Apps.title_id.in_(title_db_ids))
                .all()
            )
            existing_base_by_title = {}
            existing_app_pairs = set()
            for app_row in existing_apps_rows:
                title_fk = app_row.title_id
                if title_fk not in existing_base_by_title:
                    existing_base_by_title[title_fk] = False
                if app_row.app_type == APP_TYPE_BASE:
                    existing_base_by_title[title_fk] = True
                existing_app_pairs.add((
                    int(title_fk),
                    str(app_row.app_id or ''),
                    str(app_row.app_version or '0'),
                ))

            for row in title_rows:
                title_id = row.title_id
                title_db_id = row.id
                processed += 1
                if not title_id:
                    logger.warning(f'Skipping title with None title_id: {row}')
                    continue

                # Add base game if not present at all (any base version).
                if not existing_base_by_title.get(title_db_id, False):
                    new_base_app = Apps(
                        app_id=title_id,
                        app_version="0",
                        app_type=APP_TYPE_BASE,
                        owned=False,
                        title_id=title_db_id
                    )
                    db.session.add(new_base_app)
                    apps_added += 1
                    existing_base_by_title[title_db_id] = True
                    existing_app_pairs.add((int(title_db_id), str(title_id), "0"))
                    logger.debug(f'Added missing base app: {title_id}')

                # Add missing update versions.
                title_versions = titles_lib.get_all_existing_versions(title_id)
                for version_info in title_versions:
                    version = str(version_info['version'])
                    update_app_id = title_id[:-3] + '800'
                    pair = (int(title_db_id), str(update_app_id), version)
                    if pair not in existing_app_pairs:
                        new_update_app = Apps(
                            app_id=update_app_id,
                            app_version=version,
                            app_type=APP_TYPE_UPD,
                            owned=False,
                            title_id=title_db_id
                        )
                        db.session.add(new_update_app)
                        apps_added += 1
                        existing_app_pairs.add(pair)
                        logger.debug(f'Added missing update app: {update_app_id} v{version}')

                # Add missing DLC.
                title_dlc_ids = titles_lib.get_all_existing_dlc(title_id)
                for dlc_app_id in title_dlc_ids:
                    dlc_versions = titles_lib.get_all_app_existing_versions(dlc_app_id)
                    if not dlc_versions:
                        continue
                    for dlc_version in dlc_versions:
                        dlc_version_str = str(dlc_version)
                        pair = (int(title_db_id), str(dlc_app_id), dlc_version_str)
                        if pair in existing_app_pairs:
                            continue
                        new_dlc_app = Apps(
                            app_id=dlc_app_id,
                            app_version=dlc_version_str,
                            app_type=APP_TYPE_DLC,
                            owned=False,
                            title_id=title_db_id
                        )
                        db.session.add(new_dlc_app)
                        apps_added += 1
                        existing_app_pairs.add(pair)
                        logger.debug(f'Added missing DLC app: {dlc_app_id} v{dlc_version}')

                if processed % _IDENTIFY_COMMIT_INTERVAL == 0:
                    db.session.commit()
                    db.session.expunge_all()
                    _diag_sample_identity_map(phase)
                    logger.info(f'Processed {processed} titles, added {apps_added} missing apps so far')
                    if processed % (_IDENTIFY_COMMIT_INTERVAL * 10) == 0:
                        gc.collect()
                        _diag_note_gc(phase)

        db.session.commit()
        db.session.expunge_all()
        _diag_sample_identity_map(phase)
        gc.collect()
        _diag_note_gc(phase)
        logger.info(f'Finished adding missing apps to database. Total apps added: {apps_added}')
    except Exception as e:
        _diag_phase_error(phase, e)
        raise
    finally:
        _diag_phase_end(phase, processed=processed, apps_added=apps_added)

def process_library_identification(app):
    logger.info(f"Starting library identification process for all libraries...")
    if not titles_lib.keys_loaded():
        logger.warning(
            "Keys are not loaded. Falling back to filename-based library identification."
        )
    try:
        with app.app_context():
            libraries = get_libraries()
            for library in libraries:
                identify_library_files(library.path)

    except Exception as e:
        logger.error(f"Error during library identification process: {e}")
    logger.info(f"Library identification process for all libraries completed.")

def update_titles():
    phase = 'update_titles'
    _diag_phase_start(phase)
    _diag_sample_identity_map(phase)
    # Remove titles that no longer have any owned apps
    titles_removed = remove_titles_without_owned_apps()
    if titles_removed > 0:
            logger.info(f"Removed {titles_removed} titles with no owned apps.")

    last_title_pk = 0
    processed = 0
    try:
        while True:
            title_batch = (
                Titles.query
                .filter(Titles.id > last_title_pk)
                .order_by(Titles.id)
                .limit(_IDENTIFY_QUERY_BATCH_SIZE)
                .all()
            )
            if not title_batch:
                break
            last_title_pk = title_batch[-1].id
            title_batch_ids = [title.id for title in title_batch]
            _sync_apps_owned_flags(title_ids=title_batch_ids)
            app_rows = (
                db.session.query(
                    Apps.title_id,
                    Apps.app_id,
                    Apps.app_version,
                    Apps.app_type,
                    Apps.owned
                )
                .filter(Apps.title_id.in_(title_batch_ids))
                .all()
            )
            apps_by_title_fk = {}
            for app_row in app_rows:
                apps_by_title_fk.setdefault(app_row.title_id, []).append(app_row)

            for title in title_batch:
                title_apps = apps_by_title_fk.get(title.id, [])

                # check have_base - look for owned base apps
                owned_base_apps = [
                    app for app in title_apps
                    if app.app_type == APP_TYPE_BASE and bool(app.owned)
                ]
                have_base = len(owned_base_apps) > 0

                # check up_to_date - find highest owned update version
                owned_update_apps = [
                    app for app in title_apps
                    if app.app_type == APP_TYPE_UPD and bool(app.owned) and not bool(getattr(app, 'ignored', False))
                ]
                available_update_apps = [
                    app for app in title_apps
                    if app.app_type == APP_TYPE_UPD and not bool(getattr(app, 'ignored', False))
                ]

                if not available_update_apps:
                    up_to_date = True
                elif not owned_update_apps:
                    up_to_date = False
                else:
                    highest_available_version = max(_safe_int(app.app_version) for app in available_update_apps)
                    highest_owned_version = max(_safe_int(app.app_version) for app in owned_update_apps)
                    up_to_date = highest_owned_version >= highest_available_version

                # check complete - latest version of all available DLC are owned
                available_dlc_apps = [
                    app for app in title_apps
                    if app.app_type == APP_TYPE_DLC and not bool(getattr(app, 'ignored', False))
                ]
                if not available_dlc_apps:
                    complete = True
                else:
                    dlc_by_id = {}
                    for app in available_dlc_apps:
                        app_id = app.app_id
                        version = _safe_int(app.app_version)
                        if app_id not in dlc_by_id or version > dlc_by_id[app_id]['version']:
                            dlc_by_id[app_id] = {
                                'version': version,
                                'owned': bool(app.owned)
                            }
                    complete = all(dlc_info['owned'] for dlc_info in dlc_by_id.values())

                title.have_base = have_base
                title.up_to_date = up_to_date
                title.complete = complete
                processed += 1

            db.session.commit()
            db.session.expunge_all()
            _diag_sample_identity_map(phase)

        gc.collect()
        _diag_note_gc(phase)
    except Exception as e:
        _diag_phase_error(phase, e)
        raise
    finally:
        _diag_phase_end(phase, processed=processed, titles_removed=titles_removed)

def get_library_status(title_id):
    title = get_title(title_id)
    title_apps = get_all_title_apps(title_id)

    available_versions = titles_lib.get_all_existing_versions(title_id)
    for version in available_versions:
        if len(list(filter(lambda x: x.get('app_type') == APP_TYPE_UPD and str(x.get('app_version')) == str(version['version']), title_apps))):
            version['owned'] = True
        else:
            version['owned'] = False

    library_status = {
        'has_base': title.have_base,
        'has_latest_version': title.up_to_date,
        'version': available_versions,
        'has_all_dlcs': title.complete
    }
    return library_status

def _compute_library_cache_state_token():
    """Build a token from library-related table state (not whole DB file mtime)."""
    try:
        row = db.session.execute(
            text(
                """
                SELECT
                    COALESCE((SELECT COUNT(*) FROM files), 0),
                    COALESCE((SELECT MAX(id) FROM files), 0),
                    COALESCE((SELECT SUM(size) FROM files), 0),
                    COALESCE((SELECT SUM(CASE WHEN identified THEN 1 ELSE 0 END) FROM files), 0),
                    COALESCE((SELECT SUM(
                        (LENGTH(COALESCE(filepath, '')) + LENGTH(COALESCE(filename, '')) + COALESCE(size, 0))
                        * ((id % 131) + 1)
                    ) FROM files), 0),
                    COALESCE((SELECT COUNT(*) FROM apps), 0),
                    COALESCE((SELECT MAX(id) FROM apps), 0),
                    COALESCE((SELECT SUM(CASE WHEN owned THEN 1 ELSE 0 END) FROM apps), 0),
                    COALESCE((SELECT SUM(CASE WHEN ignored THEN 1 ELSE 0 END) FROM apps), 0),
                    COALESCE((SELECT SUM(COALESCE(app_version_num, 0)) FROM apps), 0),
                    COALESCE((SELECT SUM(
                        (COALESCE(title_id, 0) + COALESCE(app_version_num, 0))
                        * ((id % 127) + 1)
                    ) FROM apps), 0),
                    COALESCE((SELECT COUNT(*) FROM titles), 0),
                    COALESCE((SELECT MAX(id) FROM titles), 0),
                    COALESCE((SELECT SUM(CASE WHEN have_base THEN 1 ELSE 0 END) FROM titles), 0),
                    COALESCE((SELECT SUM(CASE WHEN up_to_date THEN 1 ELSE 0 END) FROM titles), 0),
                    COALESCE((SELECT SUM(CASE WHEN complete THEN 1 ELSE 0 END) FROM titles), 0),
                    COALESCE((SELECT COUNT(*) FROM app_files), 0),
                    COALESCE((SELECT MAX(app_id) FROM app_files), 0),
                    COALESCE((SELECT MAX(file_id) FROM app_files), 0)
                """
            )
        ).first()
    except Exception:
        # Conservative fallback during migration/bootstrap windows.
        row = None

    if row is None:
        parts = []
        for label, path in (('db', DB_FILE), ('config', CONFIG_FILE)):
            try:
                st = os.stat(path)
                mtime_ns = getattr(st, 'st_mtime_ns', int(st.st_mtime * 1e9))
                parts.append(f"{label}:{int(mtime_ns)}:{int(st.st_size)}")
            except OSError:
                parts.append(f"{label}:missing")
        return "|".join(parts)
    else:
        fingerprint = ":".join(str(int(value or 0)) for value in row)

    try:
        config_stat = os.stat(CONFIG_FILE)
        config_token = f"{int(getattr(config_stat, 'st_mtime_ns', int(config_stat.st_mtime * 1e9)))}:{int(config_stat.st_size)}"
    except OSError:
        config_token = "missing"

    return f"lib:{fingerprint}|cfg:{config_token}"


def invalidate_library_cache_state_token():
    with _library_state_token_lock:
        _library_state_token_cache['token'] = None
        _library_state_token_cache['updated_at'] = 0.0


def get_library_cache_state_token(force_refresh=False):
    now = time.time()
    with _library_state_token_lock:
        cached_token = _library_state_token_cache.get('token')
        cached_ts = float(_library_state_token_cache.get('updated_at') or 0.0)
        if (
            not force_refresh
            and cached_token
            and (now - cached_ts) < _LIBRARY_STATE_TOKEN_CACHE_TTL_S
        ):
            return str(cached_token)

    token = _compute_library_cache_state_token()
    with _library_state_token_lock:
        _library_state_token_cache['token'] = token
        _library_state_token_cache['updated_at'] = time.time()
    return token


# Bump this when the cached library schema changes.
LIBRARY_CACHE_VERSION = 8

def is_library_unchanged():
    cache_path = Path(LIBRARY_CACHE_FILE)
    if not cache_path.exists():
        return False

    saved_library = load_library_from_disk()
    if not saved_library:
        return False

    if saved_library.get('version') != LIBRARY_CACHE_VERSION:
        return False

    saved_state_token = str(saved_library.get('state_token') or '').strip()
    if not saved_state_token:
        return False

    current_state_token = get_library_cache_state_token(force_refresh=True)
    return saved_state_token == current_state_token

def save_library_to_disk(library_data):
    cache_path = Path(LIBRARY_CACHE_FILE)
    # Ensure cache directory exists
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    safe_write_json(cache_path, library_data)

def load_library_from_disk():
    cache_path = Path(LIBRARY_CACHE_FILE)
    if not cache_path.exists():
        return None

    try:
        with cache_path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except:
        return None

def generate_library():
    phase = 'generate_library'
    """Generate the game library from Apps table, using cached version if unchanged"""
    if is_library_unchanged():
        saved_library = load_library_from_disk()
        if saved_library:
            _diag_phase_start(phase, cached=True)
            _diag_phase_end(phase, cached=True, items=len(saved_library.get('library') or []))
            return saved_library['library']

    # If the schema changed, regenerate and overwrite the cache.
    try:
        cache_path = Path(LIBRARY_CACHE_FILE)
        if cache_path.exists():
            cache_path.unlink(missing_ok=True)
    except Exception:
        pass

    logger.info('Generating library ...')
    _diag_phase_start(phase, cached=False)
    _diag_sample_identity_map(phase)
    games_info = []
    apps_snapshot = []
    processed_dlc_apps = set()  # Track processed DLC app_ids to avoid duplicates.
    try:
        with titles_lib.titledb_session():
            apps_snapshot = get_all_apps()
            snapshot_app_ids = {
                str(entry.get('app_id') or '').strip().upper()
                for entry in apps_snapshot
                if str(entry.get('app_id') or '').strip()
            }
            apps_lookup = {}
            if snapshot_app_ids:
                apps_with_files = (
                    db.session.query(Apps)
                    .options(joinedload(Apps.files))
                    .filter(Apps.app_id.in_(snapshot_app_ids))
                    .all()
                )
                apps_lookup = {
                    (
                        str(app.app_id or '').strip().upper(),
                        str(app.app_version or '0').strip(),
                    ): app
                    for app in apps_with_files
                    if str(app.app_id or '').strip()
                }
            logger.info(f'Found {len(apps_snapshot)} apps in database')

            apps_by_title = {}
            for app_entry in apps_snapshot:
                title_id = app_entry.get('title_id')
                if title_id:
                    apps_by_title.setdefault(title_id, []).append(app_entry)

            title_state = {
                row.title_id: {
                    'have_base': bool(row.have_base),
                    'up_to_date': bool(row.up_to_date),
                    'complete': bool(row.complete),
                }
                for row in db.session.query(Titles.title_id, Titles.have_base, Titles.up_to_date, Titles.complete).all()
                if row.title_id
            }
            titledb_info_cache = {}

            def _titledb_info(title_id):
                key = str(title_id or '').strip().upper()
                if not key:
                    return None
                if key not in titledb_info_cache:
                    titledb_info_cache[key] = titles_lib.get_game_info(key)
                return titledb_info_cache.get(key)

            for app_entry in apps_snapshot:
                title = dict(app_entry)
                app_lookup_key = (
                    str(title.get('app_id') or '').strip().upper(),
                    str(title.get('app_version') or '0').strip(),
                )
                app_obj = apps_lookup.get(app_lookup_key)
                file_list = []
                if app_obj:
                    for file_entry in app_obj.files:
                        file_list.append({
                            'filepath': file_entry.filepath,
                            'filename': file_entry.filename,
                            'folder': file_entry.folder,
                            'size': file_entry.size,
                        })
                title['files'] = file_list
                has_none_value = any(value is None for value in title.values())
                if has_none_value:
                    logger.warning(f'File contains None value, it will be skipped: {title}')
                    continue
                if title['app_type'] == APP_TYPE_UPD:
                    continue

                info_from_titledb = _titledb_info(title.get('app_id'))
                if info_from_titledb is None:
                    logger.warning(f'Info not found for game: {title}')
                    continue
                title.update(info_from_titledb)

                title['genre'] = title.get('category') or ''
                if title.get('category') is None:
                    title['category'] = ''

                if title['app_type'] == APP_TYPE_BASE:
                    current_state = title_state.get(title.get('title_id')) or {}
                    title['has_base'] = bool(current_state.get('have_base'))
                    title['has_latest_version'] = (
                        bool(current_state.get('have_base')) and bool(current_state.get('up_to_date'))
                    )
                    title['has_all_dlcs'] = bool(current_state.get('complete'))

                    title_apps = apps_by_title.get(title.get('title_id'), [])
                    update_apps = [app for app in title_apps if app.get('app_type') == APP_TYPE_UPD]

                    available_versions = titles_lib.get_all_existing_versions(title.get('title_id'))
                    version_release_dates = {v['version']: v['release_date'] for v in available_versions}

                    version_list = []
                    for update_app in update_apps:
                        app_version = int(update_app['app_version'])
                        version_list.append({
                            'version': app_version,
                            'owned': update_app.get('owned', False),
                            'size': update_app.get('size', 0) or 0,
                            'release_date': version_release_dates.get(app_version, 'Unknown')
                        })

                    title['version'] = sorted(version_list, key=lambda x: x['version'], reverse=True)
                    title['title_id_name'] = title['name']

                elif title['app_type'] == APP_TYPE_DLC:
                    if title['app_id'] in processed_dlc_apps:
                        continue
                    processed_dlc_apps.add(title['app_id'])

                    title_apps = apps_by_title.get(title.get('title_id'), [])
                    dlc_apps = [app for app in title_apps if app.get('app_type') == APP_TYPE_DLC and app['app_id'] == title['app_id']]

                    version_list = []
                    for dlc_app in dlc_apps:
                        app_version = int(dlc_app['app_version'])
                        version_list.append({
                            'version': app_version,
                            'owned': dlc_app.get('owned', False),
                            'release_date': 'Unknown'
                        })

                    title['version'] = sorted(version_list, key=lambda x: x['version'], reverse=True)
                    title['owned'] = any(app.get('owned') for app in dlc_apps)

                    if dlc_apps:
                        highest_version = max(int(app['app_version']) for app in dlc_apps)
                        owned_versions = [int(app['app_version']) for app in dlc_apps if app.get('owned')]
                        title['has_latest_version'] = (
                            len(owned_versions) > 0 and max(owned_versions) >= highest_version
                        )
                    else:
                        title['has_latest_version'] = True

                    titleid_info = _titledb_info(title.get('title_id'))
                    title['title_id_name'] = titleid_info['name'] if titleid_info else 'Unrecognized'

                games_info.append(title)

        library_data = {
            'version': LIBRARY_CACHE_VERSION,
            'state_token': get_library_cache_state_token(force_refresh=True),
            'library': sorted(games_info, key=lambda x: (
                "title_id_name" not in x,
                x.get("title_id_name", "Unrecognized") or "Unrecognized",
                x.get('app_id', "") or ""
            ))
        }

        save_library_to_disk(library_data)
        gc.collect()
        _diag_note_gc(phase)
        _diag_sample_identity_map(phase)
        logger.info('Generating library done.')
        return library_data['library']
    except Exception as e:
        _diag_phase_error(phase, e)
        raise
    finally:
        _diag_phase_end(
            phase,
            cached=False,
            apps_snapshot=len(apps_snapshot),
            generated_items=len(games_info),
        )

def _sanitize_component(value, fallback='Unknown'):
    value = str(value or '').strip()
    value = re.sub(r'[<>:"/\\\\|?*]', '', value)
    value = value.rstrip('. ')
    return value if value else fallback

def _sanitize_relative_path(path_value, fallback='Other'):
    raw = str(path_value or '').strip().replace('\\', '/')
    parts = [part for part in raw.split('/') if part and part not in ('.', '..')]
    clean_parts = [_sanitize_component(part, fallback='') for part in parts]
    clean_parts = [part for part in clean_parts if part]
    if not clean_parts:
        return _sanitize_component(fallback)
    return os.path.join(*clean_parts)

def _is_base_dir_template(rendered):
    # True when a rendered folder template refers only to the current/base
    # directory (e.g. ".", "./", ".."). Such a template means "no subfolder";
    # the file belongs directly in the library base directory. Without this the
    # "." used by the Flat preset would be stripped by _sanitize_relative_path
    # and fall through to the 'Other' fallback.
    raw = str(rendered or '').strip().replace('\\', '/')
    parts = [part for part in raw.split('/') if part]
    return bool(parts) and all(part in ('.', '..') for part in parts)

def _safe_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default

def _format_version_txt(value):
    text = str(value or '').strip()
    if not text:
        return '0.0.0'
    # Already semantic-like (for example "1.0.0").
    if re.fullmatch(r'\d+(?:\.\d+){1,3}', text):
        return text
    num = _safe_int(text, default=-1)
    if num < 0:
        return text
    major = (num >> 16) & 0xFFFF
    minor = (num >> 8) & 0xFF
    patch = num & 0xFF
    return f"{major}.{minor}.{patch}"

def _ensure_unique_path(path):
    if not os.path.exists(path):
        return path
    base, ext = os.path.splitext(path)
    counter = 1
    while True:
        candidate = f"{base} ({counter}){ext}"
        if not os.path.exists(candidate):
            return candidate
        counter += 1

def _get_file_signature(filepath):
    if not titles_lib.keys_loaded():
        return None
    try:
        identification, success, contents, error = titles_lib.identify_file(filepath)
    except Exception as e:
        logger.debug(f"Failed to identify file for signature {filepath}: {e}")
        return None
    if not success or not contents:
        return None
    signature = set()
    for content in contents:
        signature.add((
            content.get('title_id'),
            content.get('app_id'),
            content.get('type'),
            content.get('version')
        ))
    return signature or None

def _get_nsz_keys_file():
    return KEYS_FILE if os.path.exists(KEYS_FILE) else None

def _ensure_nsz_keys():
    key_source = _get_nsz_keys_file()
    if not key_source:
        return False, f"Keys file not found at {KEYS_FILE}."
    return True, None

def _quote_arg(value):
    value = str(value)
    if value.startswith('"') and value.endswith('"'):
        return value
    return f"\"{value}\""

def _get_nsz_runner():
    if importlib.util.find_spec('nsz') is not None:
        # `nsz` does not expose __main__ in this fork; call entrypoint directly.
        return f"{_quote_arg(sys.executable)} -c \"import nsz; nsz.main()\""
    return None

def _format_nsz_command(command_template, input_file, output_file, threads=None, verify=True):
    nsz_runner = _get_nsz_runner() or 'nsz'
    nsz_keys = _get_nsz_keys_file() or KEYS_FILE
    if not command_template:
        command_template = '{nsz_runner} --keys "{nsz_keys}" --minimal-output --verify -C -o "{output_dir}" "{input_file}"'
    command = command_template.format(
        nsz_runner=nsz_runner,
        nsz_exe=nsz_runner,
        nsz_keys=nsz_keys,
        input_file=input_file,
        output_file=output_file,
        output_dir=os.path.dirname(output_file),
        threads=threads or ''
    )
    if verify:
        if re.search(r'(^|\s)--verify(\s|$)', command) is None:
            command = f"{command} --verify"
    else:
        command = re.sub(r'(^|\s)--verify(?=\s|$)', ' ', command)
        command = re.sub(r'\s+', ' ', command).strip()
    if threads and re.search(r'(^|\\s)(-t|--threads)\\s', command) is None:
        command = f"{command} -t {threads}"
    return command

def _parse_command_args(command):
    if isinstance(command, (list, tuple)):
        args = [str(part) for part in command if str(part)]
    else:
        text = str(command or '').strip()
        if not text:
            raise ValueError('Conversion command is empty.')
        try:
            args = shlex.split(text, posix=(os.name != 'nt'))
        except ValueError as e:
            raise ValueError(f'Invalid conversion command syntax: {e}') from e
    if os.name == 'nt':
        # shlex with posix=False preserves the quotes around Windows paths and
        # quoted Python -c snippets. subprocess then treats those quotes as
        # literal characters in the executable/path and raises WinError 2.
        args = [
            arg[1:-1]
            if len(arg) >= 2 and arg[0] == arg[-1] and arg[0] in ('"', "'")
            else arg
            for arg in args
        ]
    if not args:
        raise ValueError('Conversion command is empty.')
    return args

def _format_command_for_log(command):
    args = _parse_command_args(command)
    if os.name == 'nt':
        return subprocess.list2cmdline(args)
    return ' '.join(shlex.quote(arg) for arg in args)

def _expected_compressed_output_path(input_file):
    base, ext = os.path.splitext(str(input_file or ''))
    ext = str(ext or '').strip().lower()
    if ext in ('.xci', '.xcz'):
        return f"{base}.xcz"
    return f"{base}.nsz"

def _alternate_compressed_output_path(path):
    base, ext = os.path.splitext(str(path or ''))
    ext = str(ext or '').strip().lower()
    if ext == '.xcz':
        return f"{base}.nsz"
    if ext == '.nsz':
        return f"{base}.xcz"
    return None

def _resolve_existing_output_path(preferred_path):
    if preferred_path and os.path.exists(preferred_path):
        return preferred_path
    alt = _alternate_compressed_output_path(preferred_path)
    if alt and os.path.exists(alt):
        return alt
    return preferred_path

def _get_conversion_staging_dir():
    try:
        from app.settings import load_settings
        settings = load_settings()
    except Exception:
        return ''
    library_cfg = settings.get('library', {}) if isinstance(settings, dict) else {}
    raw_dir = str(library_cfg.get('conversion_staging_dir') or '').strip()
    if not raw_dir:
        return ''
    return os.path.abspath(os.path.expanduser(raw_dir))

def _ensure_conversion_staging_dir(path):
    if not path:
        return True, None
    try:
        os.makedirs(path, exist_ok=True)
    except Exception as e:
        return False, f"Failed to create conversion staging directory {path}: {e}"
    if not os.path.isdir(path):
        return False, f"Conversion staging directory is not a directory: {path}"
    if not os.access(path, os.W_OK):
        return False, f"Conversion staging directory is not writable: {path}"
    return True, None

def _build_staging_output_path(source_path, expected_output_file, staging_root):
    if not staging_root:
        return expected_output_file
    source_abs = os.path.abspath(str(source_path or ''))
    hash_suffix = hashlib.sha1(source_abs.encode('utf-8')).hexdigest()[:16]
    base_name = _sanitize_component(os.path.splitext(os.path.basename(source_abs))[0], fallback='file')
    staging_dir = os.path.join(staging_root, f"{base_name}-{hash_suffix}")
    return os.path.join(staging_dir, os.path.basename(expected_output_file))

def _clear_staging_output_candidates(staged_output_file):
    candidates = [staged_output_file]
    alt = _alternate_compressed_output_path(staged_output_file)
    if alt:
        candidates.append(alt)
    for candidate in candidates:
        if candidate and os.path.exists(candidate):
            os.remove(candidate)

def _cleanup_empty_parent_dirs(path, stop_path):
    current = os.path.abspath(str(path or ''))
    stop = os.path.abspath(str(stop_path or ''))
    while current:
        try:
            common = os.path.commonpath([current, stop])
        except ValueError:
            break
        if common != stop:
            break
        if current == stop:
            break
        try:
            os.rmdir(current)
        except OSError:
            break
        current = os.path.dirname(current)

def _final_output_path_from_source(source_path, produced_output_path):
    source_dir = os.path.dirname(str(source_path or ''))
    produced_name = os.path.basename(str(produced_output_path or ''))
    if not produced_name:
        produced_name = os.path.basename(_expected_compressed_output_path(source_path))
    return os.path.join(source_dir, produced_name)

def _finalize_staged_conversion_output(source_path, staged_output_path, staging_root):
    final_output_path = _final_output_path_from_source(source_path, staged_output_path)
    existing_final = _resolve_existing_output_path(final_output_path)
    if existing_final and os.path.exists(existing_final):
        raise FileExistsError(f"Output already exists: {existing_final}")
    os.makedirs(os.path.dirname(final_output_path), exist_ok=True)
    shutil.move(staged_output_path, final_output_path)
    _cleanup_empty_parent_dirs(os.path.dirname(staged_output_path), staging_root)
    return final_output_path


def _is_hardlinked_file(path):
    try:
        return os.stat(path).st_nlink > 1
    except OSError:
        return False

def _summarize_conversion_failure(log_text, output_file=None):
    text = str(log_text or '')
    lowered = text.lower()

    if 'verification detected hash mismatch' in lowered or '[bad verify]' in lowered:
        summary = 'Verification failed (hash mismatch). Source file is likely bad or corrupted.'
    elif 'permissionerror' in lowered and 'winerror 32' in lowered:
        summary = 'Conversion failed and cleanup could not remove failed output (WinError 32: file in use).'
    else:
        summary = 'Conversion failed.'

    if output_file and os.path.exists(output_file):
        summary = f"{summary} Output file exists but is unverified and may be invalid: {output_file}"
    return summary

def _run_command(command, log_cb=None, stream_output=False, cancel_cb=None, timeout_seconds=None):
    command_args = _parse_command_args(command)
    env = os.environ.copy()
    env['PYTHONIOENCODING'] = 'utf-8'
    env['PYTHONUTF8'] = '1'
    if not stream_output:
        return subprocess.run(command_args, shell=False, capture_output=True, text=True, env=env)

    process = subprocess.Popen(
        command_args,
        shell=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        env=env
    )
    start_time = time.time()
    streamed_lines = []
    if process.stdout:
        while True:
            if cancel_cb and cancel_cb():
                process.terminate()
                break
            if timeout_seconds and (time.time() - start_time) > timeout_seconds:
                if log_cb:
                    log_cb(f"Timeout after {timeout_seconds}s, terminating process.")
                process.terminate()
                break
            line = process.stdout.readline()
            if line:
                clean_line = line.rstrip()
                streamed_lines.append(clean_line)
                if len(streamed_lines) > 120:
                    streamed_lines = streamed_lines[-120:]
                if log_cb:
                    log_cb(clean_line)
            elif process.poll() is not None:
                break
            else:
                time.sleep(0.2)
    returncode = process.wait()
    stderr_summary = '\n'.join(streamed_lines[-40:]) if streamed_lines else ''
    result = subprocess.CompletedProcess(command_args, returncode, '', stderr_summary)
    return result

def _choose_primary_app(apps):
    if not apps:
        return None
    priority = {
        APP_TYPE_BASE: 0,
        APP_TYPE_UPD: 1,
        APP_TYPE_DLC: 2
    }
    return sorted(
        apps,
        key=lambda app: (
            priority.get(app.app_type, 99),
            app.app_id or '',
            _safe_int(app.app_version)
        )
    )[0]

def _compute_relative_folder(library_path, full_path):
    folder = os.path.dirname(full_path)
    if os.path.normpath(library_path) == os.path.normpath(folder):
        return ''
    normalized = folder.replace(library_path, '')
    return normalized if normalized.startswith(os.sep) else os.sep + normalized

def _sync_apps_owned_flags(app_ids=None, title_ids=None):
    has_files_expr = (
        db.session.query(app_files.c.app_id)
        .filter(app_files.c.app_id == Apps.id)
        .exists()
    )
    query = db.session.query(Apps)
    if app_ids is not None:
        scoped_app_ids = [int(v) for v in (app_ids or []) if v is not None]
        if not scoped_app_ids:
            return 0
        query = query.filter(Apps.id.in_(scoped_app_ids))
    elif title_ids is not None:
        scoped_title_ids = [int(v) for v in (title_ids or []) if v is not None]
        if not scoped_title_ids:
            return 0
        query = query.filter(Apps.title_id.in_(scoped_title_ids))
    return int(query.update({Apps.owned: has_files_expr}, synchronize_session=False) or 0)

def _replace_or_create_converted_file_row(
    source_file_id,
    source_path,
    output_file,
    source_library_id,
    output_ext,
    source_multicontent,
    source_nb_content,
    source_identification_type,
    source_identification_attempts,
    source_last_attempt,
    source_apps
):
    library_path = get_library_path(source_library_id)
    folder = _compute_relative_folder(library_path, output_file)
    row_data = {
        'library_id': source_library_id,
        'filepath': output_file,
        'folder': folder,
        'filename': os.path.basename(output_file),
        'extension': output_ext,
        'compressed': True,
        'size': os.path.getsize(output_file),
    }

    updated = (
        db.session.query(Files)
        .filter(Files.id == source_file_id)
        .update(row_data, synchronize_session=False)
    )
    if updated == 0 and source_path:
        updated = (
            db.session.query(Files)
            .filter(Files.filepath == source_path)
            .update(row_data, synchronize_session=False)
        )
    if updated == 0:
        updated = (
            db.session.query(Files)
            .filter(Files.filepath == output_file)
            .update(row_data, synchronize_session=False)
        )

    if updated > 0:
        for app in source_apps:
            app.owned = True
        return

    new_file = Files(
        filepath=output_file,
        library_id=source_library_id,
        folder=folder,
        filename=os.path.basename(output_file),
        extension=output_ext,
        size=os.path.getsize(output_file),
        compressed=True,
        multicontent=source_multicontent,
        nb_content=source_nb_content,
        identified=True,
        identification_type=source_identification_type,
        identification_attempts=source_identification_attempts,
        last_attempt=source_last_attempt
    )
    db.session.add(new_file)
    db.session.flush()
    for app in source_apps:
        if new_file not in app.files:
            app.files.append(new_file)
        app.owned = True

def _normalize_naming_templates(raw_templates):
    default_templates = (
        DEFAULT_SETTINGS.get('library', {})
        .get('naming_templates', {})
        .get('templates', {})
    )
    default_active = (
        DEFAULT_SETTINGS.get('library', {})
        .get('naming_templates', {})
        .get('active', 'default')
    )

    templates = {}
    if isinstance(raw_templates, dict):
        templates = raw_templates.get('templates', {}) or {}
        active = raw_templates.get('active') or default_active
    else:
        active = default_active

    if not isinstance(templates, dict) or not templates:
        templates = default_templates
        active = default_active

    normalized = {}
    for template_name, template_cfg in templates.items():
        if not isinstance(template_cfg, dict):
            continue
        clean_template = {}
        for key in ('base', 'update', 'dlc', 'other'):
            section = template_cfg.get(key) or {}
            if not isinstance(section, dict):
                section = {}
            fallback = (default_templates.get('default') or {}).get(key, {})
            clean_template[key] = {
                'folder': str(section.get('folder') or fallback.get('folder') or ''),
                'filename': str(section.get('filename') or fallback.get('filename') or ''),
            }
        normalized[str(template_name).strip() or 'default'] = clean_template

    if not normalized:
        normalized = default_templates
        active = default_active

    if active not in normalized:
        active = next(iter(normalized.keys()))

    return {
        'active': active,
        'templates': normalized,
    }

def _get_active_template():
    from app.settings import load_settings

    app_settings = load_settings()
    library = (app_settings or {}).get('library', {})
    naming_templates = _normalize_naming_templates(library.get('naming_templates'))
    active = naming_templates.get('active')
    templates = naming_templates.get('templates') or {}
    return templates.get(active) or next(iter(templates.values()))

def _render_template(template, values):
    class _SafeFormatDict(dict):
        def __missing__(self, key):
            return ''
    try:
        return str(template or '').format_map(_SafeFormatDict(values))
    except Exception:
        return ''

def _build_destination(library_path, file_entry, app, title_name, dlc_name, active_template=None):
    if active_template is None:
        active_template = _get_active_template()
    title_id = app.title.title_id if app.title else None
    safe_title = _sanitize_component(title_name or title_id or app.app_id)
    safe_title_id = _sanitize_component(title_id or app.app_id)
    version = app.app_version or '0'
    extension = file_entry.extension or os.path.splitext(file_entry.filename or '')[1].lstrip('.')
    safe_ext = _sanitize_component(extension, fallback='nsp')
    safe_app_id = _sanitize_component(app.app_id or safe_title_id)
    safe_dlc_name = _sanitize_component(dlc_name or app.app_id)
    version_txt = None
    app_id_for_lookup = str(app.app_id or '').strip()
    if app_id_for_lookup:
        for candidate in (app_id_for_lookup, app_id_for_lookup.lower(), app_id_for_lookup.upper()):
            version_txt = titles_lib.get_app_id_version_from_versions_txt(candidate)
            if version_txt:
                break
    semantic_version_txt = _format_version_txt(version_txt or version)
    safe_version_txt = _sanitize_component(semantic_version_txt, fallback='0.0.0')

    template_vars_common = {
        'title': safe_title,
        'title_id': safe_title_id,
        'app_id': safe_app_id,
        'version': str(version),
        'ext': safe_ext,
        'dlc_name': safe_dlc_name,
    }
    template_vars_filename = dict(template_vars_common)
    template_vars_filename['version_txt'] = safe_version_txt

    if app.app_type == APP_TYPE_BASE:
        section = active_template.get('base', {})
        folder_tpl = section.get('folder')
        filename_tpl = section.get('filename')
    elif app.app_type == APP_TYPE_UPD:
        section = active_template.get('update', {})
        folder_tpl = section.get('folder')
        filename_tpl = section.get('filename')
    elif app.app_type == APP_TYPE_DLC:
        section = active_template.get('dlc', {})
        folder_tpl = section.get('folder')
        filename_tpl = section.get('filename')
    else:
        section = active_template.get('other', {})
        folder_tpl = section.get('folder')
        filename_tpl = section.get('filename')

    folder_rel = _render_template(folder_tpl, template_vars_common)
    if not folder_rel:
        # No folder template configured -> default to a per-title folder.
        folder_rel = _sanitize_component(f"{safe_title} [{safe_title_id}]")
        folder_rel = _sanitize_relative_path(folder_rel, fallback='Other')
    elif _is_base_dir_template(folder_rel):
        # Template explicitly targets the library base directory (e.g. "." in the
        # Flat preset) -> place the file directly under library_path, no subfolder.
        folder_rel = ''
    else:
        folder_rel = _sanitize_relative_path(folder_rel, fallback='Other')

    filename = _render_template(filename_tpl, template_vars_filename)
    if not filename:
        filename = file_entry.filename or f"{safe_title} [{safe_title_id}] [UNKNOWN].{safe_ext}"
    filename = _sanitize_component(filename)

    folder = os.path.join(library_path, folder_rel) if folder_rel else library_path
    return folder, filename

def organize_library(dry_run=False, verbose=False, detail_limit=200):
    results = {
        'success': True,
        'moved': 0,
        'skipped': 0,
        'folders_deleted': 0,
        'folders_failed': 0,
        'mutated': False,
        'errors': [],
        'details': []
    }
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    def plan_empty_dirs(root_dir):
        """Return a bottom-up list of empty directories (excluding root_dir).

        In dry_run mode we plan deletions so parent directories that only contain
        empty directories are also considered deletable.
        """
        root_dir = os.path.normpath(root_dir or '')
        if not root_dir or not os.path.isdir(root_dir):
            return []

        removable = set()
        planned = []
        for dirpath, dirnames, filenames in os.walk(root_dir, topdown=False):
            try:
                norm_dirpath = os.path.normpath(dirpath)
                if norm_dirpath == root_dir:
                    continue
                if os.path.islink(dirpath):
                    continue

                has_remaining = False
                with os.scandir(dirpath) as it:
                    for entry in it:
                        try:
                            if entry.is_dir(follow_symlinks=False):
                                if os.path.normpath(entry.path) in removable:
                                    continue
                                has_remaining = True
                                break
                            else:
                                has_remaining = True
                                break
                        except OSError:
                            has_remaining = True
                            break

                if not has_remaining:
                    removable.add(norm_dirpath)
                    planned.append(dirpath)
            except OSError:
                continue
        return planned

    with titles_lib.titledb_session():
        title_name_cache = {}
        app_name_cache = {}
        active_template = _get_active_template()
        last_file_id = 0

        while True:
            files = (
                Files.query
                .filter(Files.identified.is_(True), Files.id > last_file_id)
                .order_by(Files.id)
                .limit(_ORGANIZE_BATCH_SIZE)
                .all()
            )
            if not files:
                break
            last_file_id = files[-1].id

            for file_entry in files:
                if not file_entry.filepath or not os.path.exists(file_entry.filepath):
                    results['skipped'] += 1
                    add_detail('Skip missing file path.')
                    continue
                library_path = get_library_path(file_entry.library_id)
                if not library_path:
                    results['skipped'] += 1
                    add_detail(f"Skip missing library for {file_entry.filepath}.")
                    continue
                primary_app = _choose_primary_app(list(file_entry.apps))
                if not primary_app:
                    results['skipped'] += 1
                    add_detail(f"Skip no app mapping for {file_entry.filepath}.")
                    continue

                title_id = primary_app.title.title_id if primary_app.title else None
                if title_id not in title_name_cache:
                    info = titles_lib.get_game_info(title_id) if title_id else None
                    title_name_cache[title_id] = info['name'] if info else title_id or primary_app.app_id

                title_name = title_name_cache.get(title_id)
                dlc_name = None
                if primary_app.app_type == APP_TYPE_DLC:
                    if primary_app.app_id not in app_name_cache:
                        info = titles_lib.get_game_info(primary_app.app_id)
                        app_name_cache[primary_app.app_id] = info['name'] if info else primary_app.app_id
                    dlc_name = app_name_cache.get(primary_app.app_id)

                dest_dir, dest_filename = _build_destination(
                    library_path,
                    file_entry,
                    primary_app,
                    title_name,
                    dlc_name,
                    active_template=active_template,
                )
                dest_path = os.path.join(dest_dir, dest_filename)
                if os.path.normpath(dest_path) == os.path.normpath(file_entry.filepath):
                    results['skipped'] += 1
                    add_detail(f"Skip already organized: {file_entry.filepath}.")
                    continue
                if os.path.exists(dest_path):
                    old_path = file_entry.filepath
                    signature_match = False
                    old_signature = _get_file_signature(old_path)
                    dest_signature = _get_file_signature(dest_path)
                    if old_signature and dest_signature:
                        signature_match = bool(old_signature.intersection(dest_signature))
                    try:
                        old_size = os.path.getsize(old_path) if os.path.exists(old_path) else None
                        dest_size = os.path.getsize(dest_path)
                    except OSError:
                        old_size = None
                        dest_size = None

                    if signature_match:
                        existing_entry = Files.query.filter_by(filepath=dest_path).first()
                        if existing_entry:
                            for app in list(file_entry.apps):
                                if existing_entry not in app.files:
                                    app.files.append(existing_entry)
                                if file_entry in app.files:
                                    app.files.remove(file_entry)
                                app.owned = len(app.files) > 0
                            db.session.delete(file_entry)
                            db.session.commit()
                            results['mutated'] = True
                        else:
                            update_file_path(library_path, old_path, dest_path)
                        if os.path.exists(old_path) and os.path.normpath(old_path) != os.path.normpath(dest_path):
                            os.remove(old_path)
                            results['mutated'] = True
                        results['skipped'] += 1
                        add_detail(f"Skip duplicate; kept existing: {dest_path}.")
                        continue
                dest_path = _ensure_unique_path(dest_path)

                if not dry_run:
                    try:
                        os.makedirs(dest_dir, exist_ok=True)
                        old_path = file_entry.filepath
                        shutil.move(old_path, dest_path)
                        update_file_path(library_path, old_path, dest_path)
                        results['moved'] += 1
                        results['mutated'] = True
                        add_detail(f"Moved: {old_path} -> {dest_path}.")
                    except Exception as e:
                        logger.error(f"Failed to move {file_entry.filepath}: {e}")
                        results['errors'].append(str(e))
                        add_detail(f"Error moving {file_entry.filepath}: {e}.")
                else:
                    results['moved'] += 1
                    add_detail(f"Plan move: {file_entry.filepath} -> {dest_path}.")
            db.session.expunge_all()

    # Cleanup: delete empty folders created or left behind after organizing.
    try:
        library_roots = [lib.path for lib in get_libraries() if lib and lib.path]
    except Exception:
        library_roots = []

    planned_dirs = []
    for root in library_roots:
        planned_dirs.extend(plan_empty_dirs(root))

    if planned_dirs:
        if dry_run:
            results['folders_deleted'] = len(planned_dirs)
            for d in planned_dirs[:detail_limit]:
                add_detail(f"Plan delete empty folder: {d}.")
        else:
            for d in planned_dirs:
                try:
                    os.rmdir(d)
                    results['folders_deleted'] += 1
                    results['mutated'] = True
                    add_detail(f"Deleted empty folder: {d}.")
                except OSError:
                    results['folders_failed'] += 1
                    add_detail(f"Failed to delete empty folder: {d}.")

    if results['errors']:
        results['success'] = False
    return results

def organize_files(filepaths, dry_run=False, verbose=False, detail_limit=200):
    results = {
        'success': True,
        'moved': 0,
        'skipped': 0,
        'errors': [],
        'details': []
    }
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    if not filepaths:
        return results

    with titles_lib.titledb_session():
        title_name_cache = {}
        app_name_cache = {}
        active_template = _get_active_template()

        unique_paths = list(dict.fromkeys(filepaths))
        files = Files.query.filter(Files.filepath.in_(unique_paths)).all()
        file_lookup = {file.filepath: file for file in files}

        for filepath in unique_paths:
            file_entry = file_lookup.get(filepath)
            if not file_entry:
                results['skipped'] += 1
                add_detail(f"Skip missing file record: {filepath}.")
                continue
            if not file_entry.filepath or not os.path.exists(file_entry.filepath):
                results['skipped'] += 1
                add_detail('Skip missing file path.')
                continue
            if not file_entry.identified:
                results['skipped'] += 1
                add_detail(f"Skip not identified: {file_entry.filepath}.")
                continue
            library_path = get_library_path(file_entry.library_id)
            if not library_path:
                results['skipped'] += 1
                add_detail(f"Skip missing library for {file_entry.filepath}.")
                continue
            primary_app = _choose_primary_app(list(file_entry.apps))
            if not primary_app:
                results['skipped'] += 1
                add_detail(f"Skip no app mapping for {file_entry.filepath}.")
                continue

            title_id = primary_app.title.title_id if primary_app.title else None
            if title_id not in title_name_cache:
                info = titles_lib.get_game_info(title_id) if title_id else None
                title_name_cache[title_id] = info['name'] if info else title_id or primary_app.app_id

            title_name = title_name_cache.get(title_id)
            dlc_name = None
            if primary_app.app_type == APP_TYPE_DLC:
                if primary_app.app_id not in app_name_cache:
                    info = titles_lib.get_game_info(primary_app.app_id)
                    app_name_cache[primary_app.app_id] = info['name'] if info else primary_app.app_id
                dlc_name = app_name_cache.get(primary_app.app_id)

            dest_dir, dest_filename = _build_destination(
                library_path,
                file_entry,
                primary_app,
                title_name,
                dlc_name,
                active_template=active_template,
            )
            dest_path = os.path.join(dest_dir, dest_filename)
            if os.path.normpath(dest_path) == os.path.normpath(file_entry.filepath):
                results['skipped'] += 1
                add_detail(f"Skip already organized: {file_entry.filepath}.")
                continue
            if os.path.exists(dest_path):
                old_path = file_entry.filepath
                signature_match = False
                old_signature = _get_file_signature(old_path)
                dest_signature = _get_file_signature(dest_path)
                if old_signature and dest_signature:
                    signature_match = bool(old_signature.intersection(dest_signature))
                try:
                    old_size = os.path.getsize(old_path) if os.path.exists(old_path) else None
                    dest_size = os.path.getsize(dest_path)
                except OSError:
                    old_size = None
                    dest_size = None

                if signature_match:
                    existing_entry = Files.query.filter_by(filepath=dest_path).first()
                    if existing_entry:
                        for app in list(file_entry.apps):
                            if existing_entry not in app.files:
                                app.files.append(existing_entry)
                            if file_entry in app.files:
                                app.files.remove(file_entry)
                            app.owned = len(app.files) > 0
                        db.session.delete(file_entry)
                        db.session.commit()
                    else:
                        update_file_path(library_path, old_path, dest_path)
                    if os.path.exists(old_path) and os.path.normpath(old_path) != os.path.normpath(dest_path):
                        os.remove(old_path)
                    results['skipped'] += 1
                    add_detail(f"Skip duplicate; kept existing: {dest_path}.")
                    continue
            dest_path = _ensure_unique_path(dest_path)

            if not dry_run:
                try:
                    os.makedirs(dest_dir, exist_ok=True)
                    old_path = file_entry.filepath
                    shutil.move(old_path, dest_path)
                    update_file_path(library_path, old_path, dest_path)
                    results['moved'] += 1
                    add_detail(f"Moved: {old_path} -> {dest_path}.")
                except Exception as e:
                    logger.error(f"Failed to move {file_entry.filepath}: {e}")
                    results['errors'].append(str(e))
                    add_detail(f"Error moving {file_entry.filepath}: {e}.")
            else:
                results['moved'] += 1
                add_detail(f"Plan move: {file_entry.filepath} -> {dest_path}.")
    if results['errors']:
        results['success'] = False
    return results

def enqueue_organize_paths(filepaths):
    if not filepaths:
        return
    with _organize_lock:
        for path in filepaths:
            if not path:
                continue
            normalized_path = os.path.normpath(path)
            if os.path.isfile(normalized_path):
                _pending_organize_paths.add(normalized_path)
                continue
            if os.path.isdir(normalized_path):
                for root, _, filenames in os.walk(normalized_path):
                    for filename in filenames:
                        _pending_organize_paths.add(os.path.normpath(os.path.join(root, filename)))
                continue
            _pending_organize_paths.add(normalized_path)


def enqueue_cleanup_roots(paths):
    if not paths:
        return
    with _organize_lock:
        for path in paths:
            if path and os.path.isdir(path):
                _pending_cleanup_roots.add(os.path.normpath(path))


def _cleanup_import_staging_roots(paths):
    for root in paths or []:
        if not root or not os.path.isdir(root):
            continue
        for dirpath, _, filenames in os.walk(root, topdown=False):
            for filename in filenames:
                if is_supported_content_path(filename):
                    continue
                try:
                    os.remove(os.path.join(dirpath, filename))
                except OSError:
                    continue
            try:
                if not os.listdir(dirpath):
                    os.rmdir(dirpath)
            except OSError:
                continue

def organize_pending_downloads():
    with _organize_lock:
        if not _pending_organize_paths:
            pending = []
        else:
            pending = list(_pending_organize_paths)
            _pending_organize_paths.clear()
        cleanup_roots = list(_pending_cleanup_roots)
        _pending_cleanup_roots.clear()
    if pending:
        results = organize_files(pending, dry_run=False, verbose=False)
        if not results.get('success'):
            logger.warning("Failed to auto-organize completed downloads: %s", results.get('errors'))
    if cleanup_roots:
        _cleanup_import_staging_roots(cleanup_roots)

def _new_delete_results():
    return {
        'success': True,
        'deleted': 0,
        'skipped': 0,
        'mutated': False,
        'errors': [],
        'details': []
    }

def _merge_delete_results(results, partial_results, add_detail=None):
    if not partial_results:
        return
    results['deleted'] += int(partial_results.get('deleted') or 0)
    results['skipped'] += int(partial_results.get('skipped') or 0)
    if partial_results.get('mutated'):
        results['mutated'] = True
    results['errors'].extend(partial_results.get('errors') or [])
    if add_detail:
        for detail in partial_results.get('details') or []:
            add_detail(detail)

def _resolve_delete_targets(scope, title_id=None, app_id=None, app_type=None, version=None):
    scope_name = str(scope or '').strip().lower()
    normalized_title_id = str(title_id or '').strip().upper()
    normalized_app_id = str(app_id or '').strip().upper()
    normalized_app_type = str(app_type or '').strip().upper()
    normalized_version = None if version is None else str(version).strip()

    if scope_name == 'title_cascade':
        if not normalized_title_id:
            raise ValueError('Missing title_id for title cascade delete.')
        title = Titles.query.filter(func.upper(Titles.title_id) == normalized_title_id).first()
        if not title:
            raise ValueError(f'Title {normalized_title_id} was not found.')
        return (
            Apps.query
            .filter(
                Apps.title_id == title.id,
                Apps.owned.is_(True),
                Apps.app_type.in_([APP_TYPE_BASE, APP_TYPE_UPD, APP_TYPE_DLC])
            )
            .all()
        )

    if scope_name == 'app_version':
        if not normalized_app_id:
            raise ValueError('Missing app_id for app version delete.')
        if normalized_app_type not in (APP_TYPE_UPD, APP_TYPE_DLC):
            raise ValueError('app_type must be UPDATE or DLC for app version delete.')
        if normalized_version in (None, ''):
            raise ValueError('Missing version for app version delete.')
        return (
            Apps.query
            .filter(
                func.upper(Apps.app_id) == normalized_app_id,
                Apps.app_type == normalized_app_type,
                Apps.app_version == normalized_version,
                Apps.owned.is_(True)
            )
            .all()
        )

    raise ValueError(f'Unsupported delete scope: {scope}')

def _delete_target_apps(target_apps, dry_run=False, verbose=False, detail_limit=200, include_skip_details=True, count_skips=True):
    results = _new_delete_results()
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    target_apps = [app for app in (target_apps or []) if app is not None]
    if not target_apps:
        add_detail('No owned content matched the requested delete target.')
        return results

    target_app_ids = {int(app.id) for app in target_apps if getattr(app, 'id', None) is not None}
    processed_file_ids = set()
    candidate_filepaths = []

    for app in target_apps:
        app_label = f"{app.app_type} {app.app_id} v{app.app_version}"
        app_files_list = [file_entry for file_entry in list(app.files or []) if file_entry]
        if not app_files_list:
            if count_skips:
                results['skipped'] += 1
            if include_skip_details:
                add_detail(f"Skip {app_label}: no linked files.")
            continue

        for file_entry in app_files_list:
            file_id = getattr(file_entry, 'id', None)
            if file_id is None or file_id in processed_file_ids:
                continue
            processed_file_ids.add(file_id)

            filepath = str(getattr(file_entry, 'filepath', '') or '')
            linked_apps = [linked for linked in list(getattr(file_entry, 'apps', []) or []) if linked is not None]
            foreign_apps = [linked for linked in linked_apps if getattr(linked, 'id', None) not in target_app_ids]
            if foreign_apps:
                foreign_labels = ', '.join(
                    f"{linked.app_type} {linked.app_id} v{linked.app_version}"
                    for linked in foreign_apps
                )
                if count_skips:
                    results['skipped'] += 1
                if include_skip_details:
                    add_detail(f"Skip shared file {filepath}: linked to non-target apps {foreign_labels}.")
                continue

            candidate_filepaths.append(filepath)

    unique_filepaths = list(dict.fromkeys([path for path in candidate_filepaths if path]))
    if not unique_filepaths:
        add_detail('No deletable files matched the requested delete target.')
        return results

    for filepath in unique_filepaths:
        if dry_run:
            results['deleted'] += 1
            add_detail(f"Plan delete: {filepath}.")
            continue
        try:
            if os.path.exists(filepath):
                os.remove(filepath)
            delete_file_by_filepath(filepath)
            results['deleted'] += 1
            results['mutated'] = True
            add_detail(f"Deleted: {filepath}.")
        except Exception as e:
            logger.error(f"Failed to delete file {filepath}: {e}")
            db.session.rollback()
            results['errors'].append(str(e))
            add_detail(f"Error deleting {filepath}: {e}.")

    if results['errors']:
        results['success'] = False
    return results

def delete_library_content(scope, dry_run=False, verbose=False, detail_limit=200, title_id=None, app_id=None, app_type=None, version=None):
    try:
        target_apps = _resolve_delete_targets(
            scope=scope,
            title_id=title_id,
            app_id=app_id,
            app_type=app_type,
            version=version
        )
    except ValueError as e:
        results = _new_delete_results()
        results['success'] = False
        results['errors'].append(str(e))
        return results

    return _delete_target_apps(
        target_apps,
        dry_run=dry_run,
        verbose=verbose,
        detail_limit=detail_limit
    )

def delete_orphaned_addons(dry_run=False, verbose=False, detail_limit=200):
    base_apps = aliased(Apps)
    owned_base_title_ids = (
        db.session.query(base_apps.title_id.label('title_fk'))
        .filter(
            base_apps.app_type == APP_TYPE_BASE,
            base_apps.owned.is_(True)
        )
        .distinct()
        .subquery()
    )
    target_apps = (
        Apps.query
        .join(Titles, Apps.title_id == Titles.id)
        .filter(
            Apps.owned.is_(True),
            Apps.app_type.in_([APP_TYPE_UPD, APP_TYPE_DLC]),
            ~Apps.title_id.in_(db.session.query(owned_base_title_ids.c.title_fk))
        )
        .all()
    )
    results = _delete_target_apps(
        target_apps,
        dry_run=dry_run,
        verbose=verbose,
        detail_limit=detail_limit,
        include_skip_details=False,
        count_skips=False,
    )
    return results

def delete_older_updates(dry_run=False, verbose=False, detail_limit=200):
    results = _new_delete_results()
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    titles = Titles.query.all()
    for title in titles:
        update_apps = Apps.query.filter_by(
            title_id=title.id,
            app_type=APP_TYPE_UPD,
            owned=True
        ).all()
        if len(update_apps) <= 1:
            continue

        latest_app = max(update_apps, key=lambda app: _safe_int(app.app_version))
        for app in update_apps:
            if app.id == latest_app.id:
                continue
            remaining_detail_limit = max(0, detail_limit - detail_count)
            partial_results = _delete_target_apps(
                [app],
                dry_run=dry_run,
                verbose=verbose,
                detail_limit=remaining_detail_limit,
                include_skip_details=False,
                count_skips=False,
            )
            _merge_delete_results(results, partial_results, add_detail=add_detail)

    if results['errors']:
        results['success'] = False
    return results

def delete_duplicates(dry_run=False, verbose=False, detail_limit=200):
    results = _new_delete_results()
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    def _filename_duplicate_rank(app, file_entry):
        filename = os.path.basename(str(getattr(file_entry, 'filepath', '') or ''))
        if filename.lower().endswith('.hdf'):
            filename = filename[:-4]
        detected_app_id = str(titles_lib.get_app_id_from_filename(filename) or '').strip().upper()
        detected_version = _safe_int(titles_lib.get_version_from_filename(filename), default=-1)
        current_app_id = str(getattr(app, 'app_id', '') or '').strip().upper()
        app_id_matches = 1 if not detected_app_id or detected_app_id == current_app_id else 0
        version_rank = detected_version if detected_version >= 0 else _safe_int(getattr(app, 'app_version', 0))
        return app_id_matches, version_rank

    def file_rank(app, file_entry):
        app_id_matches, version_rank = _filename_duplicate_rank(app, file_entry)
        ext = str(file_entry.extension or '').strip().lower()
        ext_priority = {
            'nsz': 5,
            'xcz': 4,
            'nsp': 3,
            'xci': 2,
        }.get(ext, 1)
        mtime = 0
        try:
            if file_entry.filepath and os.path.exists(file_entry.filepath):
                mtime = int(os.path.getmtime(file_entry.filepath))
        except Exception:
            mtime = 0
        return (app_id_matches, version_rank, ext_priority, mtime, _safe_int(file_entry.size), _safe_int(file_entry.id))

    apps = Apps.query.filter(Apps.owned.is_(True)).all()
    for app in apps:
        app_files_list = [f for f in list(app.files or []) if f and f.filepath]
        if len(app_files_list) <= 1:
            continue

        ordered = sorted(app_files_list, key=lambda file_entry: file_rank(app, file_entry), reverse=True)
        keeper = ordered[0]
        duplicates = ordered[1:]
        add_detail(
            f"Keep {app.app_id} v{app.app_version}: {keeper.filepath} "
            f"(ext={keeper.extension or ''}, size={_safe_int(keeper.size)})."
        )
        for dup in duplicates:
            dup_filepath = str(getattr(dup, 'filepath', '') or '')
            dup_ext = str(getattr(dup, 'extension', '') or '')
            dup_size = _safe_int(getattr(dup, 'size', 0))
            try:
                linked_apps_count = len(list(dup.apps or []))
            except Exception:
                linked_apps_count = 0
            if linked_apps_count > 1:
                continue

            if dry_run:
                results['deleted'] += 1
                add_detail(
                    f"Plan delete duplicate {app.app_id} v{app.app_version}: "
                    f"{dup_filepath} (ext={dup_ext}, size={dup_size})."
                )
                continue

            try:
                if dup_filepath and os.path.exists(dup_filepath):
                    os.remove(dup_filepath)
                if dup_filepath:
                    delete_file_by_filepath(dup_filepath)
                results['deleted'] += 1
                results['mutated'] = True
                add_detail(
                    f"Deleted duplicate {app.app_id} v{app.app_version}: "
                    f"{dup_filepath} (ext={dup_ext}, size={dup_size})."
                )
            except Exception as e:
                logger.error(f"Failed to delete duplicate file {dup_filepath}: {e}")
                results['errors'].append(str(e))
                add_detail(f"Error deleting duplicate {dup_filepath}: {e}.")

    if results['errors']:
        results['success'] = False
    return results

def convert_to_nsz(command_template, delete_original=True, dry_run=False, verbose=False, detail_limit=200, log_cb=None, progress_cb=None, stream_output=False, threads=None, library_id=None, cancel_cb=None, timeout_seconds=None, min_size_bytes=None, verify=True):
    # Clear any previous failed transaction state before starting a new conversion run.
    db.session.rollback()
    results = {
        'success': True,
        'converted': 0,
        'skipped': 0,
        'mutated': False,
        'errors': [],
        'details': []
    }
    detail_count = 0

    def add_detail(message):
        nonlocal detail_count
        if (verbose or dry_run) and detail_count < detail_limit:
            results['details'].append(message)
            detail_count += 1

    keys_ok, keys_error = _ensure_nsz_keys()
    if not keys_ok:
        results['success'] = False
        results['errors'].append(keys_error)
        add_detail(keys_error)
        return results

    if '{nsz_runner}' in (command_template or '') and not _get_nsz_runner():
        warning = 'NSZ tool not found. Install the nsz Python package from requirements and run via python -m nsz.'
        add_detail(warning)
        if log_cb:
            log_cb(warning)
    conversion_staging_dir = _get_conversion_staging_dir()
    staging_ok, staging_error = _ensure_conversion_staging_dir(conversion_staging_dir)
    if not staging_ok:
        results['success'] = False
        results['errors'].append(staging_error)
        add_detail(staging_error)
        return results
    if conversion_staging_dir and log_cb:
        log_cb(f"Using conversion staging directory: {conversion_staging_dir}")

    query = Files.query.filter(Files.extension.in_(['nsp', 'xci']))
    if library_id:
        query = query.filter_by(library_id=library_id)
    files = [file_entry for file_entry in query.all() if not _is_hardlinked_file(file_entry.filepath)]
    total_files = len(files)
    processed = 0
    if progress_cb:
        progress_cb(0, total_files)
    if log_cb:
        log_cb(f"Found {total_files} file(s) to convert.")
    for file_entry in files:
        if cancel_cb and cancel_cb():
            if log_cb:
                log_cb('Conversion cancelled.')
            break
        source_path = str(file_entry.filepath or '')
        source_file_id = file_entry.id
        source_library_id = file_entry.library_id
        source_multicontent = file_entry.multicontent
        source_nb_content = file_entry.nb_content
        source_size = file_entry.size
        source_identification_type = file_entry.identification_type
        source_identification_attempts = file_entry.identification_attempts
        source_last_attempt = file_entry.last_attempt
        source_apps = list(file_entry.apps or [])

        if not source_path or not os.path.exists(source_path):
            results['skipped'] += 1
            add_detail('Skip missing file path.')
            if log_cb:
                log_cb('Skip missing file path.')
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        if _is_hardlinked_file(source_path):
            results['skipped'] += 1
            add_detail(f"Skip hardlinked file retained for torrent seeding: {source_path}.")
            if log_cb:
                log_cb(f"Skip hardlinked file retained for torrent seeding: {source_path}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        if min_size_bytes and source_size and source_size < min_size_bytes:
            results['skipped'] += 1
            add_detail(f"Skip small file (<{min_size_bytes} bytes): {source_path}.")
            if log_cb:
                log_cb(f"Skip small file (<{min_size_bytes} bytes): {source_path}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        final_output_file = _expected_compressed_output_path(source_path)
        existing_output = _resolve_existing_output_path(final_output_file)
        if existing_output and os.path.exists(existing_output):
            results['skipped'] += 1
            add_detail(f"Skip existing output: {existing_output}.")
            if log_cb:
                log_cb(f"Skip existing output: {existing_output}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        command_output_file = _build_staging_output_path(source_path, final_output_file, conversion_staging_dir)
        if conversion_staging_dir:
            try:
                os.makedirs(os.path.dirname(command_output_file), exist_ok=True)
                _clear_staging_output_candidates(command_output_file)
            except Exception as e:
                results['errors'].append(str(e))
                add_detail(f"Error preparing staging output for {source_path}: {e}.")
                processed += 1
                if progress_cb:
                    progress_cb(processed, total_files)
                continue

        command = _format_nsz_command(
            command_template,
            source_path,
            command_output_file,
            threads=threads,
            verify=verify
        )
        try:
            command_args = _parse_command_args(command)
        except ValueError as e:
            results['errors'].append(str(e))
            add_detail(f"Error preparing command for {source_path}: {e}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        if dry_run:
            results['converted'] += 1
            add_detail(f"Plan convert: {source_path} -> {final_output_file}.")
            if log_cb:
                log_cb(f"Plan convert: {source_path} -> {final_output_file}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
            continue

        try:
            if log_cb:
                log_cb(f"Running: {_format_command_for_log(command_args)}")
            process = _run_command(
                command_args,
                log_cb=log_cb,
                stream_output=stream_output,
                cancel_cb=cancel_cb,
                timeout_seconds=timeout_seconds
            )
            if process.returncode != 0:
                failed_output = _resolve_existing_output_path(command_output_file)
                failure_message = _summarize_conversion_failure(process.stderr, failed_output)
                results['errors'].append(failure_message)
                add_detail(f"Error converting {source_path}: {failure_message}.")
                processed += 1
                if progress_cb:
                    progress_cb(processed, total_files)
                continue
            output_file = _resolve_existing_output_path(command_output_file)
            if not output_file or not os.path.exists(output_file):
                results['errors'].append(f'Output not found: {output_file}')
                add_detail(f"Error missing output: {output_file}.")
                processed += 1
                if progress_cb:
                    progress_cb(processed, total_files)
                continue
            if conversion_staging_dir:
                try:
                    output_file = _finalize_staged_conversion_output(
                        source_path=source_path,
                        staged_output_path=output_file,
                        staging_root=conversion_staging_dir
                    )
                except Exception as e:
                    try:
                        _clear_staging_output_candidates(command_output_file)
                    except Exception:
                        pass
                    results['errors'].append(str(e))
                    add_detail(f"Error finalizing staged output for {source_path}: {e}.")
                    processed += 1
                    if progress_cb:
                        progress_cb(processed, total_files)
                    continue

            output_ext = os.path.splitext(output_file)[1].lstrip('.').lower() or 'nsz'
            if delete_original:
                old_path = source_path
                if os.path.exists(old_path):
                    os.remove(old_path)
                _replace_or_create_converted_file_row(
                    source_file_id=source_file_id,
                    source_path=source_path,
                    output_file=output_file,
                    source_library_id=source_library_id,
                    output_ext=output_ext,
                    source_multicontent=source_multicontent,
                    source_nb_content=source_nb_content,
                    source_identification_type=source_identification_type,
                    source_identification_attempts=source_identification_attempts,
                    source_last_attempt=source_last_attempt,
                    source_apps=source_apps
                )
                for app in source_apps:
                    app.owned = True
                _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
                db.session.commit()
                results['mutated'] = True
                add_detail(f"Converted and replaced: {old_path} -> {output_file}.")
            else:
                library_path = get_library_path(source_library_id)
                folder = _compute_relative_folder(library_path, output_file)
                existing_file = Files.query.filter_by(filepath=output_file).first()
                if existing_file:
                    existing_file.extension = output_ext
                    existing_file.compressed = True
                    existing_file.size = os.path.getsize(output_file)
                    for app in source_apps:
                        if existing_file not in app.files:
                            app.files.append(existing_file)
                        app.owned = True
                    _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
                    db.session.commit()
                    results['mutated'] = True
                    add_detail(f"Converted output already indexed: {output_file}.")
                else:
                    new_file = Files(
                        filepath=output_file,
                        library_id=source_library_id,
                        folder=folder,
                        filename=os.path.basename(output_file),
                        extension=output_ext,
                        size=os.path.getsize(output_file),
                        compressed=True,
                        multicontent=source_multicontent,
                        nb_content=source_nb_content,
                        identified=True,
                        identification_type=source_identification_type,
                        identification_attempts=source_identification_attempts,
                        last_attempt=source_last_attempt
                    )
                    db.session.add(new_file)
                    db.session.flush()
                    for app in source_apps:
                        app.files.append(new_file)
                        app.owned = True
                    _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
                    db.session.commit()
                    results['mutated'] = True
                    add_detail(f"Converted: {source_path} -> {output_file}.")

            results['converted'] += 1
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)
        except Exception as e:
            db.session.rollback()
            logger.error(f"Failed to convert {source_path}: {e}")
            results['errors'].append(str(e))
            add_detail(f"Error converting {source_path}: {e}.")
            processed += 1
            if progress_cb:
                progress_cb(processed, total_files)

    if results['errors']:
        results['success'] = False
    return results

def list_convertible_files(limit=2000, library_id=None, min_size_bytes=200 * 1024 * 1024):
    query = Files.query.filter(Files.extension.in_(['nsp', 'xci']))
    if library_id:
        query = query.filter_by(library_id=library_id)
    files = query.limit(limit).all()
    filtered = [
        {
            'id': file.id,
            'filename': file.filename,
            'filepath': file.filepath,
            'extension': file.extension,
            'size': file.size or 0
        }
        for file in files
        if (not min_size_bytes or not file.size or file.size >= min_size_bytes)
        and not _is_hardlinked_file(file.filepath)
    ]
    return filtered

def convert_single_to_nsz(file_id, command_template, delete_original=True, dry_run=False, verbose=False, log_cb=None, progress_cb=None, stream_output=False, threads=None, cancel_cb=None, timeout_seconds=None, verify=True):
    # Clear any previous failed transaction state before starting a new conversion run.
    db.session.rollback()
    results = {
        'success': True,
        'converted': 0,
        'skipped': 0,
        'mutated': False,
        'errors': [],
        'details': []
    }

    file_entry = Files.query.filter_by(id=file_id).first()
    if not file_entry:
        return {
            'success': False,
            'converted': 0,
            'skipped': 0,
            'errors': ['File not found.'],
            'details': []
        }

    source_path = str(file_entry.filepath or '')
    source_file_id = file_entry.id
    source_library_id = file_entry.library_id
    source_multicontent = file_entry.multicontent
    source_nb_content = file_entry.nb_content
    source_identification_type = file_entry.identification_type
    source_identification_attempts = file_entry.identification_attempts
    source_last_attempt = file_entry.last_attempt
    source_apps = list(file_entry.apps or [])

    if not source_path or not os.path.exists(source_path):
        results['success'] = False
        results['errors'].append('File path missing.')
        return results

    if _is_hardlinked_file(source_path):
        results['skipped'] = 1
        results['details'].append('Skip hardlinked file retained for torrent seeding.')
        if log_cb:
            log_cb(f"Skip hardlinked file retained for torrent seeding: {source_path}.")
        if progress_cb:
            progress_cb(1, 1)
        return results

    keys_ok, keys_error = _ensure_nsz_keys()
    if not keys_ok:
        results['success'] = False
        results['errors'].append(keys_error)
        if verbose:
            results['details'].append(keys_error)
        return results

    if '{nsz_runner}' in (command_template or '') and not _get_nsz_runner() and verbose:
        warning = 'NSZ tool not found. Install the nsz Python package from requirements and run via python -m nsz.'
        results['details'].append(warning)
        if log_cb:
            log_cb(warning)
    conversion_staging_dir = _get_conversion_staging_dir()
    staging_ok, staging_error = _ensure_conversion_staging_dir(conversion_staging_dir)
    if not staging_ok:
        results['success'] = False
        results['errors'].append(staging_error)
        if verbose:
            results['details'].append(staging_error)
        return results
    if conversion_staging_dir and log_cb:
        log_cb(f"Using conversion staging directory: {conversion_staging_dir}")

    final_output_file = _expected_compressed_output_path(source_path)
    existing_output = _resolve_existing_output_path(final_output_file)
    if existing_output and os.path.exists(existing_output):
        results['skipped'] = 1
        if verbose:
            results['details'].append(f"Skip existing output: {existing_output}.")
        return results

    command_output_file = _build_staging_output_path(source_path, final_output_file, conversion_staging_dir)
    if conversion_staging_dir:
        try:
            os.makedirs(os.path.dirname(command_output_file), exist_ok=True)
            _clear_staging_output_candidates(command_output_file)
        except Exception as e:
            results['success'] = False
            results['errors'].append(str(e))
            if verbose:
                results['details'].append(f"Error preparing staging output: {e}.")
            return results

    command = _format_nsz_command(
        command_template,
        source_path,
        command_output_file,
        threads=threads,
        verify=verify
    )
    try:
        command_args = _parse_command_args(command)
    except ValueError as e:
        results['success'] = False
        results['errors'].append(str(e))
        if verbose:
            results['details'].append(f"Error preparing command for {source_path}: {e}.")
        if progress_cb:
            progress_cb(1, 1)
        return results

    if cancel_cb and cancel_cb():
        if log_cb:
            log_cb('Conversion cancelled.')
        return results

    if dry_run:
        results['converted'] = 1
        if verbose:
            results['details'].append(f"Plan convert: {source_path} -> {final_output_file}.")
        if progress_cb:
            progress_cb(1, 1)
        return results

    try:
        if log_cb:
            log_cb(f"Running: {_format_command_for_log(command_args)}")
        process = _run_command(
            command_args,
            log_cb=log_cb,
            stream_output=stream_output,
            cancel_cb=cancel_cb,
            timeout_seconds=timeout_seconds
        )
        if process.returncode != 0:
            failed_output = _resolve_existing_output_path(command_output_file)
            failure_message = _summarize_conversion_failure(process.stderr, failed_output)
            results['success'] = False
            results['errors'].append(failure_message)
            if verbose:
                results['details'].append(f"Error converting {source_path}: {failure_message}.")
            if progress_cb:
                progress_cb(1, 1)
            return results
        output_file = _resolve_existing_output_path(command_output_file)
        if not output_file or not os.path.exists(output_file):
            results['success'] = False
            results['errors'].append(f'Output not found: {output_file}')
            if verbose:
                results['details'].append(f"Error missing output: {output_file}.")
            if progress_cb:
                progress_cb(1, 1)
            return results
        if conversion_staging_dir:
            try:
                output_file = _finalize_staged_conversion_output(
                    source_path=source_path,
                    staged_output_path=output_file,
                    staging_root=conversion_staging_dir
                )
            except Exception as e:
                try:
                    _clear_staging_output_candidates(command_output_file)
                except Exception:
                    pass
                results['success'] = False
                results['errors'].append(str(e))
                if verbose:
                    results['details'].append(f"Error finalizing staged output: {e}.")
                if progress_cb:
                    progress_cb(1, 1)
                return results

        output_ext = os.path.splitext(output_file)[1].lstrip('.').lower() or 'nsz'
        if delete_original:
            old_path = source_path
            if os.path.exists(old_path):
                os.remove(old_path)
            _replace_or_create_converted_file_row(
                source_file_id=source_file_id,
                source_path=source_path,
                output_file=output_file,
                source_library_id=source_library_id,
                output_ext=output_ext,
                source_multicontent=source_multicontent,
                source_nb_content=source_nb_content,
                source_identification_type=source_identification_type,
                source_identification_attempts=source_identification_attempts,
                source_last_attempt=source_last_attempt,
                source_apps=source_apps
            )
            for app in source_apps:
                app.owned = True
            _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
            db.session.commit()
            results['mutated'] = True
            if verbose:
                results['details'].append(f"Converted and replaced: {old_path} -> {output_file}.")
        else:
            library_path = get_library_path(source_library_id)
            folder = _compute_relative_folder(library_path, output_file)
            existing_file = Files.query.filter_by(filepath=output_file).first()
            if existing_file:
                existing_file.extension = output_ext
                existing_file.compressed = True
                existing_file.size = os.path.getsize(output_file)
                for app in source_apps:
                    if existing_file not in app.files:
                        app.files.append(existing_file)
                    app.owned = True
                _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
                db.session.commit()
                results['mutated'] = True
                if verbose:
                    results['details'].append(f"Converted output already indexed: {output_file}.")
            else:
                new_file = Files(
                    filepath=output_file,
                    library_id=source_library_id,
                    folder=folder,
                    filename=os.path.basename(output_file),
                    extension=output_ext,
                    size=os.path.getsize(output_file),
                    compressed=True,
                    multicontent=source_multicontent,
                    nb_content=source_nb_content,
                    identified=True,
                    identification_type=source_identification_type,
                    identification_attempts=source_identification_attempts,
                    last_attempt=source_last_attempt
                )
                db.session.add(new_file)
                db.session.flush()
                for app in source_apps:
                    app.files.append(new_file)
                    app.owned = True
                _sync_apps_owned_flags(app_ids=[app.id for app in source_apps if app and app.id is not None])
                db.session.commit()
                results['mutated'] = True
            if verbose:
                results['details'].append(f"Converted: {source_path} -> {output_file}.")

        results['converted'] = 1
        if progress_cb:
            progress_cb(1, 1)
    except Exception as e:
        db.session.rollback()
        logger.error(f"Failed to convert {source_path}: {e}")
        results['success'] = False
        results['errors'].append(str(e))
        if verbose:
            results['details'].append(f"Error converting {source_path}: {e}.")
        if progress_cb:
            progress_cb(1, 1)

    return results
