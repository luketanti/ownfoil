from app.constants import *
from app.utils import *
import threading
import time, os
from watchdog.observers import Observer
from watchdog.observers.polling import PollingObserver
from watchdog.events import FileSystemEventHandler
from types import SimpleNamespace
import logging

# Retrieve main logger
logger = logging.getLogger('main')


class Watcher:
    def __init__(self, callback):
        self.directories = set()  # Use a set to store directories
        self.callback = callback
        self.event_handler = Handler(self.callback)
        use_polling = str(os.environ.get('WATCHDOG_POLLING', '')).strip().lower() in ('1', 'true', 'yes')
        if use_polling:
            self.observer = PollingObserver()
            logger.info('Watchdog using polling observer (WATCHDOG_POLLING enabled).')
        else:
            self.observer = Observer()
            logger.info('Watchdog using native observer.')
        self.scheduler_map = {}

    def run(self):
        self.observer.start()
        logger.debug('Successfully started observer.')

    def stop(self):
        logger.debug('Stopping observer...')
        self.observer.stop()
        self.observer.join()
        # Best effort: dispatch any deletions still buffered for the debounced
        # flush so a clean shutdown does not drop them.
        try:
            self.event_handler._flush_deleted_events()
        except Exception:
            logger.exception('Failed to flush pending deleted events on stop')
        logger.debug('Successfully stopped observer.')

    def add_directory(self, directory):
        if directory not in self.directories:
            if not os.path.exists(directory):
                logger.warning(f'Directory {directory} does not exist, not added to watchdog.')
                return False
            logger.info(f'Adding directory {directory} to watchdog.')
            task = self.observer.schedule(self.event_handler, directory, recursive=True)
            self.scheduler_map[directory] = task
            self.directories.add(directory)
            self.event_handler.add_directory(directory)
            return True
        return False
    
    def remove_directory(self, directory):
        logger.debug(f'Removing {directory} from watchdog monitoring...')
        if directory in self.directories:
            if directory in self.scheduler_map:
                self.observer.unschedule(self.scheduler_map[directory])
                del self.scheduler_map[directory]
            self.directories.remove(directory)
            self.event_handler.remove_directory(directory)
            logger.info(f'Removed {directory} from watchdog monitoring.')
            return True
        else:
            logger.info(f'{directory} not in watchdog, nothing to do.')
        return False

class Handler(FileSystemEventHandler):
    def __init__(self, callback, stability_duration=5, delete_batch_window=2):
        self._raw_callback = callback  # Callback to invoke for stable files
        self.directories = []
        self.stability_duration = stability_duration  # Stability duration in seconds
        self._tracked_files_lock = threading.Lock()
        self.tracked_files = {}  # Tracks files being copied
        self.debounced_check_final = self._debounce(self._check_file_stability, stability_duration)
        # Deleted events are coalesced into one callback per burst so a mass
        # deletion does not dispatch (and hit the database) one file at a time.
        # The window is shorter than stability_duration, so a delete followed
        # by a re-create of the same path is normally processed in order; the
        # flush is trailing-only, so a sustained delete stream can postpone it
        # past a re-create's stabilization — the periodic scan reconciles that
        # rare case, as it already does for events lost while not running.
        self.pending_deleted_events = []
        self._pending_deleted_lock = threading.Lock()
        self.debounced_flush_deleted = self._debounce(self._flush_deleted_events, delete_batch_window)

    def add_directory(self, directory):
        if directory not in self.directories:
            self.directories.append(directory)
    
    def remove_directory(self, directory):
        if directory in self.directories:
            self.directories.remove(directory)

    def _debounce(self, func, wait):
        """Debounce decorator for the stability check."""
        @debounce(wait)
        def debounced():
            func()
        return debounced

    def _track_file(self, event):
        """Start or update tracking for a file."""
        if event.type == 'moved':
            file_path = event.dest_path
        else:
            file_path = event.src_path
        with self._tracked_files_lock:
            if event.type == 'moved':
                self.tracked_files.pop(event.src_path, None)
            current_size = self._file_size(file_path)
            if current_size is None:
                self.tracked_files.pop(file_path, None)
                return
            event.size = current_size
            event.timestamp = time.time()
            self.tracked_files[file_path] = event

    def _file_size(self, file_path):
        try:
            return os.path.getsize(file_path)
        except FileNotFoundError:
            logger.debug('Ignoring stale watcher path: %s', file_path)
        except OSError:
            logger.warning('Unable to stat watcher path: %s', file_path, exc_info=True)
        return None

    def _flush_deleted_events(self):
        """Dispatch every buffered deleted event as a single batch."""
        with self._pending_deleted_lock:
            batch = self.pending_deleted_events
            self.pending_deleted_events = []
        if batch:
            self._raw_callback(batch)

    def _check_file_stability(self):
        """Check for stable files and invoke the callback."""
        now = time.time()
        stable_files = []

        # Event dispatch and the debounced timer can run concurrently.
        with self._tracked_files_lock:
            for file_path, file_data in list(self.tracked_files.items()):
                current_size = self._file_size(file_path)
                if current_size is None:
                    self.tracked_files.pop(file_path, None)
                    continue
                if current_size != file_data.size:
                    file_data.size = current_size
                    file_data.timestamp = now
                elif (now - file_data.timestamp) >= self.stability_duration:
                    stable_files.append(file_data)
                    self.tracked_files.pop(file_path, None)
            pending = bool(self.tracked_files)

        # A final write may arrive before the file has stabilized. Keep checking
        # even if no further filesystem events arrive.
        if pending:
            self.debounced_check_final()
        if stable_files:
            self._raw_callback(stable_files)

    def collect_event(self, source_event, directory):
        """Track file events and trigger the stability check."""
        if source_event.event_type not in ('created', 'modified', 'moved', 'deleted'):
            return
        if source_event.is_directory:
            return

        if not (
            is_supported_content_path(source_event.src_path)
            or is_supported_content_path(source_event.dest_path)
        ):
            return

        library_event = SimpleNamespace(
            type=source_event.event_type,
            directory=directory,
            src_path=source_event.src_path,
            dest_path=source_event.dest_path,
        )

        if library_event.type == 'moved' and not is_supported_content_path(library_event.dest_path):
            library_event.type = 'deleted'

        if library_event.type == 'deleted':
            with self._pending_deleted_lock:
                self.pending_deleted_events.append(library_event)
            self.debounced_flush_deleted()

        else:
            # Track file on create or modify
            self._track_file(library_event)
            self.debounced_check_final()

        self._check_file_stability()

    def on_any_event(self, event):
        for directory in self.directories:
            if event.src_path.startswith(directory):
                try:
                    self.collect_event(event, directory)
                except Exception:
                    logger.exception('Failed to process library filesystem event: %s', event)
                break
