import unittest
from types import SimpleNamespace
from unittest.mock import patch

from app.file_watcher import Handler


class FileWatcherTests(unittest.TestCase):
    @patch("app.file_watcher.os.path.getsize", return_value=10)
    def test_collect_event_tracks_wrapped_supported_file(self, getsize_mock):
        callback_events = []
        handler = Handler(callback_events.extend, stability_duration=5)
        handler.debounced_check_final = lambda: None
        with patch.object(handler, "_check_file_stability") as check_mock:
            handler.collect_event(
                SimpleNamespace(
                    is_directory=False,
                    event_type="created",
                    src_path="X:\\library\\Example DLC.nsp.hdf",
                    dest_path="X:\\library\\Example DLC.nsp.hdf",
                ),
                "X:\\library",
            )

        self.assertIn("X:\\library\\Example DLC.nsp.hdf", handler.tracked_files)
        check_mock.assert_called_once()

    def test_collect_event_treats_wrapped_move_to_unsupported_path_as_delete(self):
        callback_events = []
        handler = Handler(callback_events.extend, stability_duration=5)
        handler.debounced_check_final = lambda: None
        handler.debounced_flush_deleted = lambda: None
        with patch.object(handler, "_check_file_stability") as check_mock:
            handler.collect_event(
                SimpleNamespace(
                    is_directory=False,
                    event_type="moved",
                    src_path="X:\\library\\Example DLC.nsp.hdf",
                    dest_path="X:\\library\\Example DLC.txt",
                ),
                "X:\\library",
            )

        # Deleted events are buffered until the debounced flush fires.
        self.assertEqual(len(callback_events), 0)
        self.assertEqual(len(handler.pending_deleted_events), 1)
        self.assertEqual(handler.pending_deleted_events[0].type, "deleted")
        handler._flush_deleted_events()
        self.assertEqual(len(callback_events), 1)
        self.assertEqual(callback_events[0].type, "deleted")
        check_mock.assert_called_once()

    def test_deleted_events_coalesce_into_one_batch(self):
        batches = []
        handler = Handler(batches.append, stability_duration=5)
        handler.debounced_check_final = lambda: None
        handler.debounced_flush_deleted = lambda: None
        with patch.object(handler, "_check_file_stability"):
            for name in ("A.nsp", "B.nsp"):
                handler.collect_event(
                    SimpleNamespace(
                        is_directory=False,
                        event_type="deleted",
                        src_path=f"X:\\library\\{name}",
                        dest_path="",
                    ),
                    "X:\\library",
                )

        self.assertEqual(batches, [])
        handler._flush_deleted_events()
        self.assertEqual(len(batches), 1)
        self.assertEqual(
            [event.src_path for event in batches[0]],
            ["X:\\library\\A.nsp", "X:\\library\\B.nsp"],
        )
        # An empty buffer must not dispatch another callback.
        handler._flush_deleted_events()
        self.assertEqual(len(batches), 1)


class FileWatcherRecoveryTests(unittest.TestCase):
    def setUp(self):
        self.batches = []
        self.handler = Handler(self.batches.append, stability_duration=5)
        self.handler.debounced_check_final = lambda: None

    def event(self, kind='created', path='X:/fixture-root/Example.nsp'):
        return SimpleNamespace(event_type=kind, type=kind, src_path=path,
                               dest_path='X:/fixture-root/Organized.nsp', is_directory=False)

    def test_missing_queued_path_does_not_block_next_file(self):
        with patch('app.file_watcher.os.path.getsize', side_effect=FileNotFoundError):
            self.handler.collect_event(self.event(), 'X:/fixture-root')
        self.assertEqual(self.handler.tracked_files, {})
        with patch('app.file_watcher.os.path.getsize', return_value=10):
            self.handler.collect_event(self.event(), 'X:/fixture-root')
            with patch('app.file_watcher.time.time', return_value=10**12):
                self.handler._check_file_stability()
        self.assertEqual(len(self.batches), 1)

    def test_disappearing_file_during_stability_check_is_removed(self):
        with patch('app.file_watcher.os.path.getsize', return_value=10):
            self.handler._track_file(self.event())
        with patch('app.file_watcher.os.path.getsize', side_effect=FileNotFoundError):
            self.handler._check_file_stability()
        self.assertEqual(self.handler.tracked_files, {})
        self.assertEqual(self.batches, [])

    def test_move_discards_old_path_and_tracks_destination(self):
        with patch('app.file_watcher.os.path.getsize', return_value=10):
            self.handler._track_file(self.event())
            self.handler._track_file(self.event('moved'))
        self.assertEqual(list(self.handler.tracked_files), ['X:/fixture-root/Organized.nsp'])

    def test_read_events_do_not_restart_tracking(self):
        with patch('app.file_watcher.os.path.getsize') as stat:
            for kind in ('opened', 'closed', 'closed_no_write'):
                self.handler.collect_event(self.event(kind), 'X:/fixture-root')
        stat.assert_not_called()

    def test_growth_reschedules_and_eventually_completes_without_new_event(self):
        with patch('app.file_watcher.os.path.getsize', return_value=10), patch('app.file_watcher.time.time', return_value=0):
            self.handler._track_file(self.event())
        with patch.object(self.handler, 'debounced_check_final') as retry:
            with patch('app.file_watcher.os.path.getsize', return_value=20), patch('app.file_watcher.time.time', return_value=6):
                self.handler._check_file_stability()
            retry.assert_called_once()
        self.assertEqual(self.batches, [])
        with patch('app.file_watcher.os.path.getsize', return_value=20), patch('app.file_watcher.time.time', return_value=12):
            self.handler._check_file_stability()
        self.assertEqual(len(self.batches), 1)
        self.assertEqual(self.handler.tracked_files, {})

    def test_unexpected_handler_failure_does_not_escape_dispatch(self):
        self.handler.add_directory('X:/fixture-root')
        with patch.object(self.handler, 'collect_event', side_effect=[RuntimeError('fixture failure'), None]) as collect:
            with self.assertLogs('main', level='ERROR'):
                self.handler.on_any_event(self.event())
            self.handler.on_any_event(self.event())
        self.assertEqual(collect.call_count, 2)
