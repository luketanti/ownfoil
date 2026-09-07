import ast
import logging
import threading
import time
import unittest
from contextlib import nullcontext
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock


def load_function(name, namespace):
    # Isolate orchestration from application startup and external services.
    source = Path(__file__).resolve().parents[1] / 'app/app.py'
    tree = ast.parse(source.read_text(encoding='utf-8'))
    function = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name)
    function.decorator_list = []
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(source), 'exec'), namespace)
    return namespace[name]


class LibraryScanRecoveryTests(unittest.TestCase):
    def test_rebuild_status_clears_even_when_cleanup_fails(self):
        for failing_cleanup in ('release', 'memory'):
            with self.subTest(cleanup=failing_cleanup):
                status = {'in_progress': False}
                release = Mock(side_effect=RuntimeError('release failed') if failing_cleanup == 'release' else None)
                memory = Mock(side_effect=RuntimeError('memory failed') if failing_cleanup == 'memory' else None)
                namespace = dict(
                    _is_conversion_running=lambda: False,
                    library_rebuild_lock=threading.Lock(), library_rebuild_status=status,
                    time=time, app=SimpleNamespace(app_context=nullcontext),
                    invalidate_library_cache_state_token=Mock(side_effect=RuntimeError('processing failed')),
                    titles=SimpleNamespace(release_titledb=release), _release_process_memory=memory,
                )
                run = load_function('_run_post_library_change', namespace)
                with self.assertRaises(RuntimeError):
                    run()
                self.assertFalse(status['in_progress'])
                release.assert_called_once()
                memory.assert_called_once()

    def test_failed_scan_returns_serializable_error_and_can_retry(self):
        scan = Mock(side_effect=[FileNotFoundError('fixture moved'), None])
        namespace = dict(
            request=SimpleNamespace(json={}), _is_conversion_running=lambda: False,
            scan_in_progress=False, scan_lock=threading.Lock(), scan_library=scan,
            post_library_change=Mock(), jsonify=lambda value: value,
            logger=logging.getLogger('scan-test'),
        )
        run = load_function('scan_library_api', namespace)
        with self.assertLogs('scan-test', level='ERROR'):
            response = run()
        self.assertFalse(response['success'])
        self.assertEqual(response['errors'], ['fixture moved'])
        self.assertFalse(namespace['scan_in_progress'])
        self.assertTrue(run()['success'])
        self.assertFalse(namespace['scan_in_progress'])
