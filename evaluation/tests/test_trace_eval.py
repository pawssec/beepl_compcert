"""Exercise event assertions and descriptor cleanup without tracing privileges."""
from contextlib import contextmanager, redirect_stdout
import io
import pathlib
import sys
import unittest
from unittest.mock import Mock, patch
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
from trace_eval import run_cases
from kernel import Program


class Events:
    def __init__(self, name, broken=False):
        self.name, self.broken = name, broken
        self.values = {}
        self.attached = False

    def map_update(self, key, value):
        self.values[key] = value

    def map_lookup(self, key):
        return [self.values.get(key, 0)]

    @contextmanager
    def raw_tracepoint(self, name):
        assert name == 'sys_enter'
        self.attached = True
        try:
            yield
        finally:
            self.attached = False

    def trigger(self, number, count):
        owner = 0 if self.name == 'raw_syscall_count' else 256
        if not self.attached or self.broken or self.values.get(owner) != 123:
            return
        if self.name == 'raw_syscall_count':
            if number == self.values.get(1):
                self.values[2] = self.values.get(2, 0) + count
        elif number < 256:
            self.values[number] = self.values.get(number, 0) + count


class TraceTests(unittest.TestCase):
    def test_filters_configuration_and_detachment(self):
        for name, expected in [('raw_syscall_count', 8), ('syscall_histogram', 7)]:
            program = Events(name)
            results = []
            with redirect_stdout(io.StringIO()):
                run_cases(program, name, results, trigger=program.trigger, pid=123)
            self.assertEqual(len(results), expected)
            self.assertTrue(all(x['passed'] for x in results))
            self.assertFalse(program.attached)

    def test_missing_events_fail_and_detach(self):
        program = Events('raw_syscall_count', broken=True)
        with redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
            run_cases(program, program.name, [], trigger=program.trigger, pid=123)
        self.assertFalse(program.attached)

    def test_raw_attachment_fd_closed_on_error(self):
        program = Program.__new__(Program)
        program.fd, program.attachments = 5, set()
        program.lib = Mock()
        program.lib.bpf_raw_tracepoint_open.return_value = 42
        with patch('kernel.os.close') as close:
            with self.assertRaisesRegex(RuntimeError, 'event failure'):
                with program.raw_tracepoint('sys_enter'):
                    raise RuntimeError('event failure')
            close.assert_called_once_with(42)
        self.assertEqual(program.attachments, set())


if __name__ == '__main__':
    unittest.main()
