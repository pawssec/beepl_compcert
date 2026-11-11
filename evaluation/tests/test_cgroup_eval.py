"""Check cgroup test assertions and attachment cleanup without privileges."""
from contextlib import contextmanager, redirect_stdout
import errno
import io
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import Mock
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
from cgroup_eval import CGROUP_PROGRAMS, run_cases
from kernel import Program


class Policy:
    def __init__(self, name):
        self.name = name
        self.attached = False

    @contextmanager
    def cgroup(self, fd):
        self.attached = True
        try:
            yield
        finally:
            self.attached = False

    def attempt(self, path, kind, family):
        denied = self.attached and path is not None and (
            self.name == 'cgroup_sock_deny' or (self.name == 'cgroup_sock_udp' and kind == 2) or
            (self.name == 'cgroup_sock_ipv4' and family == 10))
        return {'created': not denied, 'errno': errno.EPERM if denied else 0}


class CgroupTests(unittest.TestCase):
    def test_policies_and_controls(self):
        for name in CGROUP_PROGRAMS:
            policy = Policy(name)
            results = []
            with redirect_stdout(io.StringIO()):
                run_cases(policy, name, results, tempfile.TemporaryDirectory, policy.attempt)
            self.assertEqual(len(results), 20)
            self.assertTrue(all(r['passed'] for r in results))
            self.assertFalse(policy.attached)

    def test_wrong_denial_errno_fails_and_detaches(self):
        policy = Policy('cgroup_sock_deny')
        def attempt(path, kind, family):
            result = policy.attempt(path, kind, family)
            if result['errno']:
                result['errno'] = errno.EAFNOSUPPORT
            return result
        with redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
            run_cases(policy, policy.name, [], tempfile.TemporaryDirectory, attempt)
        self.assertFalse(policy.attached)

    def test_ipv6_unavailable_fails_control(self):
        policy = Policy('cgroup_sock_allow')
        def attempt(path, kind, family):
            if family == 10:
                return {'created': False, 'errno': errno.EAFNOSUPPORT}
            return policy.attempt(path, kind, family)
        results = []
        with redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
            run_cases(policy, policy.name, results, tempfile.TemporaryDirectory, attempt)
        self.assertEqual(results[-1]['case'], 'before_ipv6_tcp')
        self.assertFalse(results[-1]['passed'])
        self.assertFalse(policy.attached)

    def test_link_destroyed_when_child_fails(self):
        program = Program.__new__(Program)
        program.program = 42
        program.lib = Mock()
        program.lib.bpf_program__attach_cgroup.return_value = 77
        program.lib.libbpf_get_error.return_value = 0
        program.lib.bpf_link__destroy.return_value = 0
        with self.assertRaisesRegex(RuntimeError, 'child failed'):
            with program.cgroup(9):
                raise RuntimeError('child failed')
        program.lib.bpf_link__destroy.assert_called_once_with(77)

    def test_attach_failure_not_treated_as_success(self):
        program = Program.__new__(Program)
        program.program = 42
        program.lib = Mock()
        program.lib.bpf_program__attach_cgroup.return_value = None
        program.lib.libbpf_get_error.return_value = -errno.EPERM
        with self.assertRaises(OSError):
            with program.cgroup(9):
                self.fail('Attachment must fail')
        program.lib.bpf_link__destroy.assert_not_called()
