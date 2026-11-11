"""Socket-create enforcement in a disposable cgroup v2, using child processes."""
from contextlib import contextmanager
import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from kernel import Program

CGROUP_PROGRAMS = {'cgroup_sock_allow', 'cgroup_sock_deny', 'cgroup_sock_udp', 'cgroup_sock_ipv4'}
CGROUP_SECTION = 'cgroup/sock_create'

# Only this subprocess moves. Imports happen before joining the test cgroup.
CHILD = '''
import json, os, pathlib, socket, sys
path, kind, family = sys.argv[1:]
if path != '-':
    pathlib.Path(path, 'cgroup.procs').write_text(str(os.getpid()))
try:
    with socket.socket(int(family), int(kind)):
        result = {'created': True, 'errno': 0}
except OSError as error:
    result = {'created': False, 'errno': error.errno}
print(json.dumps(result))
'''


def validate_object(path, name):
    with Program(path, name, load=False) as program:
        actual = {'type': program.lib.bpf_program__type(program.program),
                  'attach_type': program.lib.bpf_program__expected_attach_type(program.program)}
        if actual != {'type': 9, 'attach_type': 2}:
            raise AssertionError(f'Incorrect cgroup socket metadata: {actual}')
        return actual


@contextmanager
def temporary_cgroup():
    root = Path('/sys/fs/cgroup')
    if not (root / 'cgroup.controllers').is_file():
        raise RuntimeError('Socket-create tests require cgroup v2 at /sys/fs/cgroup')
    path = Path(tempfile.mkdtemp(prefix='beepl-eval-', dir=root))
    try:
        yield path
    finally:
        # Children are reaped before returning from socket_attempt. Never move
        # other tasks or recursively delete a cgroup that we did not create.
        path.rmdir()


def socket_attempt(path, kind, family):
    try:
        result = subprocess.run([sys.executable, '-c', CHILD, str(path) if path else '-', str(kind), str(family)],
                                capture_output=True, text=True, timeout=10)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError('Socket test child timed out and was reaped') from error
    if result.returncode:
        raise RuntimeError(f'Socket test child failed: {result.stderr.strip()}')
    return json.loads(result.stdout)


def run_cases(program, name, results, group_factory=temporary_cgroup, attempt=socket_attempt):
    if name not in CGROUP_PROGRAMS:
        raise ValueError(name)
    with group_factory() as group:
        fd = os.open(group, os.O_RDONLY | os.O_DIRECTORY)
        try:
            def check(label, kind, family, allowed, inside=True):
                actual = attempt(group if inside else None, kind, family)
                expected = {'created': allowed, 'errno': 0 if allowed else errno.EPERM}
                passed = actual == expected
                results.append({'case': label, 'socket_type': kind, 'family': family, 'inside_cgroup': inside,
                                'actual': actual, 'expected': expected, 'passed': passed})
                print(f'{name} {label}: {actual}; {"PASS" if passed else "FAIL"}', flush=True)
                if not passed:
                    raise AssertionError(f'{name} {label}: expected {expected}, got {actual}')
            cases = [('ipv4_tcp', 1, 2), ('ipv4_udp', 2, 2),
                     ('ipv6_tcp', 1, 10), ('ipv6_udp', 2, 10)]
            for label, kind, family in cases:
                check('before_' + label, kind, family, True)
            with program.cgroup(fd):
                for repeat in range(2):
                    for label, kind, family in cases:
                        allowed = (name == 'cgroup_sock_allow' or
                                   (name == 'cgroup_sock_udp' and kind == 1) or
                                   (name == 'cgroup_sock_ipv4' and family == 2))
                        check(f'attached_{label}_{repeat}', kind, family, allowed)
                for label, kind, family in cases:
                    check('outside_' + label, kind, family, True, inside=False)
            for label, kind, family in cases:
                check('after_' + label, kind, family, True)
        finally:
            os.close(fd)
