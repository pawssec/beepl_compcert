"""Raw syscall tracing: real events, PID filtering, map readback and detachment."""
import ctypes as C
import os
import platform

from kernel import Program

TRACE_PROGRAMS = {'raw_syscall_count': 3, 'syscall_histogram': 257}
TRACE_SECTION = 'raw_tracepoint/sys_enter'


def validate_object(path, name):
    with Program(path, name, load=False) as program:
        info = program.map_info()
        expected = {'type': 6, 'key_size': 4, 'value_size': 8,
                    'max_entries': TRACE_PROGRAMS[name]}
        for field, value in expected.items():
            if info[field] != value:
                raise AssertionError(f'Trace map {field}: expected {value}, got {info[field]}')
        return expected


def syscall_trigger():
    if platform.machine() != 'x86_64':
        raise RuntimeError('Tracing fixture syscall numbers currently require Linux x86_64')
    library = C.CDLL(None, use_errno=True)
    library.syscall.restype = C.c_long
    def trigger(number, count):
        for _ in range(count):
            # Calling syscall directly avoids libc/vDSO caching or substitutions.
            if library.syscall(C.c_long(number)) < 0:
                raise OSError(C.get_errno(), f'syscall {number} failed')
    return trigger


def run_cases(program, name, results, trigger=None, pid=None):
    trigger = syscall_trigger() if trigger is None else trigger
    pid = os.getpid() if pid is None else pid
    owner_key = 0 if name == 'raw_syscall_count' else 256
    keys = [2] if name == 'raw_syscall_count' else [39, 102]
    def totals():
        return {key: sum(program.map_lookup(key)) for key in keys}
    def check(label, calls, expected):
        before = totals()
        for number, count in calls:
            trigger(number, count)
        after = totals()
        delta = {key: after[key] - before[key] for key in keys}
        passed = delta == expected
        results.append({'case': label, 'before': before, 'after': after,
                        'delta': delta, 'expected_delta': expected, 'passed': passed,
                        'syscalls': [{'number': n, 'count': c} for n, c in calls],
                        'pid_filter': pid})
        print(f'{name} {label}: {before} -> {after}; '
              f'{"PASS" if passed else "FAIL"}', flush=True)
        if not passed:
            raise AssertionError(f'{name}: {label}: expected {expected}, got {delta}')
    zero = {key: 0 for key in keys}
    program.map_update(owner_key, pid)
    if name == 'raw_syscall_count':
        program.map_update(1, 39)
    check('before_attach_control', [(39, 2), (102, 2)], zero)
    with program.raw_tracepoint('sys_enter'):
        if name == 'raw_syscall_count':
            check('selected_getpid', [(39, 3)], {2: 3})
            check('unselected_getuid', [(102, 4)], {2: 0})
            program.map_update(1, 102)
            check('switch_to_getuid', [(102, 2)], {2: 2})
            check('old_target_ignored', [(39, 2)], {2: 0})
            program.map_update(owner_key, 0)
            check('wrong_pid_ignored', [(102, 3)], {2: 0})
            program.map_update(owner_key, pid)
            check('restore_pid', [(102, 1)], {2: 1})
        else:
            check('getpid_bucket', [(39, 3)], {39: 3, 102: 0})
            check('getuid_bucket', [(102, 4)], {39: 0, 102: 4})
            check('mixed_buckets', [(39, 2), (102, 1)], {39: 2, 102: 1})
            program.map_update(owner_key, 0)
            check('wrong_pid_ignored', [(39, 2), (102, 2)], zero)
            program.map_update(owner_key, pid)
            check('restore_pid', [(39, 1)], {39: 1, 102: 0})
    check('after_detach_control', [(39, 2), (102, 2)], zero)
