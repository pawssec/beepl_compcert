"""Observe real TC ingress filtering in two disposable network namespaces."""
import hashlib
import json
import os
import platform
import shutil
import signal
import subprocess
import sys
import uuid
from datetime import datetime, timezone

from run import HERE, BUILD, prebuilt_program


def command(args, allowed=(0,)):
    result = subprocess.run(args, text=True, capture_output=True, timeout=20)
    if result.returncode not in allowed:
        raise RuntimeError(f'{args!r}: exit {result.returncode}: {result.stderr.strip()}')
    return result


def main():
    suffix = uuid.uuid4().hex[:10]
    sender, receiver = f'beepl_tc_s_{suffix}', f'beepl_tc_r_{suffix}'
    created = []
    report = {'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'kernel': platform.release(), 'programs': [], 'passed': False,
              'namespaces': [sender, receiver], 'cleanup_errors': []}
    def interrupted(*unused):
        raise KeyboardInterrupt()
    signal.signal(signal.SIGTERM, interrupted)
    try:
        if os.geteuid() != 0:
            raise RuntimeError('Run sudo make -C evaluation/examples tc-live')
        for tool in ('ip', 'tc', 'ping'):
            if not shutil.which(tool):
                raise RuntimeError(f'Required tool not installed: {tool}')
        compiler = BUILD / 'compiler/ccomp'
        objects = {}
        for name in ('tc_pass', 'tc_drop', 'tc_ipv4'):
            source = HERE / 'examples' / (name + '.bpl')
            objects[name] = prebuilt_program(compiler, source, BUILD / 'objects')
        for ns in (sender, receiver):
            command(['ip', 'netns', 'add', ns])
            created.append(ns)
            command(['ip', '-n', ns, 'link', 'set', 'dev', 'lo', 'up'])
        command(['ip', '-n', sender, 'link', 'add', 'name', 'tx', 'type', 'veth', 'peer', 'name', 'rx'])
        command(['ip', '-n', sender, 'link', 'set', 'dev', 'rx', 'netns', receiver])
        for ns, dev, address, mac in (
                (sender, 'tx', '192.0.2.1/30', '02:00:00:00:00:01'),
                (receiver, 'rx', '192.0.2.2/30', '02:00:00:00:00:02')):
            command(['ip', '-n', ns, 'link', 'set', 'dev', dev, 'address', mac])
            command(['ip', '-n', ns, 'addr', 'add', address, 'dev', dev])
            command(['ip', '-n', ns, 'link', 'set', 'dev', dev, 'up'])
        # Fixed neighbors isolate the IPv4 decision from ARP filtering.
        for ns, dev, address, mac in (
                (sender, 'tx', '192.0.2.2', '02:00:00:00:00:02'),
                (receiver, 'rx', '192.0.2.1', '02:00:00:00:00:01')):
            command(['ip', '-n', ns, 'neigh', 'add', address, 'lladdr', mac,
                     'nud', 'permanent', 'dev', dev])
        tc = ['ip', 'netns', 'exec', receiver, 'tc']
        command(tc + ['qdisc', 'add', 'dev', 'rx', 'clsact'])
        for name, delivered in (('tc_pass', True), ('tc_drop', False), ('tc_ipv4', True)):
            source = HERE / 'examples' / (name + '.bpl')
            entry = {'program': name, 'tests': [],
                     'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                     'object_sha256': hashlib.sha256(objects[name].read_bytes()).hexdigest(),
                     'compiler_sha256': hashlib.sha256(compiler.read_bytes()).hexdigest()}
            report['programs'].append(entry)
            def check(label, expected):
                result = command(['ip', 'netns', 'exec', sender, 'ping', '-n',
                                  '-c', '1', '-W', '1', '-I', 'tx', '192.0.2.2'], allowed=(0, 1))
                received = result.returncode == 0
                passed = received == expected
                entry['tests'].append({'case': label, 'reply_received': received,
                                       'expected_reply': expected, 'passed': passed,
                                       'ping_output': result.stdout})
                print(f'{name} {label}: {"REPLY" if received else "NO REPLY"}'
                      f' — {"PASS" if passed else "FAIL"}', flush=True)
                if not passed:
                    raise AssertionError(f'{name}: unexpected delivery for {label}')
            check('before_attach_control', True)
            command(tc + ['filter', 'add', 'dev', 'rx', 'ingress', 'pref', '1',
                          'bpf', 'da', 'obj', str(objects[name]), 'sec', 'tc'])
            for i in range(3):
                check(f'filter_attached_{i + 1}', delivered)
            entry['tc_filter_stats'] = json.loads(command(
                tc + ['-s', '-j', 'filter', 'show', 'dev', 'rx', 'ingress']).stdout)
            command(tc + ['filter', 'del', 'dev', 'rx', 'ingress', 'pref', '1'])
            check('after_detach_control', True)
        report['passed'] = True
    except (OSError, RuntimeError, AssertionError, ValueError,
            subprocess.TimeoutExpired, KeyboardInterrupt) as error:
        report['error'] = str(error) or 'Interrupted'
        print(f'TC live test failed: {report["error"]}', file=sys.stderr)
    finally:
        for ns in reversed(created):
            try:
                command(['ip', 'netns', 'del', ns])
            except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
                report['cleanup_errors'].append(str(error))
                report['passed'] = False
        report['cleanup_complete'] = not report['cleanup_errors']
        destination = HERE / 'results/tc-live.json'
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2) + '\n')
        print(f'Report: {destination}')
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
