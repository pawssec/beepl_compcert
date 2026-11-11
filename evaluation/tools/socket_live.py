"""Observe BeePL socket filters on real loopback UDP delivery (requires BPF privileges)."""
import hashlib
import json
import platform
import socket
import sys
from datetime import datetime, timezone

from kernel import Program
from run import HERE, BUILD, prebuilt_program

SO_ATTACH_BPF = 50
SO_DETACH_BPF = 27


def exchange(sender, receiver, payload):
    sender.sendto(payload, receiver.getsockname())
    try:
        data, _ = receiver.recvfrom(4096)
    except socket.timeout:
        return False
    if data != payload:
        raise AssertionError(f'Unexpected payload: {data!r}')
    return True


def main():
    compiler = BUILD / 'compiler/ccomp'
    report = {'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'kernel': platform.release(), 'programs': [], 'passed': False}
    try:
        for name, expect_delivery in [('socket_accept', True), ('socket_drop', False)]:
            source = HERE / 'examples' / (name + '.bpl')
            obj = prebuilt_program(compiler, source, BUILD / 'objects')
            entry = {'program': name, 'tests': [], 'object_sha256':
                     hashlib.sha256(obj.read_bytes()).hexdigest(),
                     'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                     'compiler_sha256': hashlib.sha256(compiler.read_bytes()).hexdigest()}
            report['programs'].append(entry)
            with Program(obj, name) as program, \
                    socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as receiver, \
                    socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sender:
                receiver.bind(('127.0.0.1', 0))
                receiver.settimeout(1.0)
                def check(label, expected):
                    delivered = exchange(sender, receiver, f'{name}:{label}'.encode())
                    passed = delivered == expected
                    entry['tests'].append({'case': label, 'delivered': delivered,
                                           'expected_delivery': expected, 'passed': passed})
                    print(f'{name} {label}: {"RECEIVED" if delivered else "NO DELIVERY (timeout)"}'
                          f' — {"PASS" if passed else "FAIL"}', flush=True)
                    if not passed:
                        raise AssertionError(f'{name}: {label} delivery mismatch')
                check('before_attach_control', True)
                receiver.setsockopt(socket.SOL_SOCKET, SO_ATTACH_BPF, program.fd)
                for i in range(3):
                    check(f'filter_attached_{i + 1}', expect_delivery)
                receiver.setsockopt(socket.SOL_SOCKET, SO_DETACH_BPF, 0)
                check('after_detach_control', True)
        report['passed'] = True
    except (OSError, RuntimeError, AssertionError) as error:
        report['error'] = str(error)
        print(f'Live socket test failed: {error}', file=sys.stderr)
    finally:
        destination = HERE / 'results/socket-live.json'
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2) + '\n')
        print(f'Report: {destination}')
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
