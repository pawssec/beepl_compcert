"""Observe syscall numbers 0..255 for one host TGID for a bounded duration."""
import argparse
import hashlib
import json
import os
import platform
import sys
import time
from datetime import datetime, timezone

from kernel import Program
from run import HERE, BUILD, prebuilt_program
from trace_eval import validate_object


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pid', type=int, required=True, help='host TGID to observe')
    parser.add_argument('--seconds', type=int, default=5)
    args = parser.parse_args()
    if args.pid <= 0 or not 1 <= args.seconds <= 60:
        parser.error('PID must be positive and seconds must be between 1 and 60')
    report = {'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'kernel': platform.release(), 'architecture': platform.machine(),
              'pid_filter': args.pid, 'seconds': args.seconds, 'completed': False}
    try:
        if platform.machine() != 'x86_64':
            raise RuntimeError('Current syscall histogram fixture requires Linux x86_64')
        os.kill(args.pid, 0)
        name = 'syscall_histogram'
        source = HERE / 'applications' / (name + '.bpl')
        compiler = BUILD / 'compiler/ccomp'
        obj = prebuilt_program(compiler, source, BUILD / 'objects')
        report.update({key: hashlib.sha256(path.read_bytes()).hexdigest() for key, path in
                       [('source_sha256', source), ('object_sha256', obj), ('compiler_sha256', compiler)]})
        validate_object(obj, name)
        with Program(obj, name) as program:
            program.map_update(256, args.pid)
            print(f'Observing host PID {args.pid} for {args.seconds}s (syscall numbers 0..255)...', flush=True)
            with program.raw_tracepoint('sys_enter'):
                time.sleep(args.seconds)
            # Detach before taking the final snapshot.
            counts = {str(key): sum(program.map_lookup(key)) for key in range(256)}
            report['event_counts'] = {key: count for key, count in counts.items() if count}
            report['total_observed_events'] = sum(counts.values())
            report['detached'] = True
        report['completed'] = True
        for key, count in report['event_counts'].items():
            print(f'syscall {key}: {count}')
        if not report['event_counts']:
            print('No matching events observed. This is not a failed test or proof of tracing behavior.')
    except (OSError, RuntimeError, AssertionError, KeyboardInterrupt) as error:
        report['error'] = str(error) or 'Interrupted'
        print(f'Observation failed: {report["error"]}', file=sys.stderr)
    finally:
        path = HERE / 'results/trace-observe.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(report, indent=2) + '\n')
        print(f'Report: {path}')
    return 0 if report['completed'] else 1


if __name__ == '__main__':
    sys.exit(main())
