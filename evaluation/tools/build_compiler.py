#!/usr/bin/env python3
"""Build an isolated ebpf64 compiler from this working tree (GNU make >= 4.3)."""
import argparse
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
BUILD = ROOT / 'evaluation' / '.build'
DEST = BUILD / 'compiler'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-j', '--jobs', type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('jobs must be positive')
    DEST.mkdir(parents=True, exist_ok=True)
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    # Include the new source module before it is added to the git index.
    names.append('bparser/beepl_maps.ml')
    for name in names:
        if not name or name.startswith('evaluation/'):
            continue
        src, dst = ROOT / name, DEST / name
        if not src.is_file():
            continue
        if not dst.exists() or src.read_bytes() != dst.read_bytes():
            dst.parent.mkdir(parents=True, exist_ok=True)
            # A source may change while an earlier build is running. Preserve
            # contents, not its older mtime, so make invalidates stale objects.
            shutil.copy(src, dst)
    commands = []
    if not (DEST / 'Makefile.config').exists():
        commands.append(['./configure', 'ebpf64'])
    else:
        config = (DEST / 'Makefile.config').read_text().splitlines()
        if 'ARCH=ebpf' not in config or 'BITSIZE=64' not in config:
            raise SystemExit('Isolated compiler has the wrong target; use a fresh .build directory.')
    commands += [['make', 'depend'], ['make', f'-j{args.jobs}']]
    with (BUILD / 'build.log').open('w') as log:
        for cmd in commands:
            print(' '.join(cmd), flush=True)
            result = subprocess.run(cmd, cwd=DEST, stdout=log, stderr=subprocess.STDOUT)
            log.flush()
            if result.returncode:
                print('\n'.join((BUILD / 'build.log').read_text().splitlines()[-30:]))
                raise SystemExit(result.returncode)
    print(f'Built {DEST / "ccomp"}')


if __name__ == '__main__':
    main()
