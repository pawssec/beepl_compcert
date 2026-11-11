#!/usr/bin/env python3
"""Compile BeePL evaluation cases; optionally execute them in the Linux kernel."""
import argparse
import hashlib
import json
import pathlib
import platform
import struct
import subprocess
import sys
from datetime import datetime, timezone
from cgroup_eval import (CGROUP_PROGRAMS, CGROUP_SECTION, validate_object as validate_cgroup,
                         run_cases as run_cgroup_cases)
from vlan_eval import VLAN_NAMES, cases as vlan_cases
from map_eval import MAP_TYPES, validate_object, run_cases as run_map_cases
from trace_eval import (TRACE_PROGRAMS, TRACE_SECTION, validate_object as validate_trace,
                        run_cases as run_trace_cases)

HERE = pathlib.Path(__file__).resolve().parents[1]
ROOT = HERE.parent
BUILD = HERE / '.build'


def program_kind(name):
    if name in CGROUP_PROGRAMS:
        return CGROUP_SECTION
    if name in TRACE_PROGRAMS:
        return TRACE_SECTION
    return 'tc' if name.startswith('tc_') else ('socket' if name.startswith('socket_') else 'xdp')


def case_mark(program, case):
    return int(case.removeprefix('mark_')) if program == 'tc_mark' else 0


def skb_context(mark):
    # UAPI __sk_buff prefix; all fields except the supplied mark are zero.
    # bpf_ctx_init zero-extends the remaining context fields.
    return struct.pack('<5I', 0, 0, mark, 0, 0)


def packet(ethertype=0x0800, dport=80, protocol=17, ihl=0x45, frag=0):
    ethernet = bytes.fromhex('020000000001020000000002') + struct.pack('!H', ethertype)
    ip = struct.pack('!BBHHHBBH4s4s', ihl, 0, 28, 1, frag, 64, protocol, 0,
                     bytes([192, 0, 2, 1]), bytes([198, 51, 100, 2]))
    udp = struct.pack('!HHHH', 12345, dport, 8, 0)
    return ethernet + ip + udp + bytes(18)


def checksum(data):
    """Internet checksum used to build realistic IPv4/TCP test frames."""
    if len(data) % 2:
        data += b'\0'
    value = sum(struct.unpack('!' + 'H' * (len(data) // 2), data))
    while value >> 16:
        value = (value & 0xffff) + (value >> 16)
    return (~value) & 0xffff


def ipv4_frame(protocol=17, dport=53, ttl=64, fragment=0, flags=2,
               ip_options=b'', tcp_options=b'', pad=True):
    """Ethernet/IPv4/UDP or TCP; options must occupy whole 32-bit words."""
    if len(ip_options) % 4 or len(tcp_options) % 4:
        raise ValueError('Options must occupy whole 32-bit words')
    src, dst = bytes([192, 0, 2, 1]), bytes([198, 51, 100, 2])
    if protocol == 6:
        words = 5 + len(tcp_options) // 4
        transport = struct.pack('!HHIIBBHHH', 12345, dport, 1, 0, words << 4,
                                flags, 4096, 0, 0) + tcp_options
        pseudo = src + dst + struct.pack('!BBH', 0, protocol, len(transport))
        transport = transport[:16] + struct.pack('!H', checksum(pseudo + transport)) + transport[18:]
    else:
        transport = struct.pack('!HHHH', 12345, dport, 8, 0)
    ihl = 5 + len(ip_options) // 4
    ip = struct.pack('!BBHHHBBH4s4s', 0x40 | ihl, 0, ihl * 4 + len(transport),
                     1, fragment, ttl, protocol, 0, src, dst) + ip_options
    ip = ip[:10] + struct.pack('!H', checksum(ip)) + ip[12:]
    frame = bytes.fromhex('0200000000010200000000020800') + ip + transport
    return frame.ljust(60, b'\0') if pad else frame


def cases():
    normal = packet()
    udp = ipv4_frame()
    tcp = ipv4_frame(protocol=6)
    # Linux XDP test-run requires >=14 bytes. Exercise every shorter length
    # from that floor to the complete schema, without asking the kernel for
    # an invalid test input. Even malformed frames must be safely rejected.
    def truncated(frame, size):
        return [(f'truncated_{n}_bytes', frame[:n], [1]) for n in range(14, size)]
    ipv4_cases = [('ipv4', udp, [2]), ('ipv6_ethertype', packet(0x86dd), [1]),
                 ('arp_ethertype', packet(0x0806), [1])]
    return {
        **vlan_cases(),
        'tc_pass': [('ipv4', normal, [0]), ('ipv6', packet(0x86dd), [0])],
        'tc_drop': [('ipv4', normal, [2]), ('ipv6', packet(0x86dd), [2])],
        'tc_ipv4': [('ipv4', normal, [0]), ('ipv6', packet(0x86dd), [2]),
                    ('arp', packet(0x0806), [2])],
        'tc_length': [(f'frame_{n}', (normal + bytes(100))[:n], [0 if n <= 80 else 2])
                      for n in (34, 60, 79, 80, 81, 128)],
        'tc_mark': [(f'mark_{n}', normal, [0 if n == 42 else 2])
                    for n in (0, 41, 42, 43, 0xffffffff)],
        'tc_host': [('unicast', normal, [0]),
                    ('broadcast', bytes([255]) * 6 + normal[6:], [0]),
                    ('multicast', bytes.fromhex('01005e000001') + normal[6:], [0])],
        'tc_type_error': [('unicast', normal, [0]),
                          ('broadcast', bytes([255]) * 6 + normal[6:], [0])],
        'socket_accept': [('ipv4', normal, [0xffffffff]),
                          ('ipv6', packet(0x86dd), [0xffffffff])],
        'socket_drop': [('ipv4', normal, [0]), ('ipv6', packet(0x86dd), [0])],
        'socket_ipv4': [('ipv4', normal, [0xffffffff]),
                        ('ipv6', packet(0x86dd), [0]), ('arp', packet(0x0806), [0])],
        'socket_length': [(f'frame_{n}', (normal + bytes(100))[:n],
                           [0xffffffff if n - 14 >= 32 else 0])
                          for n in (34, 45, 46, 60, 128)],
        'xdp_eth_ipv4': ipv4_cases + [('ethernet_exact', udp[:14], [2])],
        'xdp_ipv4_ttl': ipv4_cases + [
            ('ttl_zero', ipv4_frame(ttl=0), [1]),
            ('ttl_one', ipv4_frame(ttl=1), [1]),
            ('ttl_two', ipv4_frame(ttl=2), [2]),
            ('ttl_255', ipv4_frame(ttl=255), [2]),
            ('ip_options', ipv4_frame(ip_options=bytes(4)), [1]),
            ('ipv4_header_exact', udp[:34], [2]),
        ] + truncated(udp, 34),
        'xdp_ipv4_fragments': ipv4_cases + [
            ('dont_fragment', ipv4_frame(fragment=0x4000), [2]),
            ('more_fragments', ipv4_frame(fragment=0x2000), [1]),
            ('offset_one', ipv4_frame(fragment=1), [1]),
            ('offset_maximum', ipv4_frame(fragment=0x1fff), [1]),
            ('ip_options', ipv4_frame(ip_options=bytes(4)), [1]),
            ('ipv4_header_exact', udp[:34], [2]),
        ] + truncated(udp, 34),
        'xdp_udp_dns': [
            ('dns_port_53', udp, [2]), ('port_52', ipv4_frame(dport=52), [1]),
            ('port_54', ipv4_frame(dport=54), [1]),
            ('port_byte_swapped', ipv4_frame(dport=0x3500), [1]),
            ('tcp_port_53', ipv4_frame(protocol=6), [1]),
            ('fragment', ipv4_frame(fragment=1), [1]),
            ('ip_options', ipv4_frame(ip_options=bytes(4)), [1]),
            ('ipv6_ethertype', packet(0x86dd), [1]),
            ('udp_header_exact', ipv4_frame(pad=False), [2]),
        ] + truncated(udp, 42),
        'xdp_tcp_syn': [
            ('syn', tcp, [2]), ('syn_ack', ipv4_frame(protocol=6, flags=18), [1]),
            ('ack', ipv4_frame(protocol=6, flags=16), [1]),
            ('no_flags', ipv4_frame(protocol=6, flags=0), [1]),
            ('syn_ecn', ipv4_frame(protocol=6, flags=0xc2), [2]),
            ('udp', udp, [1]), ('ipv6_ethertype', packet(0x86dd), [1]),
            ('fragment', ipv4_frame(protocol=6, fragment=0x2000), [1]),
            ('ip_options', ipv4_frame(protocol=6, ip_options=bytes(4)), [1]),
            ('tcp_options', ipv4_frame(protocol=6, tcp_options=bytes(4)), [1]),
            ('tcp_header_exact', ipv4_frame(protocol=6, pad=False), [2]),
        ] + truncated(tcp, 54),
        'xdp_pass': [('ipv4', normal, [2]), ('ipv6', packet(0x86dd), [2])],
        'xdp_drop': [('ipv4', normal, [1]), ('ipv6', packet(0x86dd), [1])],
        'xdp_queue': [('default_queue', normal, [2])],
        'xdp_arithmetic': [('zero_divisor_default_queue', normal, [2])],
        'xdp_loop': [('four_iterations', normal, [2])],
        'xdp_loop_limits': [('unsigned_endpoints', normal, [2])],
        'xdp_loop_empty': [('reversed_bounds', normal, [2])],
        'xdp_array': [('array_initialization_and_reads', normal, [2])],
        'xdp_cast': [('narrowing_cast', normal, [2])],
        'xdp_shift': [('out_of_range_shift', normal, [2])],
        'xdp_signed_div': [('signed_division', normal, [2])],
        'xdp_modulo': [('zero_modulus', normal, [2])],
        'xdp_boolean': [('boolean_negation', normal, [2])],
        'xdp_option_some': [('nonnull_match_and_dereference', normal, [2])],
        'xdp_option_none': [('null_match', normal, [2])],
        'xdp_clock': [('monotonic_time_nonzero', normal, [2])],
        'xdp_random': [(f'random_{i}', normal, [1, 2]) for i in range(16)],
        'ipv6_guard': [('ipv4', normal, [2]), ('ipv6', packet(0x86dd), [1]),
                       ('arp', packet(0x0806), [2]),
                       ('ethernet_boundary', normal[:14], [2])],
        'udp_port_filter': [
            ('allowed_udp', normal, [2]), ('blocked_udp', packet(dport=9999), [1]),
            ('tcp_same_port', packet(dport=9999, protocol=6), [2]),
            ('ipv6', packet(0x86dd), [2]), ('arp', packet(0x0806), [2]),
            ('short_ipv4', normal[:14], [1]), ('header_one_byte_short', normal[:41], [1]),
            ('header_exact', normal[:42], [2]), ('options', packet(ihl=0x46), [1]),
            ('fragment_offset', packet(frag=1), [1]),
            ('more_fragments', packet(frag=0x2000), [1]),
            ('dont_fragment', packet(frag=0x4000), [2]),
        ],
    }


def compile_program(compiler, source, out):
    obj = out / (source.stem + '.o')
    command = [str(compiler), '-typecheck', '-bpfmap', '-c', '-o', str(obj), str(source)]
    result = subprocess.run(command, capture_output=True, text=True, cwd=ROOT)
    log = result.stdout + result.stderr
    (out / (source.stem + '.compile.log')).write_text(log)
    if result.returncode:
        raise RuntimeError(log.strip())
    data = obj.read_bytes()
    # ELF64 little-endian EM_BPF (247), not a native object or exported Rocq AST.
    if data[:6] != b'\x7fELF\x02\x01' or struct.unpack_from('<H', data, 18)[0] != 247:
        raise RuntimeError('Compiler did not produce a little-endian ELF64 eBPF object')
    relocations = subprocess.check_output(['llvm-readelf', '-r', str(obj)], text=True)
    if 'bpf_' in relocations:
        raise RuntimeError('Object still contains unresolved eBPF helper relocations:\n' + relocations)
    assembly = subprocess.check_output(['llvm-objdump', '-d', str(obj)], text=True)
    (out / (source.stem + '.disasm')).write_text(assembly)
    manifest = {key: hashlib.sha256(path.read_bytes()).hexdigest() for key, path in
                [('source_sha256', source), ('compiler_sha256', compiler), ('object_sha256', obj)]}
    (out / (source.stem + '.manifest.json')).write_text(json.dumps(manifest, indent=2) + '\n')
    return obj


def prebuilt_program(compiler, source, out):
    obj = out / (source.stem + '.o')
    manifest_path = out / (source.stem + '.manifest.json')
    if not manifest_path.is_file() or not obj.is_file():
        raise RuntimeError('No validated build artifacts; run make -C evaluation/examples check first')
    manifest = json.loads(manifest_path.read_text())
    for key, path in [('source_sha256', source), ('compiler_sha256', compiler), ('object_sha256', obj)]:
        if manifest.get(key) != hashlib.sha256(path.read_bytes()).hexdigest():
            raise RuntimeError(f'Stale {key}; run make -C evaluation/examples check before loading')
    return obj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', action='store_true', help='load and test programs; needs BPF privileges')
    parser.add_argument('--emulate', action='store_true', help='run limited userspace instruction smoke tests (not kernel tests)')
    parser.add_argument('--program', help='test just this entry-point/file stem')
    parser.add_argument('--vlan-only', action='store_true', help='test on-wire VLAN and QinQ parsers')
    parser.add_argument('--packet-parsing', action='store_true', help='test the five fixed-layout packet parsing examples')
    parser.add_argument('--cgroup-only', action='store_true', help='test socket-create cgroup policies')
    parser.add_argument('--socket-only', action='store_true', help='test socket filters only')
    parser.add_argument('--tc-only', action='store_true', help='test TC classifiers only')
    parser.add_argument('--maps-only', action='store_true', help='test typed maps and kernel state readback')
    parser.add_argument('--trace-only', action='store_true', help='attach tracing programs and assert real syscall events')
    parser.add_argument('--examples-only', action='store_true', help='exclude applications')
    parser.add_argument('--prebuilt', action='store_true', help='load saved objects after checking their source/compiler/object hashes; do not compile')
    parser.add_argument('--compiler', type=pathlib.Path, default=BUILD / 'compiler/ccomp')
    parser.add_argument('--report', type=pathlib.Path, default=HERE / 'results/latest.json')
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    if not compiler.is_file():
        parser.error('Build the eBPF compiler first: python3 evaluation/tools/build_compiler.py')
    out = BUILD / 'objects'
    out.mkdir(parents=True, exist_ok=True)
    results = []
    sources = sorted((HERE / 'examples').glob('*.bpl')) + sorted((HERE / 'applications').glob('*.bpl'))
    if args.examples_only:
        sources = [p for p in sources if p.parent.name == 'examples']
    if args.cgroup_only:
        sources = [p for p in sources if p.stem in CGROUP_PROGRAMS]
    if args.socket_only:
        sources = [p for p in sources if p.stem.startswith('socket_')]
    if args.tc_only:
        sources = [p for p in sources if p.stem.startswith('tc_')]
    if args.maps_only:
        sources = [p for p in sources if p.stem in MAP_TYPES]
    if args.trace_only:
        sources = [p for p in sources if p.stem in TRACE_PROGRAMS]
    if args.program:
        sources = [p for p in sources if p.stem == args.program]
    if args.vlan_only:
        sources = [p for p in sources if p.stem in VLAN_NAMES]
    if args.packet_parsing:
        sources = [p for p in sources if p.stem in {
            'xdp_eth_ipv4', 'xdp_ipv4_ttl', 'xdp_ipv4_fragments',
            'xdp_udp_dns', 'xdp_tcp_syn'}]
    if not sources:
        parser.error('No matching programs')
    for source in sources:
        program_type = program_kind(source.stem)
        entry = {'program': source.stem, 'source': str(source.relative_to(ROOT)),
                 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                 'compile': 'failed', 'kernel': 'not_requested', 'emulation': 'not_requested',
                 'tests': [], 'emulated_tests': []}
        entry['program_type'] = program_type
        try:
            obj = (prebuilt_program if args.prebuilt else compile_program)(compiler, source, out)
            entry['compile'] = 'passed'
            entry['object_sha256'] = hashlib.sha256(obj.read_bytes()).hexdigest()
            if source.stem in MAP_TYPES:
                entry['map_metadata'] = validate_object(obj, source.stem)
                if args.emulate:
                    entry['emulation'] = 'not_supported'
            if source.stem in TRACE_PROGRAMS:
                entry['map_metadata'] = validate_trace(obj, source.stem)
                if args.emulate:
                    entry['emulation'] = 'not_supported'
            if source.stem in CGROUP_PROGRAMS:
                entry['attach_metadata'] = validate_cgroup(obj, source.stem)
                if args.emulate:
                    entry['emulation'] = 'not_supported'
            if args.emulate and source.stem not in MAP_TYPES and source.stem not in TRACE_PROGRAMS and source.stem not in CGROUP_PROGRAMS:
                from emulate import execute, xdp_section
                entry['emulation'] = 'failed'
                code = xdp_section(obj, program_type)
                for i, (name, data, expected) in enumerate(cases()[source.stem]):
                    actual = execute(code, data, random_value=i, program_type=program_type,
                                     mark=case_mark(source.stem, name))
                    entry['emulated_tests'].append({'case': name, 'expected': expected,
                                                    'actual': actual, 'passed': actual in expected})
                    if actual not in expected:
                        raise AssertionError(f'Emulation {name}: expected {expected}, got {actual}')
                entry['emulation'] = 'passed'
            if args.kernel:
                from kernel import Program
                entry['kernel'] = 'failed'
                with Program(obj, source.stem) as program:
                    if source.stem in CGROUP_PROGRAMS:
                        entry['execution_mode'] = 'live_cgroup_socket_create'
                        run_cgroup_cases(program, source.stem, entry['tests'])
                    if source.stem in MAP_TYPES:
                        run_map_cases(program, source.stem, packet(), entry['tests'])
                    if source.stem in TRACE_PROGRAMS:
                        entry['execution_mode'] = 'live_raw_tracepoint'
                        run_trace_cases(program, source.stem, entry['tests'])
                    for name, data, expected in cases().get(source.stem, []):
                        context = skb_context(case_mark(source.stem, name)) if source.stem == 'tc_mark' else None
                        actual, output, ns = program.run(data, context=context)
                        # skb test-run restores a zeroed Ethernet header in its
                        # output; socket-filter byte counts are not XDP actions.
                        preserved = (output == data if program_type in ('xdp', 'tc')
                                     else output == bytes(14) + data[14:])
                        passed = actual in expected and preserved
                        entry['tests'].append({'case': name, 'expected': expected,
                                               'actual': actual, 'passed': passed,
                                               'packet_preserved': preserved, 'duration_ns': ns})
                        if not passed:
                            raise AssertionError(f'{name}: expected {expected}, got {actual}; '
                                                 f'expected packet output: {preserved}')
                entry['kernel'] = 'passed'
        except (RuntimeError, OSError, AssertionError) as error:
            if (isinstance(error, OSError) and error.errno in (1, 13)
                    and entry['kernel'] == 'failed' and not entry['tests']):
                entry['kernel'] = 'blocked'
            entry['error'] = str(error)
            print(f'FAIL {source.stem}: {error}', file=sys.stderr)
        print(f'{source.stem}: compile={entry["compile"]}, emulation={entry["emulation"]}, kernel={entry["kernel"]}', flush=True)
        results.append(entry)
    rejections = []
    # Privileged loading consumes the recorded artifacts and does no build work.
    manifest = {} if args.prebuilt else json.loads((HERE / 'tests/rejections.json').read_text())
    for name, diagnostic in manifest.items():
        source = HERE / 'tests/reject' / (name + '.bpl')
        result = subprocess.run([str(compiler), '-S', '-o', str(out / (name + '.s')), str(source)],
                                capture_output=True, text=True, cwd=ROOT)
        log = result.stdout + result.stderr
        passed = result.returncode != 0 and diagnostic in log
        (out / (name + '.reject.log')).write_text(log)
        rejections.append({'case': name, 'passed': passed, 'diagnostic': log.strip()})
        print(f'{name}: rejection={"passed" if passed else "FAILED"}')
    report = {'timestamp_utc': datetime.now(timezone.utc).isoformat(), 'kernel': platform.release(),
              'compiler': str(compiler), 'compiler_sha256': hashlib.sha256(compiler.read_bytes()).hexdigest(),
              'kernel_requested': args.kernel, 'programs': results, 'rejections': rejections}
    report['prebuilt'] = args.prebuilt
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Report: {args.report}')
    failed = any(x['compile'] != 'passed' or (args.kernel and x['kernel'] != 'passed') for x in results)
    failed |= any(not x['passed'] for x in rejections)
    failed |= args.emulate and any(x['emulation'] != 'passed' and
                                  not ((x['program'] in MAP_TYPES or x['program'] in TRACE_PROGRAMS) and x.get('map_metadata')
                                       and x['emulation'] == 'not_supported') and
                                  not (x['program'] in CGROUP_PROGRAMS and x.get('attach_metadata')
                                       and x['emulation'] == 'not_supported') for x in results)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
