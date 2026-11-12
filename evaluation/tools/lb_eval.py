"""Packet-level assertions for the TC direct-server-return UDP load balancer."""
import socket
import struct
from kernel import Program

LB_NAME = 'tc_udp_lb'
VIP = '192.0.2.100'
PORT = 9000
MACS = [bytes.fromhex('020000000011020000000010'), bytes.fromhex('020000000021020000000020')]


def validate_object(path, name=LB_NAME):
    with Program(path, name, load=False) as program:
        info = program.map_info()
        expected = dict(type=2, key_size=4, value_size=8, max_entries=9)
        if any(info[k] != v for k,v in expected.items()):
            raise AssertionError(f'Invalid load balancer map: {info}')
        return expected


def configure(program, ifindices=(1, 1), macs=MACS):
    program.map_update(0, 3)  # disabled while initializing the backend tuples
    for backend, (index, header) in enumerate(zip(ifindices, macs)):
        base = 1 + backend * 4
        program.map_update(base, index)
        for word in range(3):
            program.map_update(base + word + 1, int.from_bytes(header[word*4:word*4+4], 'little'))
    program.map_update(0, 0)


def frame(sport=40000, dport=PORT, dst=VIP, fragment=0, options=b'', protocol=17):
    from run import ipv4_frame, checksum
    data = bytearray(ipv4_frame(protocol=protocol, dport=dport, fragment=fragment, ip_options=options))
    data[30:34] = socket.inet_aton(dst)
    size = (data[14] & 15) * 4
    data[24:26] = b'\0\0'
    data[24:26] = struct.pack('!H', checksum(data[14:14+size]))
    if protocol == 17:
        data[14+size:16+size] = struct.pack('!H',sport)
    return bytes(data)


def packet_cases():
    # Parity uses the low bit of the first source-port byte (network order).
    a, b = frame(40000), frame(40256)
    def altered(offset, value):
        p=bytearray(a); p[offset:offset+len(value)]=value; return bytes(p)
    oversize = bytearray(a)
    oversize[16:18] = struct.pack('!H',100)
    oversize[38:40] = struct.pack('!H',80)
    cases = [('hash_backend_a', a, 0, 7, 0), ('hash_backend_b', b, 0, 7, 1),
             ('stable_a_repeat', a, 0, 7, 0), ('force_b', a, 2, 7, 1),
             ('force_a', b, 1, 7, 0), ('disabled', a, 3, 2, None),
             ('invalid_mode', a, 99, 2, None), ('other_vip', frame(dst='192.0.2.101'),0,0,None),
             ('other_port', frame(dport=9001),0,0,None), ('tcp',frame(protocol=6),0,0,None),
             ('fragment',frame(fragment=0x2000),0,2,None), ('fragment_offset',frame(fragment=1),0,2,None),
             ('ip_options',frame(options=bytes(4)),0,2,None),
             ('udp_length_short',altered(38,b'\0\x07'),0,2,None),
             ('udp_ip_length_mismatch',altered(38,b'\0\x09'),0,2,None),
             ('ip_length_exceeds_packet',bytes(oversize),0,2,None)]
    # skb test-run rejects ETH_P_IP frames below Ethernet+IPv4 (34 bytes)
    # before invoking BPF. Use experimental EtherType 0x88b5 below that floor
    # to exercise helper bounds failures, which precede protocol selection.
    for n in range(14,42):
        short = bytearray(a[:n])
        kind = 'ipv4'
        if n < 34:
            short[12:14] = bytes.fromhex('88b5')
            kind = 'l2'
        cases.append((f'truncated_{kind}_{n}',bytes(short),0,2,None))
    return cases


def run_cases(program, results):
    configure(program)
    for name,data,mode,expected,backend in packet_cases():
        program.map_update(0,mode)
        try:
            actual, output, ns = program.run(data)
        except OSError as error:
            raise RuntimeError(f'{name}: kernel test invocation failed: {error}') from error
        target = data if backend is None else MACS[backend]+data[12:]
        passed = actual == expected and output == target
        results.append(dict(case=name,actual=actual,expected=[expected],packet_matches=output==target,
                            backend=backend,duration_ns=ns,passed=passed))
        print(f'{LB_NAME} {name}: action={actual}, packet_matches={output==target}; {"PASS" if passed else "FAIL"}',flush=True)
        if not passed: raise AssertionError(f'{name}: expected action {expected} and exact Ethernet rewrite')
