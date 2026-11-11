"""On-wire VLAN fixtures; no hardware VLAN stripping is modeled."""
import struct

VLAN_NAMES = {'xdp_vlan_ipv4', 'xdp_qinq_ipv4'}


def vlan_frame(tags=((0x8100, 100),), inner=0x0800):
    # Valid IPv4/UDP payload comes from the existing checksummed fixture.
    from run import ipv4_frame
    base = ipv4_frame(pad=False)
    header = base[:12] + b''.join(struct.pack('!HH', tpid, tci) for tpid, tci in tags)
    return (header + struct.pack('!H', inner) + base[14:]).ljust(60, b'\0')


def cases():
    single = vlan_frame()
    double = vlan_frame(((0x88a8, 200), (0x8100, 100)))
    result = {}
    for name, frame, size in [('xdp_vlan_ipv4', single, 18), ('xdp_qinq_ipv4', double, 22)]:
        tags = [(0x8100, 100)] if size == 18 else [(0x88a8, 200), (0x8100, 100)]
        rows = [('matching_tags', frame, [2]), ('header_exact', frame[:size], [2]),
                ('untagged', vlan_frame(()), [1]),
                ('inner_ipv6', vlan_frame(tags, 0x86dd), [1]),
                ('inner_arp', vlan_frame(tags, 0x0806), [1]),
                ('extra_tag', vlan_frame(tags + [(0x8100, 100)]), [1])]
        for index, (tpid, vid) in enumerate(tags):
            for value in (0, vid - 1, vid + 1, 4095, 0x6400):
                altered = tags.copy(); altered[index] = (tpid, value)
                rows.append((f'tag_{index}_wrong_tci_{value}', vlan_frame(altered), [1]))
            for flags in (0x1000, 0x2000, 0xe000, 0xf000):
                altered = tags.copy(); altered[index] = (tpid, vid | flags)
                rows.append((f'tag_{index}_priority_dei_{flags}', vlan_frame(altered), [2]))
            altered = tags.copy(); altered[index] = (0x88a8 if tpid == 0x8100 else 0x8100, vid)
            rows.append((f'tag_{index}_wrong_tpid', vlan_frame(altered), [1]))
        if size == 22:
            rows.append(('single_tag', single, [1]))
        rows += [(f'truncated_{n}', frame[:n], [1]) for n in range(14, size)]
        result[name] = rows
    return result
