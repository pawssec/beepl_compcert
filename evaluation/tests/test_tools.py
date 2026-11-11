"""Tests for the smoke interpreter's failure modes and packet fixtures."""
import pathlib
import struct
import sys
import unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
from emulate import execute
from run import packet, ipv4_frame, checksum
from vlan_eval import vlan_frame


def insn(op, dst=0, src=0, off=0, imm=0):
    return struct.pack('<BBhi', op, dst | src << 4, off, imm)


class SmokeInterpreterTests(unittest.TestCase):
    def test_alu32_zero_extension(self):
        code = insn(0xb4, imm=-1) + insn(0x77, imm=32) + insn(0x95)
        self.assertEqual(execute(code, packet()), 0)

    def test_signed_jump(self):
        code = (insn(0xb4, imm=-1) + insn(0xc6, off=1, imm=0)
                + insn(0xb4, imm=10) + insn(0x95))
        self.assertEqual(execute(code, packet()), 0xffffffff)

    def test_uninitialized_register(self):
        with self.assertRaisesRegex(RuntimeError, 'Uninitialized register'):
            execute(insn(0x95), packet())

    def test_uninitialized_stack(self):
        with self.assertRaisesRegex(RuntimeError, 'memory read'):
            execute(insn(0x79, src=10, off=-8) + insn(0x95), packet())

    def test_stack_roundtrip(self):
        code = (insn(0xb7, imm=123) + insn(0x7b, dst=10, off=-8)
                + insn(0x79, src=10, off=-8) + insn(0x95))
        self.assertEqual(execute(code, packet()), 123)

    def test_helper_clobbers_arguments(self):
        code = insn(0x85, imm=5) + insn(0xbf, src=1) + insn(0x95)
        with self.assertRaisesRegex(RuntimeError, 'Uninitialized register r1'):
            execute(code, packet())

    def test_unknown_opcode(self):
        with self.assertRaisesRegex(RuntimeError, 'Unsupported opcode'):
            execute(insn(0x00), packet())

    def test_out_of_bounds_stack_write(self):
        with self.assertRaisesRegex(RuntimeError, 'stores only to stack'):
            execute(insn(0x7a, dst=10, off=0) + insn(0x95), packet())

    def test_packet_field_offsets(self):
        data = packet(dport=9999, frag=0x2000)
        self.assertEqual(len(data), 60)
        self.assertEqual(data[12:14], b'\x08\x00')
        self.assertEqual(data[20:22], b'\x20\x00')
        self.assertEqual(data[23], 17)
        self.assertEqual(data[36:38], struct.pack('!H', 9999))

    def test_vlan_wire_layout(self):
        frame = vlan_frame(((0x8100, 0xf064),))
        self.assertEqual(frame[12:18], bytes.fromhex('8100f0640800'))
        self.assertEqual(frame[18] >> 4, 4)
        self.assertEqual(checksum(frame[18:38]), 0)

    def test_qinq_wire_layout(self):
        frame = vlan_frame(((0x88a8, 200), (0x8100, 100)))
        self.assertEqual(frame[12:22], bytes.fromhex('88a800c8810000640800'))
        self.assertEqual(frame[22] >> 4, 4)
        self.assertEqual(checksum(frame[22:42]), 0)

    def test_ipv4_fixture_checksum_and_length(self):
        for options in (b'', bytes(4)):
            data = ipv4_frame(ip_options=options, pad=False)
            size = (data[14] & 15) * 4
            self.assertEqual(size, 20 + len(options))
            self.assertEqual(checksum(data[14:14 + size]), 0)
            self.assertEqual(int.from_bytes(data[16:18], 'big'), len(data) - 14)
            self.assertEqual(data[14 + size + 2:14 + size + 4], b'\x00\x35')

    def test_tcp_fixture_checksum_and_flags(self):
        for options in (b'', bytes(4)):
            data = ipv4_frame(protocol=6, tcp_options=options, flags=0x12, pad=False)
            tcp = data[34:]
            pseudo = data[26:34] + struct.pack('!BBH', 0, 6, len(tcp))
            self.assertEqual(checksum(pseudo + tcp), 0)
            self.assertEqual((tcp[12] >> 4) * 4, 20 + len(options))
            self.assertEqual(tcp[13], 0x12)

    def test_socket_context_length_excludes_ethernet(self):
        code = insn(0x61, src=1) + insn(0x95)
        self.assertEqual(execute(code, packet(), program_type='socket'), 46)

    def test_socket_context_protocol_offset(self):
        code = insn(0x61, src=1, off=16) + insn(0x95)
        self.assertEqual(execute(code, packet(), program_type='socket'), 8)
        self.assertEqual(execute(code, packet(0x86dd), program_type='socket'), 0xdd86)

    def test_tc_context_includes_ethernet_and_mark(self):
        code = insn(0x61, src=1) + insn(0x95)
        self.assertEqual(execute(code, packet(), program_type='tc'), 60)
        code = insn(0x61, src=1, off=8) + insn(0x95)
        self.assertEqual(execute(code, packet(), program_type='tc', mark=42), 42)

    def test_tc_helper_updates_packet_type(self):
        code = (insn(0xbf, dst=6, src=1) + insn(0xb7, dst=2, imm=0)
                + insn(0x85, imm=32) + insn(0x61, src=6, off=4) + insn(0x95))
        self.assertEqual(execute(code, packet(), program_type='tc'), 0)

    def test_tc_helper_invalid_type_errno_and_no_mutation(self):
        code = (insn(0xbf, dst=6, src=1) + insn(0xb7, dst=2, imm=7)
                + insn(0x85, imm=32))
        self.assertEqual(execute(code + insn(0x95), packet(), program_type='tc'),
                         0xffffffea)
        self.assertEqual(execute(code + insn(0x61, src=6, off=4) + insn(0x95),
                                 packet(), program_type='tc'), 3)


if __name__ == '__main__':
    unittest.main()
