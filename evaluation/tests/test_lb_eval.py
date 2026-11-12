"""Independent wire-format checks for load-balancer test packets."""
import pathlib
import socket
import struct
import sys
import unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'tools'))
from lb_eval import frame, packet_cases, VIP, PORT, MACS
from run import checksum


class LoadBalancerFixtures(unittest.TestCase):
    def test_valid_wire_header(self):
        p=frame()
        self.assertEqual(p[12:14],b'\x08\x00')
        self.assertEqual(p[30:34],socket.inet_aton(VIP))
        self.assertEqual(struct.unpack('!HHHH',p[34:42]),(40000,PORT,8,0))
        self.assertEqual(checksum(p[14:34]),0)
        self.assertEqual(int.from_bytes(p[16:18],'big'),28)
        self.assertTrue(all(len(m)==12 for m in MACS))

    def test_oversize_fixture_reaches_packet_bound_check(self):
        p=next(data for name,data,*_ in packet_cases() if name=='ip_length_exceeds_packet')
        ip_length=int.from_bytes(p[16:18],'big');udp_length=int.from_bytes(p[38:40],'big')
        self.assertEqual(ip_length,udp_length+20)
        self.assertGreater(ip_length+14,len(p))

    def test_truncation_covers_each_header_boundary(self):
        sizes={len(data) for name,data,*_ in packet_cases() if name.startswith('truncated_')}
        self.assertEqual(sizes,set(range(14,42)))

    def test_short_fixtures_satisfy_skb_test_run_protocol_minimum(self):
        for name,data,*_ in packet_cases():
            if name.startswith('truncated_'):
                self.assertEqual(data[12:14], b'\x88\xb5' if len(data)<34 else b'\x08\x00')
                self.assertEqual(name.startswith('truncated_l2_'),len(data)<34)
