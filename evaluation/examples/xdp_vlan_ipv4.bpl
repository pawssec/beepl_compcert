(* RUN GUIDE: xdp_vlan_ipv4
Pass frames with one 802.1Q tag with VID 100 and inner IPv4 EtherType.
All other frames drop. PCP/DEI bits are ignored; VLAN IDs must match exactly.
This is an Ethernet/tag classifier: IPv4 contents, lengths and checksums are
not validated. Even an exact 18-byte matching header passes by design.
The compiler generates bounds checks for Pbytes; BeePL uses no pointer arithmetic.
Only on-wire tags are read. Hardware-stripped VLAN metadata is not supported.
Verifier and kernel execution results await your privileged run.

Run from the repository root with the existing compiler, LLVM, libbpf and
bpftool dependencies. Build without sudo:
1. make -C evaluation/examples build EXAMPLE=xdp_vlan_ipv4
   make -C evaluation/examples test EXAMPLE=xdp_vlan_ipv4
   llvm-objdump -d evaluation/.build/objects/xdp_vlan_ipv4.o
   Saved artifacts: evaluation/.build/objects/xdp_vlan_ipv4.s, .o, .bin, .disasm
   Userspace emulation is not kernel verification. Load .o, not raw .bin.
2. Verify and execute all packet fixtures in the kernel, then unload:
   sudo make -C evaluation/examples kernel-test EXAMPLE=xdp_vlan_ipv4
   Report: evaluation/results/xdp_vlan_ipv4-kernel.json
   Or test both VLAN programs:
   sudo make -C evaluation/examples kernel-vlan-check
   Report: evaluation/results/kernel-vlan.json
   Tests cover tag types/IDs, PCP/DEI, extra/missing tags, inner EtherTypes,
   exact bounds and every truncated length from Ethernet's 14-byte minimum.
   Expected return values: 2=XDP_PASS, 1=XDP_DROP. Packet bytes must be unchanged.
   This uses BPF_PROG_TEST_RUN; it does not attach to an interface.
3. Optional manual verifier load and inspection:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=xdp_vlan_ipv4
   sudo make -C evaluation/examples inspect EXAMPLE=xdp_vlan_ipv4
   sudo make -C evaluation/examples jited EXAMPLE=xdp_vlan_ipv4
   sudo make -C evaluation/examples run EXAMPLE=xdp_vlan_ipv4
   The default untagged IPv4 fixture returns 1 (DROP). Use kernel-vlan-check
   for tagged PASS cases. Stop on load errors.
4. Optional live attachment, only on a test interface carrying on-wire tags:
   sudo make -C evaluation/examples attach EXAMPLE=xdp_vlan_ipv4 IFACE=TEST_IFACE
   sudo bpftool net show dev TEST_IFACE
   Generate tagged traffic from a peer. NIC tag stripping can affect visibility;
   automated test-run fixtures do not exercise NIC offload behavior.
   sudo make -C evaluation/examples detach EXAMPLE=xdp_vlan_ipv4 IFACE=TEST_IFACE
5. Remove the optional pin (detach first if attached):
   sudo make -C evaluation/examples unload EXAMPLE=xdp_vlan_ipv4
The automated kernel test owns and closes its separate program FD on errors too.
*)
struct _xdp_md_bee {
  _data_bee : bytes, _data_meta : uint32, _ingress_ifindex : uint32,
  _rx_queue_index : uint32, _egress_ifindex : uint32
}
struct packet_header {
  dst0 : uint16, dst1 : uint16, dst2 : uint16,
  src0 : uint16, src1 : uint16, src2 : uint16,
  tag_type : uint16, tag_hi : uint8, tag_lo : uint8, inner_type : uint16
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section xdp
fun xdp_vlan_ipv4 (ostruct _xdp_md_bee* ctx) : int32, [] {
  match ctx with
  | some packet -> (
      match packet._data_bee with
      | Pbytes header : struct packet_header [ tag_type : uint16, tag_hi : uint8, tag_lo : uint8, inner_type : uint16 ] ->
          if ((tag_type) == (uint16)129) then (if ((tag_hi & (uint8)15) == (uint8)0) then (if ((tag_lo) == (uint8)100) then (if ((inner_type) == (uint16)8) then (2) else 1) else 1) else 1) else 1
      | Pbytes rest : bytes [] -> 1
    )
  | none -> 1
}
