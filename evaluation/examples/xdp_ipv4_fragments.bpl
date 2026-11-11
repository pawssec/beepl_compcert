(* RUN GUIDE
xdp_ipv4_fragments: Drop fragmented IPv4; allow the dont-fragment flag.

Run these commands from the beepl_compcert repository root.
Prerequisites: the repository build dependencies, GNU make >= 4.3, LLVM tools,
Python 3 for the existing test harness, bpftool, and libbpf for kernel tests.
Kernel verification/execution is PENDING until your sudo run succeeds.

1. Compile this program and save all bytecode artifacts (no sudo):
   make -C evaluation/examples build EXAMPLE=xdp_ipv4_fragments
   Output files in evaluation/.build/objects/:
     xdp_ipv4_fragments.s       eBPF assembly
     xdp_ipv4_fragments.o       ELF object to load with bpftool
     xdp_ipv4_fragments.bin     raw xdp-section instruction bytes (not an ELF loader input)
     xdp_ipv4_fragments.disasm  readable instruction listing

Inspect the generated object before loading (no sudo):
   file evaluation/.build/objects/xdp_ipv4_fragments.o
   Expected: ELF 64-bit LSB relocatable, eBPF.
   llvm-objdump -d evaluation/.build/objects/xdp_ipv4_fragments.o
   Expected: an xdp section with the xdp_ipv4_fragments function and an exit instruction.
   The .disasm file saves this listing; .bin saves the raw instructions.

2. Check expected results in userspace (NOT kernel verification):
   make -C evaluation/examples test EXAMPLE=xdp_ipv4_fragments

3. Recommended kernel test: load, verify, execute all this program's packet
   cases, assert the results, and automatically release the program:
   sudo make -C evaluation/examples kernel-test EXAMPLE=xdp_ipv4_fragments
   Results: evaluation/results/xdp_ipv4_fragments-kernel.json
   A successful load establishes verifier acceptance on THIS kernel only.
   A passing kernel test additionally establishes the tested behavior.

4. Alternatively, load and run manually with bpftool:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=xdp_ipv4_fragments
   sudo make -C evaluation/examples run EXAMPLE=xdp_ipv4_fragments
   Expected JSON retval for the default IPv4 packet: 2 (XDP_PASS).
   No interface is attached: 'run' executes the supplied packet in the kernel.
   These examples do not print trace messages; check retval and the test report.

A successful load exits with status zero and creates this pin:
   ls -l /sys/fs/bpf/beepl_eval_xdp_ipv4_fragments
   On a verifier rejection, load exits nonzero and prints diagnostics.
   Do not continue to attach/run a rejected program.

5. Inspect the loaded program and its kernel-translated bytecode:
   sudo make -C evaluation/examples inspect EXAMPLE=xdp_ipv4_fragments
   Expected: program type xdp, a kernel-assigned ID, and translated instructions.
   IDs, tags, timings and JIT code vary with kernel and compiler versions.
   Optional JIT machine-code dump (requires kernel JIT support):
   sudo make -C evaluation/examples jited EXAMPLE=xdp_ipv4_fragments

6. Optional attachment to actual incoming traffic on a test interface:
   ip -brief link
   Choose an existing TEST interface from that list, then substitute its name
   for TEST_IFACE in both commands below. This is separate from test-run.
   sudo make -C evaluation/examples attach EXAMPLE=xdp_ipv4_fragments IFACE=TEST_IFACE
   sudo bpftool net show dev TEST_IFACE
   Generate incoming traffic from a peer connected to TEST_IFACE. The program
   will pass or drop packets according to the behavior described above.
   There is no printk output for this program. Use the deterministic kernel-test
   target for assertions; ping loss alone is not a conclusive test result.
   Detach the optional live attachment before deleting the pin:
   sudo make -C evaluation/examples detach EXAMPLE=xdp_ipv4_fragments IFACE=TEST_IFACE

7. Unload (after detaching if you performed step 6):
   sudo make -C evaluation/examples unload EXAMPLE=xdp_ipv4_fragments
   This removes only /sys/fs/bpf/beepl_eval_xdp_ipv4_fragments.
   If load reports an existing pin, unload that earlier instance before retrying.

New packet parsing collection: sudo make -C evaluation/examples kernel-packet-check
Report: evaluation/results/kernel-packet-parsing.json

Whole collection: make -C evaluation/examples check
Then: sudo make -C evaluation/examples kernel-check
A load rejection or failed assertion is a failure, never a passing example.
*)
(* MEMORY ACCESS: the BeePL program performs no pointer arithmetic.
   A C implementation would compute data + 34, compare it with data_end,
   cast data to a header pointer, then read fields through that pointer.
   Pbytes asks the compiler to generate those calculations and the bound check.
   This schema is exactly 34 bytes, with scalar fields in wire order.
   Multibyte constants use little-endian representations of network bytes.
   IPv4/TCP option layouts, VLAN tags, checksums and payload contents are not
   parsed by this example. The pattern does not advance a user-visible cursor.
   Run kernel-test for matching, nonmatching and truncated-header assertions.
*)
struct _xdp_md_bee {
  _data_bee : bytes, _data_meta : uint32, _ingress_ifindex : uint32,
  _rx_queue_index : uint32, _egress_ifindex : uint32
}
struct packet_header {
  dst0 : uint16, dst1 : uint16, dst2 : uint16,
  src0 : uint16, src1 : uint16, src2 : uint16, ether_type : uint16,
  ip_version_ihl : uint8, ip_tos : uint8, ip_length : uint16,
  ip_id : uint16, ip_fragment : uint16, ip_ttl : uint8, ip_protocol : uint8,
  ip_checksum : uint16, ip_src_hi : uint16, ip_src_lo : uint16,
  ip_dst_hi : uint16, ip_dst_lo : uint16
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section xdp
fun xdp_ipv4_fragments (ostruct _xdp_md_bee* ctx) : int32, [] {
  match ctx with
  | some packet -> (
      match packet._data_bee with
      | Pbytes header : struct packet_header [ ether_type : uint16, ip_version_ihl : uint8, ip_fragment : uint16 ] ->
          if (ether_type != (uint16)8) then 1 else
          if (ip_version_ihl != (uint8)69) then 1 else
          if ((ip_fragment & (uint16)65343) == (uint16)0) then 2 else 1
      | Pbytes rest : bytes [] -> 1
    )
  | none -> 1
}
