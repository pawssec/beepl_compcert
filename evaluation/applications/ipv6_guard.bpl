(* RUN GUIDE
ipv6_guard: Parse a bounds-checked Ethernet header and drop IPv6.

Run these commands from the beepl_compcert repository root.
Prerequisites: the repository build dependencies, GNU make >= 4.3, LLVM tools,
Python 3 for the existing test harness, bpftool, and libbpf for kernel tests.
Kernel verification/execution is PENDING until your sudo run succeeds.

1. Compile this program and save all bytecode artifacts (no sudo):
   make -C evaluation/examples build EXAMPLE=ipv6_guard
   Output files in evaluation/.build/objects/:
     ipv6_guard.s       eBPF assembly
     ipv6_guard.o       ELF object to load with bpftool
     ipv6_guard.bin     raw xdp-section instruction bytes (not an ELF loader input)
     ipv6_guard.disasm  readable instruction listing

Inspect the generated object before loading (no sudo):
   file evaluation/.build/objects/ipv6_guard.o
   Expected: ELF 64-bit LSB relocatable, eBPF.
   llvm-objdump -d evaluation/.build/objects/ipv6_guard.o
   Expected: an xdp section with the ipv6_guard function and an exit instruction.
   The .disasm file saves this listing; .bin saves the raw instructions.

2. Check expected results in userspace (NOT kernel verification):
   make -C evaluation/examples test EXAMPLE=ipv6_guard

3. Recommended kernel test: load, verify, execute all this program's packet
   cases, assert the results, and automatically release the program:
   sudo make -C evaluation/examples kernel-test EXAMPLE=ipv6_guard
   Results: evaluation/results/ipv6_guard-kernel.json
   A successful load establishes verifier acceptance on THIS kernel only.
   A passing kernel test additionally establishes the tested behavior.

4. Alternatively, load and run manually with bpftool:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=ipv6_guard
   sudo make -C evaluation/examples run EXAMPLE=ipv6_guard
   Expected JSON retval for the default IPv4 packet: 2 (XDP_PASS).
   No interface is attached: 'run' executes the supplied packet in the kernel.
   These examples do not print trace messages; check retval and the test report.

A successful load exits with status zero and creates this pin:
   ls -l /sys/fs/bpf/beepl_eval_ipv6_guard
   On a verifier rejection, load exits nonzero and prints diagnostics.
   Do not continue to attach/run a rejected program.

5. Inspect the loaded program and its kernel-translated bytecode:
   sudo make -C evaluation/examples inspect EXAMPLE=ipv6_guard
   Expected: program type xdp, a kernel-assigned ID, and translated instructions.
   IDs, tags, timings and JIT code vary with kernel and compiler versions.
   Optional JIT machine-code dump (requires kernel JIT support):
   sudo make -C evaluation/examples jited EXAMPLE=ipv6_guard

6. Optional attachment to actual incoming traffic on a test interface:
   ip -brief link
   Choose an existing TEST interface from that list, then substitute its name
   for TEST_IFACE in both commands below. This is separate from test-run.
   sudo make -C evaluation/examples attach EXAMPLE=ipv6_guard IFACE=TEST_IFACE
   sudo bpftool net show dev TEST_IFACE
   Generate incoming traffic from a peer connected to TEST_IFACE. The program
   will pass or drop packets according to the behavior described above.
   There is no printk output for this program. Use the deterministic kernel-test
   target for assertions; ping loss alone is not a conclusive test result.
   Detach the optional live attachment before deleting the pin:
   sudo make -C evaluation/examples detach EXAMPLE=ipv6_guard IFACE=TEST_IFACE

7. Unload (after detaching if you performed step 6):
   sudo make -C evaluation/examples unload EXAMPLE=ipv6_guard
   This removes only /sys/fs/bpf/beepl_eval_ipv6_guard.
   If load reports an existing pin, unload that earlier instance before retrying.

Whole collection: make -C evaluation/examples check
Then: sudo make -C evaluation/examples kernel-check
A load rejection or failed assertion is a failure, never a passing example.
*)
struct _xdp_md_bee {
  _data_bee : bytes, _data_meta : uint32, _ingress_ifindex : uint32,
  _rx_queue_index : uint32, _egress_ifindex : uint32
}
struct ethhdr {
  dst0 : uint16, dst1 : uint16, dst2 : uint16,
  src0 : uint16, src1 : uint16, src2 : uint16,
  protocol : uint16
}
#section license
let _license : int8[4] = "GPL"
(* EtherType 0x86dd appears as 0xdd86 on the little-endian eBPF target. *)
#ebpf
#section xdp
fun ipv6_guard (ostruct _xdp_md_bee* ctx) : int32, [] {
  match ctx with
  | some packet -> (
      match packet._data_bee with
      | Pbytes eth : struct ethhdr [ protocol : uint16 ] ->
          if (protocol == (uint16)56710) then 1 else 2
      | Pbytes rest : bytes [] -> 1
    )
  | none -> 1
}
