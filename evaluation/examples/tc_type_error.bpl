(* RUN GUIDE: tc_type_error
Check that invalid packet type 7 returns -EINVAL without mutation.
This is a TC direct-action classifier (SCHED_CLS), not XDP or a socket filter.
TC_ACT_OK = 0; TC_ACT_SHOT = 2. Kernel verification is pending your sudo run.
All commands run from the repository root. Use the existing compiler/LLVM,
libbpf and bpftool dependencies; live tests also require iproute2 and ping.

1. Compile/typecheck, test in userspace, and save assembly/ELF/raw bytecode:
   make -C evaluation/examples build EXAMPLE=tc_type_error
   file evaluation/.build/objects/tc_type_error.o
   llvm-objdump -d evaluation/.build/objects/tc_type_error.o
   Artifacts: evaluation/.build/objects/tc_type_error.s, .o, .bin, .disasm
   The ELF section is tc. Load .o, never raw .bin.
2. Load into kernel, run the verifier, assert test cases and release the program:
   sudo make -C evaluation/examples kernel-test EXAMPLE=tc_type_error
   Report: evaluation/results/tc_type_error-kernel.json
   Whole TC group: sudo make -C evaluation/examples kernel-tc-check
   Cases include nonmatching inputs and applicable boundary/error conditions.
3. Manually load/pin, inspect and execute a fixture:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=tc_type_error
   sudo make -C evaluation/examples inspect EXAMPLE=tc_type_error
   sudo make -C evaluation/examples jited EXAMPLE=tc_type_error
   sudo make -C evaluation/examples run EXAMPLE=tc_type_error
   Expected retval with the default IPv4 packet and zero mark: 0.
   A successful load confirms verifier acceptance on this kernel. Stop on errors.
   Synthetic test-run returns a decision; it does not send a real packet.
4. Unpin the manually loaded program:
   sudo make -C evaluation/examples unload EXAMPLE=tc_type_error
5. Observe real TC traffic using the isolated live collection:
   sudo make -C evaluation/examples tc-live
   Creates two temporary network namespaces joined by a veth pair. It attaches tc_pass,
   tc_drop and tc_ipv4 at ingress, checks ping before/during/after filtering,
   saves tc filter counters, and removes the namespace and devices on exit.
   Report: evaluation/results/tc-live.json. This does not change host interfaces.
   tc_mark, tc_length and helper tests use kernel-test for deterministic inputs.

Context: first five uint32 fields of Linux __sk_buff in UAPI order. TC test-run
includes Ethernet in ctx.len. protocol is network byte order (IPv4 = 8 here).
The mark example receives synthetic mark values via test-run's context input.
Helper calls require write, io effects; failed mutation is checked explicitly.
No arbitrary field stores, packet-byte mutation, or TC Pbytes parsing is added.
*)
struct __sk_buff {
  len : uint32, pkt_type : uint32, mark : uint32,
  queue_mapping : uint32, protocol : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section tc
fun tc_type_error (struct __sk_buff* ctx) : int32, write, io {
  let before : uint32 = ctx.pkt_type in
  let result : long = bpf_skb_change_type(ctx, (uint32)7) in
  if (result == (long)(0 - 22)) then
    if (ctx.pkt_type == before) then 0 else 2
  else 2
}
