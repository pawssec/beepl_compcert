(* RUN GUIDE: socket_ipv4
Accept IPv4, reject other EtherTypes using skb protocol metadata.
Run from the repository root. Same Coq/OCaml/LLVM/libbpf/bpftool dependencies
as the XDP examples. Kernel verification is pending your privileged run.

1. Compile/typecheck, emulate, and save .s/.o/.bin/.disasm artifacts:
   make -C evaluation/examples build EXAMPLE=socket_ipv4
   file evaluation/.build/objects/socket_ipv4.o
   llvm-objdump -d evaluation/.build/objects/socket_ipv4.o
   The ELF section is socket. Load .o, not the raw .bin instruction bytes.
2. Load, verify and assert all kernel test cases, then release the program:
   sudo make -C evaluation/examples kernel-test EXAMPLE=socket_ipv4
   Report: evaluation/results/socket_ipv4-kernel.json
   All socket examples: sudo make -C evaluation/examples kernel-socket-check
3. Alternatively, load and inspect a pinned program:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=socket_ipv4
   sudo make -C evaluation/examples inspect EXAMPLE=socket_ipv4
   sudo make -C evaluation/examples jited EXAMPLE=socket_ipv4
   A successful load means verifier acceptance on this kernel. Stop on errors.
4. Execute a fixture inside the kernel, without attaching to a socket:
   sudo make -C evaluation/examples run EXAMPLE=socket_ipv4
   Expected retval: 4294967295 (accept IPv4).
   Socket-filter return values are byte counts, NOT XDP PASS/DROP actions.
   Test-run removes Ethernet before execution: ctx.len is frame length minus 14.
   It reports the return value without delivering or truncating a real packet.
5. Remove this pin:
   sudo make -C evaluation/examples unload EXAMPLE=socket_ipv4

Live socket observation (accept/drop examples, no interface changes):
   sudo make -C evaluation/examples socket-live
This loads socket_accept/socket_drop and attaches each to a temporary loopback
UDP receiver using SO_ATTACH_BPF. It prints receipt for accept and timeout for
drop, plus a successful control delivery after detachment. All sockets and
programs close automatically. Report: evaluation/results/socket-live.json.
Socket filtering affects delivery to that socket, not a host-wide firewall.

ABI: this struct is the first five uint32 fields of Linux __sk_buff, in order.
Only len and protocol are read. No direct packet pointers, writes, or Pbytes.
protocol contains network-order EtherType (IPv4 is 8 on little-endian eBPF).
*)
struct __sk_buff {
  len : uint32, pkt_type : uint32, mark : uint32,
  queue_mapping : uint32, protocol : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section socket
fun socket_ipv4 (struct __sk_buff* ctx) : int32, [] {
  if (ctx.protocol == (uint32)8) then -1 else 0
}
