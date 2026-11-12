(* UDP direct-server-return load balancer. See evaluation/LOAD_BALANCER.md.
Compile: make -C evaluation/examples build EXAMPLE=tc_udp_lb
Kernel fixtures: sudo make -C evaluation/examples kernel-lb-check
Real requests/replies: sudo make -C evaluation/examples lb-live
Reports: evaluation/results/kernel-lb.json and evaluation/results/lb-live.json.
The live runner loads/verifies, attaches in temporary namespaces, configures
backend maps, tests replies, detaches and removes namespaces automatically.
Inspect saved bytecode: llvm-objdump -d evaluation/.build/objects/tc_udp_lb.o
Artifacts: evaluation/.build/objects/tc_udp_lb.{s,o,bin,disasm}.
A manual packet run target is not supported; use the dedicated runners.
VIP 192.0.2.100, UDP port 9000; IPv4 IHL=5; fragments drop. Bad lengths drop.
No NAT: rewrite only Ethernet addresses, preserving IP/UDP checksums and VIP.
Backend hosts must own the VIP and route replies to the client. No conntrack.
Map counts: array uint32->ulong, 9 slots. 0=mode (0 hash,1 A,2 B,3 disabled).
Slots1..4 and5..8 contain output ifindex and three little-endian Ethernet words
(destination MAC then source MAC). Update mode atomically; backend tuples must
be initialized before attach or updated only while detached (no snapshot lock).
Hash parity is a demonstration policy, not production-quality load distribution.
IPv4/UDP checksums are preserved, not validated; backend IP stack validates them.
Kernel verifier/live results are pending your privileged run.
*)
#section .maps
struct counts { map_type : uint32[2], key : uint32, value : ulong, max_entries : uint32[9] }
struct __sk_buff { len : uint32, pkt_type : uint32, mark : uint32, queue_mapping : uint32, protocol : uint32 }
#section license
let _license : int8[4] = "GPL"
#ebpf
#section tc
fun tc_udp_lb (struct __sk_buff* ctx) : int32,
  alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, write, io, read, alloc, read, io, read, alloc, read, io, read, alloc, read, io, read, alloc, read, io, read, alloc, read, io, read, alloc, read, write, io, alloc, read, write, io, alloc, read, write, io, io {
  let ether_buf : uint32* = ref (uint32)0 in
  let ether_status : long = bpf_skb_load_bytes(ctx, (uint32)12, ether_buf, (uint32)4) in
  if (ether_status != (long)0) then 2 else (
  let ether : uint32 = !ether_buf in
  let lengths_buf : uint32* = ref (uint32)0 in
  let lengths_status : long = bpf_skb_load_bytes(ctx, (uint32)16, lengths_buf, (uint32)4) in
  if (lengths_status != (long)0) then 2 else (
  let lengths : uint32 = !lengths_buf in
  let fragment_buf : uint32* = ref (uint32)0 in
  let fragment_status : long = bpf_skb_load_bytes(ctx, (uint32)20, fragment_buf, (uint32)4) in
  if (fragment_status != (long)0) then 2 else (
  let fragment : uint32 = !fragment_buf in
  let proto_buf : uint32* = ref (uint32)0 in
  let proto_status : long = bpf_skb_load_bytes(ctx, (uint32)22, proto_buf, (uint32)4) in
  if (proto_status != (long)0) then 2 else (
  let proto : uint32 = !proto_buf in
  let source_buf : uint32* = ref (uint32)0 in
  let source_status : long = bpf_skb_load_bytes(ctx, (uint32)26, source_buf, (uint32)4) in
  if (source_status != (long)0) then 2 else (
  let source : uint32 = !source_buf in
  let dest_buf : uint32* = ref (uint32)0 in
  let dest_status : long = bpf_skb_load_bytes(ctx, (uint32)30, dest_buf, (uint32)4) in
  if (dest_status != (long)0) then 2 else (
  let dest : uint32 = !dest_buf in
  let ports_buf : uint32* = ref (uint32)0 in
  let ports_status : long = bpf_skb_load_bytes(ctx, (uint32)34, ports_buf, (uint32)4) in
  if (ports_status != (long)0) then 2 else (
  let ports : uint32 = !ports_buf in
  let udp_buf : uint32* = ref (uint32)0 in
  let udp_status : long = bpf_skb_load_bytes(ctx, (uint32)38, udp_buf, (uint32)4) in
  if (udp_status != (long)0) then 2 else (
  let udp : uint32 = !udp_buf in
  if ((ether & (uint32)65535) != (uint32)8) then 0 else (
  if (((ether >> (uint32)16) & (uint32)255) != (uint32)69) then 2 else (
  if ((fragment & (uint32)65343) != (uint32)0) then 2 else (
  if (((proto >> (uint32)8) & (uint32)255) != (uint32)17) then 0 else (
  let ip_size : uint32 = ((lengths & (uint32)255) << (uint32)8) + ((lengths >> (uint32)8) & (uint32)255) in
  let udp_size : uint32 = ((udp & (uint32)255) << (uint32)8) + ((udp >> (uint32)8) & (uint32)255) in
  if (udp_size < (uint32)8) then 2 else (
  if (ip_size != (udp_size + (uint32)20)) then 2 else (
  if (ctx.len < (ip_size + (uint32)14)) then 2 else (
  if (dest != (uint32)1677852864) then 0 else (
  if ((ports >> (uint32)16) != (uint32)10275) then 0 else (
  let mode_key : uint32* = ref ((uint32)0) in
  let mode_opt : oulong* = bpf_map_lookup_elem(counts, mode_key) in
  match mode_opt with | none -> 2 | some mode_ptr -> (
  let mode : uint32 = (uint32)!mode_ptr in
  if (mode >= (uint32)3) then 2 else (
  let choice : uint32 = if (mode == (uint32)0) then ((source ^ ports) & (uint32)1) else (mode - (uint32)1) in
  let base : uint32 = (uint32)1 + (choice * (uint32)4) in
  let outdev_key : uint32* = ref (base) in
  let outdev_opt : oulong* = bpf_map_lookup_elem(counts, outdev_key) in
  match outdev_opt with | none -> 2 | some outdev_ptr -> (
  let outdev : uint32 = (uint32)!outdev_ptr in
  if (outdev == (uint32)0) then 2 else (
  let mac0_key : uint32* = ref (base + (uint32)1) in
  let mac0_opt : oulong* = bpf_map_lookup_elem(counts, mac0_key) in
  match mac0_opt with | none -> 2 | some mac0_ptr -> (
  let mac0 : uint32 = (uint32)!mac0_ptr in
  let mac1_key : uint32* = ref (base + (uint32)2) in
  let mac1_opt : oulong* = bpf_map_lookup_elem(counts, mac1_key) in
  match mac1_opt with | none -> 2 | some mac1_ptr -> (
  let mac1 : uint32 = (uint32)!mac1_ptr in
  let mac2_key : uint32* = ref (base + (uint32)3) in
  let mac2_opt : oulong* = bpf_map_lookup_elem(counts, mac2_key) in
  match mac2_opt with | none -> 2 | some mac2_ptr -> (
  let mac2 : uint32 = (uint32)!mac2_ptr in
  let word0 : uint32* = ref mac0 in
  let stored0 : long = bpf_skb_store_bytes(ctx, (uint32)0, word0, (uint32)4, (ulong)0) in
  if (stored0 != (long)0) then 2 else (
  let word1 : uint32* = ref mac1 in
  let stored1 : long = bpf_skb_store_bytes(ctx, (uint32)4, word1, (uint32)4, (ulong)0) in
  if (stored1 != (long)0) then 2 else (
  let word2 : uint32* = ref mac2 in
  let stored2 : long = bpf_skb_store_bytes(ctx, (uint32)8, word2, (uint32)4, (ulong)0) in
  if (stored2 != (long)0) then 2 else (
  (int32)bpf_redirect(outdev, (ulong)0)
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
}
