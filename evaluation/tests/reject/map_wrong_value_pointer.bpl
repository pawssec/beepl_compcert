#section .maps
struct counts {
  map_type : uint32[1], key : uint32, value : ulong,
  max_entries : uint32[1]
}
struct xdp_md {
  _data : uint32, _data_end : uint32, _data_meta : uint32,
  _ingress_ifindex : uint32, _rx_queue_index : uint32, _egress_ifindex : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section xdp
fun xdp_map_update (struct xdp_md* ctx) : int32, alloc, alloc, write, io {
  let key : uint32* = ref (uint32)7 in
  let value : uint32* = ref (uint32)42 in
  let result : long = bpf_map_update_elem(counts, key, value, (ulong)0) in
  if (result == (long)0) then 2 else 1
}
