#section .maps
struct counts {
  map_type : uint32[6], key : uint32, value : ulong,
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
fun xdp_map_counter (struct xdp_md* ctx) : int32, alloc, read, io, read, write {
  let key : uint32* = ref counts[0] in
  let found : oulong* = bpf_map_lookup_elem(counts, key) in
  match found with
  | some cell -> (let done : unit = cell := (!cell + (ulong)1) in 2)
  | none -> 1
}
