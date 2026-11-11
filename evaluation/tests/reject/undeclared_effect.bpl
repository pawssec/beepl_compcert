struct xdp_md { _data : uint32, _data_end : uint32, _data_meta : uint32, _ingress_ifindex : uint32, _rx_queue_index : uint32, _egress_ifindex : uint32 }
#ebpf
#section xdp
fun main (struct xdp_md* ctx) : int32, [] { let n : ulong = bpf_ktime_get_ns() in 2 }
