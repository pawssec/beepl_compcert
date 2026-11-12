struct __sk_buff { len : uint32, pkt_type : uint32, mark : uint32, queue_mapping : uint32, protocol : uint32 }
#ebpf
#section tc
fun bad (struct __sk_buff* ctx) : int32, [] { (int32)bpf_redirect((uint32)1, (ulong)1) }
