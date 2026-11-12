struct __sk_buff { len : uint32, pkt_type : uint32, mark : uint32, queue_mapping : uint32, protocol : uint32 }
#ebpf
#section tc
fun bad (struct __sk_buff* ctx) : int32, [] { let buf : uint8* = ref (uint8)0 in (int32)bpf_skb_load_bytes(ctx, (uint32)0, buf, (uint32)4) }
