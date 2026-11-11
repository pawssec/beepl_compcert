struct __sk_buff { len : uint32, pkt_type : uint32, mark : uint32, queue_mapping : uint32, protocol : uint32 }
#ebpf
#section socket
fun tc_helper_wrong_hook (struct __sk_buff* ctx) : int32, write, io {
 let result : long = bpf_skb_change_type(ctx, (uint32)0) in
 if (result == (long)0) then 0 else 2
}
