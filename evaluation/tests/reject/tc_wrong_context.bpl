struct wrong_context { len : uint32 }
#ebpf
#section tc
fun tc_wrong_context (struct wrong_context* ctx) : int32, [] { 0 }
