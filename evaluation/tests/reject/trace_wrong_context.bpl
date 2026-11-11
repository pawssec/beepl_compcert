struct wrong_context { reserved_regs : ulong, syscall_id : long }
#ebpf
#section raw_tracepoint/sys_enter
fun trace_bad (struct wrong_context* ctx) : int32, [] { 0 }
