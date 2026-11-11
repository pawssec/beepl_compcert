struct bpf_raw_sys_enter { reserved_regs : ulong, syscall_id : int32 }
#ebpf
#section raw_tracepoint/sys_enter
fun trace_bad (struct bpf_raw_sys_enter* ctx) : int32, [] { 0 }
