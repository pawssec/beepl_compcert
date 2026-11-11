struct bpf_raw_sys_enter { reserved_regs : ulong, syscall_id : long }
#ebpf
#section raw_tracepoint/sys_enter
fun trace_bad (struct bpf_raw_sys_enter* ctx) : int32, [] { let copy : struct bpf_raw_sys_enter = !ctx in 0 }
