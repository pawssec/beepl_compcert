struct bpf_sock_create { bound_dev_if : uint32, family : uint32, type : uint32, protocol : uint32 }
#ebpf
#section cgroup/sock_create
fun bad (struct bpf_sock_create* ctx) : int32, write { let done : unit = ctx := (struct bpf_sock_create (bound_dev_if, family, type, protocol) ((uint32)0, (uint32)0, (uint32)0, (uint32)0)) in 1 }
