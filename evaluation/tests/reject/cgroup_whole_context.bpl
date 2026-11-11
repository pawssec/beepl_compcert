struct bpf_sock_create { bound_dev_if : uint32, family : uint32, type : uint32, protocol : uint32 }
#ebpf
#section cgroup/sock_create
fun bad (struct bpf_sock_create* ctx) : int32, read { let copy : struct bpf_sock_create = !ctx in 1 }
