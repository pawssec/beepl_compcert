struct bpf_sock_create { family : uint32, type : uint32 }
#ebpf
#section cgroup/sock_create
fun bad (struct bpf_sock_create* ctx) : int32, [] { 1 }
