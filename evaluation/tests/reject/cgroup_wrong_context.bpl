struct wrong { family : uint32 }
#ebpf
#section cgroup/sock_create
fun bad (struct wrong* ctx) : int32, [] { 1 }
