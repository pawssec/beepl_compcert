fun a (int32 x) : int32, [] { b(x) }
#ebpf
#section xdp
fun b (int32 x) : int32, [] { a(x) }
