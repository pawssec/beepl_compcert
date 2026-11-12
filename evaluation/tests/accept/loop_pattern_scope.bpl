(* Compiler regression: `count` in the some-pattern belongs to that branch.
   It must not conflict with the separately scoped `count` in the loop body.
   Compile from the repository root (no sudo):
     ./ccomp -typecheck -S evaluation/tests/accept/loop_pattern_scope.bpl -o /tmp/beepl-loop-pattern-scope.s
   Expected: SUCCESS: Program type checks! and a generated assembly file.
   This is a compilation regression; kernel execution is not asserted here.
*)
struct xdp_md {
  _data : uint32, _data_end : uint32, _data_meta : uint32,
  _ingress_ifindex : uint32, _rx_queue_index : uint32, _egress_ifindex : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section xdp
fun scoped_loop (struct xdp_md* ctx) : int32, alloc, write, read {
  let count : int32* = ref 0 in
  let optional : oint32* = some count in
  let done : unit = for ((match optional with | some count -> let ignored : int32* = count in 0 | none -> 0), 0, Up, count := 1) in
  if (!count == 1) then 2 else 1
}
