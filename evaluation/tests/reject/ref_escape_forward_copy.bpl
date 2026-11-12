(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_forward_copy.bpl -o /tmp/ref_escape_forward_copy.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
struct holder { saved : int32* }
fun forward (struct holder* output, struct holder value) : int32, write {
  let copied : struct holder = value in
  let done : unit = output := copied in
  0
}
fun escape (struct holder* output) : int32, alloc, write {
  let pointer : int32* = ref 42 in
  let payload : struct holder = struct holder(saved)(pointer) in
  forward(output, payload)
}
