(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_array_return.bpl -o /tmp/ref_escape_array_return.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
fun escape () : int32*[2], alloc, alloc {
  let first : int32* = ref 1 in
  let second : int32* = ref 2 in
  let result : int32*[2] = {first, second} in
  result
}
