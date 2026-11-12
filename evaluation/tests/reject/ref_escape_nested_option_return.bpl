(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_nested_option_return.bpl -o /tmp/ref_escape_nested_option_return.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
struct holder { saved : option(option(int32*)) }
fun escape () : struct holder, alloc {
  let pointer : int32* = ref 42 in
  let result : struct holder = struct holder(saved)(some (some pointer)) in
  result
}
