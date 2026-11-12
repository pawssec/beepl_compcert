(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_nested_return.bpl -o /tmp/ref_escape_nested_return.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
struct inner { saved : int32* }
struct outer { child : struct inner }
fun escape () : struct outer, alloc {
  let pointer : int32* = ref 42 in
  let child : struct inner = struct inner(saved)(pointer) in
  let result : struct outer = struct outer(child)(child) in
  result
}
