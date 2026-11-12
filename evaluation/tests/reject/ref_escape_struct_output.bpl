(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_struct_output.bpl -o /tmp/ref_escape_struct_output.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
struct holder { saved : int32* }
fun keep (struct holder* output, int32 value) : int32, alloc, write {
  let fresh : int32* = ref value in
  let result : struct holder = struct holder(saved)(fresh) in
  let written : unit = output := result in
  0
}
fun test (struct holder* first, struct holder* second) : int32, alloc, write, alloc, write, read {
  let done1 : int32 = keep(first, 1) in
  let done2 : int32 = keep(second, 2) in
  let kept : int32* = first.saved in
  if (!kept == 1) then 0 else 7
}
