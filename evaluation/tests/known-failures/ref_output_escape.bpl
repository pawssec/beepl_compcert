(* HISTORICAL COMPILER SEMANTICS FAILURE: references through struct output.
   The reference-escape gate now rejects this program before code generation.
   This is historical evidence, NOT an accepted regression or kernel test.
   From the repository root, after building the native compiler with make:

   ./ccomp -typecheck -S evaluation/tests/known-failures/ref_output_escape.bpl -o /tmp/beepl-ref-output-escape.s
   Expected now: nonzero status, Reference escape check failed.
   The old reproduction steps below apply ONLY to a compiler before the gate:
   gcc -no-pie /tmp/beepl-ref-output-escape.s evaluation/tests/known-failures/ref_output_escape_harness.c -o /tmp/beepl-ref-output-escape
   /tmp/beepl-ref-output-escape
   echo $?

   Both source typecheckers accept this program. In the source semantics each
   Ref allocates a fresh memory block, and returning from a call does not free
   that block: test must therefore return 0 (the first saved value remains 1).

   Unrestricted C lowering uses an automatic local for Ref. keep writes its address
   into caller-owned storage and returns, leaving a dangling reference. The
   second call can reuse that stack slot. One observed native run returned 7
   with equal saved addresses, but the dangling access has undefined behavior:
   no particular native result, address comparison, or exit status is promised.
   Even a native result of 0 would NOT establish correctness or fix the bug.
   Pointer-return rejection does not prevent this aggregate output escape.
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
