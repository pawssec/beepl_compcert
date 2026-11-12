(* Reference-escape rejection regression. From the repository root:
   make
   ./ccomp -typecheck -S evaluation/tests/reject/ref_escape_loop_output.bpl -o /tmp/ref_escape_loop_output.s
   Expected: nonzero compiler status containing the complete diagnostic
   Reference escape check failed
   before code generation. Do not link or load. A later C lowering failure
   alone does NOT count as a successful rejection test.
*)
struct holder { saved : int32* }
fun test (struct holder* output) : int32, alloc, read, alloc, read, write, read, write, read {
  let count : int32* = ref 0 in
  let done : unit = for (0, 2, Up,
    let fresh : int32* = ref (!count + 1) in
    let updated : unit = if (!count == 0) then
      let replacement : struct holder = struct holder(saved)(fresh) in
      output := replacement
    else unit in
    count := (!count + 1)) in
  let kept : int32* = output.saved in
  if (!kept == 1) then 0 else 7
}
