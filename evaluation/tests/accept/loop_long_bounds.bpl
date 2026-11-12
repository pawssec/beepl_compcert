(* Regression for 64-bit loop bounds, including empty ranges and endpoints.
   From the repository root after make:
     ./ccomp -typecheck -S evaluation/tests/accept/loop_long_bounds.bpl -o /tmp/beepl-loop-long.s
     cc -no-pie /tmp/beepl-loop-long.s -o /tmp/beepl-loop-long
     /tmp/beepl-loop-long
     echo $?
   Expected exit status: 0. Native execution, not kernel verification.
   Validated native exit 0; included in loop-bounds-native. The Coq regression also
   checks the actual Csyntax evaluator, which requires int comparison results.
*)
fun main () : int32, alloc, read, write, read, write, read, write, read, write, read, write, read, write, read {
  let count : int32* = ref 0 in
  let up : unit = for ((long)0, (long)2, Up, count := (!count + 1)) in
  let down : unit = for ((long)2, (long)0, Down, count := (!count + 1)) in
  let empty_up : unit = for ((long)2, (long)0, Up, count := (!count + 100)) in
  let empty_down : unit = for ((long)0, (long)2, Down, count := (!count + 100)) in
  let maximum : unit = for ((ulong)((long)(0 - 1)), (ulong)((long)(0 - 1)), Up, count := (!count + 1)) in
  let minimum : unit = for ((ulong)0, (ulong)0, Down, count := (!count + 1)) in
  if (!count == 8) then 0 else 7
}
