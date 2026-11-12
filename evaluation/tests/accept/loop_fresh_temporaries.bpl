(* Regression: loop-index storage must be fresh against temporaries introduced
   make -C evaluation/tests loop-temporaries-native
   while compiling the body. Before the fix this program exited 1 (one iteration).
   From the repository root:
     ./ccomp -typecheck -S evaluation/tests/accept/loop_fresh_temporaries.bpl -o /tmp/beepl-loop-fresh.s
     gcc -no-pie /tmp/beepl-loop-fresh.s -o /tmp/beepl-loop-fresh
     /tmp/beepl-loop-fresh; echo $?
   Expected exit status: 0. Native execution only; no kernel claim.
*)
fun main () : int32, alloc, alloc, read, write, read {
 let count : long* = ref (long)0 in
 let _ : unit = for (0, 1, Up,
   let temporary : int32* = ref 42 in
   count := (!count + (long)1)) in
 if (!count == (long)2) then 0 else 1
}
