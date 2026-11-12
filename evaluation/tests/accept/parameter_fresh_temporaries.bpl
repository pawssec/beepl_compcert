(* Regression: generated locals must not overwrite source parameters.
   make -C evaluation/tests parameter-temporaries-native
   Before reservation repair this typechecked program exited 1.
   From the repository root:
     ./ccomp -typecheck -S evaluation/tests/accept/parameter_fresh_temporaries.bpl -o /tmp/beepl-parameter-fresh.s
     gcc -no-pie /tmp/beepl-parameter-fresh.s -o /tmp/beepl-parameter-fresh
     /tmp/beepl-parameter-fresh; echo $?
   Expected exit status: 0. Native execution only, not kernel verification.
*)
fun collide (int32 __fresh__1000) : int32, alloc {
 let pointer : int32* = ref 1 in
 __fresh__1000
}
fun main () : int32, alloc {
 if (collide(42) == 42) then 0 else 1
}
