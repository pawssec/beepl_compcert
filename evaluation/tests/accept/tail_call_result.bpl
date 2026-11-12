(* Native regression for returning the result of a call in tail position.
   From the repository root:
   make -C evaluation/tests tail-call-native
   Or, after make, the complete manual commands:
   ./ccomp -typecheck -S evaluation/tests/accept/tail_call_result.bpl -o /tmp/beepl-tail-call-result.s
   gcc -no-pie /tmp/beepl-tail-call-result.s -o /tmp/beepl-tail-call-result
   /tmp/beepl-tail-call-result
   echo $?
   Expected exit status after repair: 0. Native execution, not kernel testing.
   Before repair, wrapper lowers to Sdo(Ecall(...)) and falls off the nonvoid
   function instead of returning the callee's result. One observed run exits7;
   the unspecified target result is not guaranteed to fail on every run.
   Included in make -C evaluation/tests native-check.
*)
fun answer (int32 value) : int32, [] { value + 1 }
fun wrapper (int32 value) : int32, [] { answer(value) }
fun main () : int32, [] { if (wrapper(41) == 42) then 0 else 7 }
