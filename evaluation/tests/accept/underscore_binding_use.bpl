(* Accepted underscore-variable regression; from the repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/underscore_binding_use.bpl -o /tmp/beepl-underscore-binding-use.s
   gcc -no-pie /tmp/beepl-underscore-binding-use.s -o /tmp/beepl-underscore-binding-use
   /tmp/beepl-underscore-binding-use; echo $?
   Required behavior after repair: compilation succeeds and native exit is 0.
   Baseline: source type checking succeeds, but C compilation fails with
   "Unusedglob: reference to undefined global" because '_' is treated as a
   discarded binder even when its lexical variable is read.
   Validated after repair: native exit 0. Included in scoped-bindings-native.
*)
fun main () : int32, [] {
  let _ : int32 = 42 in
  if (_ == 42) then 0 else 7
}
