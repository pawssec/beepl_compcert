(* Lexical Some-binder shadowing regression. From repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/option_match_shadow.bpl -o /tmp/beepl-option-match-shadow.s
   gcc -no-pie /tmp/beepl-option-match-shadow.s -o /tmp/beepl-option-match-shadow
   /tmp/beepl-option-match-shadow; echo $?
   Required exit status: 0. Native test, not a kernel test.
   The Some binder x shadows the outer x only within its branch. The outer
   reference must still point to 1 after the match, so the sum is 3.
   Before the hygiene repair this accepted program exited 7 (sum 4).
   Validated after repair: native exit 0. Included in scoped-bindings-native.
*)
fun main () : int32, alloc, alloc, read, read {
  let x : int32* = ref 1 in
  let other : int32* = ref 2 in
  let y : int32 = match some other with | some x -> !x | none -> 0 in
  if (!x + y == 3) then 0 else 7
}
