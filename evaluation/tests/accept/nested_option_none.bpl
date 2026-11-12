(* Accepted nested-option surface regression. From the repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/nested_option_none.bpl -o /tmp/nested_option_none.s
   This is a compile-only fixture, not a kernel program.
   Nested option tags distinguish outer none from some none.
*)
fun main () : int32, [] {
  match none oint32* with | some found -> 2 | none -> 1
}
