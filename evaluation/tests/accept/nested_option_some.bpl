(* Accepted nested-option surface regression. From the repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/nested_option_some.bpl -o /tmp/nested_option_some.s
   This is a compile-only fixture, not a kernel program.
   Nested option tags distinguish outer none from some none.
*)
fun main (oint32* p) : int32, [] {
  match some p with | some found -> 2 | none -> 1
}
