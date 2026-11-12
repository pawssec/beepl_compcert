(* Ordinary nullable-option single-evaluation regression, from repository root:
   make -C evaluation/tests option-match-native
   Equivalent individual commands after building the compiler with make:
   ./ccomp -typecheck -S evaluation/tests/accept/option_match_once.bpl -o /tmp/beepl-option-match-once.s
   gcc -no-pie /tmp/beepl-option-match-once.s -o /tmp/beepl-option-match-once
   /tmp/beepl-option-match-once; echo $?
   Expected exit status: 0. This is native execution, not a kernel test.
   Both expression-position and statement-position match scrutinees increment
   a counter once. Exit 3 diagnoses both being incorrectly evaluated twice;
   other nonzero results also indicate a compiler regression.
*)
fun expression_case (int32* counter, int32* pointer) : int32, read, write, read, read {
  let observed : int32 = match
    (let _ : unit = counter := (!counter + 1) in some pointer)
    with | some found -> !found | none -> 100 in
  if (observed == 42) then !counter else 100
}
fun statement_case (int32* counter, int32* pointer) : int32, read, write, read, read {
  match (let _ : unit = counter := (!counter + 1) in some pointer)
    with | none -> 100 | some found ->
      if (!found == 42) then !counter else 100
}
fun main () : int32, alloc, alloc, read, write, read, read, write, read, write, read, read {
  let counter : int32* = ref 0 in
  let pointer : int32* = ref 42 in
  let expression_count : int32 = expression_case(counter, pointer) in
  let _ : unit = counter := 0 in
  let statement_count : int32 = statement_case(counter, pointer) in
  if (expression_count == 1) then
    if (statement_count == 1) then 0 else 2
  else if (expression_count == 2) then
    if (statement_count == 2) then 3 else 1
  else 4
}
