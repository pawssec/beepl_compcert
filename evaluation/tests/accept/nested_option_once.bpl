(* Native single-evaluation and fresh-name regression, from repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/nested_option_once.bpl -o /tmp/beepl-nested-option-once.s
   gcc -no-pie /tmp/beepl-nested-option-once.s -o /tmp/beepl-nested-option-once
   /tmp/beepl-nested-option-once; echo $?
   Expected exit status: 0. No sudo or kernel loading is involved.
   Constructor operand and match scrutinee each increment the counter once.
   User names deliberately resemble generated temporary/type/field names.
*)
struct __beepl_nested_option_type_0 {
  __beepl_nested_option_tag_1 : int32,
  __beepl_nested_option_payload_2 : int32
}
fun main () : int32, alloc, alloc, read, write, read, write, read, read {
  let __beepl_nested_option_some_3 : int32* = ref 0 in
  let __beepl_nested_option_match_4 : int32* = ref 42 in
  let constructed : option(option(int32*)) = some
    (let _ : unit = __beepl_nested_option_some_3 := (!__beepl_nested_option_some_3 + 1) in
     some __beepl_nested_option_match_4) in
  let observed : int32 = match
    (let _ : unit = __beepl_nested_option_some_3 := (!__beepl_nested_option_some_3 + 1) in
     constructed)
    with | none -> 100 | some inner ->
      (match inner with | some pointer -> !pointer | none -> 101) in
  if (observed == 42) then
    if (!__beepl_nested_option_some_3 == 2) then 0 else 1
  else 2
}
