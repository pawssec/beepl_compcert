(* Native runtime regression, from the repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/nested_option_cases.bpl -o /tmp/beepl-nested-option-cases.s
   gcc -no-pie /tmp/beepl-nested-option-cases.s -o /tmp/beepl-nested-option-cases
   /tmp/beepl-nested-option-cases; echo $?
   Expected exit status: 0. No sudo or kernel loading is involved.
   Both pattern orders distinguish all depth-two and depth-three states;
   named function parameters carry nested options and dereference the payload.
*)
fun depth_two (option(option(int32*)) value) : int32, read {
  match value with | none -> 0 | some inner ->
    (match inner with | some pointer -> !pointer | none -> 1)
}
fun depth_two_reverse (option(option(int32*)) value) : int32, read {
  match value with | some inner ->
    (match inner with | none -> 1 | some pointer -> !pointer) | none -> 0
}
fun depth_three (option(option(option(int32*))) value) : int32, read {
  match value with | none -> 0 | some middle ->
    (match middle with | some inner ->
      (match inner with | none -> 2 | some pointer -> !pointer) | none -> 1)
}
fun depth_three_reverse (option(option(option(int32*))) value) : int32, read {
  match value with | some middle ->
    (match middle with | none -> 1 | some inner ->
      (match inner with | some pointer -> !pointer | none -> 2)) | none -> 0
}
fun main () : int32, alloc, read, read, read, read, read, read, read, read, read, read, read, read, read, read {
  let pointer : int32* = ref 42 in
  let a : option(option(int32*)) = none option(int32*) in
  let b : option(option(int32*)) = some (none int32*) in
  let c : option(option(int32*)) = some (some pointer) in
  let d : option(option(option(int32*))) = none option(option(int32*)) in
  let e : option(option(option(int32*))) = some a in
  let f : option(option(option(int32*))) = some b in
  let g : option(option(option(int32*))) = some c in
  if (depth_two(a) == 0) then
  if (depth_two(b) == 1) then
  if (depth_two(c) == 42) then
  if (depth_two_reverse(a) == 0) then
  if (depth_two_reverse(b) == 1) then
  if (depth_two_reverse(c) == 42) then
  if (depth_three(d) == 0) then
  if (depth_three(e) == 1) then
  if (depth_three(f) == 2) then
  if (depth_three(g) == 42) then
  if (depth_three_reverse(d) == 0) then
  if (depth_three_reverse(e) == 1) then
  if (depth_three_reverse(f) == 2) then
  if (depth_three_reverse(g) == 42) then 0 else 14
  else 13 else 12 else 11 else 10 else 9 else 8 else 7
  else 6 else 5 else 4 else 3 else 2 else 1
}
