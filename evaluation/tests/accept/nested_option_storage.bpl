(* Native aggregate-storage regression, from repository root:
   ./ccomp -typecheck -S evaluation/tests/accept/nested_option_storage.bpl -o /tmp/beepl-nested-option-storage.s
   gcc -no-pie /tmp/beepl-nested-option-storage.s -o /tmp/beepl-nested-option-storage
   /tmp/beepl-nested-option-storage; echo $?
   Expected exit status: 0. This is not a kernel execution test.
   Nested options survive array-element copies and a named struct field.
*)
struct NestedHolder { value : option(option(int32*)) }
fun classify_storage (option(option(int32*)) value) : int32, read {
  match value with | none -> 0 | some inner ->
    (match inner with | none -> 1 | some pointer -> !pointer)
}
fun main () : int32, alloc, read, read, read, read {
  let pointer : int32* = ref 42 in
  let a : option(option(int32*)) = none option(int32*) in
  let b : option(option(int32*)) = some (none int32*) in
  let c : option(option(int32*)) = some (some pointer) in
  let entries : option(option(int32*))[3] = {a, b, c} in
  let holder : struct NestedHolder = struct NestedHolder (value) (entries[2]) in
  if (classify_storage(entries[0]) == 0) then
  if (classify_storage(entries[1]) == 1) then
  if (classify_storage(entries[2]) == 42) then
  if (classify_storage(holder.value) == 42) then 0 else 4
  else 3 else 2 else 1
}
