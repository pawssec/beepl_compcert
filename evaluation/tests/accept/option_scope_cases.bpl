(* Scoped option bindings: parameters, globals, nested patterns, and None.
   From the repository root after building with make:
   ./ccomp -typecheck -S evaluation/tests/accept/option_scope_cases.bpl -o /tmp/beepl-option-scope-cases.s
   cc -no-pie /tmp/beepl-option-scope-cases.s -o /tmp/beepl-option-scope-cases
   /tmp/beepl-option-scope-cases
   echo $?
   Required exit status: 0. Native execution, not kernel verification.
   Validated after repair: native exit 0. Included in scoped-bindings-native.
*)
let shared : int32 = 7

fun parameter_case (int32* pointer, int32* other) : int32, read, read {
  let matched : int32 = match some other with
    | some pointer -> !pointer | none -> 0 in
  !pointer + matched
}

fun nested_case (int32* pointer, int32* other, int32* third) : int32, read, read, read {
  let matched : int32 = match some other with
    | some pointer ->
      let inner : int32 = match some third with
        | none -> 0 | some pointer -> !pointer in
      !pointer + inner
    | none -> 0 in
  !pointer + matched
}

fun none_case (int32* pointer) : int32, read, read {
  let matched : int32 = match none int32* with
    | some pointer -> !pointer | none -> 0 in
  !pointer + matched
}

fun global_case (int32* other) : int32, read {
  let matched : int32 = match some other with
    | some shared -> !shared | none -> 0 in
  shared + matched
}

fun main () : int32, alloc, alloc, alloc, read, read, read, read, read, read, read, read {
  let first : int32* = ref 10 in
  let second : int32* = ref 20 in
  let third : int32* = ref 30 in
  if (parameter_case(first, second) == 30) then
    if (nested_case(first, second, third) == 60) then
      if (none_case(first) == 10) then
        if (global_case(second) == 27) then 0 else 4
      else 3
    else 2
  else 1
}
