(* Must fail before elaboration: generated structs cannot bypass the source
   prohibition on returning pointers to local storage.
   ./ccomp -typecheck -S evaluation/tests/reject/nested_option_pointer_return.bpl -o /tmp/beepl-invalid-return.s
   Expected error: Functions cannot return pointers
*)
fun main () : option(option(int32*)), alloc {
  let pointer : int32* = ref 42 in
  some (some pointer)
}
