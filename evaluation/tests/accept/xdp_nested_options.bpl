(* Pending kernel acceptance: this fixture is deliberately outside examples/.
   Complete commands from the repository root:

   1. Build the compiler and save compiled artifacts:
      make -C evaluation/tests nested-options-build
      Saves assembly (.s), ELF (.o), disassembly (.disasm), entry bytecode (.bin),
      subprogram bytecode (.text.bin),
      and source/compiler/object hashes in evaluation/.build/objects/.
      Report: evaluation/results/nested-options-build.json
      The loader uses the complete ELF .o, including subprogram relocations.
      Compilation does not establish kernel verifier acceptance.
      Optional: make -C evaluation/tests nested-options-check
      The current emulator cannot execute BPF subprogram calls and reports
      that limitation as a failure, not a passed execution test.

   2. Load the saved object through the Linux verifier and run packet tests:
      sudo make -C evaluation/tests nested-options-kernel-check
      Report: evaluation/results/nested-options-kernel.json
      The runner verifies hashes, loads via libbpf, executes IPv4, IPv6 and
      minimum Ethernet packets, asserts XDP_PASS (2) and unchanged packet data,
      and releases the program. No interface is attached; no pin is retained.
      Compilation is never performed under sudo. Re-run step 1 after edits.

   3. Inspect the generated code without privileges:
      llvm-objdump -d evaluation/.build/objects/xdp_nested_options.o

   Every invocation checks all depth-two and depth-three states and dereferences
   the contained pointer. Any mismatch returns XDP_DROP (1).
*)
struct xdp_md {
  _data : uint32, _data_end : uint32, _data_meta : uint32,
  _ingress_ifindex : uint32, _rx_queue_index : uint32, _egress_ifindex : uint32
}
#section license
let _license : int8[4] = "GPL"
fun nested_two (option(option(int32*)) value) : int32, read {
  match value with | none -> 0 | some inner ->
    (match inner with | some pointer -> !pointer | none -> 1)
}
fun nested_three (option(option(option(int32*))) value) : int32, read {
  match value with | some middle ->
    (match middle with | none -> 1 | some inner ->
      (match inner with | some pointer -> !pointer | none -> 2)) | none -> 0
}
#ebpf
#section xdp
fun xdp_nested_options (struct xdp_md* ctx) : int32, alloc, read, read, read, read, read, read, read {
  let pointer : int32* = ref 42 in
  let a : option(option(int32*)) = none option(int32*) in
  let b : option(option(int32*)) = some (none int32*) in
  let c : option(option(int32*)) = some (some pointer) in
  let d : option(option(option(int32*))) = none option(option(int32*)) in
  let e : option(option(option(int32*))) = some a in
  let f : option(option(option(int32*))) = some b in
  let g : option(option(option(int32*))) = some c in
  if (nested_two(a) == 0) then
  if (nested_two(b) == 1) then
  if (nested_two(c) == 42) then
  if (nested_three(d) == 0) then
  if (nested_three(e) == 1) then
  if (nested_three(f) == 2) then
  if (nested_three(g) == 42) then 2 else 1
  else 1 else 1 else 1 else 1 else 1 else 1
}
