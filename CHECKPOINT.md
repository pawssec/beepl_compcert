# BeePL checkpoint — 2026-11-11

This checkpoint saves the work before continuing the eBPF nested-option backend.
The user requested a checkpoint and push, then authorized continuing. Source
soundness and native nested-option tests pass; eBPF nested options remain work
in progress.

## Checked work

- Source-state progress, preservation, finite-execution safety, and typed
  terminal values: `cfrontend/BeePL_program_soundness_assembly.v` and
  `cfrontend/BeePL_program_multistep.v`, exported by `BeePL_typesystem_proofs.v`.
- `make -j4` passed for the configured native compiler after the assignment fix.
- `make soundness-check` passed: 14 results, no admitted BeePL dependencies;
  only the four explicitly permitted inherited classical/extensionality axioms.
- `make -C evaluation/tests nested-options-native` passed all three executables:
  nested states/function arguments, single evaluation/name collisions, and
  arrays/struct fields. The single-evaluation fixture retains an int32 counter.
- Nested-option representation roundtrips/injectivity and core constructor/
  match typing lemmas are checked in `BeePL_nested_option_model.v`,
  `BeePL_nested_option_tags.v`, and `BeePL_nested_option_elaboration.v`.

## Representation and proof boundaries

Surface `option(option(int32*))` is lowered by
`bparser/beepl_nested_options.ml` into private core records. Each extra layer
has a pointer-width unsigned tag and an inner payload; ordinary options retain
the nullable-pointer representation. Inactive payloads are initialized and
constructors/scrutinees are evaluated once. Original surface restrictions are
checked before lowering, including the prohibition on pointer returns.

The existing core soundness theorem applies to checked lowered programs. A full
simulation theorem for the OCaml elaboration and its fresh-name traversal is
not yet proved. The raw Coq core still rejects nested nullable-pointer `Otype`
values; nested surface programs must pass through elaboration. This checkpoint
does not claim completed BeePL-to-C compiler correctness, helper correctness,
or verifier replacement. See `PROOFS.md` for the existing source proof scope.

The runtime regression exposed an existing assignment-width bug. Both Csyntax
lowering paths now store using the pointee type; expression assignment casts
the result to its source annotation (void for well-typed unit assignments).
Compiler inversion/type lemmas were adapted. The 26 existing admitted compiler
proof declarations remain; no new admission was introduced for this fix.

## Unfinished eBPF backend work

Tagged record copies require fixed-size memcpy support. The initial eBPF
fixture failed compilation with `Builtin memcpy is not supported by eBPF`.
The saved backend changes use standard `Pbuiltin` semantics in Asmgen and
expand the pseudo-instruction to static loads/stores in `Asmexpand.ml`, using
declared scratch registers and full pointer-width transfers where aligned.

The current backend proof adaptation in `ebpf/Asmgenproof.v` is unfinished:
the last targeted build failed near line 955 with `congruence failed` in the
builtin PC/register-preservation case. `ebpf/Asmgen_memcpy_tests.v` is drafted,
not yet checked. The changed eBPF compiler has not completed its build, and
nested options have not passed the kernel verifier or kernel execution.
The native configuration remains buildable. The backend changes are saved in
a separate WIP commit so the preceding checkpoint is independently usable.

## Resume sequence

1. Complete `Asmgenproof.v` without new admissions; check scratch/emission
   regressions and the extraction/Asmexpand boundary.
2. Run `make -C evaluation/tests nested-options-check`. Resolve compilation or
   emulator failures and retain `.s`, `.o`, `.disasm`, `.bin`, and hash manifests.
3. Run `sudo make -C evaluation/tests nested-options-kernel-check` in a privileged
   session. Sudo outside the sandbox currently requires the user's password;
   no privileged result has been claimed. The runner loads/tests/unloads without
   attaching to a live interface.
4. Keep fixtures in `evaluation/tests/accept` until kernel acceptance is
   established; do not move unverified fixtures into `evaluation/examples`.
5. Continue the requested BeePL-to-Csyntax correctness work, building on
   `cfrontend/BeePL_compiler_proofs.v`, with elaboration correspondence explicit.

Generated compiler binaries, Coq objects, test artifacts and result logs remain
ignored; source, proof scripts, fixtures and Make targets are committed.
