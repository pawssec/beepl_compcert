# Existing BeePL proof completion

Priority: complete and validate the existing language's proofs. Keep the Linux
verifier enabled. Extend applications only within current language capabilities;
new language features and ownership/borrow checking are deferred.

## Current status

**Source type soundness is now proved for the formalized BeePL small-step
semantics, starting from an initialized, coherent program configuration.**
This is the state-based claim in the paper's progress, preservation, and
soundness lemmas. It is not a compiler-correctness, termination, or Linux
verifier-replacement theorem.

The public entry point is
[`cfrontend/BeePL_typesystem_proofs.v`](cfrontend/BeePL_typesystem_proofs.v).
The final proof covers every expression constructor admitted by the current
declarative typing relation; it does not assume an expression belongs to a
restricted supported fragment. Internal calls include unit, scalar, reference,
option, aggregate, packet-descriptor, and immutable function parameters.
Mixed structure/array initialization, mutation, packet matching, lexical
bindings, and loop/call frames use the same evolving heap invariant.

| Result | Checked API |
| --- | --- |
| A well-formed typed expression is a value or takes an actual step | `program_expression_progress_checked` |
| Every actual step preserves its result type, a well-formed shared heap, and a residual subeffect | `program_expression_preservation_checked` |
| The same preservation holds across actual expression/list executions | `program_closure_preservation`, `program_closures_preservation` |
| A reachable expression cannot get stuck | `program_reaches_cannot_get_stuck` |
| A terminal expression state is a value of the original result type | `program_closure_normal_form_is_typed_value` |
| A reachable list is entirely values or has a nonvalue list step | `program_closures_values_or_progress` |

`BeePL_program_soundness_assembly.v` assembles the full structural theorem;
`BeePL_program_multistep.v` proves the execution and terminal-state results.
Allocation explicitly extends the store typing and tracked heap objects.
Effects can shrink as operations execute. The list result distinguishes values
from actual evaluation because the existing list semantics includes identity
steps for lists of values. No termination assumption is used to prove safety.

### Preconditions and evidence that they can be satisfied

`program_runtime_configuration` combines declarative expression typing with
initialized/coherent memory, valid located values and packet descriptors,
valid captured environments, authenticated internal code, and typed function
bodies. It contains no premise that a future step or a safe successor exists.
The theorem requires these initial facts and preserves them.

`BeePL_initial_program.v` additionally derives a loaded configuration for
programs containing internal code definitions and no data globals, using the
real `Genv.init_mem` loader. Code typing and global symbol bindings are derived;
source-body location validity and the absence of runtime frames remain explicit
source well-formedness conditions. `BeePL_initial_program_execution.v` supplies
a concrete checker-accepted loaded program whose function body is
`Cond(true, 41, 0)`, constructs its complete initial configuration, and proves
that its initial application takes an actual call step. Thus the new invariant
is not vacuous.

General loader adequacy for initialized data globals, external helpers, and
parser-produced body well-formedness remains separate work. In particular,
source application semantics currently models internal calls; the theorem does
not establish correctness of arbitrary eBPF helper implementations or their
kernel contracts. It also does not prove the executable checker complete/sound
for every input or prove the compiler preserves source semantics.

### Reproducing the checks

From the repository root, with the configured Coq dependencies available:

```sh
make -j4 proof
make -j4 soundness-check
make -j4 soundness-kernel-check
```

`proof` checks the registered development. `soundness-check` reruns
`Print Assumptions` for the actual public results and loaded witness, even if
all proof objects are already current, and rejects every dependency axiom
except the four explicitly permitted inherited Coq/CompCert classical and
functional-extensionality axioms. Its output is saved in
`evaluation/results/type-soundness-assumptions.log`.
`soundness-kernel-check` also runs `coqchk` on the public proof and loaded
witness modules. These are Coq kernel checks, not Linux kernel tests.

Validation completed: `make -j4 proof soundness-kernel-check` returned success.
The fresh audit checked 14 public results (one closed under the global context;
the others use only the permitted inherited axioms), and `coqchk` succeeded.
The audit script also passed 3 positive, 13 negative, and 2 invocation fixtures,
including rejection of a leaked admitted BeePL theorem. No Linux kernel tests
were needed for this proof-only change.

The soundness results have no admitted BeePL theorem in their dependency
closure. This does **not** mean all proofs elsewhere in the repository are
finished; unrelated compiler, checker, memory, and eBPF-property admissions
remain. A successful generic `make` is not evidence for those separate claims.

### Why the five legacy statements were replaced

`BeePL_legacy_soundness_audit.v` proves that the old `store_well_typed`
precondition is impossible: its function invariant demands incompatible
signatures at the same address. The old stateful-effect classifier also always
returns true, and the old normalization statement quantifies arbitrary final
states while incorrectly requiring the input to be a value. We did not fill
those admissions using contradictions or tautologies. Their unfinished proofs
were retired in favor of the checked APIs above; checked substitution/read
helpers were retained. `sub_effect_trans` in `BeePL_auxlemmas.v` is now proved,
removing the final admitted dependency from the assembled safety theorem.

The historical `BeePL_ebpf_proofs.v` consumers of the old signatures remain
unfinished separate work and must migrate to the new state invariant. The
sections below record the development history and include limitations that
later milestones have repaired.

## Compiler correctness: checked foundations and remaining work

Source soundness above is complete for its stated formal core; the
BeePL-to-Csyntax semantic simulation is **not complete**. The checked compiler
modules below do not import the legacy admitted compiler development.

`BeePL_compiler_source_semantics_audit.v` also demonstrates why the old
`bsem_expr` simulation target must be replaced: after a real allocation and
initialization, its reference rule can report any block, including a proved
invalid block. The current source safety theorem uses `ssem_expr` and its
closures. The new full compiler simulation must use those actual small-step
configurations; filling the old big-step admissions would not establish it.


**Reference lifetime boundary:** source allocation remains live after return,
but C lowering uses automatic locals. A callee that writes a local reference
into a caller-owned structure therefore leaves a dangling C pointer. The
historically accepted witness and native harness are retained in
`evaluation/tests/known-failures/`.
`BeePL_compiler_lifetime_audit.v` proves that a source-readable cell cannot
remain injected into a freed target slot, with an actual allocation/free witness.
The native result is undefined and must not be treated as a stable expected
failure code. The chosen interim policy is conservative rejection, enforced by
`check_reference_escapes` inside `BeePL_compcert`, before code generation.

- `BeePL_escape_types.v` recursively checks structures and arrays for reference
  storage. Pointers (including nested options), Bytes and function values fail
  this check; missing or cyclic structure metadata also fails closed.
- `BeePL_escape_check.v` rejects reference-bearing internal results and memory
  stores, including aggregate copies. Local immutable reference-bearing values
  remain allowed. Array initialization must name a declared local array, not a
  parameter, global or shadowed variable. Calls must resolve directly to a
  checked internal function or an explicitly supported external helper.
  Duplicate global identifiers, indirect calls and reference casts are rejected.
- `BeePL_escape_helpers.v` checks actual external declarations, embedded
  signatures and permitted argument shapes against explicit synchronous helper
  contracts. Unknown externals, including unrestricted libc variadic I/O, are
  rejected. Helper implementation behavior is a trusted ABI boundary; the
  Boolean check does not prove that behavior or buffer bounds.
- `BeePL_compiler_escape.v` connects successful compilation to the gate and
  its internal-function result/body requirements. These are syntactic policy
  theorems. They do **not** establish semantic lifetime safety or complete the
  compiler simulation. Their safety interpretation still needs source typing,
  the helper contracts, and the remaining memory/call simulation proofs.
- `BeePL_escape_policy.v` proves that the store and direct-call requirements
  hold throughout each checked body, including nested branches, loops and
  binding scopes. Every store payload is reference-free; every call has an
  accepted contract under its checked scope.
- `BeePL_escape_resolution.v` proves that the gate's direct function lookup
  agrees with the source global environment, using the enforced uniqueness of
  global identifiers.

The semantic lifetime development now has separate source and target memories:

- `BeePL_compiler_frame_release.v` proves injection restriction and target
  `free_list` preservation when retained source memory contains no pointers
  into retired target blocks. A concrete two-block witness retains a caller
  mapping while retiring a still-live source allocation's target mapping.
  Fresh private source allocation and private-slot initialization preserve this
  closure property. The closure premise is not yet established for complete
  checked calls.
- `BeePL_escape_store.v` proves actual typed primitive assignments cannot
  introduce pointer fragments. `BeePL_compiler_frame_confinement.v` uses this
  fact and permission preservation to establish closure after typed scalar
  assignments and their finite sequences. Aggregate padding needs additional
  reasoning: typed reference-free fields do not constrain arbitrary padding
  bytes, so these results do not claim whole-aggregate confinement.
- `BeePL_compiler_reference_evaluation.v` connects actual evaluated scalar
  `Ref` lowering to Cstrategy execution, allocating the source block into an
  unused preallocated target slot and establishing the resulting injection.
  It requires scalar cast stability and target slot/permission facts; it is
  not yet a complete expression-induction theorem.
- `BeePL_compiler_binary_translation.v` proves evaluation of actual guarded
  32/64-bit shift, division and modulo helpers for both signedness choices and
  all operand values, including agreement with source unsafe-operation
  detection. These lemmas start with evaluated operands; they do not assume
  branch evaluation or a successful arithmetic result. Guarded arithmetic now
  captures each operand once, in source
  order. Negative counts return zero; modulo statement lowering uses modulo;
  guard comparisons use C's int type even for long operands. The simulation of
  effectful operand capture is checked below under explicit child/frame
  premises; deriving them for arbitrary child executions remains open. Its native
  regressions are `binary_guard_once.bpl` and `binary_guard_edges.bpl`, run with
  `make -C evaluation/tests binary-guards-native`.
- `BeePL_compiler_reference_step.v` connects an actual `ssem_expr` primitive
  reference-allocation step to execution of the generated C expression and an
  extended memory injection. It also handles source `Mbool` versus target
  unsigned-byte stores by proving equality of stored bytes. The preallocated,
  unused target slot and nonvolatile/typed scalar premises remain explicit;
  target execution and the final memory injection are derived.
  `BeePL_compiler_reference_child.v` extends this to arbitrary translated child
  expressions, using the child simulation and preserving its trace; it does
  not assume the enclosing target reference evaluation.
- `translated_typed_scalar_reference_allocation` additionally handles narrow
  integer cast normalization: it derives equal stored bytes and a memory
  extension rather than assuming the cast leaves the value unchanged. The
  original stable-cast theorem remains available as a compatibility API.
- `BeePL_compiler_cast_evaluation.v` connects successful evaluated-operand
  primitive cast lowering to target execution and source decoding, reusing
  the existing generated-cast evaluation proof, including Bool normalization.
- `BeePL_compiler_dereference_evaluation.v` and `BeePL_compiler_bool_read.v`
  transport actual surface primitive reads through a memory injection, including
  Bool. A successful source `Mbool` read already guarantees a canonical byte
  (`0` or `1`), so the existing unsigned-byte target read agrees. The earlier
  claim that source `Mbool` normalizes any nonzero byte was incorrect: raw byte
  `2` gives `Vundef` and source decoding fails. Checked lemmas demonstrate this
  boundary; the misleading native counterexample fixtures have been removed.
  Raw Coq `Tint IBool` is distinct from surface `Tbool` and is excluded from this
  theorem: its source and target access modes differ. These read lemmas concern
  explicit target `Evalof` expressions. `BeePL_compiler_variable_read.v`
  connects local and global primitive variables to actual generated evaluation
  using source reads and memory injection, without assuming a target read.
  `BeePL_compiler_dereference_translation.v` derives evaluation of the actual
  enclosing dereference from the child simulation, preserving its trace.

- `BeePL_compiler_rvalue_audit.v` checks that bare Csyntax variables and
  dereferences cannot evaluate as rvalues, and proves evaluation of the corrected
  actual variable lowering. The compiler now emits explicit `Evalof` for reads,
  including struct results and affected packet-field operands; assignment and
  address operands retain their location forms. Unit variables emit their value
  directly because there is no readable void cell. The legacy simulation's
  conversion wrapper no longer changes emitted code. Array initializers now
  consume translated RHS values directly rather than adding a second `Evalof`;
  `BeePL_compiler_array_rhs.v` checks the exact generated shapes and the reason
  the old literal-read form could not execute.
- `BeePL_representation_check.v` rejects raw `Tint IBool` recursively in program
  types, annotations, signatures and composites. This internal Coq constructor
  is distinct from surface `Tbool`. `BeePL_raw_ibool_audit.v` demonstrates why
  typing and escape checks alone do not exclude it. The compiler invokes the
  representation check separately, and `BeePL_compiler_representation.v`
  derives its guarantees from successful compilation. Ordinary Bool and nested
  options remain permitted.
- `BeePL_binary_capture_evaluation.v` connects successful `guarded_binop`
  lowering to execution of both real temporary stores and the arithmetic guard,
  for both integer widths. The proof preserves left-to-right traces and derives
  the final guard result. Child evaluation, allocated distinct slots, casts and
  protection of the left slot during the right evaluation remain explicit
  induction/invariant obligations.

- `BeePL_compiler_temporary_frame.v` constructs matching target stores and
  proves that mapped scalar writes cannot overwrite an unused capture slot.
  Finite write sequences and allocation into another local preserve the slot
  and its captured value. Arbitrary calls still require their own frame proof.
- `BeePL_compiler_aggregate_confinement.v` extends caller-memory closure to
  actual aggregate assignments. Retained source mappings provide closure for
  copied bytes, including padding; private aggregates can supply explicit
  scalar-byte/padding provenance. Deriving that provenance across whole checked
  calls remains open.
- `BeePL_compiler_tail_calls.v` connects actual statement-call lowering to its
  return behavior. A non-unit tail call now emits `Sreturn`, correcting a native
  regression where a wrapper discarded the callee's result. Unit calls keep
  `Sdo`. `tail_call_result.bpl` is included in `native-check`; the local execution
  theorem composes with a target call evaluation and does not assume source
  callee simulation has already been proved.

**Validated scoped-binding repair:** the accepted witness
`evaluation/tests/accept/option_match_shadow.bpl` shadows an outer
reference in a Some pattern. Source scope preserves the outer binding, but
the previous lowering reused its target slot (observed native exit 7, expected
0). The revised lowering uses fresh lexical slots, restores the incoming scope
after each binding, and treats `fn_vars` as a name catalogue rather than
predeclared locals. This also avoids a later pattern binder shadowing a global
throughout a whole C function. The `_` spelling is an ordinary source identifier;
nonunit `_` bindings now receive storage too. Unit bindings need no storage.
The binding helpers, exact translation decompositions, annotation preservation,
and primitive variable-read bridges have been checked against this translation.
The read bridge resolves source identifiers through the compiler binding map
and derives target reads from source reads and memory injection. The rebuilt
native compiler passes the shadowing, nested-scope, global-name and referenced
underscore regressions in `evaluation/tests/accept`. Whole-program scope
simulation remains open; these native results do not establish Linux kernel
acceptance.

`BeePL_compiler_binding_evaluation.v` composes actual child translations and
evaluations into the generated binding assignment/comma execution, preserving
their traces. Its source-head lemma uses the real `ssem_bind2` substitution
step, with a target-only private local store and a nonidentity value injection.
`BeePL_compiler_scoped_values.v` relates source substituted values to lexical
target slots and derives actual compiled variable reads. This relation currently
covers unit and values stored in scalar/pointer slots. Slot separation,
nonvolatile access, and canonical load results are explicit premises; the
whole-program invariant must establish them.

`BeePL_compiler_loop_rvalue_audit.v` checks the actual generated loop guards
for both directions and for int32 and signed-long bounds. The compiler now
emits explicit rvalue reads for its captured bounds and gives comparisons their
correct C `int` result type. Previously the guards used bare lvalues, which
cannot evaluate as Csyntax rvalues; long comparison results also had an
incompatible Boolean-test annotation. These are guard execution proofs, not a
complete simulation of loop bodies or divergence.

**Resume point after the requested pause:** complete the relation between a
source body after value substitution and the original body compiled under its
lexical scope. Aggregate bindings additionally require copied-value views:
source substitution retains an aggregate location, whereas C can copy its
contents into another local block. Do not assume these duplicate aggregate
addresses have the same memory-injection mapping. The existing
`BeePL_copy_bytes.copied_bytes_scalar_load` lemma is a starting point for
relating fields of copied aggregates. Whole-call entry/exit, lifetime and
helper-contract composition, and whole-program small-step simulation remain
open. The 18 legacy `Admitted` theorem boundaries are not part of the checked
compiler foundation audit and have not been claimed as completed proofs.

The policy deliberately rejects some safe borrowed-reference returns/stores.
Supporting those precisely is deferred to a future lifetime analysis. Source
soundness is unchanged: the compiler now accepts a narrower source subset.
Run the targeted negative tests with `make -C evaluation/tests escape-rejections`
and the local-use positives with `make -C evaluation/tests native-check`.

- `BeePL_compiler_expression_types.v` proves result-type annotation preservation
  for every successful expression translation. The structure initializer now
  retains its declared structure and pointer attributes. This is annotation
  preservation, not a theorem that every generated C expression is well typed.
- `BeePL_compiler_decomposition.v` checks the executable translation inversion
  facts used by the old proof. Its explicitly enumerated cases expose actual
  operand translations and generated syntax; cases mapped to `True` make no
  decomposition claim. The legacy decomposition and type-preservation admissions
  have been replaced by wrappers around these checked results.
- `BeePL_compiler_statement_decomposition.v` checks the selected statement
  inversion cases formerly admitted as `trans_expr_st_ind`. Guarded operators
  expose their intermediate operand context and actual capture-helper run;
  the legacy lemma now wraps this checked result. Its existing default `True`
  branch makes no inversion claim for unlisted syntax constructors.
- `BeePL_compiler_structure.v` derives actual leaf shapes, function signatures,
  external argument conversions, final generated local declarations, and the
  particular body-translation run. Generated locals are not equated to source
  declarations.
- `BeePL_compiler_globals.v` derives matching global-definition lists from
  successful `BeePL_compcert` execution and proves symbol/function lookup
  correspondence. `BeePL_compiler_initial_memory.v` proves that both actual
  loaders produce identical initial global memory, including symbol-based
  initializers. This does not equate memories during local allocation.
- `BeePL_compiler_composites.v` proves preservation of each source composite's
  layout through actual successful compilation, including the Bytes seed,
  optional XDP metadata and other generated composites. Complete C
  representation types retain their size/alignment. Source `sizeof_type` is
  a separate relation and is not silently identified with C representation size.
- `BeePL_compiler_operator_translation.v` closes the existing unary-operation
  and cast correspondence lemmas using actual translation and successful value
  decoding. These are operation lemmas, not full expression simulation.
- `BeePL_compiler_local_allocation.v` constructively allocates one run's final
  target context, proves typed lookup, block validity and permissions, and
  frames existing memory. `BeePL_compiler_context_growth.v` and
  `BeePL_compiler_statement_growth.v` cover all successful expression/list/
  statement translations. `BeePL_compiler_reserved_names.v` proves that no
  reserved names are introduced, compiler metadata is preserved, and distinct
  source parameters/locals imply distinct target parameters/locals. Its
  allocation corollary constructs all target function-entry storage.
- `BeePL_compiler_memory_injection.v` maps a later source allocation into an
  unused preallocated target local, preserving previous mappings and simulating
  scalar initialization. A concrete int32 allocation/store/read witness is
  included. Slot separation remains a real hypothesis: this does not resolve
  escaped or repeatedly reused live references.
- `BeePL_option_capture_evaluation.v` proves actual target expression and
  statement evaluation of a once-only scrutinee capture, with its original
  trace. It constructs the store from writable-slot evidence and proves reload.
  Full integration still needs freshness, allocation and memory-framing facts.

The old `fctx_fresh_in_ff` quantified over *every* input context and required all
outputs to fit in one finite context. `BeePL_compiler_context_audit.v` proves
this premise impossible without importing any legacy admission. Consequently,
the old main simulation statement cannot establish useful compiler correctness
by filling its proof: its invariant must be replaced. The legacy file also
contains checked counterexamples to its incomplete expression/statement
specification relations. Remaining legacy admissions are not certified by the
new audit.

The ordinary option Match compiler evaluated an effectful scrutinee twice in
both expression and statement positions. `option_match_once.bpl` reproduced
this with counters returning two instead of one. Lowering now stores the
scrutinee once in a fresh typed local and reuses that local, preserving all
scrutinee-generated declarations. Further freshness proofs exposed and repaired
three statement-context bugs: a pointer structure initializer lost its generated
slot, loop indices could collide with body temporaries, and Bytes matching lost
branch temporaries. Generated names now also reserve actual parameters and
program identifiers, fixing a user parameter named `__fresh__1000` being
clobbered by reference storage. None of these fixes implements lifetime checks.
Seven legacy compiler admissions have been replaced with checked proofs. The
proof-only rvalue conversion was separately retired: its compatibility wrapper
is now the identity, so its evaluation lemma is trivial and is not counted as
new compiler correctness evidence. Eighteen legacy admissions remain, including
the unusable old simulation target.
Run the native regressions with:

```sh
make -C evaluation/tests option-match-native
make -C evaluation/tests loop-temporaries-native
make -C evaluation/tests parameter-temporaries-native
make -C evaluation/tests native-check
```

The compiler audit and Coq kernel checks are:

```sh
make -j4 compiler-check
make -j4 compiler-kernel-check
```

These audit the listed checked foundations, **not whole compiler correctness**.
Compiler mode permits the inherited classical/extensionality axioms, the
existing `SimplExpr.first_unused_ident` generator parameter, and CompCert's
`external_functions_sem` / `inline_assembly_sem` parameters used by target
operational semantics. It does not assert correctness of helpers or inline
assembly. The stricter source-soundness allowlist is unchanged.

The eBPF Asmgen proof now accepts the standard `Pbuiltin EF_memcpy` form without
new admissions; fixed-size copies expand to loads/stores in `Asmexpand.ml`.
Checked emission tests cover scratch registers, offsets, sizes and integer/
pointer representation. Expansion itself remains a trusted boundary: there is
no complete byte-copy refinement proof for arbitrary partial pointer fragments
or undefined padding. Nested-option ELF compilation has succeeded; the current
userspace emulator cannot execute its BPF subprogram calls. Kernel acceptance
has not been established for that fixture.

Validation at the paused scoped-binding/loop checkpoint: `make -j3 all`
passed. All 13 native regression programs passed (the previous nine plus
`option_match_shadow`, `option_scope_cases`, `underscore_binding_use`, and
`loop_long_bounds`), as did the six escape-rejection fixtures. Run them with
`make -C evaluation/tests native-check escape-rejections`. The compiler
assumption audit passed 126 results (48 closed); the source audit passed 14
results (one closed). Both independent `coqchk` targets
(`compiler-kernel-check` and `soundness-kernel-check`) passed. The
assumption-checker fixtures passed 5 positive,
16 negative and 2 invocation checks. The newly registered scoped-value
relation covers scalar/pointer/unit bindings; aggregate copied views and
whole-program simulation remain open. No eBPF rebuild or Linux kernel run
was performed for this final runtime snapshot; the eBPF results below belong
to the preceding checkpoint and must not be presented as validation of these
latest runtime changes.

Validation at the rvalue/representation/tail-call checkpoint: the native and
isolated eBPF compiler builds passed. All nine native regression executables
passed, including the repaired tail-call case and the option, loop-index,
parameter-collision and guarded-arithmetic cases. The compiler assumption audit
passed 114 results (43 closed); the source audit passed 14 results. Both
independent `coqchk` targets passed. Assumption-checker fixtures passed 5 positive,
16 negative and 2 invocation checks. These checks exclude the still-open whole
simulation and, at that earlier checkpoint, the pattern-shadowing counterexample
that the newer checkpoint repairs.

The escape gate rejected all six targeted escape fixtures with the intended
diagnostic. All 45 examples and four applications compiled with the isolated
eBPF compiler. Evaluation passed 37 supported emulations, all 51 rejection
fixtures, and 33 evaluation-runner unit tests; 12 programs require kernel-specific
execution and were marked unsupported by the emulator. Saved bytecode matched
all 49 corresponding ELF sections. Source/compiler/object hash validation passed
for all 49 prebuilt programs and the separately compiled nested-option fixture.
The final proof-only inventory refresh left the compiler binary hash unchanged.
No new kernel verification or execution run is claimed.

The guarded-shift repair exposed a missing eBPF backend `Oshrlu` register-count
case in the tracing programs. It now lowers to `Palu RSH W64`. The existing
operation/compiler proofs recompiled unchanged, and `Asmgen_shift_tests.v`
checks emitted instructions and unsigned-shift behavior. Independent `coqchk`
of the backend proof and shift tests passed. All 49 evaluation
programs compile again after this repair. The earlier alleged surface Bool-read
mismatch was subsequently disproved by the checked canonical-read lemmas above.

The latest nested-option eBPF fixture compiled successfully, and prebuilt
source/compiler/object hash verification passed after exporting assembly, ELF,
disassembly, XDP-section bytecode and separate subprogram-section bytecode.
These artifacts are under `evaluation/.build/objects/xdp_nested_options.*`;
`evaluation/results/nested-options-build.json` records compilation only.
Kernel verification and execution were not run. The historical lifetime
counterexample is retained for diagnosis; equivalent programs are now tested
as required compiler rejections.

## First completed repair

`cfrontend/BeePL_memory_proofs.v`: `store_well_typed_ext` now requires
`Gamma ! x = None` and ends in `Qed`, replacing its admission. The old statement
allowed arbitrary environment replacement and could redirect a variable required
by the typing context to an unrelated block. The new lemma is explicitly a
fresh-identifier extension lemma; it does not claim arbitrary rebinding is safe.
There were no callers of this lemma to migrate.

`Print Assumptions store_well_typed_ext` reports inherited standard-library
classical/functional-extensionality assumptions, not admitted BeePL theorems.
No new axioms were introduced. This does not complete source soundness.

## Coq-checked blockers

`cfrontend/BeePL_proof_audit.v` is included in the regular build. It establishes:

| Witness | Consequence for existing proofs |
| --- | --- |
| `unsigned_min_signed_counterexample` | `ty_vali` permits `Int.min_signed` at every integer width/signedness. The admitted `int_range_invalid` lemma is false under that rule, including its narrow unsigned uses in division/modulo proofs. |
| `int32_location_invariant_counterexample` | The current `well_formed_loc` demands aligned whole-chunk access at every byte offset from zero through the chunk size. Offset 1 violates int32 alignment, so the invariant cannot describe an int32 allocation. |
| `fresh_allocation_undefined_counterexample` | A fresh four-byte allocation successfully loads `Vundef`, but BeePL rejects conversion of `Vundef`. Thus successful memory access alone does not justify `load_not_error` or initialization. |

The first two witnesses are closed under the global context. The allocation
witness uses CompCert memory lemmas and reports inherited classical/extensionality
assumptions. None of these witnesses depends on the admitted BeePL operator,
progress, preservation, or compiler-equivalence theorems. They document defects;
they must not be combined with the false admitted claims to prove arbitrary goals.

## Dependency order

### Initialized scalar memory foundation

`cfrontend/BeePL_soundness_memory.v` contains seven completed lemmas, using
definitions and CompCert memory results without importing admitted BeePL proof
modules:

- Reading an initialized scalar cell produces a value of its declared shape.
- Primitive value shape typing implies declarative value typing.
- Dereferencing such a primitive cell takes an actual BeePL small step to a
  declaratively typed value.
- Storing preserves the cell invariant when the chunk-normalized value has the
  required type.
- A store to another block preserves an initialized cell.
- Allocating four bytes and storing any int32 produces an initialized int32 cell;
  the theorem includes the actual allocation and store equations.
- Assignment to a primitive cell takes an actual BeePL small step and preserves
  its invariant under the explicit normalized-value premise.

All seven end in `Qed`; their assumptions are printed during compilation. They
have no dependency on admitted BeePL theorems. Memory lemmas inherit CompCert's
classical/extensionality assumptions. This is a foundation, **not full type
soundness**: the new invariant still needs integration with store typing,
allocation, aggregates and helper contracts. The legacy progress and preservation
theorems remain admitted. The normalized-value premise is explicit because the
legacy integer rule alone cannot justify arbitrary chunk conversions.

### Small-step boolean and comparison repair

`BeePL_sem.v` now decodes C integer boolean results into BeePL `Vbool` for
small-step negation and comparisons. Binary evaluation contexts retain the
expression's result annotation, so an integer comparison can evaluate its
operands while retaining its boolean result type. Numeric comparison reduction
uses `binary_result_type`; boolean equality and inequality have explicit rules
(the numeric rule requires a signedness, which boolean types do not have).
The negation branch in the legacy progress proof now constructs a boolean result
directly instead of using an integer-result lemma.

`cfrontend/BeePL_soundness_operators.v` independently proves boolean decoding
produces a declaratively typed value, negation and boolean equality/inequality
progress with typed results, and all six signed/unsigned int32 and int64
comparison reductions. These results import definitions, not admitted proof
modules. The big-step operator rules still need alignment with the repaired
small-step rules; no big-step/small-step equivalence is claimed. Narrow integer
promotion and the remaining arithmetic rules still require proof.

`comparison_value_preservation` and `notbool_value_preservation` quantify over
every allowed small-step successor of value operands: the successor has boolean
type and the memory and variable environment are unchanged. These complement
the earlier existential progress witnesses.

The shift guard in `check_unsafe_op` now checks its second operand (the shift
count), rather than its first operand (the payload). Four completed progress
lemmas cover left/right shifts for signed and unsigned int32/int64, for all
payloads and counts. Valid counts take the normal CompCert operation;
out-of-range counts take BeePL's zero-result rule. Each lemma also establishes
typing of the constructed result. This is not yet universal shift preservation
or a theorem about compiler output.

### Substitution machinery

`subst` previously substituted into every match branch, including branches whose
patterns bound the substituted identifier. It now uses `subst_match_branches`;
the relational `S_Match` rule uses a corresponding `SubstMatch` relation that
respects pattern binders. The helper recurses structurally on branch expressions,
so the executable substitution remains accepted by Coq's termination checker.

`cfrontend/BeePL_substitution_proofs.v` proves, for every expression constructor,
that functional substitution and relational substitution agree in both directions.
It also proves determinism of the relation and a pattern-shadowing regression.
All printed assumptions are closed under the global context. These results do
establish functional/relational correspondence. Typing preservation for value
substitution is now proved separately below. Operational `Bind` substitutes values;
capture by free variables in an arbitrary replacement expression is a distinct
issue from pattern shadowing.

`typing_context_weakening` covers every current expression and expression-list
typing constructor, including repeated context extension under pattern binders.
`value_typing_context_independent` proves that changing the variable context
does not change the typing of runtime values. Both are closed under the global
context and are prerequisites for value substitution under binders.

The small-step match context now propagates the scrutinee's resulting memory and
variable environment. The two valid option pattern orders have `Some` reductions
that substitute the payload into the selected branch, using the option payload
type. Coq checks that an identity branch returns its payload in either order.
The old rule merely selected the branch without binding the payload.
`ty_matcho` now checks branches separately under `pattern_context`: `None`
introduces no variables, `Some x` introduces the payload type, and byte patterns
introduce their declared root/field bindings. It requires valid pattern shapes,
equal pattern/branch counts, and a common result type. Each branch has its own
effect, required to be a subeffect of the match effect; different branch effects
remain supported.
`type_infer_match` was updated and proved for the repaired rule. Context and
store weakening were rechecked against this rule.

The branch typing lemmas and `none_branch_cannot_use_some_binder` are closed under
the global context. `none_match_step_preservation` proves typing and unchanged
state for every reduction of the `[None; Some x]` match on `None`, with the
selected branch effect bounded by the original effect. The `[None; Some x]` `Some`
preservation case now uses the proved value-substitution theorem. `ty_valo` now requires
typing of every `Some` payload at its declared payload type; `None` has no
payload obligation. The big-step match rules and byte
pattern reductions also remain to be aligned. Global match preservation is not
yet established.

### Allocation integration

The small-step `ssem_ref2` rule now preserves the variable environment instead of
allowing an arbitrary output environment. `reference_allocation_preserves_environment`
proves that property for every reduction of a reference applied to a value.
`typing_store_extension` proves weakening for **all** existing expression and
expression-list typing constructors, by mutual induction; it is closed under
the global context. Fresh-extension, reflexivity and transitivity lemmas support
its use across allocations.

`int32_reference_allocation` connects actual allocation and initialization to the
repaired reduction rule. Assuming every block named by the old store context is
already allocated, it establishes a fresh extending context, a typed result
pointer and an initialized result cell. This completes a concrete allocation case,
not general preservation: integration of the whole-store invariant, aggregate allocation,
arbitrary offsets and the other expression cases still require integration.
`initialized_scalar_alloc_frame` and `initialized_scalar_alloc_store_frame`
additionally prove that every previously initialized scalar cell survives allocation
and a store into the fresh block, including its typed contents and permissions.

`initialized_layout` lifts this invariant to all cells in an explicit layout,
including scalar fields at nonzero offsets within a block. The layout allocation
theorem preserves every old cell and adds the freshly initialized int32 cell.
`initialized_layout_store` preserves the entire layout under a write whose target
is present and whose byte interval does not overlap any different cell.
`initialized_layout_assignment_progress` and `initialized_layout_deref_progress`
connect these layout results to actual BeePL steps with typed results.

This layout is not yet the global source store typing: the existing `Sigma`
records only one type per block and cannot express these offset and extent facts.
Relating source locations to layout membership, supporting pointer-valued cells,
and integrating variable/function environments remain necessary. The layout
theorems are not a replacement for global progress or universal preservation.

### Remaining integration

1. Repair the store invariant to describe actual allocation extents, alignment,
   permissions, and initialized contents. State how store typings extend on allocation.
   The current global all-local/all-global variable classification also needs audit
   for mixed environments. Establish realizable initial stores, avoiding vacuous safety.
2. Align runtime values, narrow integer normalization, declarative typing, executable
   checking, and arithmetic semantics. Repair the division/modulo reasoning rather
   than retaining `int_range_invalid` as an axiom.
3. Complete allocation, dereference, assignment and substitution lemmas; then progress,
   one-step preservation and multi-step preservation. Specify external/helper contracts.
4. Repair termination/normalization statements before proving them. `normalization`
   currently universally quantifies final states and step counts, and one clause
   tests the initial expression for being a value. Audit recursion, loops, arithmetic
   endpoints, and external-call assumptions before asserting termination.
5. Resume BeePL-to-Csyntax semantic equivalence, including the existing assignment work,
   and identify the assumptions required to connect it to target eBPF safety.

No step is complete merely because a file containing `Admitted` compiles.
For each completed theorem, inspect `Print Assumptions`, check that its hypotheses
are realizable, and verify dependent files. Preserve negative examples as regression
checks. Do not strengthen a theorem's premises merely to restate its conclusion.

## Validation

```sh
make depend
make cfrontend/BeePL_memory_proofs.vo cfrontend/BeePL_proof_audit.vo cfrontend/BeePL_soundness_memory.vo
make -j4
```

`BeePL_proof_audit.v` prints its theorem assumptions during compilation. The first
repair and witnesses compile; the broader proof development remains incomplete.
Application testing is a separate source of evidence and is not a substitute for
these proofs. The UDP load balancer has passed its live test; its corrected packet
suite still needs the privileged rerun already requested.

## Option-value typing repair

`typed_option_payload` extracts payload typing from a typed `Some` value.
`some_constructor_result_typed` and `some_constructor_step_preservation` prove
that constructing an option from a typed value produces a typed option and
leaves the store unchanged. `option_int32_rejects_boolean_payload` is a
Coq-checked rejection of an invalid payload that the old rule admitted.
Value-context independence uses induction over value typing;
context and store weakening remain proved under the stronger rule. The later
nullable-reference repair below corrects the payload type and excludes nested
optional references, which do not have a distinct nullable-pointer encoding. The legacy
global soundness proofs remain unfinished.

## Structure-initializer substitution repair

`Sinit` now substitutes through its field expressions even when the initializer
label equals the substituted variable. That label is not a binder in the field
typing rule. The relational substitution rule was changed consistently, and the
full functional/relational equivalence and determinism proofs still compile.
`structure_initializer_substitutes_fields` checks the formerly skipped case.
The context shadowing and commuting lemmas needed under `Bind` are also proved.
The general value-substitution typing theorem is now completed; see below.

## Completed value substitution and binding preservation

`value_substitution_typing` covers every constructor of the current mutual
expression/expression-list typing relation. Substituting a typed value removes
its variable-context entry while preserving the expression type and exact effect.
It includes binder shadowing, branch-specific option/byte pattern contexts,
structure initializer fields, and loops. `BeePL_substitution_freevars.v` proves
that this substitution introduces no free variables and preserves the loop
disjoint-variable checks. Both main results are closed under the global context.

The admitted `subst_preservation` in `BeePL_typesystem_proofs.v` was replaced by
a proved value-substitution theorem. The former arbitrary-expression statement
did not handle capture and is not asserted as proved; the new statement matches
the value substitution actually used by `ssem_bind2` and option matching.

`bind_value_step_preservation` proves type/effect preservation and unchanged
state for every reduction of a value binding. `some_match_step_preservation`
proves type preservation, effect reduction and unchanged state for selection of
a `Some` branch in `[None; Some x]` order. These are real cases of preservation,
not a claim that global progress or preservation is finished.

## Option-match value case and scrutinee composition

`typed_option_match_shape` extracts both correctly scoped branches, their separate
effects, and either permitted pattern order from a typing derivation.
`option_match_value_progress` proves a reduction exists for every well-typed
match whose scrutinee is an option value. `option_match_value_preservation`
quantifies over every such reduction, covering `None` and `Some` in both orders,
and proves unchanged memory/environment, result typing and effect reduction.

`match_scrutinee_typing_preservation` lifts an induction hypothesis for a
scrutinee step through the match constructor, allowing an extending store
context. Branch typings are weakened to the extended context and the reduced
scrutinee effect is combined with the branch effect. This composition lemma is
closed under the global context. It does not assume global preservation as an
axiom; the scrutinee result is an explicit induction-hypothesis premise. Global
soundness, memory/store integration and byte-pattern runtime binding remain open.

## Universal scalar read/write preservation

`deref_full_deterministic` establishes uniqueness of a full-cell read. The read
preservation lemmas therefore cover every read/reduction of an initialized
primitive cell, not just the witness chosen by a progress proof.

The ordinary `ssem_massgn3` rule now requires `Full` assignment. Previously it
quantified over an arbitrary bitfield even though the reference assignment
expression contains no bitfield selector. This allowed unrelated bitfield writes
as successors. Explicit bitfield memory operations remain separate relations.

`full_scalar_assignment_store` identifies the actual CompCert store performed by
a full scalar assignment. `initialized_layout_assignment_step_preservation` then
proves that every permitted assignment reduction preserves the complete
nonoverlapping cell layout and returns a typed unit value with the same variable
environment. Integer/long normalization lemmas derive the required stored-value
type from the access mode for all integer widths and signednesses. The resulting
integer/long assignment preservation theorems do not require an extra
normalized-value typing premise. Boolean memory representation is repaired below. Pointer memory representation
and connection of source store typing to the layout remain unresolved.

## Boolean memory and primitive allocation

`decode_memory_value` decodes a boolean cell to `Vbool` instead of the generic
`Vint` conversion. Full-cell and bitfield reads use the declared type for this
decoding. The initialized-cell invariant and its preservation proofs now use
this decoder. Boolean assignment explicitly stores `Val.of_bool` with `Mbool`;
it cannot choose an arbitrary noncanonical integer representation.

`allocate_initialized_boolean` proves a real one-byte allocation and canonical
initialization. Boolean assignment progress and universal step preservation
preserve the entire compatible cell layout. Previously completed primitive
read preservation now applies to these inhabited boolean cells.

`chunk_of_ptype` now selects the actual boolean/8-bit/16-bit memory chunks, rather
than using a 32-bit chunk for one- or two-byte allocations.
`primitive_chunk_access` and `primitive_chunk_size` prove agreement with access
mode and allocation size. `allocate_initialized_primitive` and
`primitive_reference_allocation_progress` cover all primitive widths and both
signednesses under the existing nonvolatile-access requirement. These proofs
include initialization and the actual reference-allocation small step.

`safe_deref_valid_pointers_gc` was corrected to require initialized, decodable
contents and the actual access mode. Its old proof invoked the false admitted
`load_not_error` assertion. The repaired proof does not use that assertion. The
unused application of the old lemma in the unfinished assignment proof was
removed. Pointer cells, full store integration and global soundness remain open.

## Declaratively typed memory and allocation

`cfrontend/BeePL_soundness_store.v` strengthens initialized cells by requiring
that decoded contents have an actual `type_expr` derivation under the store
context. Shape checks alone did not establish this for reference-valued contents.
The new invariant implies the earlier initialized-cell invariant, and primitive
initialized cells can be lifted to it without additional hypotheses.

Completed proofs cover:

- Typed reads and preservation for every full-cell read; lifting these results to
  small-step dereference progress and universal preservation.
- Store-context extension, compatible writes and disjoint-write framing.
- Allocation framing, including initialization of a fresh block while preserving
  all existing cells and their declarative typings.
- Primitive reference allocation progress with an extending store context and
  an extended cell layout, for every primitive width and signedness.
- Universal primitive reference allocation preservation, using determinism of
  the actual allocation step. The result also preserves validity of every block
  named by the extended store context, allowing subsequent allocations.

These lemmas end in `Qed`. The checked assumption reports contain only inherited
CompCert/classical/extensionality assumptions, not admitted BeePL results. The
module is included in both the regular build and isolated compiler source copy.

This is not yet global type soundness. In particular, source reference typing
currently permits any offset into a block named by the store context. The
new dereference theorems explicitly require membership of the accessed cell in
the typed layout; the current source typing rule alone cannot establish that
premise. Reference-valued contents having a declarative type similarly does not
prove that their target offsets are safe. Source-store/layout consistency,
aggregate and array accesses, calls, byte-pattern matching and the remaining
operator cases still need integration or repair before the admitted global
progress and preservation theorems can be replaced.

## Variable reads and the reference-offset counterexample

`variable_layout` resolves each variable independently, allowing mixed local and
global bindings and respecting local shadowing. `typed_variable_progress` and
`typed_variable_preservation` establish actual small-step progress and universal
preservation using the typed cells reached by that lookup. Layout extension
preserves lookup evidence. `variable_layout_rebinding` proves that changing both
the typing entry and its local binding is sound when the new cell belongs to the
layout. This differs from the old lemma that updated only the environment while
keeping the original typing context.

The formerly admitted `well_typed_val_expr` in `BeePL_typesystem_proofs.v` now ends
in `Qed`. Its corrected statement requires membership in a typed memory layout
and a full-cell read, and concludes value typing with the empty effect. It does
not assert the old, false claim that a bare read gives any desired effect and
sufficient store-context evidence for a loaded reference. Its assumptions contain
only inherited classical/extensionality assumptions; it uses no admitted BeePL
lemma. Global progress and preservation are still admitted.

`BeePL_proof_audit.v` now proves that an int32 reference at offset one is typed by
the current block-only reference rule, but that dereferencing it has no small
step in any memory. The failure follows from CompCert's int32 alignment
requirement. These are checked counterexample lemmas, not assumptions. They show
why a nonvacuous global memory invariant must be paired with offset-aware
reference typing or a preserved runtime-location invariant; validity of the
block alone cannot close progress. Legitimate subobject references must remain
representable in that repair.

## Runtime location evidence

`cfrontend/BeePL_runtime_locations.v` adds an explicit runtime-location invariant.
A location context records allowed block/offset/type triples. Value validity
recurses into option payloads; expression validity checks embedded values and
`Addr` nodes throughout every expression constructor. There is no zero-offset
restriction. Context extension preserves validity, and value substitution
preserves it across all constructors, including shadowing and match branches.
Those two metatheorems are closed under the global context.

For scalar references, the context is derived from exact typed cell membership.
`memory_locations` additionally requires references read from those cells to be
valid in the location context. Dereference progress and universal preservation
now consume reference-location evidence rather than a separate, unexplained
cell-membership assumption, and produce both declarative typing and runtime
location validity for the result. Primitive-only typed layouts satisfy the
memory-location condition for any location context. The checked regression
`located_int32_rejects_unaligned` excludes the offset-one counterexample, while
`scalar_reference_at_cell` accepts any offset backed by a cell in the layout.

Actual value-binding and value-match reductions preserve runtime location
validity, including substitution of reference-containing option payloads. The
match lemma proves only location preservation; it does not repair the incomplete
byte-pattern semantics or claim its type preservation.

This invariant is a component of the required runtime configuration theorem,
not a completed replacement for global soundness. It still needs preservation
through allocation, mutation, aggregate access, calls and all evaluation
contexts, plus establishment from initial program states. Aggregate locations
need their own layout evidence rather than a fictitious scalar read of a whole
aggregate. The existing block-only reference typing rule and the legacy global
admissions are unchanged in this step. The new module is part of both regular
builds and the isolated compiler source copy.

`full_read_alloc_store_frame` proves that allocation and initialization of a
fresh block preserve the actual value read from every existing full cell.
`memory_locations_primitive_allocation` uses this fact to preserve the validity
of references stored in old cells under the extended scalar location context;
new primitive contents are location-valid by their checked declarative typing.
The theorem takes the allocation/store equations and the previously established
typed resulting layout, and is checked without admitted BeePL dependencies.

## Location validity through allocation and mutation

`located_primitive_reference_preservation` now covers every actual primitive
reference-allocation successor with all of: extended store typing, valid store
blocks, result typing, the extended typed memory layout, reference validity in
its contents, and runtime validity of the returned reference. It combines the
checked allocation equations with the framing result above, rather than assuming
that old reference payloads remain valid.

`full_read_store_disjoint` preserves actual values at disjoint cells, including
nonoverlapping cells in the same block. `memory_locations_store` uses this to
preserve reference validity throughout a compatible write. The target cell is
checked against the actual chunk-normalized value. `located_layout_store`
combines this result with declarative cell typing and successful CompCert storage.

`located_assignment_preservation` lifts these results to every actual assignment
successor for a generically encoded value. Its normalized-value typing and
location-validity premises are explicit. The separate
`located_boolean_assignment_preservation` handles the canonical boolean encoding
without those extra normalization premises. Both preserve store-block validity,
typed memory and stored-reference validity, and return a typed, location-valid
unit value with an unchanged variable environment. These theorems are checked
without admitted BeePL dependencies. They do not complete the global induction,
aggregate/call cases, or establishment of runtime invariants at program entry.

## Structure-field value semantics

The compiler translates field access to C `Evalof (Efield ...)`, which loads the
field value. The former small-step rule instead returned the computed address
annotated with the field's result type. `ssem_sfield2` now performs `deref_addr`
using the resolved offset and bitfield descriptor and returns the loaded value.
The big-step rule does the same, uses the structure identifier from the base
expression's type, and preserves the memory/environment resulting from base
evaluation. Previously it could look up an unrelated structure and discard the
base expression's effects.

`cfrontend/BeePL_soundness_fields.v` proves progress and universal preservation
for full-cell scalar field reads whose resolved field cell is in the typed
layout. Result preservation includes runtime reference validity.
`scalar_field_big_step_result` establishes the corresponding typed big-step
result after base evaluation. `integer_field_result` is a regression theorem:
every such integer-field step returns `Vint`, never an address mislabeled as an
integer. All proofs are checked without admitted BeePL dependencies.

This does not finish structure soundness: initialization must establish the
field layout, base structure typing must imply the required field evidence,
and aggregate-valued fields, bitfield typing and read effects still need work.
No global big-step/small-step or compiler equivalence is claimed.

The regular and isolated compiler builds include the new field module. The
Makefile now refreshes Coq dependencies automatically when sources or the module
list change, including direct `.vo` targets. Dependency output is replaced only
after successful analysis, preventing stale import ordering and partial lists.
The complete rebuild passed after the semantics change; the final field
regression lemmas were then checked with the module target.

## Local allocation context threading

`alloc_variables_con` now threads the intermediate extended store context
`Sigma1` into the allocation of the remaining variables. Previously it recursed
with the original context while requiring the final context to equal the
intermediate one. For an ordinary singleton allocation from an empty context,
the recursive empty-list rule could therefore not hold.

`cfrontend/BeePL_allocation_proofs.v` proves allocation exists for every list of
local declarations, including an explicit singleton-allocation regression.
Further checked results establish extension and block validity of the final
store context, preservation of existing typed memory cells and expression
typings, and preservation of unshadowed variable lookups. The combined
`alloc_variables_preparation` theorem gives a real allocation preserving old
variable/layout evidence when the new declarations do not shadow that context.
It does not claim the new cells are initialized. These results introduce no
admissions and use no admitted BeePL theorems.

The complete rebuild passed after the allocation-rule correction. The new
allocation module and its final combined theorem passed their Coq target checks
and are registered in regular and isolated builds. Structure initialization and
function-entry initialization still need to establish typing of new contents.
In particular, the legacy structure initializer also needs its expression/result
type agreement, base offset, field environment, and final state corrected; the
allocation repair alone does not make that case complete.

## Structure initialization model repair

`sem_allocate_fields` now takes one explicit global environment for the entire
initialization. Previously each field step could choose an unrelated environment
and consequently unrelated offsets. Structure initialization now allocates the
structure's size at offset zero, writes fields using that environment and the
argument types, and returns the initialized memory. Its result annotation is
preserved. `structure_result_type` retains both structure-value and
reference-to-structure results, matching compiler-supported forms. Big-step
initialization retains the environment produced by argument evaluation;
small-step initialization requires value arguments before allocation.

The declarative initializer rule now requires its constructor tag to match the
annotated structure, its field list to equal the declaration's nonpadding field
names, and the corresponding field/type arity. The executable frontend already
requires an exact ordered field list. `typed_structure_initializer_complete`
checks these declarative consequences. This does not add a proof that every
frontend-accepted structure expression has a declarative typing derivation.

`BeePL_initialization_proofs.v` also checks field-list arities, characterizes
value-list stuttering and actual initializer successors, and proves primitive
first writes create initialized cells from valid allocated space. The latter
covers boolean and all integer widths without assuming preinitialized contents.
`initialize_single_primitive_field` realizes an actual field-initialization
relation at its resolved full-cell offset. These proofs introduce no admissions.

The revised shared definitions passed a complete rebuild; the new initialization
module and single-field result passed targeted Coq checks. The full multi-field
layout theorem, derivation of permissions from valid composite layouts,
aggregate-valued contents, bitfields, structure-value typing, and global
soundness remain unfinished. No compiler equivalence is claimed by these source
semantics repairs.

## Initialization of multiple primitive fields

`initialize_primitive_fields` now constructs an actual `sem_allocate_fields`
derivation for a list of primitive fields and proves the resulting extended
layout is declaratively typed. The premises specify each resolved full-cell
offset, primitive value shape, nonvolatile type, allocated permissions,
nonoverlapping fields, and separation from previously initialized cells. Its
induction adds each initialized field to the protected layout before writing
the remaining fields, so later writes must preserve earlier initialization.

`primitive_structure_initialization_progress` performs a real structure-sized
allocation and small-step constructor reduction. It derives permissions from
field bounds/alignment and protects existing cells using allocation freshness.
`extend_field_layout_member` and `initialized_planned_field_read` then prove that
every planned primitive field is in the final typed layout and has an actual
typed field-read step. All added theorems passed Coq checks and assumption audits
without admitted BeePL dependencies; `git diff --check` also passed.

The remaining obligation is not to assume these layout facts at every source
use: a valid composite environment and the source typing derivation must imply
the bounds, alignment, field separation and field/value plan. This step does not
cover pointer/aggregate-valued fields or bitfield layouts, prove preservation for
every possible constructor successor, or finish the global soundness induction.

## Layout facts derived from composite declarations

`BeePL_layout_proofs.v` proves that lookup in the translated composite environment
agrees with lookup and translation in the BeePL environment. From CompCert's
checked field-layout theorems, it derives primitive field bounds and alignment,
representability of offsets, and nonoverlap of distinct full-cell fields. The
plan-level results discharge the earlier explicit bounds/separation obligations
using composite consistency, representable object size, matching field types,
distinct field names, and compatible natural alignment.

`primitive_structure_progress_from_layout` combines those derived facts with
actual allocation/initialization progress. Default-alignment compatibility is
proved for targets with eight-byte 64-bit integer alignment. Consistency of
translated composite environments must still be established from BeePL program
construction, and source typing must still supply the field plan. These are
explicit remaining premises, not admitted assertions.

The eBPF target incorrectly used four-byte `align_int64`, while `Mint64` memory
accesses require eight-byte alignment. It now uses eight bytes, consistent with
[LLVM's BPF target definition](https://github.com/llvm/llvm-project/blob/main/clang/lib/Basic/Targets/BPF.h),
which gives `long` 64-bit width and alignment. Regression lemmas check both the
64-bit target alignment and an eight-byte offset for a 64-bit field following a
32-bit field. They are checked under both the host and isolated eBPF targets.

Validation: the isolated eBPF compiler rebuilt successfully; `make -C
evaluation/examples check` passed. All 49 programs compiled, 37 supported
emulations passed, 43 rejection cases passed, and 33 tool unit tests passed.
Twelve programs are not supported by the emulator. Kernel tests were not
requested or rerun, so prior kernel reports are not fresh evidence for the rebuilt
compiler. The new proofs introduce no admissions. Global soundness remains open.

## Composite completeness and the intrinsic Bytes gap

`translated_pointer_complete`, `translated_type_complete`, and
`translated_members_complete` establish completeness of translated pointers,
types, and member lists. The last two explicitly require a `bytes_t` entry in
the BeePL environment: `Bytes` translates to that struct, whereas BeePL's
completeness predicate accepts `Bytes` unconditionally.

`constructed_composite_consistent` proves consistency of a successfully built
composite when its translated members are complete.
`constructed_composite_consistent_with_bytes` derives that premise from source
construction and a present `bytes_t` entry. These are conditional results;
an arbitrary empty environment does not satisfy the Bytes premise.

The audit contains `bytes_member_completeness_mismatch` and
`bytes_composite_consistency_counterexample`. Coq checks that the raw
single-definition builder accepts a one-field Bytes struct whose translation
is not consistent if invoked on an empty environment.
The latter witness is closed under the global context. Thus unconditional
environment consistency cannot hold for arbitrary unseeded calls.
This originally prevented an unconditional program-environment theorem.

The public `build_bcomposite_env` now installs `bytes_bcomposite_definition`
before processing user declarations. C translation uses that same shared
definition and emits it even when Bytes occurs only in fields or parameters.
The reserved composite name is protected by the existing duplicate-definition
check. Supported Bytes programs are retained; the source builder now calculates
their enclosing structure layouts with the real two-pointer representation.

`built_source_composites_consistent` and
`built_translated_composites_consistent` prove consistency for every successful
public build, without an extra Bytes premise. `program_composites_consistent`
obtains this directly from `prog_comp_env_eq`.
`program_primitive_structure_progress` uses this property for the program's
actual global environment; callers no longer supply a consistency assumption.
The construction/consistency theorems are closed under the global context.
`program_type_completeness` also establishes equality of source and translated
completeness predicates for every type in a constructed program, using the
proved preservation of the intrinsic Bytes entry.
The regression `built_bytes_field_layout` checks that a single-Bytes-field
struct receives two pointer-widths of storage through the public builder.
The raw-builder counterexamples remain as witnesses for why seeding is needed.
The primitive-structure result still requires valid field plans, a typed input
memory, representable size, and the other stated layout conditions. It is not
the full language progress or preservation theorem.

Validation after the repair: the host `make -j4` completed, the isolated eBPF
compiler rebuilt, and `make -C evaluation/examples check` passed. Kernel tests
were not rerun. The proof modules also checked directly, and `git diff --check`
passed. No admissions or project axioms were added.

## Typed initializer arguments and declared member types

The former admission `type_rel_typeof_val` in `BeePL_typesystem.v` is now
proved by inversion on value typing. This establishes the existing
`typeof_value` shape predicate; that predicate alone does not establish pointer
validity or recursive option-payload safety.

`typed_planned_arguments` derives primitive value shapes and the precise
argument-type list from declarative typing of planned initializer expressions.
`primitive_member_type_from_typing` and `planned_member_types_from_typing`
connect the successful member lookup and reverse type translation used by
`ty_sinit` to the actual declared C field types. The nonvolatile premise matters:
member lookup propagates volatile attributes rather than simply returning the
unmodified field type.

`typed_structure_plan_facts` combines those results for a typed structure
initializer. `typed_primitive_structure_progress` now derives both value shapes
and matching declared field types from source typing, then applies the checked
allocation and initialization result using the actual program global
environment. It still explicitly requires valid full-cell offsets, distinct
field names, nonvolatile/default-alignment fields, representable structure
size, the target alignment condition, and typed input memory. Constructing a
field plan from arbitrary source argument lists, handling aggregate/bitfield
initializers, and the global progress/preservation induction remain unfinished.

Validation: `make -j4 proof` and `git diff --check` passed. New results were
audited with `Print Assumptions`; no admitted BeePL theorem is used. This step
changes proofs only, so compiler execution and kernel tests were not rerun.

## Resolve structure field plans from source initializers

`BeePL_structure_proofs.v` removes preselected offsets from the primitive
structure progress result. `plain_field_offset_exists` derives successful
full-cell offset lookup from declared type lookup for ordinary members.
`resolve_primitive_fields` computes those offsets, and its checked specification
preserves field names, value expressions, and member types.

`primitive_arguments_plan` constructs a plan from matching source field-name
and primitive-value argument lists. `source_primitive_structure_progress` uses
the source typing derivation to obtain the matching lengths and declared field
types, resolves actual offsets, then proves a real allocation/initialization
step and the resulting typed field memory. No caller-supplied offset, matching
field type, or composite-consistency premise remains.

This is still a constructor-specific progress result: input memory must be
typed, members ordinary and nonvolatile with the stated alignment properties,
field names distinct, and the structure size representable. It does not yet
handle bitfield/aggregate initializers, arbitrary argument evaluation, or prove
preservation for every possible successor. Extending the store context to type
the fresh structure reference is also a separate remaining obligation.
These limitations are not removed from the overall type-soundness objective.

Validation: the new module is included in the proof build and isolated compiler
source-copy list. Coq checked its proofs and `Print Assumptions` reports only the
standard CompCert classical/extensionality assumptions for the execution result;
the plan construction/specification lemmas are closed under the global context.

## Fresh structure references and actual successor agreement

`assignment_preserves_valid_blocks` covers all current assignment constructors,
including copies and bitfield writes; `field_initialization_preserves_valid_blocks`
lifts this to an entire field initialization. These preserve block validity,
not arbitrary field contents or permissions.

`initialized_structure_store_extension` adds the freshly allocated structure
block to the store context, proves that previous entries are unchanged, keeps
all entries mapped to valid blocks, weakens the final typed memory layout to
that context, and types the returned structure reference.
`source_primitive_structure_typed_progress` combines this with source-level
primitive initializer progress. It assumes initial `store_blocks_valid` as well
as the earlier memory/layout conditions. This closes the fresh-reference typing
obligation for the constructed successor; it is not a global preservation proof.

`primitive_assignment_to_store` and `primitive_assignment_deterministic` connect
actual full-cell primitive assignments to their unique memory-store result.
`planned_initialization_deterministic` proves uniqueness of initialization
memory for valid primitive field plans. `planned_structure_successors` then
classifies **every** step from the value initializer: it is either the existing
expression-list stutter or agrees with the constructed completing step in
memory, variable map, and returned value. This prepares the transfer of the
constructed successor's invariants to arbitrary successors. General argument
evaluation, aggregate/bitfield initializer soundness, and the full language
induction remain open.

All new results were checked with Coq and audited with `Print Assumptions`;
they use no admitted BeePL results or new axioms. Execution results retain only
the usual CompCert classical/extensionality assumptions.

## Universal preservation for primitive value initializers

`planned_primitive_structure_preservation` now transfers the constructed
successor's invariants to every actual small step, using the checked successor
agreement theorem. It covers both the expression-list stutter and completed
initialization. `source_primitive_structure_preservation` states the result
directly over source field-name and argument lists, constructing and resolving
the field plan internally.

The conclusion preserves the variable map, the original result type and effect
annotation, every existing typed field location, typed memory, and valid store
blocks under a store-context extension. `value_arguments_effect_nil` proves the
needed empty-effect fact for value argument lists; it does not assume the old
admitted effect-soundness results.

The result remains conditional on the explicit primitive-value, ordinary-field,
nonvolatile/default-alignment, distinct-name, representable-size, target-alignment,
and input memory/store invariants. It does not yet cover argument evaluation,
aggregate or bitfield initialization, all runtime-location invariants, or the
global induction over the language. Those are still part of the original goal.

Validation: `make -j4 proof` and `git diff --check` passed. `Print Assumptions`
shows no admitted BeePL dependencies; only standard CompCert
classical/extensionality assumptions remain. This change is proof-only.

## Repair array execution before proving its typing rules

The array operational model had several concrete defects: recursive
initialization discarded the head value, advanced one byte irrespective of
element size, and used an independently chosen global environment at each
element; allocation then looked up the new variable in the old variable map.
The final small step returned the initializer again, and reads used a raw
index as a byte offset without an array-bound premise.

`sem_array_init_helper` now fixes the environment, consumes `v :: vs`, and
advances by the element size. `sem_array_init` uses the allocated variable map
and requires the declared length to equal the value count. Completion requires
value arguments and returns the allocated location. Big- and small-step array
access now require the declared bound and element result type and multiply the
index by element size. These are repairs to the Coq operational model;
compiler C translation already uses typed pointer addition and checks bounds.

`BeePL_array_proofs.v` checks empty/singleton initialization behavior, declared
length, valid-block preservation, and progress/preservation of typed cell reads.
It proves that out-of-bounds array accesses cannot step under the repaired rules.
`initialize_int32_pair` performs both stores and proves that the resulting
memory reads back the exact first and second input values at offsets 0 and 4,
with initialized typed cells retained at both locations. Index/offset regressions
also cover the third int32 element at offset 8.

Array type soundness is not complete. The declarative typing rules still need
matching bounds/length/result-annotation constraints and a sound treatment of
array variables and returned array locations. The present typed-read results
explicitly assume the appropriate variable-map binding and typed cell; they do
not derive these from the existing `ty_aaccess` rule. Initialization preservation
and integration with argument evaluation/global soundness remain open.

Validation: the full `make -j4 proof` rebuild passed after the semantic changes,
and the exact-value regression checked afterward. No admissions were added;
assumption audits use no admitted BeePL theorem. Compiler bytecode and kernel
tests were not rerun for this operational-model change.

## Array extent, bounds, and returned-location typing

`ty_ainit` now requires matching input/result array annotations and a declared
extent equal to the argument-type count. `typed_arguments_length` connects this
to the actual source expression count. `ty_aaccess` now requires an exact element
result type and an in-bounds index for that array extent. These agree with the
existing frontend checks; they do not reject previously supported valid array
programs. Rejection proofs cover out-of-bounds accesses, mismatched initializer
annotations, and insufficient initializer elements. A positive proof retains
the ordinary two-element int32 initializer.

`ty_valarray` types the base location returned by initialization, requiring the
matching array entry in the store context. It permits only offset zero.
`array_location_typing_entry` recovers both facts from a typing derivation.
The coarse `typeof_value` shape predicate recognizes array locations; memory
validity is still a separate invariant. The old `type_infer_loc` result is now
explicitly restricted to non-array results, and its callers/induction cases
were updated. This avoids incorrectly treating array locations as references.

`singleton_allocation_maps` proves the exact variable-map and store-context
updates made by one allocation. `array_initialization_store_typing` combines
that result with valid-block preservation through element stores: initialization
extends the input store context, retains valid store blocks, and returns a
correctly typed array location. It does not yet prove all initialized element
contents or the full preservation invariant for arbitrary array small steps.
The legacy function-store allocation proof remains admitted for its outstanding
obligations; its location case now explicitly accounts for both reference and
array values. No new proof depends on that admitted result.

The array-variable binding invariant and its interaction with substitution
remain open: `ty_aaccess` still needs a sound connection to the runtime array
binding. The changes here do not constitute full array or language soundness.

Validation: `make -j4 proof` and the positive/rejection Coq regressions passed.
Assumption audits add no axioms or admitted BeePL dependencies. No compiler
backend or emitted bytecode change was made; kernel tests were not rerun.

## Array initialization: caller context and existing-state preservation

`singleton_allocation_rebase` and `array_initialization_rebase` prove that the
operational rules' auxiliary store bookkeeping can be replaced with the
caller's store context without changing allocation, element writes, variable
maps, or resulting memory. This matters because `ssem_array_init3` quantifies
over an auxiliary context, which need not initially equal the typing context.
`completed_array_store_preservation` obtains a valid context extension and typed
result for an actual completing step using the caller's context.

`array_value_initializer_step_shape` classifies all steps with value arguments
as stutters or completed array locations.
`array_value_initializer_type_preservation` combines this classification with
context rebasing for universal result-type/store-validity preservation.

The memory frame lemmas cover every current assignment constructor, including
storebytes copies and bitfields. They show that array initialization writes only
its fresh block and therefore retains the typed contents of previously existing
cells. `array_value_initializer_frame_preservation` combines these facts: every
step preserves result typing, valid store blocks, the existing typed-memory
layout under the extended context, and all other variable bindings.

This theorem intentionally states preservation of the **old** layout. It does
not yet add a typed cell for each newly initialized array element, establish
the array-variable binding invariant, or handle non-value argument evaluation.
Those remain necessary for subsequent array-read progress and global soundness.
Validation: `make -j4 proof` and `git diff --check` passed; assumption audits
introduce no admissions or new axioms and use only standard CompCert
classical/extensionality assumptions where applicable.

## Arbitrary-length primitive arrays and initialized reads

`primitive_array_frame_before` proves that a suffix of element stores preserves
a typed cell preceding it. The proof uses primitive element size and a total
extent bound to rule out wrapped pointer addresses. It covers arbitrary list
lengths rather than just the earlier two-element regression.

`primitive_array_initialized_cells` proves a typed cell for every in-bounds
element after an actual primitive-array initialization. It derives each store
from the assignment semantics, accounts for scalar normalization, and protects
earlier cells from later writes. `allocated_primitive_array_access` derives the
required initial permissions and alignment from the actual array allocation.

`primitive_array_initialization_memory_layout` combines those results with the
old-memory frame: the output layout includes all previous cells **and** every
new array element. `initialized_primitive_array_read` then proves that any
in-bounds read through the resulting array binding steps to a value of the
declared primitive element type.

The premises still include successful initialization, well-shaped primitive
values, nonvolatile elements, representable total extent, and typed old memory.
Constructing arbitrary initialization from source typing, deriving these value
premises from source argument typing, preserving array bindings through general
evaluation, and the global soundness induction remain unfinished.

Validation: `make -j4 proof` and `git diff --check` passed. Assumption audits
introduce no new axioms/admissions or admitted BeePL dependencies. This work
changes proofs and proof-side layout definitions, not compiler execution.

## Source-typed primitive array initialization progress

`primitive_array_elements_progress` constructs the element-store execution for
an arbitrary-length list from valid allocation permissions; it does not assume
that initialization has already succeeded. `primitive_array_initialization_progress`
constructs the allocation and the entire array initialization.

`primitive_type_equality_sound`, `primitive_value_arguments_shape`, and
`typed_primitive_array_arguments` connect source typing to the required primitive
value shapes and exact extent. These lemmas avoid the older admitted general
type-equality lemmas.

`source_primitive_array_progress` now starts with a typed initializer whose
arguments are values and constructs an actual small-step completion. It proves
an extending store context, valid store blocks, a result of the same type/effect,
and a memory layout containing both the old cells and all initialized array
cells. It retains explicit nonvolatile and representable-extent premises, as
well as the input memory invariants. General argument evaluation, array binding
preservation, aggregate element initialization, and global progress/preservation
remain unfinished; this is not a whole-language soundness theorem.

Validation: the array module and full `make -j4 proof` build pass, with
`Print Assumptions` showing no admitted BeePL dependencies or new axioms for the
new results (only inherited standard CompCert classical/extensionality axioms).

## Universal primitive-array initializer preservation

`completed_primitive_array_preservation` handles an arbitrary actual completing
step, rebasing the semantics' ghost store context onto the caller's context. It
proves the result type/effect, valid store blocks, the installed array binding,
and typed memory for every new element as well as the previous layout.

`source_primitive_array_preservation` covers every permitted successor of a
source-typed primitive-array initializer with value arguments. The existing
semantics permits a value-list stuttering step; that case retains the original
state and layout. The completing case extends the layout with the new element
cells. Both cases preserve existing layout entries and every other variable
binding. This strengthens the earlier old-layout-only preservation theorem and
complements `source_primitive_array_progress` without assuming the actual step
is the witness constructed by progress.

The explicit nonvolatile, extent, and input-memory premises remain. In
particular, these results do not establish the missing connection between an
arbitrary `Aaccess` expression and its runtime binding, nor preservation while
initializer arguments themselves evaluate. Global soundness remains incomplete.
Validation: the array module, `make -j4 proof`, and `git diff --check` pass;
assumption audits show no admitted BeePL dependencies or newly added axioms.

## Primitive array runtime bindings

`primitive_array_bindings` records that every primitive array in the runtime
variable map has a nonnegative extent and initialized layout entries for all
in-bounds indices. The empty runtime map satisfies it. The extension lemma
handles both adding an array name and replacing an existing name while retaining
all unrelated bindings and their cells.

`primitive_array_bindings_read_progress` derives read progress and result typing
from this shared invariant, a matching runtime lookup, the index bound, and
typed memory. Individual cell-membership assumptions are no longer needed at
each read. `source_primitive_array_bindings_preservation` proves the invariant
survives every step of a typed primitive-array initializer with value arguments,
alongside result typing, store-context extension, valid blocks, and typed memory.

This does not yet connect every source `Aaccess` to a matching runtime lookup:
its typing rule currently lacks that binding premise, and array names are not
substituted like ordinary expression variables. Those source/runtime issues and
preservation during general argument evaluation remain open. The invariant also
currently covers primitive element arrays, not aggregate element arrays.

Validation: `make -j4 proof` and `git diff --check` pass. New theorem assumption
audits contain no admitted BeePL dependencies or newly introduced axioms.

## Array declaration followed by a read

`primitive_array_declare_read` proves an actual three-step execution for the
parser's `Bind arr ... (Ainit arr ...) (Aaccess arr ...)` declaration/read shape:
initialization, binding substitution, then indexed read. It starts from source
typing of the initializer, value arguments, nonvolatile/extent conditions, an
index bound, and input memory invariants. It derives the runtime lookup from
initialization, rather than assuming a binding at the read site, and returns a
typed primitive value with valid store blocks and the extended typed layout.

The proof audit now contains two explicit regression witnesses:
`unbound_array_access_typable` and `unbound_array_access_stuck`. Together they
show why source expression typing alone cannot justify array read progress:
the current Coq access rule permits an unbound array name. The declaration/read
result discharges that obligation for the normal declaration pattern but is not
a repair of the general typing rule or a proof for arbitrary continuation bodies.
A coherent binding discipline compatible with substitution remains necessary.

Validation: `make -j4 proof` and `git diff --check` pass. The new execution proof
and audit witnesses have no admitted BeePL dependencies or newly introduced
axioms. The full language's soundness theorem remains unfinished.

## Array argument evaluation and compositional preservation

`primitive_array_argument_step` lifts nonempty typed primitive argument-list
steps into initializer steps. It derives the head value's element annotation
from typing, which is required by the tail-evaluation constructor.
`array_initializer_retype_arguments` reconstructs initializer typing after an
argument-list typing derivation changes its store context and effect list.
`array_initializer_step_cases` classifies every actual initializer step as
argument evaluation or completion on a value list.

`primitive_array_preservation_from_arguments` combines these cases into the
array case of a preservation induction. It covers arbitrary arguments, preserves
the result type, store validity, typed memory, and primitive array bindings, and
permits the effect list to decrease according to `sub_effect`. Its explicit
premise is preservation of the argument-list step, including those same memory
invariants; that premise still needs to be discharged by the whole-language
mutual induction. This is a compositional theorem, not an unconditional proof
of arbitrary argument evaluation. The source array-name/substitution issue also
remains unresolved.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits for
these lemmas contain no admitted BeePL dependencies or newly introduced axioms.

## Shared argument-list preservation

`argument_list_preservation_from_expressions` in `BeePL_substitution_proofs.v`
proves the list case from preservation hypotheses for individual member
expressions. It carries a supplied state invariant through the actual list step,
extends the store context, weakens untouched argument typings to that context,
and combines decreasing effects using the proved effect-concatenation lemma.
It covers empty lists, head-expression steps, and tail steps past value heads.

The array argument theorem now quantifies over the particular input argument
typing derivation, avoiding an unnecessarily strong requirement for one output
context to serve every possible derivation. `primitive_array_state` packages
valid store blocks, typed memory, and runtime primitive-array bindings.
`primitive_array_preservation_from_expressions` instantiates the shared list
lemma with that state and discharges the list-level premise of the array case.

These are conditional induction lemmas: whole-language preservation for each
member expression is still required. They add no assumption that arbitrary
expressions actually satisfy that obligation, and do not resolve the source
array-name binding issue or establish the global progress/preservation theorem.

Validation: `make -j4 proof` and `git diff --check` pass. New assumption audits
show only inherited standard CompCert classical/extensionality assumptions,
with no admitted BeePL dependencies or newly introduced axioms.

## Conditional and binding induction cases

`conditional_preservation_from_guard` proves every conditional step preserves
the result type and a supplied state invariant, with decreasing effects, given
the induction hypothesis for its guard. Both branch typings are transported to
an extended store context when the guard steps. For boolean branch selection,
the state is unchanged and value typing forces the guard effect to be empty.
`conditional_progress_from_guard` derives a conditional step from guard progress;
its value case uses a checked boolean canonical-forms lemma.

`bind_preservation_from_initializer` similarly covers initializer steps and the
substitution step of a `Bind`. It transports the body typing to the extended
store context and uses the checked value-substitution result on completion.
`bind_progress_from_initializer` constructs the corresponding evaluation or
substitution step. Both progress lemmas derive the expression annotations
required by the operational rules from the proved `type_rel_typeof` lemma.

These results discharge the control-flow constructor cases conditional on the
proper subexpression induction hypotheses. They do not establish those
hypotheses for every language construct, resolve array names, or replace the
still-incomplete global soundness theorems.

Validation: `make -j4 proof` and `git diff --check` pass. The new theorem
assumption audits show no admitted BeePL dependencies or new axioms; inherited
standard CompCert classical/extensionality assumptions remain.

## Loop semantics and unit results

The previous repetition rules invoked the entire `For` expression recursively
instead of its body. The old count used wrapped subtraction, ignored direction,
and excluded the inclusive endpoint. Small-step repetition also discarded a body
after one step instead of evaluating that iteration to a value.

The semantics now uses `compute_loop_iterations`: bounds are interpreted using
their declared integer width and signedness, then an inclusive, nonnegative
mathematical-integer count is computed for `Up` or `Down`. Both big-step and
small-step repetition execute the body. The new mutual `ssem_loop_body` relation
requires each iteration to reach a value before the next iteration begins.

`BeePL_loop_proofs.v` proves nonnegative counts, inclusive/empty-range equations,
signed/unsigned regression cases, unit results for both repetition relations,
and an actual four-iteration small-step loop execution. The file is registered
in the proof build and isolated compiler source copier.

The declarative `ty_for` rule previously tested the *body* for integer type,
contradicting ordinary assignment-body examples and the operational unit result.
It now tests the bound type and requires a unit body/result. Its inversion lemma
and the Coq executable checker were updated. The OCaml frontend rejects non-unit
loop bodies, whose value the statement translation could not return correctly;
a rejection fixture records this behavior. Positive typing and result-type
lemmas cover the corrected rule.

These repairs do not prove whole-loop progress or general preservation. The
atomic loop step still requires terminating execution of each body, and a
whole-language proof must account for that requirement, state invariants across
iterations, calls, and the outstanding array-name issues. Compiler correctness
and kernel-verifier replacement are not established by these results.

Paper reconciliation: rereading `TFOR` in the supplied `beepl.pdf` shows that it
assigns the body type to the whole loop without requiring unit. That conflicts
with the existing unit-returning repetition rules, particularly for zero
iterations. The user has now approved the recommendation to make loops
unit-only: both the body and the loop result have unit type, including empty
ranges. The existing tested typing/frontend correction is therefore the chosen
language rule, not a proof of the paper's original value-producing rule. The
paper must be revised to state this rule. Earlier notes below describing this
decision as pending are historical and are superseded by this approval. The
count and body-execution repairs do not depend on the result-type choice.

The candidate passed the full Coq proof build and isolated eBPF compiler build.
Evaluation compiled all 45 examples, passed 35 supported userspace emulations
(10 unsupported), and passed all 44 rejection tests, including the new non-unit
body rejection. Kernel tests were not requested for this rebuilt compiler.
Report: `evaluation/results/loop-proof-check.json`. `git diff --check` passed.

## Completed loop bodies and repetition invariants

`loop_body_completion_iff` proves that the new body evaluator holds exactly when
there is a finite `ssem_closure` ending in a value with the same final memory and
runtime map. It therefore cannot silently discard a partially evaluated body.

`loop_repetition_preserves_state` lifts preservation of a supplied state
invariant through an arbitrary actual repetition execution.
`loop_repetition_exists` constructs finite repetition from total body evaluation
that preserves that invariant. These premises remain explicit: bounded iteration
counts alone do not establish termination or preservation of arbitrary bodies.
The results concern body completion and state evolution and do not settle the
pending paper/implementation choice about the source loop's result type.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits show
no admitted BeePL dependencies or newly introduced axioms. The global soundness
proof and the loop-result design decision remain unfinished.

## Total integer arithmetic and bitwise value cases

`BeePL_soundness_operators.v` now classifies addition, subtraction,
multiplication, and bitwise AND/OR/XOR as a proof-side family. For integer and
long operands it proves the exact CompCert operation result, decoding, and
absence of a guarded-unsafe case. Integer proofs include all declared integer
sizes and both signednesses; they concern the existing shape-based value typing,
not a new invariant restricting every value to its declared narrow-width range.

`total_integer32_value_progress` and `total_integer64_value_progress` construct
execution and a typed result. The corresponding `*_value_step_result` theorems
cover every actual successor, proving unchanged memory and runtime map and the
exact arithmetic result. The result equation also yields typing of every
successor using the integer value constructors.

Division, remainder, additional unary cases, and composition with operand
expression evaluation remain separate obligations. These results neither claim
global operator soundness nor settle the pending loop-result question.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits show
no admitted BeePL dependencies or new axioms. These additions change proof-side
operator classifications and lemmas, not compiler execution.

## Guarded division and remainder values

`division32_operation` and `division64_operation` establish the correspondence
between BeePL's unsafe-operation guard and CompCert's partial division/remainder
semantics for 32-bit integers and longs. The progress theorems handle both safe
operands and the guarded zero-result cases (zero divisor and signed minimum
integer divided by minus one). `division32_value_step_result` and its long
counterpart prove the exact guarded result for every actual successor, with
unchanged memory and runtime bindings. No safe-input assumption is required.

This does not extend to arbitrary narrow unsigned values under the current
rules. `narrow_unsigned_division_counterexample` in the proof audit is a checked
witness: shape-based typing accepts uint8 operands with the int32 minimum and
minus-one bit patterns; the unsigned guard misses overflow, but CompCert
promotes the operation to signed int32 and refuses it. The expression is typed
and stuck. General soundness requires repairing the interaction of integer
promotion and guarding (or a sufficient preserved value invariant), not assuming
those shapes never occur. No source-program exploit is asserted by this
proof-level witness.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits show
no admitted BeePL dependencies or new axioms. Compiler execution is unchanged by
this turn's proof additions. Global soundness remains unfinished.

## Promoted arithmetic guards and removal of the false range axiom

`promoted_integer_signedness` and `arithmetic_signedness_of_type` distinguish
arithmetic promotion from storage signedness. Both big-step and small-step
binary-operation safety guards now use the promoted signedness: narrow integers
operate as signed int32, while int32 and long retain their declared signedness.
This repairs the previously checked uint8 division counterexample without
assuming a range property that the value typing rules do not provide.

`promoted_integer_division_operation` proves the guard/CompCert correspondence
for every integer size. `guarded_integer_division_semantics` covers matching
integer/long values whenever the promoted guard accepts them, and
`promoted_integer_division_progress` constructs a typed successor for all integer
sizes, including the guarded cases. The audit's former stuck-expression witness
is now the positive `narrow_unsigned_division_guarded` regression.

The legacy `well_formed_div` and `well_formed_mod` proofs were replaced by short
applications of the checked guard theorem, and the unfinished global induction
now requests promoted signedness. The unused false `int_range_invalid` axiom was
removed; its independent counterexample remains in the audit. This is not a
claim that all legacy operator proofs or global soundness are free of other
unfinished dependencies.

The change repairs formal arithmetic semantics. The compiler's existing narrow
division/remainder lowering limitations are not claimed resolved by these
lemmas. The loop-result design question also remains pending.

Validation: the full `make -j4 proof` build and `git diff --check` pass. A separate
`Print Assumptions` audit of `well_formed_div` and `well_formed_mod` reports only
standard CompCert classical/extensionality assumptions, with no admitted BeePL
dependencies. No new axioms or admissions were introduced.

## Source-typed integer operations and operand progress

`BeePL_soundness_operators.v` now connects operation semantics to source typing:
`typed_numeric_value_pair` derives matching integer or long runtime shapes from
operand typing. The typed division/remainder and total-integer value theorems
prove both existence of a typed successor and preservation for every actual
successor, with unchanged memory and runtime bindings. The total family includes
addition, subtraction, multiplication, bitwise AND, OR, and XOR. All integer
sizes and both long signedness choices are covered. The promoted division result
lemma identifies the exact result, including zero returned by unsafe guards.

`binary_progress_from_operands` handles left-to-right operand evaluation.
`division_progress_from_operands` and `total_integer_progress_from_operands`
instantiate it using source typing and the checked value cases. Their operand
progress premises are the intended expression-induction hypotheses; these are
not unconditional whole-language progress theorems. Preservation while operands
step still needs integration with the shared runtime-state invariant.

The new proofs contain no admissions. Their assumption audits show only the
standard CompCert classical/extensionality assumptions. The global progress and
preservation theorems remain unfinished, and the loop-result design question
remains pending.

Validation: `make -j4 proof` and `git diff --check` pass after these additions.
No compiler execution or kernel test claims are added by this proof-only work.

## Preservation through binary operand evaluation

`binary_preservation_from_operands` supplies the preservation evaluation-context
case for binary operations, parameterized by a state invariant `Q`. An operand
step may extend the store context and reduce its effects. The untouched operand
is retyped under the extended context using `typing_store_extension`, and the
two effects are combined using `sub_effect_concat`. Completed value operations
retain the original state and have no remaining effects.

`division_preservation_from_operands` and
`total_integer_preservation_from_operands` discharge the operation-specific
premises using the source typing rules and the checked value preservation
lemmas. Thus division, remainder, addition, subtraction, multiplication, AND,
OR, and XOR now have both progress and preservation cases suitable for a
whole-expression induction. The preservation premises are precisely the
operand induction hypotheses under `Q`; they do not assume preservation of the
whole binary expression. Selecting and proving a state invariant for the full
language, and completing the other expression cases, remain outstanding.

Validation: the full `make -j4 proof` build and `git diff --check` pass.
`Print Assumptions` on the generic and specialized preservation lemmas reports
only standard CompCert classical/extensionality assumptions, with no admitted
BeePL dependencies. No runtime semantics or compiler behavior changed here.

## Shift progress and preservation

The shift proofs now cover every integer size and 64-bit values, including
signed and unsigned types. `shift32_operation` and `shift64_operation` prove
that the existing safety guard agrees with CompCert's shift semantics.
Narrow integer right shifts use promoted arithmetic signedness; out-of-range
counts use BeePL's defined zero result. The exact-result theorems describe all
successful small-step successors and prove memory and runtime bindings unchanged
for a completed operation.

`typed_shift_value_progress` and `typed_shift_value_preservation` derive operand
shapes from source typing. `shift_progress_from_operands` and
`shift_preservation_from_operands` cover left-to-right operand evaluation with
expression induction hypotheses, including store extension, an arbitrary state
invariant, and decreasing effects. This closes another operator case for the
planned whole-language induction, without claiming that induction is complete.

The new theorem assumption audits contain no admitted BeePL dependencies or new
axioms; only standard CompCert classical/extensionality assumptions occur.
No runtime semantics or compiler behavior changed in these additions.

Validation: `make -j4 proof` and `git diff --check` pass after the shift proofs.

## Comparison typing and evaluation contexts

The shared binary progress/preservation lemmas now distinguish operand type
from result type. Existing arithmetic, division, and shift instantiations retain
the same type for both. Comparison instantiations use a boolean result.

`promoted_integer_comparison_value_progress` extends comparison progress to all
integer sizes. `comparison_value_progress_from_types` covers all six numeric
comparisons for integer/long operands and boolean equality/inequality, deriving
runtime value shapes from typing. `comparison_typing_components` retains the
operator-specific allowed operand types, so ordering on booleans is not assumed.
`comparison_progress_from_operands` and
`comparison_preservation_from_operands` connect these value results to the
shared evaluation-context proofs, carrying store extension, the state invariant,
and decreasing effects. These are induction cases, not a completed proof for
the whole language.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits of the
new comparison theorems report only standard CompCert classical/extensionality
assumptions, without admitted BeePL dependencies. Runtime semantics and compiler
behavior are unchanged by this work.

## Unary operator progress and preservation

`typed_integer_unary_value_progress` and
`typed_integer_unary_value_preservation` cover negation and complement for all
integer sizes and 64-bit values. They derive value shapes from typing and prove
that a completed operation preserves memory and runtime bindings.
`typed_unary_value_progress` and `typed_unary_value_preservation` combine these
with boolean negation and exclude the untyped floating-point unary operation
by inversion of the source typing rules.

`unary_progress_from_operand` and `unary_preservation_from_operand` cover the
evaluation-context cases, using the operand's type/annotation equality, store
extension, an arbitrary state invariant, and decreasing effects. These complete
the unary operator induction cases but do not resolve the outstanding full
language invariant, function, array-binding, or loop obligations. No runtime
semantics or compiler behavior changed in these additions.

Validation: `make -j4 proof` and `git diff --check` pass. Assumption audits of the
new unary theorems show only standard CompCert classical/extensionality
assumptions, without admitted BeePL dependencies or new axioms.

## Option constructors and payload preservation

`some_typing_components` recovers the payload type from source typing.
`none_progress_preservation` constructs the `None` value step, and
`none_step_preservation` covers every actual successor. For `Some`,
`some_value_step_preservation` retains the typed payload derivation required
by option-value typing and later branch substitution.

`some_progress_from_operand` and `some_preservation_from_operand` handle payload
evaluation, with store extension, a state invariant, and decreasing effects.
These connect option construction to the previously checked option branch
selection/substitution results. General match-scrutinee evaluation and the
separate Bytes-pattern semantics still require integration/repair; these
constructor proofs do not establish whole-language soundness.

Validation: `make -j4 proof` and `git diff --check` pass. The new option
constructor theorem audits show no admitted BeePL dependencies or new axioms,
only standard CompCert classical/extensionality assumptions. Runtime semantics
and compiler behavior are unchanged by these proof additions.

## Option match scrutinee evaluation

`option_match_typing_components` recovers the option scrutinee and branch typing
facts, retaining the source rule's MathComp natural-number bound for branch
effects. `typed_option_value_canonical` derives the runtime option shape.
`option_match_progress_from_scrutinee` covers both scrutinee evaluation and
branch selection, in either allowed order of the None/Some patterns.

`option_match_preservation_from_scrutinee` extends the store context for all
branches when the scrutinee steps, preserves a state invariant, and combines
the reduced scrutinee effect with the branch effect bound. Completed matches
use the existing value substitution and branch-selection preservation proofs.
The only progress/preservation premises concern the scrutinee, as required by
an expression induction. The explicit option annotation identifies the option
case of Match; this does not claim that the separate Bytes-pattern case is
sound. Whole-language progress and preservation remain unfinished.

Validation: `make -j4 proof` and `git diff --check` pass. The new assumption
audits contain no admitted BeePL dependencies or new axioms; only standard
CompCert classical/extensionality assumptions occur. No runtime semantics or
compiler behavior changed in this work.

## Bytes matching: checked model/implementation mismatch

The working frontend (`bparser/beepl_ast_typechecker.ml`) requires a header
`Pbytes` pattern followed by a Bytes fallback, and the statement compiler
(`cfrontend/BeePL_Csyntax.v`) generates the two branches with a packet-length
check and header/field bindings. In contrast, `valid_match_patterns Bytes`
currently permits one pattern only. The small-step `ssem_match_bytes` rule
immediately returns a singleton branch body without evaluating the scrutinee
or introducing any bindings.

New checked audit results make the obligations explicit:

- `bytes_two_branch_pattern_rejected` and
  `bytes_two_branch_match_untypable` show that the working two-branch shape
  cannot receive a derivation under the current formal Match rule.
- `bytes_match_binder_escape` constructs a typed singleton match that steps to
  a variable not present in its original context, so the resulting expression
  cannot be typed there at any effect. This is an expression-typing
  preservation counterexample. It deliberately does not assert that the old
  `store_well_typed` predicate admits a Bytes runtime environment.

This audit does not establish a bug in the compiled packet examples. It proves
that the current Coq model is insufficient for the requested soundness claim.
The repair must model the header/fallback pattern shape, bounded packet reads,
and the bindings introduced on each branch, and then update the substitution
and preservation arguments. Excluding packet matching would not finish the
requested language proof. No runtime or typing rules were changed by this audit.

Validation: `make -j4 proof` and `git diff --check` pass. The new audit theorems
have no admitted BeePL dependencies or new axioms; their assumption reports
contain only standard CompCert classical/extensionality assumptions.

## Bytes-pattern shape aligned with the working frontend

`valid_match_patterns Bytes` now requires a header pattern with a struct schema
and a Bytes fallback with no field bindings. This matches the currently working
frontend/compiler pattern shape. `valid_match_pattern_member` was updated for
both branches, preserving the substitution proof's treatment of pattern-bound
names.

The preceding negative two-branch audit has been replaced by
`bytes_two_branch_pattern_accepted` and `bytes_two_branch_match_typable`.
`bytes_single_branch_pattern_rejected` and
`bytes_single_branch_match_untypable` now reject the singleton shape used by the
old binder-escape counterexample. The historical audit section above describes
the model before this repair.

This is only a typing-shape repair. It does not prove schema/field validation,
bounded packet deserialization, or execution of Bytes matches. The existing
small-step model still needs a representation for packet/header values and
correct guarded branch execution with bindings. The legacy Coq executable
checker also has separate branch-context/shape discrepancies; it is not claimed
equivalent to the corrected declarative rules. The working OCaml frontend and
compiler were not changed by this repair.

Validation: the full `make -j4 proof` build and `git diff --check` pass after the
pattern-rule change. The updated audit and substitution proofs introduce no
admissions or new axioms. The new audit assumption reports contain only
standard CompCert classical/extensionality assumptions.

## Header and field instantiation for Bytes branches

`instantiate_field_values` and `instantiate_bytes_header` now provide explicit
branch instantiation functions in `BeePL.v`. They reject mismatched numbers of
fields and values. Field substitutions run from right to left, matching the
shadowing order of `extends_context`; the header binding is substituted after
its field bindings.

`instantiate_field_values_preserves_typing` and
`instantiate_bytes_header_preserves_typing` preserve the exact branch type and
effects from typed supplied values. No fresh assumption about the whole match
is used. `instantiate_field_values_rejects_arity` proves rejection on unequal
lengths. Checked shadowing regressions cover repeated field names and a field
with the same name as the header.

The runtime-location lemmas for both instantiation functions require location
evidence for each supplied value and preserve the branch's location invariant.
These are building blocks for corrected packet-match execution, not a complete
packet semantics. Producing a correctly typed header value and field values
from bounded memory reads, and connecting these functions to the Match step
rules, remain required. In particular, this does not claim the current formal
value rules already provide struct/Bytes values for packet execution.

Validation: the full `make -j4 proof` build and `git diff --check` pass. The new
typing and runtime-location proofs have no admitted BeePL dependencies or new
axioms; assumption reports show only standard CompCert classical/extensionality
assumptions. Arity and shadowing results are closed under the global context.
The new instantiation functions are not yet used by runtime Match rules.

## Offset-sensitive aggregate object layout

`stored_object_type` interprets the existing reference store entries as the
objects they allocate. `object_type_at` records an allocation root and paths
through struct members or array elements. Struct paths require the translated
member type, full-field offset, and containment bounds; array paths require a
valid index and nonnegative element size. This supplies explicit offset/type
evidence for nested aggregate values, rather than treating every offset in a
known block as a value of any aggregate type.

The layout lemmas establish store-extension monotonicity, containment inside
the root allocation, inheritance of readable range permissions, and absence
of pointer-offset wrap when the root extent is representable. These results
do not infer initialization or scalar alignment from readability. They also do
not yet add aggregate value typing or aggregate-reading step rules. Those
rules must use this evidence together with the required memory invariant;
Bytes match execution and whole-language soundness remain incomplete.

Validation: `make -j4 proof` and `git diff --check` pass. All four new object
layout theorem assumption audits are closed under the global context. No
admissions or axioms were added, and no execution rule or compiler behavior
was changed by these definitions and proofs.

## Aggregate value typing uses object-layout evidence

The formal value typing rules now include struct and Bytes locations through
`ty_valstruct` and `ty_valbytes`. Both require `object_type_at` evidence at the
location's unsigned offset. This permits justified nested aggregate locations
without accepting arbitrary offsets solely from block membership.
`typeof_value` recognizes these runtime shapes. The reference canonical-form
lemma `type_infer_loc` now excludes arrays, structs, and Bytes, since each can
be represented by a location.

Object-layout store-extension monotonicity moved to `BeePL_soundness_memory.v`
so the general typing store-extension theorem can handle the new value cases
without a dependency cycle. The unfinished global proof scripts also account
for the new value cases; their original global admissions remain, and no
new admitted case was introduced. These value rules supply the typed header
and descriptor representation needed by the packet model. Aggregate reads,
packet descriptor interpretation, and guarded Match execution still require
rules and proofs; the runtime and compiler were not changed here.

`typed_struct_value_layout` and `typed_bytes_value_layout` recover the location
and object-layout derivation from value typing. The corresponding
`typed_*_requires_allocation` lemmas recover the root store entry and prove that
the aggregate extent stays within it. They prevent a later progress proof from
silently treating an unregistered block or out-of-allocation aggregate as typed.

Validation: `make -j4 proof` and `git diff --check` pass with the new value
rules, store-extension repair, and canonical-form lemmas. The four new aggregate
canonical/allocation theorem assumption audits are closed under the global
context. No admissions or axioms were added.

## Checked aggregate field steps

`aggregate_field_access` records a declared struct/Bytes member, its full-field
layout and translated type, containment within the parent, a representable end
offset, a valid block, and readable permissions for the complete member extent.
`ssem_sfield_aggregate` uses this relation to return the aggregate's location
from a struct value or a struct reference. It does not alter memory or runtime
bindings. This is a small-step formal-semantics repair; the compiler is unchanged.

`aggregate_field_access_layout` and `aggregate_field_access_typed_result` derive
the result's subobject layout and type from the parent layout. The value-step
progress and preservation theorems cover construction and every possible
successor, respectively. The preservation proof excludes the scalar/bitfield
rules for aggregate result types. Existing scalar-field classification now
explicitly excludes aggregate types, derived from the scalar memory-cell
invariant in its callers; integer-field regression proofs remain checked.

`aggregate_field_access_from_layout` constructs the access relation from the
parent layout, declared field facts, root readability, and root representability.
Thus its bounds and readability conditions can be derived without assuming a
successful field step. Initialization of the pointers inside a Bytes descriptor,
packet-region validation, and guarded packet-match branch execution remain
separate obligations. Big-step aggregate field rules and expression-context
integration are also not claimed complete by these value-step results.

Validation: the full `make -j4 proof` build and `git diff --check` pass. The new
aggregate field proofs have no admitted BeePL dependencies or new axioms;
assumption reports contain only standard CompCert classical/extensionality
assumptions. No compiler execution or kernel verification claim is added here.

## Packet descriptor reads and guarded header-byte reads

`BeePL_packet.v` models a Bytes descriptor as two adjacent pointer-sized fields.
`read_packet_view` rejects non-pointer contents, different endpoint blocks, and
reversed endpoints. `packet_descriptor_valid` records the actual pointer loads
plus a valid, readable packet region. It does not infer packet permissions from
pointer shape. `read_packet_view_total` and `read_packet_view_sound` connect the
reader to those concrete loads and endpoint ordering.

`packet_header_fits` checks a nonnegative extent against the packet end using
mathematical offsets. The checked bounds theorem proves the accepted end offset
is representable; the readable-range and loadbytes existence theorems derive a
header read from a valid packet region.

`read_packet_header` distinguishes invalid descriptors/read failure from a
short-packet fallback and a successful header-byte read. It is total on valid
descriptors. Its success theorem exposes the actual `Mem.loadbytes` result;
its fallback theorem exposes the failed size guard. A separate equation proves
that the short path selects fallback without attempting a header-byte read.

These modules are registered in the proof build and isolated compiler source
copy list. They do not yet modify Match execution. Readability/loadbytes success
does not establish initialized scalar field values: packet-byte initialization,
aligned header copying, field decoding, and branch instantiation still need to
be connected to the small-step model. Whole-language soundness remains open.

Validation: `make -j4 proof` and `git diff --check` pass. New assumption audits
contain no admitted BeePL dependencies or new axioms. Bounds and oversize
results are closed under the global context; memory-dependent results use only
standard CompCert classical/extensionality assumptions. No compiler or kernel
execution claim is made by these model/proof additions.


## Loop-result design decision approved

The user approved the unit-only recommendation after asking which design to
choose. Retain the existing unit-body/unit-result typing and frontend checks.
The empty-range result is unit. No new feature or empty-range default value is
needed. This resolves the design decision, but not the remaining proof of loop
progress, body termination under the current atomic-loop rule, and whole-state
preservation. No proof completion is claimed from the approval alone.

## Fresh header copying

`copy_packet_header` allocates a header buffer and stores the exact memval list
returned by the guarded packet read. `copy_packet_header_total` proves the copy
can complete and that a full byte read returns the original list.
`copy_packet_header_preserves_old_bytes` frames reads of nonnegative lengths
from all previously valid blocks. `read_and_copy_packet_header` connects a
successful guarded header read to a fresh copy of the requested extent.

This proof preserves the byte contents, including any uninitialized memvals;
it does not manufacture scalar initialization or typed fields from readability.
The next integration obligations remain packet-byte initialization, header
layout/alignment, scalar decoding, and Match branch execution.

Validation: `make -j4 proof` and `git diff --check` pass. The new copy proofs
introduce no admissions or axioms; their assumption reports contain only
standard CompCert classical/extensionality assumptions.

## Initialized packet slices and scalar decoding

`initialized_packet_contents` requires that every memval can be projected to
an actual byte. `initialized_packet_subrange` derives a successful, initialized
subrange load from a whole-header load and containment bounds, using the actual
CompCert loadbytes split theorem.

`decode_packet_scalar` and `read_packet_scalar` explicitly decode wire scalars.
The checked decoding theorem covers every primitive type, and
`read_initialized_packet_scalar` / `read_copied_packet_scalar` connect field
bounds and initialized contents to an actual successful read with a declarative
value-typing derivation. No field-read success is assumed in these conclusions.

Boolean wire values need normalization: ordinary `Mbool` rejects raw byte 2,
as the checked regression `ordinary_boolean_chunk_rejects_two` demonstrates.
The packet decoder reads a boolean as `Mint8unsigned` and converts nonzero to
true; `packet_boolean_two_is_true` checks this behavior. This fixes the packet
scalar decoder's semantics but does not yet normalize the copied header's stored
boolean fields or change the compiler's packet-copy lowering. Both remain
required before claiming packet boolean support across subsequent header-field
reads and compilation. The raw copy proof by itself is not enough.

Validation: `make -j4 proof` and `git diff --check` pass. New assumption audits
contain no admitted BeePL dependencies or new axioms, only standard CompCert
classical/extensionality assumptions. The packet decoder is not yet integrated
into the Match step rules; whole-language type soundness remains incomplete.

## Stored packet boolean normalization

`normalize_packet_boolean` reads a packet boolean using the wire decoder and
stores its canonical boolean representation. `normalize_copied_packet_boolean`
proves that an initialized, in-bounds boolean field in a freshly copied header
can be normalized and then read successfully with ordinary `Mbool` semantics.
`copied_packet_header_writable` derives the required permissions from the actual
allocation and copy. `normalize_packet_boolean_preserves_other_bytes` proves
that this operation preserves reads from other blocks and disjoint byte ranges.

These are checked local lemmas, with no new admissions or axioms. They do not
yet establish normalization of every field in a schema, integration into Match,
or agreement with compiler packet-copy lowering. Those obligations and the
whole-language progress and preservation theorems remain open.

Validation: `make -j4 proof` succeeds; assumption reports for the new lemmas
contain only the standard CompCert classical/extensionality assumptions.

## Normalizing all boolean fields in a packet buffer

`normalize_packet_boolean_preserves_initialization` splits a readable,
initialized buffer around the updated byte and reconstructs the whole load
after the store. The untouched prefix and suffix retain their contents, while
the boolean encoding consists of initialized bytes.

`initialized_writable_packet_buffer` records an initialized full-buffer load
and write permissions. `normalize_packet_boolean_total` derives successful
normalization from this invariant and an in-bounds offset, and preserves the
invariant. The executable `normalize_packet_booleans` applies the operation to
a finite list of offsets. Its totality theorem derives success for a list of
in-bounds offsets, rather than assuming each store succeeds.

`normalize_copied_packet_booleans` connects these results to a freshly copied
header: the resulting buffer remains initialized and writable, and every
listed offset admits an ordinary canonical `Mbool` load. Duplicate offsets do
not require a special assumption. The byte framing theorem preserves reads
from other blocks and byte ranges disjoint from every normalized byte;
`normalize_packet_booleans_preserves_scalar` specializes it to preservation
of decoded scalar values in disjoint fields.

Validation: `make -j4 proof` and `git diff --check` pass. These lemmas introduce
no admissions or axioms; their assumption reports contain only the standard
CompCert classical/extensionality assumptions. Extracting the boolean offsets
from a validated schema and connecting this execution to the Match rules and
compiler lowering remain open. Whole-language type soundness is not complete.

## Packet schema field decoding and branch bindings

`read_packet_fields` resolves each requested field name using the declared
member layout, reads its primitive value, and returns the values in binding
order. Unsupported field types and unresolved/non-full offsets produce errors.
`read_packet_fields_total` derives successful decoding and `typed_field_values`
from an initialized header and bounded primitive fields. The associated
instantiation theorem connects the decoded list to the existing substitution
proof for the header-match branch.

`packet_fields_bounded_from_schema` derives those bounds from a consistent
struct layout, plain members, and declared member types matching the requested
primitive types. `read_packet_schema_fields` therefore does not require callers
to assume successful field reads or independently supplied numeric bounds.

`copy_packet_header_binding_typing` combines allocation, schema decoding, store
typing extension, and branch substitution. It derives a fresh typed header
location from the actual copy allocation and the hypothesis that existing
store entries name valid blocks. The substituted branch retains its type and
effects under the extended store context.

This last theorem is about expression typing, not preservation of the complete
heap invariant. In particular, raw header copying still needs schema-wide
boolean normalization before ordinary stored-field reads, and the new decoder
is not yet connected to the small-step Match constructors. The declarative
Match typing rule also still needs schema validation premises corresponding to
these layout conditions. Whole-language progress and preservation remain open.

Validation: `make -j4 proof` and `git diff --check` pass. The new theorems have
no admitted BeePL dependencies or new axioms; their assumption reports contain
only the standard CompCert classical/extensionality assumptions (the pure
layout-bound theorem is closed under the global context).

## Schema validation in declarative Match typing

The previous schema-validation gap is now repaired in `ty_matcho`: its new
`valid_match_schemas` premise requires each header schema to be a declared
struct whose members are primitive, plain fields. Every requested binding must
have the field's exact BeePL type. This follows the existing OCaml frontend's
packet restrictions; it does not introduce a new packet-language feature.

`packet_member_type` checks the source declaration, and its translation lemma
connects that lookup to Ctypes member lookup. Checking only the translated type
would conflate BeePL `bool` and `uint8`; the source lookup avoids this. Audit
lemmas check this distinction and show that a match using an undeclared schema
cannot type-check. The positive two-branch audit now requires a valid schema.

Substitution and scrutinee-preservation proofs carry the schema premise through
rebuilding Match expressions. `packet_schema_layout_facts` translates the
validated declaration into the decoder's layout facts.
`typed_bytes_match_field_bounds` derives the bounds directly from a typed match
in a program with its built composite environment. Finally,
`typed_bytes_match_fields_total` derives successful, typed field decoding from
that match and an initialized header buffer, without separate field-bound or
read-success assumptions.

Validation: the complete `make -j4 proof` build and `git diff --check` pass.
No admissions or axioms were introduced. Packet Match execution, schema-wide
stored boolean normalization, preservation of the full memory invariant, and
the whole-language soundness theorems remain unfinished. Equivalence with the
legacy Coq executable typechecker is also not established by this change.

## Preparing a complete packet header

`packet_member_type` now lives with the executable packet operations so that
schema validation and header preparation use the same source-type lookup.
`packet_boolean_offsets` collects offsets for all accessible boolean fields in
the declaration, including fields not explicitly bound by the match pattern.
It resolves the effective type by name before normalizing: repeated names use
the first declaration, consistently with ordinary field lookup. A later bool
declaration therefore cannot cause an earlier non-boolean field to be changed.

`packet_boolean_offsets_total` proves successful collection, in-bounds offsets,
and coverage of every accessible boolean field. `prepare_packet_header` combines
collection, fresh copying, and normalization. Its totality theorem derives
successful preparation for a validated schema and initialized bytes of the
schema's size. The result is an initialized, writable fresh buffer, and every
accessible boolean field admits a canonical ordinary `Mbool` load.

`prepare_packet_header_steps` exposes the executed copy and normalization for
use in preservation proofs. `prepare_packet_header_preserves_old_bytes` proves
that reads of nonnegative length from every previously valid block are
unchanged, including the original packet and its descriptor.

Validation: `make -j4 proof` and `git diff --check` pass. The new proofs add no
admissions or axioms; their assumption reports contain only standard CompCert
classical/extensionality assumptions. Schema-wide boolean preparation is now
proved at this executable-operation level. It still needs to be connected to
the Match step rules, full heap typing, and compiler lowering; whole-language
type soundness remains unfinished.

## Executing two-branch packet matches

The small-step `ssem_match_bytes` constructor now executes the actual
header/fallback pattern pair. The old singleton rule, which skipped directly
to a branch without reading the packet or substituting its bindings, is gone.
`execute_packet_match` checks the descriptor and header extent, prepares a
fresh normalized header on success, decodes the requested fields, and
instantiates the header branch. A short packet selects the fallback branch
and substitutes the original Bytes value for its binder. Existing two-branch
scrutinee evaluation still supplies the context step.

The scalar wire decoder now rejects results inconsistent with its primitive
type. In particular, pointer-valued CompCert memory fragments cannot be
converted into a packet integer binding. Initialized wire bytes retain their
previous decoding behavior.

`execute_packet_match_typed_total` proves the operation succeeds with a typed
result, given a validated schema, consistent composite environment, valid
packet descriptor, initialized packet reads, and valid old store entries.
`packet_match_value_progress` connects this result to the actual small-step
rule, preserving expression typing under a store extension and respecting the
match's effect bound. `packet_match_value_preservation` covers every actual
successor of that value match, including the fallback, and proves that the
runtime variable map and reads from previously valid blocks are unchanged.

The runtime-location lemma now accounts for header allocation. Its resulting
location context extends the original context only with header locations
supported by actual preparation operations for schemas in the match patterns.
Successful scalar/field decoding introduces no embedded runtime locations.

Validation: the complete `make -j4 proof` build and `git diff --check` pass.
No admissions or axioms were added. These are packet-value progress and
expression-typing preservation results under explicit memory premises. They
do not yet preserve the complete heap/packet invariant required to discharge
those premises at every subsequent step. Whole-language soundness, big-step
correspondence, and compiler agreement remain unfinished.

## Preserving packet state and old heap typing

`execute_packet_match_unchanged_old` now proves CompCert `unchanged_on` for all
previously valid blocks. This preserves permissions and memory contents, not
just the byte reads covered by the earlier framing lemma. Preparation proves
this by composing fresh allocation, header copying, and normalization stores
outside the old blocks.

`initialized_packet_state` records the concrete descriptor, readable packet
extent, and an initialized full-packet byte load. Its header lemma derives the
initialization premise required by the packet-match progress proof for every
successful bounded header read. `packet_match_preserves_packet_state` preserves
this state for any old descriptor, including descriptors other than the one
being matched.

`typed_memory_layout_unchanged_old` preserves every old typed cell, including
its permissions and the declarative typing of its loaded value under a store
context extension. `packet_match_preserves_old_layout` connects these facts to
an arbitrary actual packet-match step: expression typing, effect bounds, the
old typed layout, and all old initialized packet states are preserved.

The execution-totality, progress, and preservation theorems also now carry
validity of every entry in the resulting store context. The new header block
is proved valid from the actual allocation and stores, even for an empty
header; old entries remain valid through CompCert's unchanged-on relation.

Validation: `make -j4 proof` and `git diff --check` pass. The new results have
no admitted BeePL dependencies or new axioms. The outstanding heap obligation
is to add the fresh header's typed field cells to the layout and establish the
coherence needed by subsequent field accesses. Preserving the old layout alone
does not establish that obligation or whole-language type soundness.

## Typing the fresh packet header's fields

`prepare_packet_header_freeable` proves that copying and boolean normalization
preserve the fresh allocation's Freeable permissions. The field-cell proof
uses these actual permissions, initialized subrange loads, and canonical
boolean loads to establish `typed_memory_cell` for a declared field.

`packet_header_layout` extends the old scalar layout with the fresh header's
accessible primitive members. `prepare_packet_header_typed_layout` proves the
extended layout is typed, deriving field alignment from the declared layout
under explicit default-alignment and nonvolatile-field premises and 8-byte
integer alignment. The theorem also requires the header size to fit the pointer
range. It does not silently assume those premises for all possible ASTs.
`prepared_packet_header_field_read` derives an actual ordinary `deref_addr`
read with a typed result for a field recorded in this extended layout.

Validation: `make -j4 proof` and `git diff --check` pass, with no new admissions
or axioms. This establishes the fresh-field heap facts for the stated schema
conditions. Connecting them to ordinary header-value `Sfield` execution and
the global invariant remains necessary. In particular, the checked audit
`boolean_field_translation_loses_source_type` shows that the current field
rule's C-to-BeePL type reconstruction turns a source bool into uint8. Source
member typing must preserve that distinction before claiming complete
header-field soundness. Whole-language type soundness remains unfinished.

## Source field types and header-value field execution

`source_member_type` now supplies declared BeePL member types to `ty_sfield`,
object-layout evidence, and aggregate-field access. It avoids reconstructing
source types from C representations, so bool and uint8 remain distinct. The
Coq executable checker's field lookup now shares this definition. This also
uses the existing `type_bmember` interpretation for bitfield member types.
The C member lookup remains as a separate declaration/layout premise.

The declarative field rule now requires a struct value or a non-optional
struct reference. Its previous optional-pointer case contradicted the working
OCaml frontend's requirement to match some/none first. Checked audit lemmas
cover that rejection and preservation of a declared bool field type.
`type_infer_sfield` has been replaced with a proper inversion statement: it
returns the actual base typing, permitted base kind, member lookup, and result
annotation equality. The former statement's implication did not provide these
facts.

`ssem_sfield_struct` supplies the missing scalar read for a struct-valued
header. `prepared_header_field_typing`, `prepared_header_field_progress`, and
`prepared_header_field_preservation` connect the prepared heap layout to this
actual expression. The preservation theorem covers every step from that
header-field expression, and shows that memory and the variable map remain
unchanged while the result has the declared primitive type. Aggregate-field
preservation has also been updated to exclude both scalar-read constructors
when the result type is aggregate.

Validation: the complete `make -j4 proof` build (including the changed Coq
checker and its dependent examples) and `git diff --check` pass. No new
admissions or axioms were added. These repairs connect the field expression to
the fresh-header cell proofs; combining the extended layout with the complete
packet-match state theorem and the whole-language induction remains open.
Compiler correspondence and the remaining language cases are not established
by these local results.

## Packet-match preservation with the resulting header layout

`packet_match_layout_result` ties the resulting layout to the branch actually
executed: fallback retains the original layout and memory, while successful
parsing records the concrete preparation operation and adds that header's
accessible fields. It cannot be satisfied merely by selecting an arbitrary
layout that omits the new cells.

`execute_packet_match_layout` derives a typed resulting layout from execution.
For a successful parse it obtains the header-size bound from the actual packet
bounds check and the byte-list length from the actual load. Default field
alignment, nonvolatile fields, and 8-byte integer alignment remain explicit
premises, as in the field-cell theorem.

`packet_match_preserves_extended_layout` combines this with arbitrary-step
packet-match preservation. Its result includes expression typing, the effect
bound, unchanged variable map, store-context extension, typed old and new heap
cells, inclusion of all old layout entries, preservation of existing packet
states, and validity of all resulting store entries. The result also retains
the operational witness identifying which layout was produced.

Validation: `make -j4 proof` and `git diff --check` pass. No admissions or axioms
were added. The top-level progress and preservation proofs still contain
admissions. Connecting the local state facts and their coherence conditions to
that whole-language induction, and completing the remaining expression cases,
is still required for type soundness.

## Full counterexample to the legacy progress statement

Historical finding: the named-array counterexample in this section has since
been removed by the binding/substitution repair recorded below.

`legacy_progress_counterexample` strengthens the earlier unbound-array audit:
its empty typing context, empty store context, and empty runtime map satisfy
all three components of `store_well_typed`, yet the typed array access is not
a value and has no small step. The typing composite environment is the runtime
environment's own composite environment, so merely relating those environments
cannot repair this counterexample.

At that stage, `empty_legacy_store_well_typed` and
`legacy_function_invariant_vacuous` established the legacy premise because no
callable location value was typable. Those historical lemmas have since been
removed: direct function values now have shape typing. The replacement audit
lemmas show that the old function invariant is overstrong, requiring every
shape-typed address to resolve without runtime location evidence. See the
callable-state integration below; none of its checked results uses that legacy
invariant.

The legacy progress declaration is now explicitly marked invalid as stated in
its source. Its admission has not been converted into a claimed proof or used
to derive anything. Repairing the global theorem requires coherent named-array
binding and substitution, callable-value typing/contracts, and the replacement
state invariant. Adding a Gamma lookup to `ty_aaccess` alone is insufficient:
`Aaccess` currently contains an identifier that substitution leaves untouched.
The checked local proofs remain usable, but cannot prove this false global
statement unchanged.

Validation: `make -j4 proof` passed for the new audit results, and
`git diff --check` passes. Assumption reports contain no admitted BeePL theorem
dependencies or new axioms. Whole-language type soundness remains unfinished.

## Expression-based array reads for substitution

The internal builtin `ArrayRead n` reads element `n` of an array expression.
It uses the existing `Prim` expression constructor, so expression substitution
and free-variable traversal already recurse into its operand. This is the
representation needed when replacing a let-bound array name by its runtime
array value; no new surface syntax is introduced.

`ty_arrayread` requires an array operand and an in-bounds index. Small-step
semantics first evaluates the operand (including its memory and variable-map
changes), then reads the actual element cell from a zero-offset array location.
The big-step rule follows the same operand/read sequence. The Coq checker and
Csyntax lowering handle the operation, and `compilation_preserve_type` has a
checked additional case for it. This is a type-of-output result, not a proof
of semantic compiler correctness.

In `BeePL_array_proofs.v`, `array_value_read_progress` and
`array_value_read_preservation` establish progress and preservation using the
actual typed element cell, without requiring a variable-map lookup.
`array_read_context_preservation` lifts an operand step and its typing fact;
`array_read_substitution_typing` checks compatibility with the existing
value-substitution theorem. Their assumption reports contain no admitted BeePL
theorem dependencies or new axioms.

Validation: `make -j4 proof` passed, including the new lemmas and affected
compiler proof. Named `Aaccess` has not yet been connected to this operation:
its free variables, substitution relation/function, Gamma lookup typing premise,
and dependent audits must be updated together. Consequently the legacy global
progress counterexample still applies, and whole-language soundness remains
unfinished.


## Named-array binding and substitution repair

`Aaccess` now contributes its array name to `free_variables`. Substituting for
that name produces `Prim (ArrayRead n) [replacement] elem`; substituting for a
different name leaves the read unchanged. `S_Aaccess_same` and
`S_Aaccess_other` express the same behavior relationally. The functional and
relational substitution equivalence, value-substitution typing, free-variable
inclusion, and runtime-location preservation proofs have all been updated and
checked.

`ty_aaccess` now requires the declared array type at that name in Gamma. The
executable Coq checker checks this binding, the element annotation, and the
index bound. `unbound_array_access_rejected` and
`unbound_array_progress_regression` replace the former typable/stuck
counterexample: that expression is now untypable in an empty context.
Additional executable-checker lemmas accept a bound in-range read and reject
both an unbound read and an out-of-range read.

`primitive_array_declare_read` still proves the complete three-step
initialization/bind/read execution, now through the substituted array value.
`bound_array_value_read` additionally proves both typing and a two-step
bind/read execution for an already evaluated array, producing a typed element.
It quantifies over every runtime variable map, so the result does not rely on
a matching entry for the bound source name. The typed store and actual element
cell remain explicit premises.

Validation: `make -j4 proof` and `git diff --check` pass. The new checker
regressions are closed under the global context. The operational read proofs
use the existing CompCert memory assumptions, with no new axioms or admitted
BeePL dependencies. This fixes the named-array counterexample; it does not
complete the global progress/preservation proofs or repair the legacy store
invariant. Those remain the overall objective.

## Array locations and initialized heap preservation

`BeePL_soundness_arrays.v` connects arrays to the existing runtime-location
machinery. `array_reference_locations` records an array's zero offset,
nonnegative extent, and an initialized-layout cell for every in-range index.
The element type is generic; the predicate requires scalar-loadable element
cells because the current read rule uses `deref_addr`. `array_heap_locations`
combines this with scalar-reference locations and is monotone under layout
extension. Aggregate and packet locations still need their broader integration.

`located_array_read_progress` and `located_array_read_preservation` obtain the
index bound from declarative typing and the cell from the runtime-location
invariant. Both return a declaratively typed result with valid runtime
locations. Thus a loaded pointer's validity is preserved, not merely its type.
The typing and runtime composite environments are explicitly the same.

`array_value_initializer_load_frame` proves equality of loads from every
previously valid block across any step of an initializer whose arguments are
values. Its proof covers assignment stores, boolean stores, aggregate copies,
and bitfield stores to the newly allocated block. This yields an actual-value
read frame, used by `array_initialization_memory_locations` to preserve stored
pointer payloads and their location evidence.

`located_primitive_array_progress` and
`located_primitive_array_preservation` combine the allocation results with:
store-context extension, validity of store blocks, expression typing, the
extended initialized layout, valid locations for all stored values, valid
locations in the result expression, and inclusion of all old runtime
locations. These are progress and arbitrary-successor preservation results for
primitive array initializers with evaluated arguments. Nonvolatile element
types and the representable total allocation size remain explicit premises.
They do not establish preservation of Gamma-to-runtime variable bindings;
initialization currently updates its named runtime-map entry, so that state
component still needs integration/repair. The global progress/preservation
admissions remain unfinished.

Validation: `make -j4 proof` and `git diff --check` pass. The new module is in
the normal proof build and the evaluation compiler's source-copy list. Its
assumption reports contain only inherited CompCert/classical/extensionality
assumptions, with no new axioms or admitted BeePL theorem dependencies.


## Array allocation preserves source variable bindings

The outer small-step array-initialization rule now returns its original
variable map. The allocation helper still uses an internal map to identify the
fresh block, but that internal name binding is not exposed as a source-variable
update. The big-step rule likewise retains the map produced by evaluating the
arguments, rather than the allocation helper's map. `Bind` introduces the
result through the already-checked array substitution rule.

`array_value_initializer_preserves_vmap` proves map equality for every step
of an initializer whose arguments are values. Existing store, layout,
initializer-progress, preservation, and declaration/read proofs have been
migrated. The completed-initializer theorem now records map equality in place
of the formerly exposed new map entry. The low-level allocation-helper map
lemmas remain valid and are still used internally.

The combined `located_primitive_array_progress` and preservation theorems now
also expose inclusion of every old layout cell and equality of the source
variable maps. `array_value_initializer_variable_frame` and
`array_value_initializer_existing_arrays_frame` connect these facts to the
existing scalar-variable and primitive-array binding invariants.
`completed_array_allocation_fresh` proves that the result block was not valid
before allocation. `array_allocation_name_collision_safe` combines freshness
and map equality: an existing binding with the initializer's name is retained,
and the fresh result cannot alias its previously valid block.

Validation: the complete `make -j4 proof` build passes, including the updated
semantics, compiler proof files, and all dependent checked soundness modules.
`git diff --check` passes after whitespace cleanup. No admissions or axioms were
added. The global type-soundness theorem is still unfinished; these results
repair and discharge the array-allocation binding obligation rather than
establishing soundness of the remaining expression cases.

## Local and global array variables

Array variables now evaluate to their zero-offset array address in both
small-step and big-step semantics. They no longer depend on an impossible
scalar load of an entire array. Separate local and global rules preserve local
shadowing: a global symbol is used only when the local map has no entry.
Named indexed reads also have an explicit global rule with the same condition.
The unbound-read audit now requires absence from both the local map and global
symbol table, as absence from the local map alone is not an unbound name.

`array_variable_layout` relates each array-typed Gamma entry to its resolved
local/global block, exact store type, and element-location evidence. It
constrains only array entries, so it can be combined with invariants for other
binding kinds without requiring every source variable to be an array.
`array_variable_progress` and preservation establish typed addresses and valid
runtime locations. `named_array_read_progress` and preservation derive the
index bound from typing, resolve the actual binding, and prove typed and located
results using the initialized heap. `array_allocation_preserves_named_arrays`
threads this invariant through store/layout extension and unchanged variable
maps.

The scalar-variable preservation proof excludes the new array-address cases
using the scalar cell's access-mode evidence. A checked
`legacy_array_variable_impossible` lemma shows why the old whole-store premise
cannot handle arrays: it demands a scalar dereference even for array variables.
The existing admitted legacy proof uses this contradiction for those cases;
it is still not a usable global soundness theorem. The new array proofs do not
import or rely on that legacy module.

The compiler proof script has been adapted to the new semantics, with a checked
`return_array_address` Csyntax evaluation lemma. The surrounding unfinished
compiler-correctness proof still uses its existing admitted symbol-preservation
lemma; this change does not establish semantic compiler correctness.

Validation: `make -j4 proof` and `git diff --check` pass. The new array soundness
lemmas report no admitted BeePL dependencies or new axioms. Combining binding
kinds and all expression cases into global progress/preservation remains open.

## Mixed scalar/array binding and state integration

`BeePL_soundness_variables.v` supplies `heap_variable_binding` and
`mixed_variable_layout`. A context may contain both scalar cells and array
addresses, each resolved independently through the local/global lookup rule.
Binding evidence is preserved when the store context and heap layout extend.
`mixed_variable_progress` and arbitrary-step preservation return typed values
with valid runtime locations while preserving memory and the variable map.
These proofs do not use the legacy whole-store invariant.

`BeePL_soundness_state.v` combines valid store blocks, initialized typed memory,
stored-value location validity, and mixed bindings in `mixed_heap_state`.
`mixed_state_variable_progress` and preservation consume that state directly.
`mixed_array_allocation_progress` and preservation return the successor state
with an extending store context/layout; allocation preserves source bindings.
`mixed_heap_state_empty` constructs the initial empty state. The state is an
integration component for the scalar/array cases, not a replacement definition
that silently excludes the remaining language features from the overall goal.

Validation: targeted builds and the complete `make -j4 proof` build pass.
`git diff --check` passes. Both new modules are registered in the regular proof
build and evaluation source-copy list. Assumption reports contain no new axioms
or admitted BeePL dependencies.

## Parallel audit of remaining whole-language obligations

The following are current inspected defects/obligations, not completed proofs:

- The call-entry memory/caller-scope defects identified in the audit have been
  repaired as described below. Direct callable-value typing, code-location
  validity, and primitive call entry are now integrated. Full call soundness
  still needs the other parameter types and recursive frame validity.
- Callable/body/signature contracts are explicit in the new entry theorem, but
  have not yet been derived from complete program well-formedness. The legacy
  `well_formed_function` premise is overstrong and must not be used in the
  replacement theorem. Program/global/composite environment agreement remains
  a required part of the full proof.
- `Sinit` already preserves the source variable map. However, the source parser
  and executable checker support struct-valued constructors while `ty_sinit`
  and the checked constructor proofs currently cover pointer-valued ones.
  Struct variables also lack address-returning rules. Constructor checking
  still needs identifier and exact field-list validation, and aggregate
  runtime-location evidence must be integrated.
- Helper execution/contracts are not covered by the currently active source
  semantics. Bounds on loop iterations do not establish termination of each
  body evaluation; the atomic loop rule still requires that additional result
  or a transition to incremental execution.
- The legacy top-level theorems retain the invalid scalar-only store invariant
  and fixed store context. They must be replaced by a mutual expression/list
  theorem over a sufficiently complete state, with successor store extension,
  initialization, write compatibility, and size/alignment premises established
  and preserved. The mixed state above does not yet cover aggregate, packet,
  callable, or helper states.

## Internal call frames and parameter initialization

The small-step `ssem_app3` rule now takes arguments that have already been
reduced to values in the caller, allocates parameters from an empty callee map,
initializes them, and enters an internal `CallFrame` with the **post-binding
memory**. The outer configuration retains the caller map. Frame steps use and
update the captured callee map; returning a value leaves the caller map intact.
Allocated parameter storage remains live; no lifetime/freeing claim is made.

`CallFrame` has no surface syntax. Source type checking and Csyntax translation
reject it. Caller substitution leaves it unchanged because the captured body
has a separate scope. Runtime-location traversal checks its body literals, but
captured variable-map validity is a separate, still outstanding invariant.

`BeePL_call_frames.v` checks caller-map preservation, compositional frame
progress and typing preservation **assuming the corresponding body result**,
and a two-step parameter-read/return result from actual initialized parameter
memory. These are integration lemmas, not a global call-soundness theorem.

`BeePL_call_bindings.v` proves that actual parameter binding preserves valid
blocks and loads/typed cells outside parameter targets. For a list of primitive
parameters it derives initialized typed cells in the final memory from matching
initial value shapes, lookups, permissions, nonvolatile types, and distinct
parameter targets. Final initialized cells are conclusions, not assumptions.
`bind_primitive_parameters_total` also constructs successful binding from
those input permissions and shapes, without assuming initialization succeeds.

`BeePL_parameter_allocations.v` connects actual allocation to the required input
facts: distinct names yield fresh distinct target blocks and valid primitive
access permissions. Its main theorem is closed under the global context.
`BeePL_call_memory.v` proves that allocation followed by actual parameter stores
preserves old loads, dereferences, and stored-value location validity.
`BeePL_call_state.v` supplies the union of the old heap layout and new parameter
cells, preserves caller bindings, and derives callee bindings for globals plus
parameters. Callee globals are resolved with the empty local map before
parameter allocation; caller locals cannot accidentally shadow them.

`BeePL_call_entry.v` combines these results constructively. The
`primitive_internal_call_state_entry` theorem produces an actual call-entry
step, an extending store, initialized callee and preserved caller mixed heap
states, callee-body typing, and valid body literal locations in the extended
layout. Its inputs include a typed internal function, an actual function
lookup, evaluated arguments of matching primitive nonvolatile types, and
valid initial caller/global state. It does not assume successful allocation or
binding, or the final initialized state. It establishes entry only; arbitrary
callee-body execution and return-state invariants remain to be integrated.
This earlier mixed binding invariant supports data globals only. The subsequent
callable-state result below extends entry to contexts containing function-name
bindings, while retaining this checked data-only result.

Function typing and checking now extend the global context with parameters
only. `fn_vars` are backend slot metadata; lexical `Bind` and pattern rules
introduce source locals where they are initialized. Treating every backend
local as in scope at function entry previously accepted uninitialized reads and
could shadow globals prematurely. Parameter names must be distinct, including
when their types differ. The Coq executable checker also now checks variable
membership in the actual context and checks a `Bind` initializer against its
declared type. `BeePL_function_scope_proofs.v` contains checked positive and
negative regressions for these rules.

Remaining call obligations:

- Direct `Ftype` function values and named-function evaluation are now handled
  below. The program must still be shown to establish the separate code/body
  contract; bare function-value shape typing does not validate a code address.
- `ty_app` admits both function and function-pointer annotations, whereas call
  entry currently handles the exact function annotation. External helper
  execution also needs separate contracts/rules.
- Unit and aggregate parameters are accepted by typing but cannot currently be
  initialized by `bind_variables` through its scalar/copy assignment rules.
  The checked primitive-parameter result does not cover those types.
- `ty_callframe` deliberately exposes a callee-context witness; it does not
  establish that the captured map implements that context. The replacement
  runtime-state invariant must relate every nested frame to its initialized
  bindings, body typing, and valid runtime locations.
- Big-step calls still allocate both parameters and backend locals; big-step
  lexical binding still writes a preallocated slot. Agreement with the repaired
  small-step semantics and compiler correctness remains open.

Validation of this milestone: `make -j4 proof` and `git diff --check` pass.
The seven call/scope modules contain no admissions or new axioms. Allocation
and variable-binding results are closed under the global context; results
using initialized typed memory inherit the existing CompCert classical and
extensionality assumptions. A separate review found no final-state assumptions
hidden in the constructive call-entry theorem. These checks do not discharge
the admitted legacy top-level soundness theorems.

## Callable values, function-name bindings, and typed call entry

`ty_valfun` records the shape of a direct `Ftype` runtime value: a code location
with zero offset. Its validity is deliberately separate from mutable heap
`Sigma`. `ssem_global_function` and `bsem_global_function` resolve an unshadowed
function name through its actual global symbol and internal function, checking
the full signature. No surface syntax or new language feature is added.

`BeePL_callable_locations.v` requires actual function resolution and matching
signature for every function-typed location. Its combined location predicate
selects code evidence for `Ftype`, data evidence for other types; an arbitrary
heap cell cannot justify a function address. Canonical-form, resolution,
embedding, and monotonicity lemmas are closed under the global context.
`BeePL_function_variables.v` checks named-function progress and exact-result
preservation. `BeePL_callable_variables.v` combines authentic code bindings
with initialized scalar/array bindings, proving progress and arbitrary-step
preservation with runtime location evidence.

`BeePL_callable_state.v` integrates these bindings into the heap state. Actual
primitive parameter preparation preserves the caller's state and constructs
the callee's state with parameters plus global data/function bindings. Code
bindings remain independent of heap allocation and cannot be shadowed by
unrelated caller-local variables.

`BeePL_callable_entry.v` separates code-address validity from a
`primitive_internal_code_contract`: actual internal functions have typed bodies
and supported, nonvolatile primitive parameter signatures. The contract is
preserved by store-context extension. `typed_located_primitive_call_entry`
derives actual function lookup from a typed and located callee, derives
initialization input shapes from declaratively typed evaluated arguments, and
constructs the call step, extending store, preserved caller state, initialized
callee state, frame typing, and body literal-location validity. No successful
allocation, binding, or final state is assumed.

This is still an entry theorem. The global code contract and body literal
validity are supplied input invariants, not yet derived from `type_program`.
Recursive frame validity, arbitrary body execution and return preservation,
external helpers, and nonprimitive parameter initialization remain open.
`Ptrtype(Fptype ...)` remains a separate Coq-level inconsistency: existing
reference rules cannot treat code as a scalar readable/writable cell. Current
textual eBPF source uses direct named calls and rejects indirect/recursive
calls; this source restriction is not a substitute for repairing the broader
formal judgments.

Compatibility work removed six old `admit` uses in the legacy application
progress script and added function-address handling to the unfinished compiler
proof. Existing admitted top-level theorem boundaries remain. The old
`well_formed_function` allocation argument relied on there being no typed code
locations; that argument has been removed inside its existing admitted proof.
The audit now proves `legacy_function_requires_every_address` and rejects the
legacy function/store predicates when a code address is missing. No checked
soundness module relies on the legacy predicate or those admitted theorems.

Validation: the complete `make -j4 proof` build passes after updating the audit,
and `git diff --check` passes. All five new callable/function-variable modules
contain no admissions or new axioms. Their assumption reports are either
closed under the global context or contain only the inherited CompCert
classical/extensionality assumptions. Independent review found no hidden
final-state assumptions or data/code confusion in the entry theorem. This
validation does not complete the admitted whole-language soundness theorem.

## Recursive call-frame configurations

`BeePL_runtime_frames.v` now records actual captured environments recursively.
Every `CallFrame` has a witness context with a valid callable heap state and a
typed body, plus validity of any frames nested in that body. A
`runtime_configuration` combines the current heap/bindings, declarative typing,
literal-location validity, and this recursive frame invariant. It no longer
accepts a captured map merely because the body is typable in some unrelated
context.

Effects are not unique: match typing can choose a larger branch-effect bound.
`BeePL_context_retyping.v` proves that two derivations of the same annotated
expression can transfer the first derivation's effect/type into the second
context. `frame_configuration_body` uses this checked theorem to recover a
callee configuration at exactly the surrounding frame's chosen effect bound.
It does not assume effect uniqueness.

`callable_heap_evolution` records store/layout extension and valid successor
heap contents. This suffices to transport every suspended caller/frame whose
bindings use the old shared layout. Each concrete allocating/writing rule must
still establish this postcondition; it is not an operational preservation
axiom. `BeePL_frame_configurations.v` proves unconditional return preservation
and an explicitly conditional body-step lifting lemma from the body induction
hypothesis. `BeePL_environment_preservation.v` additionally proves that all
small-step expression, argument, loop, loop-body, and multistep relations
preserve their outer variable map.

`BeePL_frame_free.v` proves that successful expression/function checking excludes
runtime call frames from source bodies, and that value substitution preserves
frame absence. `BeePL_runtime_substitution.v` proves substitution preserves
captured-frame validity and lifts evaluated lexical binding to full runtime
configuration preservation. Literal code/data-address validity is still a
separate requirement; frame absence alone does not validate arbitrary runtime
`Val` nodes accepted by the executable checker.

`BeePL_runtime_call_entry.v` now constructs the recursive frame configuration
at call entry. The strengthened underlying callable-entry theorem also exposes
the actual resolved function and its body typing under globals plus parameters.
`BeePL_application_configuration.v` checks that evaluated arguments have no
effects and that direct call entry retains the application's effect bound.
The primitive-signature contract and global/source-body invariants remain
explicit. General parameter types and arbitrary body preservation are not
silently assumed complete.

`BeePL_type_equality.v` proves soundness of Boolean comparison for primitive,
basic, recursive function/pointer, and list types, including effects. The
previously admitted `eq_typ` and `eq_ptr` wrappers in `BeePL_auxlemmas.v` now use
these checked proofs. The new equality results are closed under the global
context.

`BeePL_call_determinism.v` proves that parameter allocation has identical
runtime results even when its ghost store-context arguments differ, and that
primitive parameter initialization is unique. For evaluated calls, every
actual successor is either the permitted argument-list identity step or the
same initialized call frame. `BeePL_application_preservation.v` uses that
classification to prove full configuration preservation for **every** such
step, with the original application effect bound. This strengthens the
constructive entry result; it is still restricted to the supported primitive
signatures and supplied program/code invariants.

`BeePL_frame_regressions.v` constructs a valid nested-frame configuration,
checks its two-step execution to unit, and proves that a frame with a missing
captured/global variable binding is rejected by runtime validity even though
raw frame typing can accept it through a synthetic context.

Validation: `make -j4 proof` and `git diff --check` pass with all twelve new
frame/equality/application modules registered. The new modules contain no
admissions or new axioms. Direct `Print Assumptions` checks report both formerly
admitted `eq_typ` and `eq_ptr` closed under the global context. The frame and
application results are closed or use only inherited CompCert
classical/extensionality assumptions. Full-language progress/preservation,
nonprimitive calls, helper contracts, aggregate states, and loop-body progress
remain open; no completion of the overall soundness goal is claimed.

## Reference and nullable-reference call parameters

The scalar parameter development now covers primitives, ordinary references,
and nullable ordinary references. `BeePL_scalar_parameters.v` proves that
initialization performs an actual memory store, establishes a typed cell, and
preserves the locations carried by its value. Reference normalization keeps
the exact target and offset; optional references preserve either `None` or the
entire `Some` pointer. Parameter allocation derives slot permissions from real
allocations, and binding proofs establish the final cell facts for both a
constructed binding and any actual binding derivation.

`BeePL_scalar_call_preparation.v` combines those results with preservation of
the old heap and stored locations. `BeePL_scalar_runtime_entry.v` constructs
the actual call step and its recursive frame configuration.
`BeePL_scalar_application_preservation.v` proves configuration preservation for
every evaluated direct-call step with a supported signature, including the
argument-list identity step. `internal_code_contract` requires typed function
bodies without imposing primitive-only signatures on the whole program;
supported parameter storage is checked at the selected call.

`BeePL_scalar_reference_regressions.v` constructs an initialized integer at
offset 4 in an actual allocation, passes its interior pointer through a
parameter slot, and reads back exactly the original target and nonzero offset.
This checks that the reference results do not depend on assuming all pointers
have offset zero.

These results still require supplied global bindings, code typing, and body
literal-location validity. They do not establish those invariants from a source
program. References to aggregate objects still require aggregate location
invariants; unit, aggregate, and code-pointer parameters are not covered by
this scalar initialization theorem. Unit parameters are handled separately by
the generalized call results below.

## Nullable-reference semantics aligned with the language

The paper, frontend, compiler lowering, and working option examples use
nullable references: `some p` wraps a reference, and a `some x` branch binds
that reference. The earlier Coq rules instead typed the payload and binder as
the pointed-to value. The declarative rules, substitution results, runtime
location invariant, and small-step matching now use the reference type.
The working repair currently rejects nested optional references because this
representation cannot distinguish `None` from `Some None`. This restriction is
not present in the paper's recursive grammar. The design decision is pending:
preserving that grammar requires a distinct representation for nesting, while
retaining the restriction requires an explicit specification change. This is
an unresolved obligation, not a completed proof of the paper's full language.

The previous value encoder also represented `None` as block address 1, while
the decoder never produced an option value. `None` now uses the actual
architecture-specific null representation. Type-directed decoding and an
option assignment rule use real pointer-sized stores and loads.
`BeePL_option_representation.v` proves round-trip normalization and distinguishes
null from every `Some` pointer. It also records that unit has no memory
assignment rule; the later unit repair consumes those arguments without a
memory store.

The Coq checker now checks each option branch in its own context, binds only
the `some` branch's reference, and requires one branch of each kind. Nine
executable checks in `BeePL_option_checker_regressions.v` cover both branch
orders, pointer payloads, scope isolation, and rejection of scalar/nested
payload misuse. The OCaml frontend also rejects nested optional construction;
two evaluation rejection cases exercise those diagnostics.

The collection rebuild also exposed the analogous packet-branch context bug:
the Coq checker gave all packet bindings the match result type. Struct header
bindings now use their schema type, extracted fields use their declared types,
and the bytes fallback has its own context. Packet-schema validation and full
checker soundness remain separate obligations; this context repair alone does
not establish them.

Big-step option construction now preserves the child evaluation's memory and
environment. Matching evaluates only the selected branch and substitutes the
reference payload in a `some` branch, for either branch order. This repairs the
rules but does not itself prove big-step/small-step equivalence or compiler
correctness. Full-language progress and preservation remain unfinished.

Validation of this working repair: the complete `make -j4 proof` build passes,
including the nine option-checker regressions and the nonzero-offset reference
regression. The new scalar/option modules contain no admissions or new axioms;
their assumption reports are closed or contain only the inherited CompCert
classical/extensionality assumptions. Existing top-level admissions remain.
This build result does not resolve the pending nested-option specification
decision or complete full-language soundness.

The rebuilt compiler also passes `make -C evaluation/examples check`: all 49
programs compile, 37 supported emulations pass, all 46 rejection checks pass,
and all 33 evaluation-tool tests pass. Twelve programs have no emulator support;
they were not counted as executed. No new privileged kernel run was performed
for this proof/checker change.

## Unit parameters without fabricated memory cells

Unit parameters were typable but could not be bound: their access mode is
`By_nothing`, so the old parameter-binding rule demanded an impossible memory
assignment. `bind_variables_unit` now consumes exactly `Vunit` using the
parameter's declared lookup and leaves memory unchanged. Local and global
unit-variable rules return `Vunit` without loading memory. Parameter allocation
still reserves a zero-size block, preserving the existing allocation/freshness
model; initialization does not pretend that such a block contains a scalar
cell. Unit bindings have lookup evidence in the runtime variable invariant.

`BeePL_call_parameters.v` combines unit arguments with supported scalar
arguments and derives their binding inputs from actual allocation, typed
values, and location evidence. `BeePL_value_parameter_bindings.v` constructs
mixed initialization, proves uniqueness for every actual binding derivation,
and establishes typed cells only for parameters that store scalar values.
`BeePL_call_parameter_layout.v` excludes unit slots from the scalar heap layout.

`BeePL_parameter_call_preparation.v` establishes preserved caller and callee
states for these mixed parameter lists. `BeePL_parameter_runtime_entry.v` then
constructs actual call entry and recursive frame validity.
`BeePL_parameter_application_preservation.v` proves configuration preservation
for every evaluated direct-call step with unit or supported scalar parameters.
The code/global/body invariants remain explicit; this is not yet the missing
whole-program initialization or full-expression induction theorem.

`BeePL_unit_regressions.v` constructs real zero-size allocation, parameter
binding, and unit-variable execution in both semantics. It proves that every
such unit binding or variable step leaves memory unchanged. Ordinary unit
memory reads and assignments remain impossible, as intended.

Compiler correctness is still separate. An executable probe with
`consume(unit ignored, int32 value)` type-checks but fails C lowering with
`Cshmgen.make_store`: named unit parameters are still translated as `Tvoid`.
Unit parameter erasure or a consistent ABI transformation must preserve
argument effects and repair signatures, calls, and variable uses together.
The two new compiler-proof cases are explicitly left unsolved within the
pre-existing admitted theorem; no new sound compiler claim is made.

Validation: `make -j4 proof` passes with the unit semantics, mixed-call
preservation, and unit regressions registered. The new unit/parameter modules
contain no admissions or new axioms; reported assumptions are closed or the
inherited CompCert classical/extensionality assumptions. Both new unit-variable
cases in the legacy preservation script are proved directly from unchanged
memory and unit-value typing. The legacy compiler simulation's existing
admitted boundary still includes the explicitly unsolved ABI cases.
The normal `make -j4` compiler/runtime build and `git diff --check` also pass.
Building the compiler is not evidence that named unit-parameter programs lower
successfully; the separate failing executable probe above still applies.

## Aggregate addresses and interior arrays

Aggregate dereference now has explicit address-producing operational rules,
separate from scalar loads. They require an aggregate type, nonnegative size,
a nonwrapping extent, a valid block, and readable permissions throughout that
extent. `BeePL_aggregate_memory.v` connects these descriptors to object typing,
proves their preservation under actual stores, and derives descriptors for
aggregate fields from actual field-access evidence.

`BeePL_aggregate_dereference.v` proves progress and preservation for a direct
aggregate dereference under these descriptor invariants. The resulting address
is typed and memory is unchanged. Readable extent does not imply initialized
field contents: that invariant, aggregate copying, and integration with the
complete runtime configuration remain separate obligations.

Array-value typing now uses `object_type_at` at the actual base offset. Array
read semantics and the corresponding location proofs retain that base when
computing an element address. `BeePL_interior_array_regressions.v` constructs a
real 16-byte allocation, stores 41 and 73 at offsets 8 and 12, and proves that
index 1 of the inner array at offset 8 returns 73. This checks the nonzero-base
case as well as compatibility with existing zero-base arrays.

These new modules introduce no admissions or axioms. The existing admitted
compiler simulation still has an unresolved aggregate-address case; these
source-level results do not establish compiler correctness or whole-language
type soundness.

Validation: the complete `make -j4 proof` build passes with the aggregate and
interior-array modules registered, including the updated legacy proof scripts.
`git diff --check` also passes. A successful build still permits the explicitly
documented legacy admissions; it is not a proof that those gaps are closed.

## Initialized aggregate copying

`BeePL_copy_bytes.v` proves that an actual `Mem.loadbytes`/`Mem.storebytes`
copy preserves every aligned scalar load within the copied range. The proof
compares subranges of the same memory-value list, preserving CompCert pointer
fragments directly. It does not convert pointers into integers.

`BeePL_copy_cells.v` lifts this result to declaratively typed scalar cells and
their reference-location evidence. Its whole-layout theorem checks each
successor cell against either a disjoint old cell or a corresponding source
leaf. This copy plan contains only pre-copy layout/bounds/alignment facts;
successor contents are proved from the actual byte operations. Destination
`Freeable` permission reflects the current typed-cell invariant, so this does
not yet generalize initialized cells to read-only kernel memory.

`BeePL_copy_regressions.v` constructs real allocations and a store of an
interior pointer, copies its bytes, and proves that the target block and
nonzero offset survive exactly.

The old `assign_addr_copy` required `By_copy`, an access mode that BeePL's
structs and arrays never have. It now requires an aggregate type, nonnegative
size, valid source/destination blocks, and nonwrapping extents. It retains the
existing C-sized copy, alignment, and identical-or-disjoint overlap contract.
The rule does not silently introduce partially overlapping copy semantics.

`BeePL_aggregate_copy.v` connects this rule to copy existence, small-step
aggregate assignment, and typed/located heap preservation. Descriptor-based
preparation explicitly requires agreement between BeePL and C sizes. The
whole-language proof must still derive the copy plan, alignment, and alias
separation from canonical aggregate layouts; these are explicit hypotheses,
not already completed global invariants. Aggregate `Ref` allocation, array
copy lowering, and the existing compiler simulation gaps remain unfinished.

`BeePL_aggregate_copy_regressions.v` additionally constructs source and
destination arrays in actual memory, initializes the source to 41 and 73,
executes a real `Massgn` step returning unit, and proves both destination
loads. This exercises the repaired source assignment rule.

Validation: `make -j4 proof` passes with all five new copy modules registered.
Their proofs contain no admissions or new axioms; assumption reports show
only the inherited CompCert classical/extensionality assumptions. Existing
top-level progress, preservation, and compiler admissions remain open.
The normal `make -j4` compiler/runtime build and `git diff --check` also pass.
These build results do not establish aggregate compiler simulation or array
copy lowering, which remain separate from the checked source semantics.

## Fresh aggregate references and derived copy plans

`BeePL_array_copy_layout.v` derives the copy plan for zero-based primitive
arrays, including booleans, from source-cell coverage and an actual allocation.
`BeePL_structure_copy_layout.v` derives the corresponding primitive-field
struct plan from validated composite layout, field offsets, and initialized
source-cell membership. Allocation freshness proves old cells are outside the
new destination; bounds, alignment, and struct field separation come from the
existing layout lemmas. Neither result assumes successor contents.

`BeePL_fresh_copy.v` generalizes fresh copying to all tracked scalar leaves
inside a source extent. It constructs the successor layout and preserves both
declarative cell typing and stored-reference validity. For an interior source
object, the relative alignment of its leaves remains an explicit layout
obligation. For a zero-based source, it follows directly from the initialized
cell invariant. This does not claim that arbitrary readable objects already
have complete initialized-leaf coverage.

Aggregate `Ref` now has operational rules: allocate fresh storage, copy the
source aggregate with `assign_addr`, and return the actual fresh reference.
The big-step rule evaluates the operand first and retains its resulting memory
and variable map. Both use the global environment's composite layout. The
existing primitive-reference rules are separate; their older big-step model
issues are not resolved by these aggregate rules.

`BeePL_fresh_aggregate_memory.v` derives copy readiness, fresh store-context
extension, and readable object descriptors from actual allocation. The store
entry has the reference type, as required by `ty_valloc`; the object descriptor
uses the underlying aggregate type.

`BeePL_aggregate_reference.v` proves source progress and every-step preservation
for evaluated aggregate references under these runtime invariants. It preserves
old objects and cells, types the new reference, and carries copied pointer
targets into the enlarged location context. BeePL/C size agreement is proved
for all basic referenceable types rather than assumed by these theorems.
The zero-based corollary also derives all copy alignment premises.

`BeePL_aggregate_reference_regressions.v` executes a real aggregate `Ref` on an
initialized two-element array and proves that the returned block is distinct
and contains the original 41 and 73. The global invariant connecting every
aggregate descriptor to complete leaf coverage, nested aggregate layouts,
full runtime-frame integration, and aggregate compiler correspondence remain
unfinished. These results do not close whole-language type soundness.

Validation: all six new modules are registered, `make -j4 proof` and the normal
`make -j4` build pass, and `git diff --check` is clean. New proofs contain no
admissions or new axioms. Their printed assumptions are closed or inherited
CompCert classical/extensionality assumptions. The existing top-level and
compiler admissions remain open.

## Coverage of initialized nested-object leaves

`BeePL_object_paths.v` describes finite paths through embedded structs and
array elements, proves their bounds and composition, and lifts paths to
`object_type_at`. Scalar leaves include pointer and optional-pointer fields;
paths do not follow a pointer into its target. The scalar-chunk size lemma
handles architecture-dependent pointer widths.

`BeePL_object_coverage.v` connects every scalar leaf of every certified
aggregate to an initialized typed cell. Coverage permits an equivalent
runtime memory chunk while retaining the exact BeePL field type. This matters
for Boolean cells: `BMbool` and `BMint8unsigned` have the same physical chunk,
but requiring both names in a canonical layout would wrongly reject it.

The combined `initialized_object_memory` invariant includes descriptors,
recursive scalar-leaf coverage, typed cell contents, and stored-reference
validity. Checked lemmas derive scalar reads from this coverage, preserve it
when a subobject descriptor is added, and transport it to a freshly copied
aggregate. Adding a subobject also preserves the complete combined invariant;
the result's representable offset is explicit.

`BeePL_covered_reads.v` derives scalar `ArrayRead` progress and every-step
preservation from this invariant and source typing, without a separately
supplied cell for the selected index. Scalar field wrappers similarly derive
the cell from a validated object path and support direct struct values as well
as struct references. Field lookup, Full offsets, and path validity remain
explicit layout premises.

`BeePL_initialized_reference.v` lifts aggregate `Ref` progress and every-step
preservation to this stronger initialized-object invariant. The fresh object's
leaf coverage is derived from the source's coverage and actual copied layout;
it is not a hypothesis about the resulting memory.

`BeePL_object_coverage_regressions.v` checks a finite four-cell nested array,
derives the inner array's coverage at offset 8, excludes invalid leaf offsets
2 and 16, proves paths stop at pointer values, and checks a canonical Boolean
layout against equivalent chunk names. These array tests do not claim to
check struct padding. The regression assumption reports are closed under the
global context.

This closes a coverage-preservation obligation, not whole-language soundness.
Coverage still must be established from all source initializers and integrated
with runtime frames. The audit also identified missing aggregate-valued array
read rules and no-read rules for unit fields/elements. Bitfields require their
own coverage and read model; these object paths cover Full fields only.

Validation: all five new modules are registered and compiled. `make -j4 proof`,
the normal `make -j4` build, and `git diff --check` pass. No admissions or new
axioms were added; printed assumptions are closed or the inherited CompCert
classical/extensionality assumptions. Existing whole-language admissions remain.

## Aggregate-valued array indexing

The previous array-read rules always required a scalar `deref_addr`. That is
impossible for an array or struct element, so nested aggregate indexing could
be typed yet fail to step. Both semantics now include address-producing rules
for aggregate-valued `ArrayRead` and local/global named `Aaccess`. They check
the index, a representable computed offset, and the selected object's readable
extent. Big-step expression reads retain the operand evaluation's resulting
memory and variable map. Existing scalar operations still perform real loads.

`BeePL_aggregate_array_elements.v` derives the operational bounds and
readability from the parent descriptor and index. Nonnegative element size is
derived from the parent extent and positive array length; zero-sized elements
are handled explicitly. It constructs the element's object path, proves that
address arithmetic does not wrap, and extends initialized-object coverage to
the selected subobject.

`BeePL_aggregate_array_reads.v` proves progress and every-step preservation for
these aggregate reads using source typing and initialized-object memory. Named
access proofs cover both locals and globals with actual variable-location
evidence. Result typing and runtime locations use the extended descriptor
context; no scalar cell for the whole aggregate is assumed.

The scalar compatibility proofs now exclude aggregate alternatives through
their actual typed-cell access mode. `named_array_step_location` has an
explicit nonaggregate premise because its scalar-load conclusion is no longer
true for all named accesses; its existing scalar caller derives that premise.

`BeePL_nested_array_execution.v` checks two connected steps over actual
allocated memory: select the inner array at offset 8, then load its second
element at offset 12 and obtain 73. Only the selected inner array is initialized
in this execution regression; it does not claim complete initialization of the
outer array. The general preservation theorems separately require and preserve
complete scalar-leaf coverage.

Initializer-derived object coverage, integration with runtime variable/frame
invariants, unit fields/elements, Bytes-valued elements, and bitfields remain
open. These aggregate indexing results do not close whole-language soundness
or establish compiler correspondence for nested arrays.

Validation: the three new modules are registered and compiled, the full
`make -j4 proof` and normal `make -j4` builds pass, and `git diff --check` is
clean. No admissions or axioms were added. The new assumption reports are
closed or contain only the inherited CompCert classical/extensionality
assumptions; existing top-level admissions remain open.

## Initializer-derived coverage and initialized runtime configurations

Struct initializer checking now compares exact declared BeePL member types.
The former C roundtrip conflated Bool with unsigned-byte integers, so an integer
initializer could produce a cell whose type differed from the source field.
`source_member_types` now supplies the declarative rule and Coq checker with
source types. The rule and checker accept both the direct `Stype` result used
by the frontend and the existing reference result. Field order, completeness,
and header identity remain checked. `BeePL_structure_source_regressions.v`
accepts Bool values and rejects uint8-as-Bool for both result forms. The repaired
`type_infer_sinit` inversion lemma describes both forms and exact source types;
it no longer states the false reference-only/C-roundtrip conclusion.

`BeePL_initializer_frames.v` proves permission preservation through actual
assignments, allocation, and initialization. `BeePL_array_object_coverage.v`
and `BeePL_structure_object_coverage.v` derive complete scalar-leaf coverage
from primitive initializer layouts. Struct paths use Full field offsets and
exclude bitfield padding; this is not a proof of bitfield initialization.

`BeePL_initialized_arrays.v` and `BeePL_initialized_structures.v` connect that
coverage to actual source steps. Progress constructs allocations and stores;
preservation covers every successor of the evaluated initializer, including
identity steps in argument-list evaluation. The resulting state includes typed
cells, initialized-object coverage, readable descriptors, and stored runtime
locations. Existing objects and cells are retained. Struct results support both
forms. Array proofs require primitive value arguments, a nonvolatile element
type, and representable size; struct proofs require complete primitive field
plans, a valid plain struct layout, nonvolatile fields without explicit alignas,
and the existing alignment/size conditions. Nested or pointer-valued aggregate
initializers are not silently included in this result.

`BeePL_initialized_array_execution.v` starts from empty memory, performs a real
Bool-array allocation and stores, derives initialized-object memory from that
initialization, and proves two actual reads returning true and false. Coverage
is established by the initializer theorem, not supplied as a final-state premise.

`BeePL_initialized_parameters.v` extends the same state through actual parameter
allocation and binding for supported scalar, reference, optional-reference, and
unit parameters. References may designate aggregates represented in the object
context. `BeePL_initialized_variables.v` generalizes variable reads to a location
context containing callable locations, and instantiates it with descriptor
locations; loaded aggregate references are therefore retained. This does not
add direct struct-variable operational rules.

`BeePL_initialized_runtime.v` gives configurations one shared initialized heap,
with separate binding/type evidence for each captured call environment. Heap
and descriptor growth preserve suspended environments. Frame return and body
extraction are checked. The frame-body lifting theorem explicitly consumes the
body preservation induction hypothesis; it is not a whole-language theorem.
`BeePL_initialized_configurations.v` connects actual array initializer and
variable progress/preservation to this configuration. Struct configuration
cases are in `BeePL_initialized_structure_configurations.v`.

The parameter/call-entry bridge is in `BeePL_initialized_call_entry.v` and
`BeePL_initialized_application_entry.v`. The latter constructs an actual
App-to-CallFrame step and the complete initialized successor configuration.
`BeePL_initialized_application_preservation.v` handles every actual evaluated
application successor, including argument-list identity steps, preserving the
caller map, code contract, and original effect. Supported parameter types and
function/global/body obligations remain explicit; these are not yet all derived
from whole-program checking.

Whole-language soundness remains open. In particular, remaining expression
cases must use this invariant, including allocation/write cases, helper and
packet operations, and the loop execution argument. Coverage for other aggregate
initializers, unit fields/elements, Bytes elements, and bitfields is unfinished.
The legacy top-level progress/preservation admissions have not been removed by
these case proofs. Compiler simulation and verifier replacement are separate
unproved obligations.

Validation: all new modules are registered in both build inventories. Targeted
`.vo` builds, full `make -j4 proof`, normal `make -j4` (including extraction and
compiler linking), and `git diff --check` pass. New theorem assumption reports
are closed or contain only inherited CompCert classical/extensionality axioms;
no project admissions or axioms were added. Existing top-level admissions
remain. Logs: `/tmp/beepl-initialized-final-proof.log` and
`/tmp/beepl-initialized-final-build.log`.

## Composition and writable-layout coherence

`BeePL_initialized_substitution.v` lifts value substitution to captured
initialized environments without restricting the value type. Evaluated Bind
expressions have actual progress and every-successor preservation. Bind's
initializer-context case explicitly consumes the child's preservation and heap
evolution hypotheses.

`BeePL_initialized_lists.v` supplies initialized expression-list configurations
and checks list progress/preservation from the member-expression induction
hypotheses. When one argument steps, suspended arguments retain typing,
locations, and captured bindings through heap evolution. List identity steps
remain part of the existing semantics; these progress lemmas do not establish
termination. `BeePL_initialized_contexts.v` connects these results to function
and argument evaluation in App and to struct initializer arguments.

`BeePL_initialized_control.v` checks evaluated Boolean conditionals, None/Some,
and option matches in both branch orders, including branch substitution and
effect shrinkage. Cond, Some, and two-branch Match context lifting reconstructs
the actual parent step using an explicit child induction hypothesis. The Match
context rule also covers Bytes scrutinees; packet head execution is a separate
case and is not established by this context lemma.

Mutation exposed an additional required invariant. Initialized contents alone
allow incompatible overlapping views. The checked counterexample in
`BeePL_initialized_mutation.v` allocates eight bytes, stores long zero, and
shows that the same bytes can satisfy both a word cell and a nullable-reference
cell containing None. Storing long one invalidates the nullable-reference
view. This is a counterexample to adequacy of the previous memory invariant,
not evidence that a source program can construct the overlapping layout.
The same module checks actual primitive Massgn progress/preservation under
pre-state write compatibility, preserving descriptors, coverage, stored
locations, and the unit result with a reduced effect.

`BeePL_layout_coherence.v` makes the missing condition explicit: every pair of
cells is either an exact alias (same address, type, and chunk) or occupies
disjoint bytes. It proves the empty and subset cases and derives coherence
through actual fresh primitive-array allocation and source initialization.
It does not infer nominal compatibility merely from equal physical chunks.

`BeePL_coherent_configurations.v` combines the initialized configuration with
layout coherence. Its primitive-assignment theorems derive the target cell
from the reference's runtime location and derive write compatibility from the
coherent layout; neither is supplied as a per-write assumption. Primitive
array initialization also preserves this stronger configuration, including
every actual identity/completion successor. The stronger invariant still needs
to be propagated through other allocation paths, parameters, structs, aggregate
copying, and the remaining expression cases. None of these results replaces
the unfinished global mutual progress/preservation theorem.

Validation: the seven new modules are registered in both build inventories and
compiled. Full `make -j4 proof`, normal `make -j4`, and `git diff --check` pass.
No admissions or project axioms were added. Printed assumptions are closed or
contain inherited CompCert classical/extensionality axioms. Full logs are
`/tmp/beepl-composition-final-proof.log` and
`/tmp/beepl-composition-final-build.log`.

## Coherence through references, structs, and calls

`BeePL_coherent_copy.v` proves that relocating a coherent scalar-cell layout into
a fresh block preserves coherence. Exact source aliases remain exact aliases;
source byte separation survives offset translation. Actual allocation supplies
disjointness from old cells. This applies to pointer-valued leaves as well as
primitive values. Aggregate Ref progress and every-successor preservation now
produce the coherent runtime configuration alongside initialized-object
coverage. Source-object membership and the existing copy-alignment premises
remain explicit; this does not prove arbitrary overlapping aggregate assignment.

`BeePL_coherent_references.v` constructs primitive Ref allocation/store steps
and retains old descriptors, coverage, and pointer contents. The fresh cell
extends the coherent layout. Preservation follows every actual completed-value
Ref successor, including Bool allocation. The existing nonvolatile-type premise
remains explicit.

`BeePL_coherent_parameters.v` derives disjoint parameter storage from actual
allocation and distinct parameter names. New cells either identify the same
parameter slot with the same type/chunk or inhabit distinct blocks; old cells
cannot occupy a fresh parameter block. Scalar, reference, nullable-reference,
and unit parameter preparation preserve initialized memory and coherence.
`BeePL_coherent_call_entry.v`, `BeePL_coherent_application_entry.v`, and
`BeePL_coherent_application_preservation.v` use that preparation to construct
source calls and preserve every evaluated application successor, including
identity steps. Final coherence is derived from allocation, not assumed from
final typed contents. Existing body/global/code-contract obligations remain.

`BeePL_coherent_structures.v` derives primitive field separation from validated
plain composite layouts and resolved offsets. The proof does not require a
caller-supplied field-disjointness premise. It combines that separation with
allocation freshness for coherent struct initialization. Both direct and
reference results retain initialized coverage, typing, runtime locations, and
captured-frame validity under the previous explicit layout conditions.

`BeePL_coherent_reference_execution.v` connects three actual operations starting
from empty memory: allocate a reference initialized to 41, overwrite its cell
with 73, and read back 73. The allocation and mutation use the coherent
configuration theorems; the final exact value follows from the actual store and
load. This is a source-semantics execution proof, not a kernel execution or a
claim about compiled code.

The stronger invariant still needs incorporation throughout the global
expression/list/loop induction, including aggregate mutation, helper and packet
contracts, and initial program/global-memory construction. The existing layout,
nonvolatile, and code-contract premises have not all been derived from program
typing. These results do not close the top-level soundness admissions.

Validation: all eight new modules are registered and compiled. Full
`make -j4 proof`, normal `make -j4`, and `git diff --check` pass. No new
admissions or project axioms were added; printed assumptions contain only the
inherited CompCert classical/extensionality axioms or are closed. Full logs:
`/tmp/beepl-coherence-final-proof.log` and
`/tmp/beepl-coherence-final-build.log`.

## Unit arrays, coherent reads, and aggregate mutation

Unit arrays now have explicit initialization and read rules. Their elements
consume no bytes, initialization leaves the allocated memory unchanged, and
reads require a valid array descriptor and an in-bounds logical index. The
rules do not invent scalar unit cells or change scalar dereference semantics.
`BeePL_unit_arrays.v` checks these rules and a two-element execution example.
`BeePL_initialized_unit_arrays.v` proves progress and every-successor
preservation under the coherent runtime invariant, deriving the zero-byte
allocation and retaining the existing scalar-cell layout.

`BeePL_program_member_types.v` derives member completeness from a successfully
built program composite environment. Consequently, unit-valued struct fields
cannot occur in that environment, including along nested structure paths.
This uses the existing builder restriction; local unit arrays remain legal.

`BeePL_coherent_reads.v` proves progress and every-successor preservation for
primitive dereferences and evaluated scalar, aggregate, and unit array reads.
The required cells and object descriptors follow from operand runtime
locations and the configuration invariant. Aggregate reads extend descriptors
while retaining the coherent scalar layout.

`BeePL_initialized_aggregate_mutation.v` proves aggregate assignment preserves
initialized memory and coherent configurations under explicit pre-state copy
readiness and copy-plan conditions. For zero-based primitive arrays, coverage
and coherence derive the target footprint and same-layout copy plan. General
struct assignment still needs stronger provenance or footprint information:
coverage and coherence alone do not exclude unrelated cells in struct padding.

These modules do not close whole-language soundness. Global mutual
progress/preservation, loop execution, helper/packet contracts, and initial
program-state construction remain outstanding. Some representation and layout
premises still need derivation from program typing. The big-step value rule
also still lacks raw array values; the unit-array big-step regression uses an
initializer expression rather than assuming that missing rule.

Validation: all five new modules compiled and are registered in both build
inventories. The integrated `make -j4 proof` check, normal `make -j4`, and
`git diff --check` pass. No new admissions or project axioms were introduced.
Integration logs: `/tmp/beepl-unit-integration-proof.log` and
`/tmp/beepl-unit-integration-build.log`.

## Incremental loops and complete value shapes

The earlier atomic-loop limitation is removed at the operational level.
An evaluated `For` computes its iteration count and either returns unit for an
empty range or enters an internal `LoopFrame`. Each frame transition advances
the active body once, restarts the saved template after a unit result, or
returns unit after the last iteration. Entry has no body-termination premise.
The saved template and active expression both participate in substitution,
runtime-location checks, and captured-frame checks. The frame typing rule
retains the template's effect budget and allows the active body's effects to
decrease within that budget. Source checking and translation reject internal
runtime frames, which are introduced only by execution.

The four-iteration `Unit` regression now proves nine actual small-step
transitions. Terminating summary relations remain available separately; they
are no longer premises of an operational loop-entry step. Compiler simulation
for this changed transition structure remains an outstanding proof obligation.

Value well-formedness now covers the shapes already admitted by typing:
arrays, structs, Bytes, function locations, and nullable reference values, in
addition to primitives and references. This relation checks value shapes;
object ancestry, valid memory, and code provenance remain responsibilities of
the typing and runtime invariants. `typed_well_formed_value` is now proved with
`Qed`, replacing its admission. The earlier raw-array-value big-step gap is
therefore resolved rather than assumed away.

`BeePL_coherent_loops.v` derives loop-entry progress from typed integer bounds
and proves preservation for every entry successor. Its frame progress and
preservation lemmas consume the recursive active-body hypothesis, preserve the
saved template across heap evolution, and retain coherence. No termination
premise occurs in these loop cases. These are components for the global
induction, not an independent assumption that arbitrary bodies are sound.

`BeePL_coherent_operators.v` combines the checked arithmetic, bitwise, shift,
comparison, and unary cases with the initialized coherent runtime state. It
proves evaluated-head progress/preservation and lifts recursive operand
hypotheses through operator contexts, retaining suspended operands after
allocation or mutation by the evaluated operand.

`BeePL_structure_mutation_footprint.v` derives an exact destination-block
footprint from actual fresh allocation and the initializer's field layout.
This excludes independent cells in padding. The footprint is preserved by
field/array layout extensions on other blocks and provides a same-layout copy
plan for existing struct destinations. Copy readiness and source field
coverage remain explicit. Maintaining this provenance invariant through every
language construct is still part of the unfinished global proof.

`BeePL_loop_execution.v` connects finite unit-valued body completions to both
the incremental small-step execution and the existing terminating repetition
summary. Its replay theorem explicitly requires unit-valued completions:
the untyped summary relation also accepts other terminal values, whereas the
typed loop machinery returns unit. Completion evidence is used to relate
terminating runs, not to justify loop entry or one-step progress.

The checked `typed_value_bigstep` lemma evaluates every typed value using the
now-proved shape lemma. The allocated-unit-array regression additionally
constructs the allocation and performs a big-step read directly from the
resulting array value. `Print Assumptions typed_well_formed_value` reports
`Closed under the global context`.

Validation: all four new modules are registered in both build inventories and
compiled. The full `make -j4 proof`, normal `make -j4`, and whitespace checks
pass after the loop/value changes. No admissions or project axioms were added;
the existing value well-formedness admission was removed. Other new theorem
assumptions are closed or inherited CompCert classical/extensionality axioms.
Logs: `/tmp/beepl-loop-full-proof.log`, `/tmp/beepl-loop-final-build.log`,
`/tmp/beepl-coherent-operators.log`, and `/tmp/beepl-values-compat.log` (the latter
also records an intermediate loop-execution error subsequently fixed and
validated by the full proof build).

Next concrete call gap identified at this milestone: function-valued parameters
are accepted by the AST checkers and declarative application typing, but
`Ftype` has `By_reference`
access mode and no matching parameter-assignment case. A valid code location
therefore lacks the executable binding path needed for call entry. The
existing supported-parameter premise does not cover this case. Argument-list
identity transitions can still occur, so absence of call entry must not be
misreported as absence of every small step. This also highlights the need to
separate meaningful execution progress from administrative stuttering in the
final theorem.

Parser-audit correction: the grammar declares a `FUNTYPE` production, but the
lexer does not emit that token. The function-parameter witness is therefore an
AST/type-system gap, not a confirmed runnable textual `.bpl` example.

The same audit found checker/typing obligations to address next: declarative
reference rules admit volatile types although the current OCaml source
transformer emits `noattr`; the Coq array-initializer checker does not yet
enforce the same annotation/element-count agreement as the OCaml checker; and
the Coq assignment checker uses a binding pattern where an explicit type
equality check is needed. These must be repaired or derived from an explicit
source admissibility theorem before claiming checker agreement or soundness
for all accepted programs.

## Checker repairs and meaningful argument progress

The Coq assignment checker now explicitly compares the assigned value type
with the reference's data type. The array-initializer checker now requires
matching array annotations, matching element types, and an extent equal to
the initializer length. `BeePL_checker_consistency.v` proves both accepted
cases construct the corresponding declarative typing derivation, assuming
only the recursive child-checking hypotheses. The two bridges and their
concrete acceptance/rejection regressions compile with closed global context.

Application, struct-initializer, and array-tail evaluation contexts now require
unfinished argument lists. List evaluation retains its identity cases as a
summary relation, but a completed expression head cannot use those cases as
an execution step. `BeePL_strict_progress.v` proves that evaluated calls enter
call frames and evaluated initializers produce values. It also decomposes a
guarded list step into a value prefix and an actual nonvalue expression step.
Existing data-parameter call characterizations now derive absence of function
parameters from their parameter-shape hypotheses and characterize actual
entry, excluding the new function-parameter preparation path.

Further read-only audit findings remain unresolved at this point:

- Conditional checking concatenates the two branch effects, while declarative
  conditional typing requires equal branch effects. Even a correctly typed
  reference allocation in one branch and an existing reference variable in
  the other expose the mismatch. An explicit branch-effect budget, like the
  existing Match rule, avoids introducing global effect widening for values.
- Application checking does not compare the outer result annotation with the
  function signature's result type.
- Cast checking shadows the outer annotation; declarative typing has no cast
  rule; and primitive casts to Bool decode the C integer result as a BeePL
  integer. These require a coordinated repair, not merely a new typing rule.
- Runtime `Val` checking still accepts arbitrary annotations without checking
  shape or provenance. Universal checker-to-typing soundness remains false;
  a source-only statement would require an explicit source-generation
  invariant rather than an implicit restriction.

The application-result annotation issue above is now repaired in both checker
function branches, with a checked acceptance-inversion lemma and rejection
regressions. Full application-checker soundness remains open: the argument
matcher permits an `Ftype` argument for an `Fptype` parameter, while
declarative application typing currently requires exact argument types. That
conversion cannot be justified by the annotation check alone.

`BeePL_literal_consistency.v` supplies the missing Boolean-constant typing and
small/big-step cases for the `Const (ConsBool b)` form emitted by the frontend.
Constants and `Unit` expressions now validate their annotations. Checked
lemmas cover accepted-literal typing, execution, arbitrary-successor
preservation, and positive/negative regressions. The compiler's Boolean
constant case and local function-variable case were also updated without
adding admissions.

## Immutable function parameters in the source semantics

Function-valued parameters now bind directly to authentic code addresses.
`function_parameter_partition` separates those immutable bindings from data
parameters, checking the actual internal-function lookup and exact signature.
Only data parameters allocate and initialize storage. Local code-variable
rules respect shadowing; the global exact-read lemma now explicitly requires
absence of a local binding. No function address is treated as a scalar cell in
code memory or stored in a fictitious one-byte function slot.

The six checked modules cover partitioning, generalized storage preparation,
callee bindings, constructive call entry, entry uniqueness, and regressions:
`BeePL_function_parameters.v`, `BeePL_function_parameter_storage.v`,
`BeePL_function_parameter_bindings.v`, `BeePL_function_parameter_entry.v`,
`BeePL_function_parameter_determinism.v`, and
`BeePL_function_parameter_regressions.v`. The entry module also proves
preservation for every actual evaluated-call successor. It uses the retained
partition/allocation/binding witnesses and uniqueness result; it does not
assume the successor state is initialized. The ordinary data-binding path is
proved impossible when a function parameter is present.

A singleton-code-parameter regression proves that binding allocates and stores
nothing and that local lookup returns the exact typed code pointer. The
supported parameter set is direct `Ftype` code arguments plus the previously
supported unit/scalar/reference/nullable-reference data arguments. Pointer-to-
function conversions, aggregate-by-value arguments, textual `FUNTYPE` syntax,
compiler ABI support, and whole-program readiness are not established by these
results. Whole-language progress/preservation remains unfinished.

Validation: all nine new modules from this integration are registered in both
build inventories and compiled. Full `make -j4 proof`, normal `make -j4`, a
final proof-target recheck, and `git diff --check` pass. No admissions or
project axioms were added to the checked modules. Checker/literal results are
closed under the global context; memory/call results are closed or report
inherited CompCert classical/extensionality assumptions. The old admitted
progress proof's identity-call shortcut is now explicitly left unresolved
inside its existing admission, rather than presented as valid progress.
Logs: `/tmp/beepl-calls-literals-full-proof.log`,
`/tmp/beepl-calls-literals-build.log`, and
`/tmp/beepl-calls-literals-proof-recheck.log`.

## Conditional effects and primitive casts

Conditional typing now assigns each branch its own effect and requires both
effects to fit an explicit shared budget. The Coq checker's existing union of
branch effects therefore has a declarative typing derivation, even when only
one branch writes memory. Selecting a branch may reduce the effect; it does
not require assigning a nonempty effect to a value. Substitution, store
extension, context retyping, and initialized conditional configurations have
been adapted to this rule.

Primitive casts now have an explicit declarative typing rule using the
existing `allowed_cast` relation. The checker compares the outer annotation
with the cast target. Both operational cast rules decode the result according
to its target type and propagate the operand's resulting variable map.
`BeePL_cast_soundness.v` proves totality, actual small-step progress, and
preservation for every successor of evaluated primitive casts.
`BeePL_branch_cast_checker.v` proves checker-to-typing bridges for casts and
conditionals under recursive child hypotheses, with annotation and asymmetric
branch-effect regressions.

The existing Bool representation casts to an unsigned byte before decoding
zero/nonzero. Consequently `2` becomes `true`, while `256` truncates to zero
and becomes `false`. Generated C now normalizes that byte to canonical `0` or
`1` in both translation paths, evaluating the operand once. Non-Bool cast
translation is unchanged. `BeePL_bool_cast_compiler.v` proves the generated
simple-expression evaluation agrees with decoded/reencoded source results,
including actual Cstrategy regressions for both values. This is not a proof
of the whole compiler simulation, whose existing admission remains.

`BeePL_coherent_casts.v` and `BeePL_coherent_control.v` lift the head results
to coherent initialized runtime configurations and handle operand/guard
contexts under explicit recursive preservation and progress hypotheses.
These hypotheses still need discharge in the global mutual induction.
All five new modules and the affected compiler/legacy proof modules pass
normal `.vo` compilation. No admissions were added to these checked modules.
Full `make -j4 proof`, normal `make -j4`, and `git diff --check` also pass for
this integration. Logs: `/tmp/beepl-branch-cast-full-proof.log` and
`/tmp/beepl-branch-cast-build.log`.

`BeePL_cast_evaluation.v` additionally lifts the simple Bool-cast result to
actual Cstrategy expression evaluation for every primitive cast target.
Given an operand evaluation, raw C cast, and target decoder result, it proves
the generated cast evaluates to the encoded BeePL value with exactly the
operand's trace and final memory. It imports no admitted BeePL theorem;
assumptions include CompCert's external-function/inline-assembly semantics
parameters and its usual classical/extensionality assumptions.

## Nonvolatile ordinary memory operations

`BeePL_volatile_audit.v` establishes an operational counterexample in the
attributed Coq AST: allocation of a volatile integer succeeds, but a following
dereference has no small step. The previous rules and checker accepted this
expression, including the form beginning with an ordinary integer constant.
This is independent of forged runtime pointers. The surface parser emits
`noattr`; adding volatile I/O semantics is not part of the existing-language
proof repair.

The originally commented nonvolatile premises in `ty_ref`, `ty_deref`, and
`ty_massgn` are now active, and the checker enforces the same conditions.
The audit now proves declarative/checker rejection while retaining the
unchecked operational counterexample. `BeePL_memory_checker.v` proves the
conditions follow from the typing derivations, plus accepted Ref/Deref
checker-to-typing bridges under the child-checking hypothesis. The existing
assignment bridge is adapted as well.

The coherent primitive-reference progress and preservation theorems no longer
require a separate nonvolatile hypothesis: they derive it from typing. The
actual allocation/write/read execution regression still passes. Generic
substitution/context-retyping and legacy compatibility targets compile, as do
the new checker and rejection proofs. This repair does not yet derive all
array/struct initialization, parameter, size, or program-environment
admissibility conditions; those remain obligations for the global theorem.

## Exact aggregate location checking: finite search foundation

Aggregate runtime locations require an actual object path, including nested
subobjects, so checking only a root store entry would reject valid values or
miss invalid paths. The previous `Val` checker instead accepted every
annotation unconditionally.

`BeePL_object_finiteness.v` constructs a finite type/offset domain containing
every object path and relates `object_type_at` to a path from the block's
normalized store type. `BeePL_finite_reachability.v` supplies a proved sound
and complete finite graph algorithm. These proofs allow zero-sized elements
and nominal cycles; they use no guessed recursion depth or unproved rank
condition. Both modules compile with closed global context.

`BeePL_object_edges.v` computes exactly the legal field/array successors.
`BeePL_worklist_reachability.v` proves a visited-worklist algorithm sound and
complete using a sufficient finite-domain bound, without enumerating the
proof universe at runtime. `BeePL_object_decision.v` combines them into a
sound and complete decision for `object_type_at`. Its runtime uses an
arithmetic bound and type-list/offset tests rather than materializing every
byte-offset/type combination. The exponential finite-reachability reference
algorithm is not used by the value checker. Regressions include nested
aggregate addresses, gaps/out-of-bounds, no traversal through pointers, and
a billion-element unit array handled by one zero-size edge.

`BeePL_value_checker.v` proves its Boolean decision equivalent to the exact
declarative `Val` typing relation. The main checker now calls it, with checked
acceptance-to-typing and typing-to-acceptance bridges in
`BeePL_checker_consistency.v`. This preserves the existing distinctions:
ordinary reference values require matching store entries; aggregate/Bytes
locations require valid object paths; function values require zero offsets;
and options check their shape and recursive payload. Reference offsets and
function code provenance still require the separate runtime memory/code
invariants; declarative shape checking alone does not establish safe access.
All new decision/specification proofs are closed under the global context.
Accepted option/assignment regression fixtures now supply their reference
store entries, and explicit unregistered-reference rejection tests remain.

## Initializer storage validity

The function-array audit originally exhibited a typed, located, coherent
initializer that could not step: immutable function bindings do not make a
direct `Ftype` a storable array element. That counterexample is now rejected
by typing and checking. `BeePL_function_array_audit.v` retains the unchecked
operational failure and authentic-location lemma, and proves the initializer
cannot inhabit a typed/coherent configuration under the repaired rules.

`BeePL_storage_types.v` traverses reachable inline types with the proved
visited worklist. Its specification checks necessary local storage conditions
for every reachable type: nonvolatile storage, nonnegative representable
extent, complete nominal objects, and no direct function-valued data slots.
Array elements and struct members are traversed; pointer targets and function
signatures are not. This preserves unit, primitive, reference, struct, nested
array, and `Bytes` data kinds. No arbitrary nesting bound is used. The check is
not advertised as sufficient for every operational initialization case.

`ty_ainit` now requires that check for its array type. `ty_sinit` requires it
for the actual constructed struct, even when the expression returns a pointer.
The executable checker enforces both conditions, and checked acceptance-to-
typing bridges cover both constructors. Regressions retain valid unit,
reference, nested-array and Bytes slots, and reject volatile/oversized data.
Both direct and pointer-result struct initializers reject volatile fields.

`BeePL_array_storage_typing.v` and `BeePL_structure_storage_typing.v` derive
the size/nonvolatile conditions needed by the checked primitive array and
struct initialization theorems. Their typed initialized/coherent wrappers no
longer ask callers to supply these conditions separately. Raw operational
helpers retain their needed hypotheses. Struct result retyping now preserves
the underlying struct attributes; it cannot silently turn a checked struct
into a volatile one. Genuine alignment, field-layout, distinctness, and
primitive-plan hypotheses remain separate obligations.

Validation for the preceding nonvolatile/value-checking integration: full
`make -j4 proof`, normal `make -j4`, and `git diff --check` pass. The affected
checker regressions, the fully coherent function-array counterexample, and
the reference/write/read execution proof pass normal `.vo` compilation.
Logs: `/tmp/beepl-runtime-value-full-proof.log`,
`/tmp/beepl-runtime-value-build.log`, and
`/tmp/beepl-runtime-value-integration.log`.

The rebuilt native compiler also typechecks and compiles `xdp_cast.bpl` and
`xdp_boolean.bpl`. A temporary BeePL function converting uint32 to Bool and
back to uint32 was compiled and linked to a C harness; all ten boundary
inputs passed, including 2, 255, 256, 257, 511, 512, and UINT32_MAX. This is a
native generated-code check, not a new kernel-verifier/execution result.
Whole-language soundness remains unfinished; the legacy top-level admissions
are not discharged by these build and regression results.

## Packet descriptor transport and state foundations

`BeePL_packet_descriptor_copy.v` proves actual two-pointer descriptor copies,
including fresh allocation, exact endpoint loads, old-memory framing, and
same-block disjoint descriptor framing. It preserves pointer fragments rather
than treating the descriptor as a sequence of numeric bytes.

`BeePL_packet_state.v` tracks descriptor locations with existential current
views, readable packet ranges, and initialized raw packet contents. Tracking
locations allows a future valid copy to replace a descriptor's endpoint values.
Actual scalar/byte writes preserve this state when their ranges are disjoint
from both the descriptor and its referenced packet range. Fresh descriptor
copy extends the location set and preserves all old packet bytes. Empty
packets and one-past-end endpoints are supported. A separate predicate records
`Bytes` object identity in the store typing.

`BeePL_bytes_layout.v` derives the intrinsic descriptor layout from the actual
program builder: retained `bytes_t`, two pointer-sized slots, exact offsets,
and pointer-compatible blockcopy alignment. Its size expressions use
`2 * size_chunk Mptr`. These layout/decision results are closed under the
global context; actual memory-copy/state results use inherited CompCert
classical/extensionality assumptions, not admitted BeePL theorems.

These foundations are not yet integrated into the shared runtime invariant.
The core now has dedicated `Bytes` address-read/copy cases, and source
`sizeof_type Bytes` is `2 * size_chunk Mptr`.
Existing generic variable/array/field/parameter rules use these cases without
new source syntax. Packet state now also records that each descriptor's
storage extent does not wrap the pointer range. The new operational proofs
and their downstream compatibility changes pass the full proof build.

`assign_addr_copy` now uses the source object extent consistently, including
its bounds, overlap condition, and actual load/store span. An inner unit array
occupies zero source bytes, but its translated `Tarray Tvoid` has a nonzero
C size. Using that C size attempted to copy beyond a nested unit initializer's
zero-byte allocation. Replacing the old span removes that step; adding an
alternative zero-copy rule alone would have left it enabled. Source progress
and compiler unit-storage representation remain distinct obligations. This
source repair does not establish the compiler's erased-unit ABI correctness.

Validation for the initializer-storage/packet-foundation integration: full
`make -j4 proof`, normal `make -j4`, and `git diff --check` pass. All six new
modules are registered in both build inventories. The checked initializer
bridges, strengthened typed wrappers, and positive/rejection regressions pass.
Logs: `/tmp/beepl-storage-packet-full-proof.log`,
`/tmp/beepl-storage-packet-build.log`, and
`/tmp/beepl-structure-checker.log`.

The rebuilt native compiler typechecks and compiles `xdp_array.bpl` and
`xdp_eth_ipv4.bpl`. A temporary struct-initialization program with uint32 and
Bool fields also typechecks, compiles, and passes five native execution cases.
These are frontend/native compilation checks, not new kernel results.
No admissions were added to the new checked modules. Global type soundness
and the remaining packet/copy/compiler obligations are still unfinished.

## Operational Bytes copies and packet replacement

`BeePL_bytes_execution.v` checks actual descriptor reads and copies through
`deref_addr` and `assign_addr`, including fresh parameter allocation/binding,
small- and big-step variable reads, typed results, and packet-state extension.
The source extent is now architecture-dependent and agrees with the intrinsic
two-pointer descriptor size. A descriptor read certifies accessible descriptor
storage; the separate packet invariant certifies its endpoint values and
initialized payload. These are different obligations.

`BeePL_packet_mutation.v` proves preservation for every actual `Bytes`
assignment, including replacement of an existing tracked descriptor. The
separation premise protects other descriptors and all packet payloads in the
pre-state; it does not assume a successful or well-formed final state. The
destination acquires the source's view, so requiring it to retain its old view
would be incorrect. The proof also establishes that every resulting tracked
view came from a pre-state descriptor. Consequently a scalar-write footprint
that was separated from packet state remains separated after replacement.
The same module proves that allocation preserves packet state and existing
write separation, and that writes into the fresh block are separated from
every existing descriptor and payload. These facts use actual allocation and
memory framing, for use in ordinary initializer/reference preservation.

Targeted normal `.vo` builds pass for `BeePL_packet_state.v`,
`BeePL_bytes_execution.v`, and `BeePL_packet_mutation.v`. Logs:
`/tmp/beepl-bytes-execution.log` and `/tmp/beepl-packet-mutation-final.log`.
The principal assumption reports contain inherited CompCert
classical/extensionality assumptions and no admitted BeePL theorem.
The shared runtime-invariant migration remains outstanding; these local
results do not discharge global progress or preservation.

`BeePL_packet_coverage.v` connects exact `object_path` Bytes leaves to tracked
packet locations. It derives nonwrapping descriptor addresses and object
typing from the aggregate's bounds and ancestry, derives actual descriptor
reads from packet state, and preserves coverage through nested subobject
descriptors. It also checks actual field-read progress and array-read progress
and every-successor preservation. The coverage predicate traverses embedded
objects, not pointer targets. Standalone incoming descriptors still need their
separate packet typing invariant. `BeePL_bytes_fields.v` supplies field-read
preservation with the actual field-layout evidence, including the generic
address-read alternative now enabled for Bytes.

`BeePL_nested_unit_array_copy.v` checks a typed nested-unit initializer's two
actual small steps, two zero-byte allocations, and empty byte copy. Its
general zero-sized-assignment lemma proves that every such aggregate
assignment writes the empty list; the old C-sized alternative is absent.
The regression explicitly records the source-zero/C-two-byte size mismatch,
so the source theorem cannot be mistaken for a compiler representation proof.
The nested-unit execution theorem is closed under the global context.

Targeted `.vo` builds also pass for packet coverage, Bytes field preservation,
the nested-unit execution regression, aggregate-copy/reference regressions,
and fresh aggregate copying. Logs: `/tmp/beepl-packet-coverage.log` and
`/tmp/beepl-source-copy-targets.log` (the latter records the final target
invocation, not every preceding passing invocation).

Validation for this integration: full `make -j4 proof`, normal `make -j4`,
and `git diff --check` pass. Logs:
`/tmp/beepl-bytes-source-copy-full-proof.log` and
`/tmp/beepl-bytes-source-copy-build.log`. The rebuilt native compiler also
typechecks and compiles `evaluation/examples/xdp_array.bpl` and
`evaluation/examples/xdp_eth_ipv4.bpl` to assembly. These are native frontend
checks, not new kernel execution results.

Next, packet state, exact Bytes-leaf coverage, and scalar/packet separation
must become fields of the existing shared runtime invariant. Its current
variable binding relation also lacks direct struct and Bytes bindings; direct
struct variables need an actual operational read rule before that relation
can be broadened. Global progress, preservation, and multistep safety remain
unproved. The checked local results above do not use those admissions.

## Shared runtime packet invariant

The existing `initialized_heap_state`, `initialized_heap_evolution`,
`initialized_runtime_configuration`, captured-frame predicate, and coherent
configuration now carry an explicit packet-location set. This is a direct
extension of the shared invariant, not a separate packet-only configuration.
`packet_heap_invariant` records descriptor/payload validity, descriptor typing,
coverage of every declared embedded Bytes path, and separation from scalar
write footprints. Evolution preserves old descriptor locations and establishes
the final packet invariant. Current views remain existential so assignments
can replace endpoint values without invalidating the descriptor identity.

`BeePL_packet_bindings.v` extends runtime locations and variable bindings to
tracked Bytes and aggregate objects. Actual local/global struct-variable rules
were added to both source semantics; `BeePL_structure_variables.v` proves
their exact successors and typed results from real object ancestry. The
generalized binding progress/preservation proofs cover callable, scalar,
aggregate, and Bytes bindings.

The migrated runtime, list, substitution, evaluation-context, control, loop,
operator, and cast proofs pass normal `.vo` checks. Primitive arrays, unit
arrays, primitive structs, ordinary variable reads, scalar writes, and fresh
primitive references preserve arbitrary tracked packet sets through actual
allocations/stores. Captured environments use the generalized bindings.
Parameter preparation preserves packets while allocating and binding actual
arguments; its existing supported argument kinds are unchanged. This does
not yet establish general by-value aggregate/Bytes call preparation.

`BeePL_packet_copy.v` tracks freshly copied descriptors by exact declared
Bytes paths, proves their two pointer loads, frames payload bytes, and derives
typing, coverage, and separation from copied scalar cells. Aggregate Ref
wrappers now return the enlarged packet registry. Relative descriptor
alignment is an explicit pre-copy obligation, alongside the existing scalar
copy-alignment obligation.

`BeePL_packet_replacement.v` handles in-place aggregate copies. Its pre-state
plan allows destination descriptors to be replaced by corresponding complete
source descriptors; other descriptors and payload ranges must be separated
from the write. Actual byte-copy operations establish the resulting packet
state and the origin of each resulting view. Generic aggregate assignment
and structure-write wrappers use this plan, retaining Bytes-containing
destinations instead of imposing a no-Bytes restriction.

These alignment/replacement plans are not yet derived for every typed
program. Scalar separation alone does not protect aggregate padding, nor does
one-way leaf coverage exclude unrelated descriptor views overlapping an
object. The global proof still needs object/descriptor overlap coherence,
packet-payload separation from aggregate write spans, and program-layout facts
that imply relative descriptor alignment. This migration does not close
global progress, preservation, or multistep safety.

The complete integration passes `make -j4 proof`, normal `make -j4`, and
`git diff --check`. Logs: `/tmp/beepl-shared-packet-full-proof.log` and
`/tmp/beepl-shared-packet-build.log`. The call/application wrappers, function
parameter entry, and direct-struct-variable compiler cases are checked. The
existing compiler simulation as a whole remains admitted. A legacy scalar-
only variable invariant cannot describe structs; its two new inversion cases
are discharged by a checked impossibility lemma, not used as evidence for
the broader runtime theorem.

`coherent_bytes_array_read_progress` and
`coherent_bytes_array_read_preservation` now derive registered descriptor
reads directly from the shared coherent configuration. They need no extra
per-read packet-validity assumption. The native compiler also typechecks and
compiles the existing array and Ethernet/IPv4 examples, plus a temporary
primitive-struct initialization/field-read program. These are frontend/native
compilation checks, not new kernel runs. No admissions were added to the
new checked packet/binding modules.

### Accepted layouts and representable object addresses

Two actual-builder counterexamples exposed assumptions that the previous
copy/field proofs could not derive. A union's second member used the struct
field offset despite the union's smaller allocation; an explicitly reduced
alignment put a Bytes-containing field at byte offset one. These forms are
not emitted by the current BeePL parser, which produces plain struct members,
but the Coq program builder previously accepted them.

`BeeTypes.bcomposite_of_def` now checks ordinary struct/plain-member shape,
and natural minimum alignment at inline type uses and composite definitions.
Pointer pointees are not traversed.
The underlying C-layout calculation remains in `bcomposite_layout_of_def`;
the public program builder uses the checked entry point. The checks permit
safe increased alignment rather than requiring every attribute to be empty.
`program_composite_shape` derives struct/plain metadata from the actual
successful program build. The existing composite-consistency and intrinsic
Bytes-layout proofs compile with this guarded builder.

`aggregate_objects_valid` now also records a representable object end address.
Actual source allocations have sizes bounded by `Ptrofs.max_unsigned`, and
registered subobjects inherit that bound. This retains the address of an
empty trailing field without wrapping it to zero. The raw CompCert readable
range predicate still allows an exclusive end at `Ptrofs.modulus`; readability
alone is not the invariant for source object identities. The address-bound
frame, field-extension, subobject-extension, and fresh-copy descriptor proofs
have compiled. Integration into the complete runtime proof suite is still
being checked; these changes do not establish global type soundness.

The shared `packet_heap_invariant` now includes hereditary object/descriptor
coherence, defined in `BeePL_packet_object_layout.v`. For every declared
subobject, a registered descriptor is either disjoint or corresponds to a
complete Bytes leaf; packet payloads are separated from writable object
spans, including padding. This property is preserved through actual stores,
allocation, subobject registration, and fresh aggregate copies.

`BeePL_packet_location_coherence.v` derives the replacement plan from existing
runtime locations. A tracked aggregate supplies its embedded descriptor
coverage; a scalar-array representation cannot contain a Bytes leaf. Thus
this derivation does not require an additional tracked-object premise for
array sources. The core packet heap/replacement/copy/coherence modules and
this location-based derivation have passed normal `.vo` checking. Dependent
runtime wrappers and the full build remain under integration testing.

`coherent_field_read_progress` and `coherent_field_read_preservation` now pass
normal Coq checking. They require the actual program composite environment
and the shared coherent configuration, with no per-field layout/readiness
premise. They cover all complete field result kinds: scalar values (including
reference/option representations), aggregates, and Bytes. Preservation covers
every semantic successor; aggregate results register the subobject while
preserving packet coherence. The union counterexample is now a checked
builder-rejection regression.

Scalar-cell copy plans, relative scalar-cell alignment, and general copy
readiness are separate remaining obligations; deriving packet replacement
safety does not discharge them. General initialization/call preparation and
the global source/program adequacy and progress/preservation proofs also
remain unfinished.

`BeePL_packet_alignment.v` now proves `program_bytes_path_aligned`: every
Bytes object path in an accepted program has a pointer-aligned relative
offset, for an arbitrary root type. The proof transports checked member
metadata through environment construction, uses source sizes and natural
alignment (including zero-sized unit arrays), and does not assume C/source
size equality. Its main results are closed under the global context. Checked
regressions reject weakened definition/use-site alignment while accepting
increased alignment, arrays, and pointer members. The coherent aggregate-reference wrappers now
use program-environment equality to obtain packet alignment, rather than
requiring a separate packet-alignment premise.

The next initializer proof needs a destination-subrange operation: after one
field is initialized, the destination block is no longer wholly fresh. The
existing execution relations already dispatch scalar stores, aggregate
copies, and Bytes copies. A constructive prefix invariant must preserve
previously initialized fields/elements and register the complete parent only
when initialization finishes. Reusable ingredients include the new program
field layout/alignment facts, checked storage size bounds, typed cell copies,
and packet descriptor-copy/frame lemmas.

The composite builder does not yet establish unique field names, so existing
specialized NoDup premises cannot be assumed globally. Repeated field lookup
must be handled in the general initializer proof.

A later check corrected the earlier suspected standalone-array alignment
counterexample: `alignof_blockcopy` ignores array use-site alignment
annotations. An over-aligned one-byte element array still copies with
alignment one. The proposed storage rejection was removed, as was the
unnecessary builder stride-divisibility check; natural minimum field-placement
alignment remains checked. Source-size divisibility by actual copy alignment
is proved from the representation rather than imposed as a new restriction.
No general initializer progress claim follows from that audit alone.

This integrated batch passes the complete `make -j4 proof` and normal
`make -j4` builds, with logs at
`/tmp/beepl-layout-coherence-full-proof.log` and
`/tmp/beepl-layout-coherence-build.log`. Native `./ccomp -typecheck -S`
checks also produced assembly for the primitive struct/field probe,
`evaluation/examples/xdp_array.bpl`, and
`evaluation/examples/xdp_eth_ipv4.bpl`. `git diff --check` passes. These are
compiler/proof checks, not new kernel execution tests. The five legacy
admissions in `BeePL_typesystem_proofs.v` remain; global soundness is not
complete.

`BeePL_scalar_object_coherence.v` is now registered and checked as the next
foundation. Its hereditary relation permits only declared scalar leaves to
intersect an object/subobject; foreign cells in padding must be disjoint.
Together with existing coverage, it derives scalar-copy plans and relative
alignment using the checked program layout theorem. It preserves the relation
under subobject registration and fresh copying, and proves that actual
in-place copies preserve typed and located cells using existing destination
cell permissions. Reference and option scalar representations are included.
This relation has not yet been added to the shared runtime invariant, so the
existing public aggregate wrappers still expose their scalar-copy premises.
The complete registered proof target passes again after adding the module
(`/tmp/beepl-layout-coherence-final-proof.log`). No new admissions were added.

### Shared scalar coherence and constructive initializer slots

`initialized_object_memory` now carries hereditary scalar object coherence.
The independent definition and allocation/subobject framing are in
`BeePL_scalar_object_layout.v`; `BeePL_scalar_object_coherence.v` retains the
copy-plan derivations. `BeePL_initializer_coherence.v` establishes this
property for the existing primitive-array and primitive-struct initializers
from actual allocation and declared field/element layouts. The migration
covers unit arrays, scalar references, parameter storage, subobject reads,
aggregate references, and mutation. A reference-state helper that previously
lost allocation provenance now obtains it from the actual Ref execution
before proving fresh-copy coherence.

`BeePL_scalar_location_coherence.v` derives scalar-copy plans from runtime
locations, including the older callable primitive-array representation. It
also derives relative scalar alignment for those arrays using coherent cell
intervals and their indexed layout, without introducing an extra source-object
registration premise. Public aggregate-assignment wrappers no longer take a
scalar-copy-plan premise. Aggregate-reference wrappers derive both relative
cell alignment and source block-copy alignment. Their existing source-object
premise remains, as does full writable-span readiness in the general
assignment interface; neither is silently treated as solved.

`BeePL_object_separation.v` proves that paths through a common object are
separated or related by containment. Same-type objects are consequently
identical or nonoverlapping, including repeated field lookups and array
subobjects. It also derives absolute copy alignment from typed object
provenance and the actual program layout. For tracked source/destination
objects, `program_aggregate_copy_ready` derives all existing copy-readiness
fields except destination span permission. These pure provenance/layout
results are closed under the global context.

`BeePL_initializer_slot.v` provides checked operations at arbitrary destination
offsets in a partially initialized block: scalar/reference/option stores,
aggregate copies, Bytes descriptor copies, and unit-array no-ops. Resulting
cell/packet registries, coverage, descriptor typing, and prefix preservation
follow from actual operations. It also covers the formally typable nullable
function-pointer None case and proves the scalar case split exhaustive.
These are the reusable steps for general array/struct initialization; the
complete general initializer induction remains to be assembled.

The corrected alignment analysis yields `source_storage_copy_stride`, a
universal theorem relating source size to actual copy alignment. It requires
no new executable type restriction. The unnecessary alignment-annotation
rejections and builder stride guard were removed; underaligned field placement
remains rejected, and the general Bytes-path alignment theorem still checks.

The complete shared integration passes `make -j4 proof` and normal
`make -j4` (`/tmp/beepl-scalar-coherence-full-proof.log` and
`/tmp/beepl-scalar-coherence-build.log`). The rebuilt compiler typechecks and
emits native assembly for the struct/field probe, `xdp_array.bpl`, and
`xdp_eth_ipv4.bpl`. `git diff --check` passes. No kernel tests were run in this
proof batch. No admissions were added to the new modules; the five existing
admissions in `BeePL_typesystem_proofs.v` still mark unfinished global proofs.

### Allocation bounds and general scalar-array initialization

The shared heap now records bounded extents of source-owned data allocations
(`BeePL_block_extents.v` and `BeePL_heap_extents.v`). Each tracked data block
has an actual finite allocation range, Freeable permissions inside it, and no
permissions outside it. Allocation establishes the profile; actual stores,
field/array initialization, and parameter binding preserve it. Code blocks
and kernel-owned packet payloads are not treated as writable data allocations.
This is not an adequacy theorem for CompCert readonly globals or `Genv.init_mem`.

The profile rules out wrapped indexed array layouts and derives complete
readable ranges from their existing scalar cells. Empty arrays retain their
existing representation. `BeePL_callable_array_objects.v` proves readability
for both empty and nonempty primitive arrays; registering a complete object
with scalar and packet coherence is currently proved for positive lengths.
An empty array is not silently given the stronger object-coherence invariant.

The initialized heap and heap-evolution records carry this profile. Parameter
preparation derives it from actual allocations and bindings. The struct
initializer now exposes its exact store-context update, so its profile follows
from the new allocation and field stores rather than from store extension
alone. Targeted checks pass for the shared struct/control/read wrappers,
parameter entry, array/unit/reference/mutation wrappers, and existing execution
fixtures. The complete registered `make -j4 proof` and normal `make -j4`
builds also pass (`/tmp/beepl-block-extents-full-proof.log` and
`/tmp/beepl-block-extents-build.log`).

`BeePL_general_array_initialization.v` now passes normal Coq checking for the
constructive scalar-array fold: it produces the actual initializer execution,
typed and located cells, coherent intervals, packet framing, per-index coverage,
and cell provenance. It covers all inhabited nonvolatile scalar modes,
including reference/option representations and the nullable function-pointer
None case. Checked copy-prefix and packet/source framing lemmas support the
next aggregate/Bytes fold; that full fold and general struct initialization
remain unfinished.

`BeePL_extent_copy_readiness.v` now checks the program-level aggregate
assignment progress and every-successor preservation theorems. Whole-span copy
permissions follow from the profile; bounds, alignment, and non-overlap follow
from source provenance and the actual program layout. Source readability can
use callable arrays, including empty arrays, without a new source-object
premise. These interfaces require the shared configuration and aggregate kind;
they do not require a caller-provided copy-readiness proof. The global
progress/preservation theorem remains open.

`BeePL_copy_array_initialization.v` subsequently passes its normal target
(`/tmp/beepl-copy-array.log`). It constructs actual aggregate/Bytes array
initialization and preserves typed/located coherent cells and packet views,
with per-index scalar and Bytes coverage and exact copied-cell provenance.
Its concrete prestate source facts and destination leaf-alignment facts still
need to be derived in the general source initializer wrapper. The final parent
object's hereditary coherence and full runtime-configuration bridge are not
yet claimed.

### Packet-schema correction and repeated scalar fields

The packet Match schema rule now checks full-header storage admissibility.
The executable checker validates schema existence, plain primitive members,
field-binding types, storage admissibility, and the canonical default-attribute
pattern. `BeePL_packet_schema_check.v` proves the validator's exact specification;
`BeePL_packet_schema_audit.v` checks valid Boolean headers and rejection of
volatile fields, mismatched bindings, unknown schemas, and noncanonical pattern
attributes. The original gap accepted a header whose volatile cells could not
satisfy the source memory invariant. Native source AST headers already use
default attributes; this repair does not introduce a new field-layout policy.

`BeePL_packet_header_extents.v` and `BeePL_packet_header_layout.v` pass their
normal targets. They derive header profiles from actual allocation, byte copy,
and Boolean normalization, and establish primitive-header scalar coverage and
hereditary coherence using the actual program layout. Complete Bytes Match
runtime-state and substitution integration remains in progress.

`BeePL_structure_initializer_slots.v` passes its normal target
(`/tmp/beepl-structure-scalar-slots.log`). It derives scalar slot permissions
from a real allocation profile and alignment from declared source leaves.
Existing exact aliases are updated together; other cells and packet views
are framed. A constructive `sem_allocate_fields` fold covers all inhabited
scalar representations, including references/options, and permits repeated
writes to the same declared field. It does not assume unique field names,
absence of increased alignment annotations, or a separate 64-bit alignment
premise. The generic source initializer wrapper still needs to construct its
slot facts and handle aggregate/Bytes/unit fields; the checked fold is not
presented as the complete struct-initializer theorem.

### Checked aggregate Ref and Bytes Match heads

`BeePL_empty_array_reference.v` derives the actual zero-byte allocation/copy
state without registering a synthetic source object. Together with positive
callable-array registration and the existing object case,
`BeePL_located_aggregate_reference.v` proves program-level aggregate Ref
progress and every-successor preservation from the shared coherent
configuration and aggregate kind only. Source alignment, permissions, and
object-readiness premises are no longer caller obligations.

`BeePL_callable_scalar_arrays.v` extends the source-array bridge to reference
and option elements, deriving the common scalar chunk and positive element
size from actual typed indexed cells. Empty arrays can have non-scalar elements
and do not require a positive-size source-coherence assertion.

`BeePL_initialized_packet_header.v` now checks complete evaluated Bytes Match
progress and every-successor preservation from the shared runtime configuration.
Actual packet reads supply initialized header bytes and their length; actual
header allocation, copy, and Boolean normalization establish all heap fields.
The successful branch and short-packet fallback preserve typing, locations,
captured frames, scalar/object/packet coherence, and allocation profiles.
This closes that expression head, not the whole-expression induction.

The combined registered proof build passes (`make -j4 proof`,
`/tmp/beepl-schema-extents-full-proof.log`), as does the normal compiler build
(`make -j4`, `/tmp/beepl-schema-extents-build.log`). The rebuilt `./ccomp`
typechecks and emits native assembly for the struct/field probe,
`xdp_array.bpl`, `xdp_eth_ipv4.bpl`, and `xdp_tcp_syn.bpl`. No new kernel
execution is claimed by these compiler/proof checks.

`BeePL_scalar_structure_coverage.v` additionally passes its normal-flags Coq
check. It connects typed evaluated Sinit arguments and complete member names
to the scalar slot fold and whole-parent scalar coverage, including repeated
names and ref/option fields. Deriving slot metadata and integrating aggregate
and Bytes fields remain part of the general struct-initializer work.


## General array heads, parameter admission, and coherent composition

This batch closes the evaluated `Ainit` head for the existing type constructors.
`BeePL_array_copy_sources.v` derives source copy certificates from typed,
located values and the shared heap. `BeePL_array_packet_assembly.v`,
`BeePL_copy_array_heap.v`, and `BeePL_scalar_array_heap.v` assemble actual
initialization with complete object, scalar, packet, and allocation invariants.
`BeePL_general_array_configurations.v` performs the exhaustive case split and
proves `coherent_general_array_progress` and
`coherent_general_array_preservation`. Public callers supply the actual
program environment, coherent starting configuration, and evaluated argument
list, plus the actual step for preservation. They do not supply copy-readiness,
alignment, an output heap, or an element-kind restriction.

`BeePL_initializer_determinism.v` proves full-width assignment and array
initializer uniqueness. Initializers with different existential store metadata
still have the same actual allocated memory and resulting value. This allows
constructive progress results to establish preservation of every actual
successor rather than only a selected derivation.

`BeePL_structure_field_planning.v` extracts concrete field metadata from source
typing. `BeePL_scalar_structure_heap.v` and
`BeePL_scalar_structure_preservation.v` prove evaluated all-scalar struct
progress and every-successor preservation, including reference/option fields
and repeated names. `BeePL_structure_initializer_determinism.v` proves
execution uniqueness for all field kinds in actual program layouts. It does
not by itself establish existence or preservation for mixed copy-bearing
structures; their alias-safe copy fold is still under construction.

Two operational gaps are now explicitly rejected. `ty_arrayread` and
`ty_aaccess` require `is_funtype elem = false`. The executable checker uses
the same guard. `BeePL_function_array_state_audit.v` retains the witness that
a heap can satisfy initialized coverage with a direct-function array while
its read has no step, and proves that this read is now rejected by both
interfaces. This is a guard on unsupported reads, not a ban on all array
values or a new whole-heap assumption.

`BeePL_parameter_storage_check.v` admits direct immutable function aliases
or the existing `storage_type_check` for data. `ty_function` and
`type_check_function` now require this check on all parameters.
`BeePL_call_storage_audit.v` proves rejection of a volatile data parameter
while retaining the independently proved impossible binding operation. Values
with that annotation are not globally banned. The lexical-parameter proof now
states the admission requirement explicitly.
`BeePL_storage_parameter_allocations.v` constructs general data allocations
with their exact writable extents. `BeePL_copy_parameter_binding.v` proves an
actual aggregate/Bytes singleton binding and frames other pending targets and
remaining source values. `BeePL_general_parameter_binding.v` constructs the actual heterogeneous
binding-list execution for all admitted, inhabited data kinds, using typed
values, allocated extents, and prestate source certificates. This proves
existence of the binding execution; assembling the full initialized callee
heap along that execution remains unfinished.

`BeePL_general_array_reads.v` unifies scalar, aggregate, unit and Bytes reads;
`BeePL_general_named_array_reads.v` derives the equivalent named access using
actual local/global lookup and handles shadowing. Neither public interface
requires an element-kind/readiness premise. The aggregate dereference wrapper
in `BeePL_coherent_aggregate_dereference.v` derives the registered object from
the reference's runtime location. `BeePL_coherent_lists.v` carries the layout
coherence produced by each actual child step through expression-list
preservation, ready for the mutual expression induction.

Validation: the full registered `make -j4 proof` build passed after the core
repairs. The full native `make -j4` build passed. `./ccomp -typecheck -S`
succeeded for `xdp_array.bpl`, `xdp_eth_ipv4.bpl`, `xdp_tcp_syn.bpl`, and the
existing temporary scalar-structure fixture. New head/list modules also passed
individual Coq checks and were registered in both build manifests. No kernel
tests were run in this proof batch. Whole-language soundness is still not
claimed: the five legacy admissions and the final integration obligations
remain.


## Scoped Match variables and expression-case assembly

A typed counterexample established that the former `Match` free-variable
calculation counted pattern-bound names as free. Substituting an outer `Bind`
with the same name therefore appeared to introduce a free variable: the outer
binding removed the name from its set, while substitution correctly respected
the inner pattern binder. This obstructed preservation of `For`'s disjointness
side conditions. It was not sound to assume generic free-variable decrease.

`BeePL.v` now computes each match branch's free variables after removing all
variables bound by its corresponding pattern, including packet-header and
field binders. Missing-pattern malformed syntax conservatively retains its
remaining branch variables; substitution behavior for malformed syntax is
unchanged. Existing `vars_bound_by` was moved before this calculation and is
shared by scope analysis and substitution.

`BeePL_loop_freevars_audit.v` retains the typed witness and actual reduction,
now proving both sides have the empty free-variable set.
`BeePL_substitution_freevars.v` preserves the existing weak substitution
inclusion and disjointness results. The stronger
`typed_value_substitution_removes_variable` in
`BeePL_typed_substitution_freevars.v` proves inclusion in the original set with
the substituted name removed. Typing is necessary here because arbitrary
malformed match lists retain their old substitution behavior.
`BeePL_match_arity.v` derives the required structural arity from typing and
preserves it through substitutions. `BeePL_packet_match_freevars.v` handles
actual header and field instantiation, and `BeePL_step_freevars.v` proves
free-variable nonincrease for typed small steps and their expression lists.
These results do not assume a future heap or a post-step disjointness fact.
`BeePL_coherent_loop_contexts.v` uses them to prove preservation for both
stepping loop bounds, deriving the updated disjointness checks from typing
and the actual child step.

`BeePL_coherent_array_contexts.v` lifts array-read operands and actual guarded
array-initializer argument steps. `BeePL_coherent_memory_contexts.v` lifts Ref,
Deref, field access, and both assignment operands while retaining suspended
operands' typing, locations, captured environments, and heap coherence.
`BeePL_coherent_literals.v` covers Const, Unit, and Addr.
`BeePL_general_reference_heads.v` and `BeePL_general_memory_heads.v` combine
the existing scalar and aggregate results into exhaustive typed Ref/Deref/
Massgn heads. `BeePL_reference_induction.v` proves the complete Ref expression
case from the proper operand's induction hypothesis. These are components of
the final mutual theorem, not a completed whole-language theorem.

Parameter work now includes actual allocation and heterogeneous data binding
from a coherent caller heap (`general_data_parameter_preparation_total`),
without caller-provided copy-readiness. The separate
`BeePL_scalar_parameter_heap.v`, `BeePL_aggregate_parameter_heap.v`, and
`BeePL_bytes_parameter_heap.v` construct complete shared-heap transitions for
individual independently preallocated slots. `BeePL_parameter_packet_assembly.v`
provides the common packet/object assembly. Iterating these full-state results
and constructing all callee environment bindings remains in progress.
`BeePL_mixed_structure_fields.v` and `BeePL_mixed_structure_coverage.v` now
check the actual mixed scalar/aggregate/Bytes field execution and whole-parent
coverage, including repeated field aliases; final structure heap/source
configuration integration remains in progress.

Validation: full registered `make -j4 proof` and native `make -j4` passed after
the scoped-variable correction. `xdp_loop.bpl`, `xdp_loop_limits.bpl`, and
`xdp_option_some.bpl` still compile with `./ccomp -typecheck -S`.
The previous compiler rejected the new source regression's loop guard; the
rebuilt compiler accepts it and emits assembly. The reproducible fixture is
`evaluation/tests/accept/loop_pattern_scope.bpl`, with its complete compile
command in the header. It is a compiler regression, not a claim of kernel
execution. The new proof modules were individually checked and registered in
both build manifests. Five legacy admissions and the final global integration
obligations still remain.
