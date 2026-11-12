(* Program facts needed by the whole-expression induction. These concern code
   typing, global bindings, and source bodies; they do not assert that a step
   exists or that its result satisfies the runtime invariant. Full parameter
   preparation is proved in BeePL_general_call_preparation; initial program
   adequacy is addressed separately in BeePL_initial_program. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_code_contracts BeePL_frame_free BeePL_packet_bindings.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_aggregate_memory BeePL_packet_state.

Record program_runtime_invariant (ge : genv) (globals : ty_context) (Sigma : store_context)
    (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations) : Prop := {
  program_runtime_code : internal_code_contract ge globals Sigma;
  program_runtime_globals : packet_variable_layout globals Sigma ge empty_vmap cells objects packets;
  program_runtime_bodies : forall b fn,
    Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations ge cells objects packets) fn.(fn_body);
  program_runtime_source : forall b fn,
    Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) -> frame_free fn.(fn_body)
}.

Theorem program_runtime_invariant_evolve :
  forall ge globals Sigma objects cells packets Sigma' m' objects' cells' packets',
  program_runtime_invariant ge globals Sigma objects cells packets ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  program_runtime_invariant ge globals Sigma' objects' cells' packets'.
Proof.
  intros * [Hcode Hglobals Hbodies Hsource]
    [Hstore Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents].
  constructor.
  - eapply internal_code_contract_store_extension; eauto.
  - eapply packet_variable_layout_extend; eauto.
  - intros b fn Hfind. eapply runtime_locations_monotone; [|exact (Hbodies b fn Hfind)].
    apply packet_heap_locations_monotone; assumption.
  - exact Hsource.
Qed.

Record program_runtime_configuration (p : program) (globals Gamma : ty_context)
    (Sigma : store_context) (vm : vmap) (m : Mem.mem) (objects : aggregate_object_context)
    (cells : scalar_layout) (packets : packet_locations) (e : expr) (ef : effect) (ty : type) : Prop := {
  program_configuration_code : program_runtime_invariant (globalenv p) globals Sigma objects cells packets;
  program_configuration_expression : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets e ef ty
}.

Lemma program_runtime_configuration_after_step :
  forall p globals Gamma Sigma vm m objects cells packets e ef ty
    Sigma' vm' m' objects' cells' packets' e' ef',
  program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
  initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' m' objects' cells' packets' e' ef' ty ->
  program_runtime_configuration p globals Gamma Sigma' vm' m' objects' cells' packets' e' ef' ty.
Proof.
  intros * [Hprogram Hconfig] Hevolution Hconfig'. constructor; [|exact Hconfig'].
  eapply program_runtime_invariant_evolve; eauto.
Qed.

Print Assumptions program_runtime_invariant_evolve.
