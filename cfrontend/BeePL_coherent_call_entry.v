Require Import BeePL_heap_extents BeePL_parameter_extents.
(* Entry into a source function with initialized aggregate descriptors.
   BeePL_initialized_application_entry connects this preparation record to the
   recursive initialized_runtime_configuration predicate. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_entry BeePL_call_entry BeePL_frame_free BeePL_code_contracts.
Require Import BeePL_scalar_parameters BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_parameters.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.

Require Import BeePL_initialized_call_entry BeePL_coherent_parameters BeePL_layout_coherence.

Theorem coherent_parameter_call_entry :
  forall ge Gamma globals Sigma p caller m objects cells packets v annotation fn_effects
    args effects result variadic es argument_effects,
  internal_code_contract ge globals Sigma ->
  type_expr ge.(genv_cenv) Gamma Sigma (Val v annotation) fn_effects (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations ge cells) (Val v annotation) ->
  type_exprs ge.(genv_cenv) Gamma Sigma es argument_effects args ->
  Forall (fun e => exists value ty, e = Val value ty) es ->
  all_expr_locations (runtime_locations (packet_heap_locations ge cells objects packets)) es ->
  Forall call_parameter_type args ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells -> packet_heap_invariant ge Sigma m objects cells packets -> coherent_layout cells ->
  heap_block_extents Sigma m objects cells packets ->
  packet_variable_layout Gamma Sigma ge caller cells objects packets ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  (forall b fn, Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations ge cells objects packets) fn.(fn_body)) ->
  (forall fn, Genv.find_funct ge (trans_bvalue_cvalue v) = Some (Internal fn) -> frame_free fn.(fn_body)) ->
  exists fn callee initialized Sigma',
    ssem_expr ge p caller m (App (Val v annotation) es result)
      initialized caller (CallFrame callee fn.(fn_body) result) /\
    store_context_extends Sigma Sigma' /\ internal_code_contract ge globals Sigma' /\
    initialized_entry_frame ge Gamma (bind_vars globals fn.(fn_args)) Sigma'
      caller callee initialized objects (extended_parameter_call_layout cells callee fn.(fn_args)) packets
      fn.(fn_body) effects result /\
    coherent_layout (extended_parameter_call_layout cells callee fn.(fn_args)).
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets v annotation fn_effects
    args effects result variadic es argument_effects Hcode Hfunction Hlocation
    Harguments Hvalues Harglocations Hsupported Hblocks Hmemory Hpackets Hcoherent Hextent Hcaller Hglobals Hbodies Hsource.
  destruct (located_function_value _ _ _ _ _ _ _ _ _ _ _ Hfunction Hlocation)
    as [b [fn [Hv [Hannotation [Hef [Hfind Hsignature]]]]]].
  subst v annotation fn_effects.
  pose proof (Hcode b fn Hfind) as Hfn.
  unfold type_of_function in Hsignature. inversion Hsignature; subst args effects result variadic.
  assert (Hfacts : call_parameter_values ge.(genv_cenv) Sigma
    (packet_heap_locations ge cells objects packets) (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_call_arguments; eauto. }
  pose proof (packet_call_parameter_values _ _ _ _ _ _ _ Hfacts) as Hdatafacts.
  assert (Htypes : typeof_exprs es = seq.unzip2 (fn_args fn)) by
    (eapply typed_arguments_annotations; eauto).
  inversion Hfn; subst.
  assert (Hnames : NoDup (map fst (fn_args fn))) by
    (apply parameter_names_nodup; assumption).
  assert (Hparamtypes : Forall (fun param => call_parameter_type (snd param)) (fn_args fn)).
  { clear - Hfacts. induction Hfacts; constructor; tauto. }
  destruct (coherent_initialized_parameter_preparation ge Sigma m objects cells
    (fn_args fn) (extract_values_exprs es) Hnames Hdatafacts Hblocks Hmemory Hcoherent)
    as [callee [allocated [initialized [Sigma' [Halloc [Hbind [Hext [Hblocks' [Hmemory' Hcoherent']]]]]]]]].
  assert (Hbodytyped : type_expr ge.(genv_cenv) (bind_vars globals (fn_args fn)) Sigma'
    (fn_body fn) (fn_effect fn) (fn_return fn)).
  { eapply (proj2 typing_store_extension); eauto. }
  exists fn, callee, initialized, Sigma'. split.
  - rewrite <- Htypes. eapply ssem_app3; eauto; reflexivity.
  - split; [exact Hext|]. split.
    + eapply internal_code_contract_store_extension; eauto.
    + split; [|exact Hcoherent']. constructor; try assumption.
      * eapply parameter_preparation_extents; eauto.
      * eapply parameter_preparation_packet_heap; eauto.
      * eapply packet_variable_layout_extend with (Sigma := Sigma) (cells := cells)
          (objects := objects) (packets := packets);
          [exact Hext|intros; left; assumption|auto|auto|exact Hcaller].
      * eapply callee_parameter_packet_variable_layout; eauto.
      * eapply runtime_locations_monotone; [|apply (Hbodies b fn Hfind)].
        apply packet_heap_locations_monotone; [intros; left; assumption |auto|auto].
      * apply Hsource. exact Hfind.
Qed.

Print Assumptions initialized_entry_frame_typing.
Print Assumptions coherent_parameter_call_entry.
