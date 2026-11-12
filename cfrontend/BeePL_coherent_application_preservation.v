Require Import BeePL_heap_extents BeePL_parameter_extents.
(* Every actual step of a fully evaluated application preserves the initialized
   runtime configuration, including the argument-list identity alternative. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_callable_locations BeePL_callable_variables BeePL_code_contracts.
Require Import BeePL_frame_free BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_application_configuration.
Require Import BeePL_parameter_application_preservation BeePL_initialized_runtime.
Require Import BeePL_initialized_application_entry.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.

Require Import BeePL_coherent_configurations BeePL_coherent_application_entry.

Theorem coherent_direct_application_preservation :
  forall ge Gamma globals Sigma p caller m objects cells packets v args effects result variadic es ef
    m' caller' e',
  coherent_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract ge globals Sigma ->
  Forall call_parameter_type args ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  (forall b fn, Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations ge cells objects packets) fn.(fn_body)) ->
  (forall fn, Genv.find_funct ge (trans_bvalue_cvalue v) = Some (Internal fn) ->
    frame_free fn.(fn_body)) ->
  ssem_expr ge p caller m
    (App (Val v (Ftype args effects result variadic)) es result) m' caller' e' ->
  caller' = caller /\ exists Sigma' cells',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects cells' packets /\
    internal_code_contract ge globals Sigma' /\
    coherent_runtime_configuration ge Gamma Sigma' caller' m' objects cells' packets e' ef result.
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets v args effects result variadic es ef
    m' caller' e' Hinitial Hvalues Hcode Hscalar Hglobals Hbodies Hsource Hstep.
  pose proof Hinitial as Hparts.
  destruct Hparts as [[Hheap Htyped [Hcallee Hargsloc] Hframes] Hcoherent].
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  assert (Hcallable : runtime_locations (callable_heap_locations ge cells)
    (Val v (Ftype args effects result variadic))).
  { destruct (typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Hfunction)
      as [Hnil [Hannotation [b Hv]]]. subst v. simpl in Hcallee |- *.
    eapply packet_function_location_callable; exact Hcallee. }
  destruct (located_function_value ge Gamma Sigma cells v
    (Ftype args effects result variadic) nil args effects result variadic Hfunction Hcallable)
    as [b [fn [Hv [Hannotation [Hnil [Hfind Hsignature]]]]]]. subst v.
  assert (Hargs_fn : type_exprs ge.(genv_cenv) Gamma Sigma es nil (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Harguments. }
  assert (Hscalar_fn : Forall call_parameter_type (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Hscalar. }
  assert (Hfacts : call_parameter_values ge.(genv_cenv) Sigma
    (packet_heap_locations ge cells objects packets) (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_call_arguments; eauto. }
  destruct (coherent_direct_application_entry ge Gamma globals Sigma p caller m objects cells packets
    (Vloc b Ptrofs.zero) args effects result variadic es effects
    Hinitial Hvalues Hcode Hscalar Hglobals Hbodies Hsource)
    as [chosen [callee [initialized [Sigma' [Hentry [Hupdate [Hcode' Hfinal]]]]]]].
  destruct (evaluated_parameter_application_entry_unique ge p caller m b
    (Ftype args effects result variadic) es result fn callee (fn_body chosen) initialized
    ge.(genv_cenv) Sigma (packet_heap_locations ge cells objects packets)
    Hfind Hvalues Hfacts Hentry m' caller' e' Hstep)
    as [Hcaller Hcases]. subst caller'. split; [reflexivity |].
  destruct Hcases as [[Hm He] | [Hm He]]; subst m' e'.
  - exists Sigma, cells. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; assumption.
  - exists Sigma', (extended_parameter_call_layout cells callee (fn_args chosen)).
    split; [exact Hupdate |]. split; assumption.
Qed.

Print Assumptions coherent_direct_application_preservation.
