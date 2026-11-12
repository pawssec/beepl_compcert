Require Import BeePL_heap_extents BeePL_parameter_extents.
(* Evaluated application entry in the initialized-object runtime invariant. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_callable_locations BeePL_callable_variables BeePL_code_contracts.
Require Import BeePL_frame_free BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_application_configuration.
Require Import BeePL_initialized_call_entry BeePL_initialized_runtime.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.

Lemma descriptor_function_location_callable : forall ge cells objects b ofs args effects result variadic,
  descriptor_heap_locations ge cells objects b ofs (Ftype args effects result variadic) ->
  callable_heap_locations ge cells b ofs (Ftype args effects result variadic).
Proof.
  intros ge cells objects b ofs args effects result variadic [Hcall|Hdescriptor]; auto.
  destruct Hdescriptor as [[Hkind _]|[basic [attr [Hty Hrest]]]]; discriminate.
Qed.

Lemma packet_function_location_callable : forall ge cells objects packets b ofs args effects result variadic,
  packet_heap_locations ge cells objects packets b ofs (Ftype args effects result variadic) ->
  callable_heap_locations ge cells b ofs (Ftype args effects result variadic).
Proof.
  intros. eapply descriptor_function_location_callable.
  eapply packet_heap_locations_nonbytes; [discriminate|eassumption].
Qed.

Theorem initialized_entry_frame_configuration :
  forall ge Gamma callee_Gamma Sigma caller callee m objects cells packets body effects result,
  initialized_entry_frame ge Gamma callee_Gamma Sigma caller callee m objects cells packets body effects result ->
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (CallFrame callee body result) effects result.
Proof.
  intros ge Gamma callee_Gamma Sigma caller callee m objects cells packets body effects result
    [Hblocks Hmemory Hextent Hpackets Hcaller Hcallee Htyped Hlocations Hsource].
  constructor.
  - constructor; assumption.
  - eapply ty_callframe; exact Htyped.
  - exact Hlocations.
  - simpl. exists callee_Gamma, effects. split; [exact Hcallee|]. split; [exact Htyped|].
    apply frame_free_initialized_frames. exact Hsource.
Qed.

Theorem initialized_direct_application_entry :
  forall ge Gamma globals Sigma p caller m objects cells packets v args effects result variadic es ef,
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract ge globals Sigma ->
  Forall call_parameter_type args ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  (forall b fn, Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations ge cells objects packets) fn.(fn_body)) ->
  (forall fn, Genv.find_funct ge (trans_bvalue_cvalue v) = Some (Internal fn) -> frame_free fn.(fn_body)) ->
  exists fn callee initialized Sigma',
    ssem_expr ge p caller m (App (Val v (Ftype args effects result variadic)) es result)
      initialized caller (CallFrame callee fn.(fn_body) result) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' initialized objects
      (extended_parameter_call_layout cells callee fn.(fn_args)) packets /\
    internal_code_contract ge globals Sigma' /\
    initialized_runtime_configuration ge Gamma Sigma' caller initialized objects
      (extended_parameter_call_layout cells callee fn.(fn_args)) packets
      (CallFrame callee fn.(fn_body) result) ef result.
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets v args effects result variadic es ef
    [Hheap Htyped Hlocations Hframes] Hvalues Hcode Hsupported Hglobals Hbodies Hsource.
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpackets Hextent].
  destruct Hlocations as [Hfunlocated Hargslocated].
  assert (Hcallable : runtime_locations (callable_heap_locations ge cells)
    (Val v (Ftype args effects result variadic))).
  { destruct (typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Hfunction)
      as [Hnil [Hannotation [b Hv]]]. subst v. simpl in Hfunlocated |- *.
    eapply packet_function_location_callable; exact Hfunlocated. }
  destruct (initialized_parameter_call_entry ge Gamma globals Sigma p caller m objects cells packets
    v (Ftype args effects result variadic) nil args effects result variadic es nil
    Hcode Hfunction Hcallable Harguments Hvalues Hargslocated Hsupported Hblocks Hmemory Hpackets Hextent
    Hbindings Hglobals Hbodies Hsource)
    as [fn [callee [initialized [Sigma' [Hstep [Hext [Hcode' Hentry]]]]]]].
  exists fn, callee, initialized, Sigma'. split; [exact Hstep|]. split.
  - destruct Hentry as [Hblocks' Hmemory' Hextent' Hpackets' Hcaller Hcallee Hbody Hlocated Hfree].
    constructor; try assumption; intros; try assumption. left; assumption.
  - split; [exact Hcode'|]. apply initialized_entry_frame_configuration with
      (callee_Gamma := bind_vars globals (fn_args fn)). exact Hentry.
Qed.

Print Assumptions initialized_entry_frame_configuration.
Print Assumptions initialized_direct_application_entry.
