Require Import BeePL_heap_extents BeePL_parameter_extents.
(* Entry into a source function with initialized aggregate descriptors.
   BeePL_initialized_application_entry connects this preparation record to the
   recursive initialized_runtime_configuration predicate. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_entry BeePL_call_entry BeePL_frame_free BeePL_code_contracts.
Require Import BeePL_scalar_parameters BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_parameters.
Import ListNotations.
Local Open Scope Z_scope.

Require Import BeePL_soundness_variables.
Require Import BeePL_call_state BeePL_scalar_call_layout.
Require Import BeePL_packet_descriptor_copy BeePL_packet BeePL_packet_state BeePL_packet_mutation BeePL_packet_heap BeePL_packet_bindings BeePL_parameter_allocations.

Lemma packet_value_locations_nonbytes : forall ge cells objects packets v ty,
  ty <> Bytes -> value_locations (packet_heap_locations ge cells objects packets) v ty ->
  value_locations (descriptor_heap_locations ge cells objects) v ty.
Proof.
  intros ge cells objects packets. fix IH 1. intros v ty Hnot Hloc.
  destruct v as [|boolean|integer|long|block offset|optionvalue]; simpl in *; auto.
  - eapply packet_heap_locations_nonbytes; eauto.
  - destruct optionvalue as [payload|]; simpl in *; auto.
    destruct ty; try contradiction. destruct p; try contradiction.
    eapply IH; [discriminate|exact Hloc].
Qed.

Lemma packet_call_parameter_values : forall ge Sigma cells objects packets params values,
  call_parameter_values ge.(genv_cenv) Sigma
    (packet_heap_locations ge cells objects packets) params values ->
  call_parameter_values ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge cells objects) params values.
Proof.
  intros ge Sigma cells objects packets params values H. induction H; constructor; auto.
  destruct H as [Hsupported [Htyped Hlocated]]. repeat split; try assumption.
  eapply packet_value_locations_nonbytes; [|exact Hlocated].
  destruct Hsupported as [Hunit|[[[pt Heq]|[[bt [attr Heq]]|[bt [attr Heq]]]] Hvolatile]];
    congruence.
Qed.

Lemma parameter_allocation_packet_frame :
  forall ge Sigma vm m params callee allocated Sigma' packets,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  packet_state_valid m packets ->
  packet_state_valid allocated packets /\ packet_views_preserved m allocated packets.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' packets Ha.
  induction Ha; intros Hv.
  - split; [exact Hv|]. unfold packet_views_preserved. intros; assumption.
  - unfold balloc in H.
    destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [next fresh] eqn:Halloc.
    inversion H; subst.
    destruct (IHHa ltac:(eapply packet_state_allocation_preserved; eauto)) as [Hv' Hviews].
    split; [exact Hv'|]. intros descriptor offset Hin view Hview.
    apply Hviews; [exact Hin|]. eapply packet_descriptor_alloc_frame; eauto.
Qed.

Lemma parameter_binding_packet_frame :
  forall ge vm m params values final packets,
  bind_variables ge vm m params values final ->
  packet_state_valid m packets ->
  (forall id ty b, In (id,ty) params -> vm ! id = Some (b,ty) ->
    packet_block_disjoint m packets b) ->
  packet_state_valid final packets /\ packet_views_preserved m final packets.
Proof.
  intros ge vm m params values final packets Hb. induction Hb; intros Hv Hap.
  - split; [exact Hv|]. unfold packet_views_preserved. intros; assumption.
  - destruct (packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hv
      (Hap id ty b ltac:(left; reflexivity) H) H0) as [Hv1 Hview1].
    destruct (IHHb Hv1) as [Hv2 Hview2].
    + intros name t block Hin Hget. eapply packet_block_disjoint_frame with (m := m); [exact Hv|exact Hview1|].
      eapply Hap; [right; exact Hin|exact Hget].
    + split; [exact Hv2|]. intros descriptor offset Hin view Hview.
      apply Hview2; auto.
  - apply IHHb; [exact Hv|]. intros name t block Hin Hget.
    eapply Hap; [right; exact Hin|exact Hget].
Qed.

Theorem parameter_preparation_packet_heap :
  forall ge Sigma vm m params callee allocated Sigma' values final objects cells packets,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  bind_variables ge callee allocated params values final ->
  NoDup (map fst params) -> store_context_extends Sigma Sigma' ->
  packet_heap_invariant ge Sigma m objects cells packets ->
  packet_heap_invariant ge Sigma' final objects
    (extended_parameter_call_layout cells callee params) packets.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' values final objects cells packets
    Ha Hb Hnames Hext [Hv Htyped Hcovered Hseparated HobjectCoherence].
  destruct (parameter_allocation_packet_frame _ _ _ _ _ _ _ _ _ Ha Hv) as [Hva Hviews].
  destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Ha Hnames) as [Hslots Hdistinct].
  assert (Hapart : forall id ty b, In (id,ty) params -> callee ! id = Some (b,ty) ->
    packet_block_disjoint allocated packets b).
  { intros id ty b Hin Hget. destruct (Hslots id ty Hin) as [fresh [Hlookup [Hfresh Hrest]]].
    rewrite Hget in Hlookup; inversion Hlookup; subst fresh.
    intros descriptor offset Hpacket. split.
    - intro Heq; subst descriptor. apply Hfresh.
      destruct (Hv _ _ Hpacket) as [_ [view [bytes [Hdesc Hrest']]]].
      eapply packet_descriptor_source_block; eauto.
    - intros view Hview Heq. apply Hfresh.
      pose proof (preserved_packet_view_origin _ _ _ Hv Hviews _ _ _ Hpacket Hview) as Hold.
      rewrite <- Heq. exact (proj1 (proj2 (proj2 (proj2 Hold)))). }
  destruct (parameter_binding_packet_frame _ _ _ _ _ _ _ Hb Hva Hapart) as [Hvf Hbindviews].
  assert (Hviewsfinal : packet_views_preserved m final packets).
  { intros d o Hin v Hd. apply Hbindviews; auto. }
  constructor.
  - exact Hvf.
  - intros b ofs Hin; eapply object_type_at_store_extension; eauto.
  - exact Hcovered.
  - intros b ofs ty chunk [Hold|[Hscalar [id [Hin [Hget [Hofs Hchunk]]]]]].
    + eapply packet_write_separation_frame with (m := m); [exact Hv|exact Hviewsfinal|].
      eapply Hseparated; exact Hold.
    + apply packet_block_disjoint_write. eapply packet_block_disjoint_frame with (m := allocated);
        [exact Hva|exact Hbindviews|]. eapply Hapart; eauto.
  - eapply packet_object_coherence_frames; [exact Hv|exact Hviewsfinal|exact HobjectCoherence].
Qed.

Theorem callee_parameter_packet_variable_layout :
  forall bge Sigma Sigma' Gamma old objects packets params callee m allocated,
  packet_variable_layout Gamma Sigma bge empty_vmap old objects packets ->
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => call_parameter_type (snd param)) params ->
  store_context_extends Sigma Sigma' ->
  packet_variable_layout (bind_vars Gamma params) Sigma' bge callee
    (extended_parameter_call_layout old callee params) objects packets.
Proof.
  intros bge Sigma Sigma' Gamma old objects packets params callee m allocated
    Hglobals Halloc Hnames Hscalars Hextends x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - apply packet_variable_callable. destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots x ty Hin) as [b [Hget Hrest]].
    rewrite Forall_forall in Hscalars.
    specialize (Hscalars (x, ty) Hin). simpl in Hscalars.
    destruct Hscalars as [Hunit | Hscalar].
    + subst ty. eapply callable_variable_data with (b := b).
      * left; exact Hget.
      * apply heap_variable_unit.
      * reflexivity.
    + eapply callable_variable_data with (b := b).
      * left; exact Hget.
      * apply heap_variable_scalar with (chunk := scalar_parameter_chunk ty).
        right. split; [exact Hscalar|]. exists x.
        split; [exact Hin|]. split; [exact Hget|]. split; reflexivity.
      * apply scalar_parameter_not_function. exact Hscalar.
  - assert (Habsent : PTree.get x callee = None).
    { eapply parameter_allocation_missing_lookup; eauto. }
    destruct (Hglobals x ty Hglobal) as [Hcall|b Hloc Hkind Hobject|b Hloc Hbytes Hpacket].
    2: { eapply packet_variable_aggregate; [|exact Hkind|exact Hobject].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]].
      - unfold empty_vmap in Hlocal; rewrite PTree.gempty in Hlocal; discriminate.
      - right; split; assumption. }
    2: { eapply packet_variable_bytes; [|exact Hbytes|exact Hpacket].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]].
      - unfold empty_vmap in Hlocal; rewrite PTree.gempty in Hlocal; discriminate.
      - right; split; assumption. }
    apply packet_variable_callable.
    destruct Hcall as [b Hlocation Hbinding Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
    + eapply callable_variable_data with (b := b); [| |exact Hnonfun].
      * destruct Hlocation as [Hlocal|[Hnone Hsymbol]].
        -- unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
        -- right. split; assumption.
      * eapply heap_variable_binding_extend; [exact Hextends| |exact Hbinding].
        intros block ofs t chunk Hentry. left; exact Hentry.
    + eapply callable_variable_code; eauto.
    + unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
Qed.


Record initialized_entry_frame (ge : genv) (Gamma callee_Gamma : ty_context)
    (Sigma : store_context) (caller callee : vmap) (m : Mem.mem)
    (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations)
    (body : expr) (effects : effect) (result : type) : Prop := {
  entry_frame_blocks : store_blocks_valid Sigma m;
  entry_frame_objects : initialized_object_memory ge Sigma m objects cells;
  entry_frame_extents : heap_block_extents Sigma m objects cells packets;
  entry_frame_packets : packet_heap_invariant ge Sigma m objects cells packets;
  entry_frame_caller : packet_variable_layout Gamma Sigma ge caller cells objects packets;
  entry_frame_callee : packet_variable_layout callee_Gamma Sigma ge callee cells objects packets;
  entry_frame_body_typing : type_expr ge.(genv_cenv) callee_Gamma Sigma body effects result;
  entry_frame_body_locations : runtime_locations (packet_heap_locations ge cells objects packets) body;
  entry_frame_body_source : frame_free body
}.

Lemma initialized_entry_frame_typing : forall ge Gamma callee_Gamma Sigma caller callee m objects cells packets body effects result,
  initialized_entry_frame ge Gamma callee_Gamma Sigma caller callee m objects cells packets body effects result ->
  type_expr ge.(genv_cenv) Gamma Sigma (CallFrame callee body result) effects result /\
  runtime_locations (packet_heap_locations ge cells objects packets) (CallFrame callee body result).
Proof. intros. destruct H. split; [eapply ty_callframe; eauto | assumption]. Qed.

Theorem initialized_parameter_call_entry :
  forall ge Gamma globals Sigma p caller m objects cells packets v annotation fn_effects
    args effects result variadic es argument_effects,
  internal_code_contract ge globals Sigma ->
  type_expr ge.(genv_cenv) Gamma Sigma (Val v annotation) fn_effects (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations ge cells) (Val v annotation) ->
  type_exprs ge.(genv_cenv) Gamma Sigma es argument_effects args ->
  Forall (fun e => exists value ty, e = Val value ty) es ->
  all_expr_locations (runtime_locations (packet_heap_locations ge cells objects packets)) es ->
  Forall call_parameter_type args ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  packet_heap_invariant ge Sigma m objects cells packets ->
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
      fn.(fn_body) effects result.
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets v annotation fn_effects
    args effects result variadic es argument_effects Hcode Hfunction Hlocation
    Harguments Hvalues Harglocations Hsupported Hblocks Hmemory Hpackets Hextent Hcaller Hglobals Hbodies Hsource.
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
  destruct (initialized_object_parameter_preparation ge Sigma m objects cells
    (fn_args fn) (extract_values_exprs es) Hnames Hdatafacts Hblocks Hmemory)
    as [callee [allocated [initialized [Sigma' [Halloc [Hbind [Hext [Hblocks' Hmemory']]]]]]]].
  assert (Hbodytyped : type_expr ge.(genv_cenv) (bind_vars globals (fn_args fn)) Sigma'
    (fn_body fn) (fn_effect fn) (fn_return fn)).
  { eapply (proj2 typing_store_extension); eauto. }
  exists fn, callee, initialized, Sigma'. split.
  - rewrite <- Htypes. eapply ssem_app3; eauto; reflexivity.
  - split; [exact Hext|]. split.
    + eapply internal_code_contract_store_extension; eauto.
    + constructor; try assumption.
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
Print Assumptions initialized_parameter_call_entry.
