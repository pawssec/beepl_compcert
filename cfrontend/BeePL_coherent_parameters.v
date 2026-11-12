(* Fresh parameter blocks retain coherence independently of their scalar value
   representation. Unit slots add no cells; stored slots use canonical chunks. *)
Require Import Coqlib List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_layout_coherence.
Require Import BeePL_call_bindings BeePL_parameter_allocations BeePL_scalar_parameters.
Require Import BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_parameters.
Import ListNotations.

Theorem allocated_parameter_layout_coherent :
  forall ge cenv ValueSigma Sigma Sigma' cells vm m params callee allocated,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  NoDup (map fst params) -> coherent_layout cells -> typed_memory_layout cenv ValueSigma cells m ->
  coherent_layout (extended_parameter_call_layout cells callee params).
Proof.
  intros ge cenv ValueSigma Sigma Sigma' cells vm m params callee allocated Halloc Hnames Hcoherent Hmemory.
  destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames) as [Hslots [Hdup Hdistinct]].
  assert (Hfresh : forall id ty b, In (id, ty) params -> PTree.get id callee = Some (b, ty) ->
    forall ofs t chunk, ~ cells b ofs t chunk).
  { intros id ty b Hin Hlookup ofs t chunk Hcell.
    destruct (Hslots id ty Hin) as [target [Hget [Hnew Hrest]]].
    assert (target = b) by congruence. subst target. apply Hnew.
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
      [exact (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell))|constructor]. }
  intros b ofs ty chunk Hentry old off t ch Hold.
  destruct Hentry as [Hentry|[Hscalar [id [Hin [Hget [Hofs Hchunk]]]]]];
    destruct Hold as [Hold|[Hscalar' [id' [Hin' [Hget' [Hoff Hch]]]]]].
  - eapply Hcoherent; eauto.
  - right; left. intro Heq. subst old. eapply Hfresh; eauto.
  - right; left. intro Heq. subst old. eapply Hfresh; eauto.
  - destruct (peq old b) as [Heq|Hneq]; [|right; left; exact Hneq]. subst old.
    assert (id = id') by (eapply Hdistinct; eauto). subst id'.
    assert (t = ty) by congruence. subst t ofs off chunk ch. left. repeat split; reflexivity.
Qed.

Theorem coherent_initialized_parameter_preparation :
  forall ge Sigma m objects cells params values,
  NoDup (map fst params) ->
  call_parameter_values ge.(genv_cenv) Sigma (descriptor_heap_locations ge cells objects) params values ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells -> coherent_layout cells ->
  exists callee allocated final Sigma',
    alloc_variables ge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables ge callee allocated params values final /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final objects (extended_parameter_call_layout cells callee params) /\
    coherent_layout (extended_parameter_call_layout cells callee params).
Proof.
  intros ge Sigma m objects cells params values Hnames Hvalues Hblocks Hmemory Hcoherent.
  destruct (initialized_object_parameter_preparation ge Sigma m objects cells params values
    Hnames Hvalues Hblocks Hmemory)
    as [callee [allocated [final [Sigma' [Halloc [Hbind [Hext [Hblocks' Hmemory']]]]]]]].
  exists callee, allocated, final, Sigma'.
  split; [exact Halloc|]. split; [exact Hbind|]. split; [exact Hext|].
  split; [exact Hblocks'|]. split; [exact Hmemory'|].
  eapply allocated_parameter_layout_coherent; eauto.
  exact (initialized_object_cells _ _ _ _ _ Hmemory).
Qed.

Print Assumptions allocated_parameter_layout_coherent.
Print Assumptions coherent_initialized_parameter_preparation.
