(* Calls with unit and stored scalar values share a heap. Unit bindings need
   no memory cell; stored parameters preserve their values and locations. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_call_memory BeePL_allocation_proofs BeePL_call_bindings.
Require Import BeePL_scalar_parameters BeePL_scalar_arguments BeePL_scalar_parameter_allocations.
Require Import BeePL_scalar_parameter_bindings BeePL_scalar_call_layout.
Require Import BeePL_call_parameters BeePL_value_parameter_bindings BeePL_call_parameter_layout.
Require Import BeePL_parameter_allocations.
Import ListNotations.

Require Import BeePL_initialized_parameters BeePL_coherent_parameters BeePL_initializer_frames.

Lemma mapped_parameter_preparation_load_frame :
  forall bge bookkeeping initial m params callee allocated bookkeeping' values final,
  alloc_variables bge bookkeeping initial m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  forall b chunk ofs, Mem.valid_block m b ->
  Mem.load chunk final b ofs = Mem.load chunk m b ofs.
Proof.
  intros bge bookkeeping initial m params callee allocated bookkeeping' values final
    Halloc Hnames Hbind b chunk ofs Hvalid.
  rewrite (bind_parameters_load_frame _ _ _ _ _ _ Hbind b chunk ofs).
  - eapply parameter_allocations_load_frame; eauto.
  - intros [id [ty [Hin Hlookup]]].
    destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots id ty Hin) as [target [Hget [Hfresh Hrest]]].
    assert (target = b) by congruence. subst target. contradiction.
Qed.

Lemma mapped_parameter_preparation_read_frame :
  forall bge bookkeeping initial m params callee allocated bookkeeping' values final,
  alloc_variables bge bookkeeping initial m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  forall b ofs ty v, deref_addr ty m b ofs Full v ->
    deref_addr ty final b ofs Full v.
Proof.
  intros bge bookkeeping initial m params callee allocated bookkeeping' values final
    Halloc Hnames Hbind b ofs ty v Hread.
  inversion Hread; subst.
  - match goal with Hload : Mem.loadv _ _ _ = Some _ |- _ =>
    simpl in Hload;
    assert (Hvalid : Mem.valid_block m b) by
      (apply Mem.load_valid_access in Hload; eapply Mem.valid_access_valid_block;
       eapply Mem.valid_access_implies; [exact Hload | constructor]);
    eapply deref_addr_value; eauto; simpl;
    rewrite (mapped_parameter_preparation_load_frame _ _ _ _ _ _ _ _ _ _ Halloc Hnames Hbind b _ _ Hvalid);
    exact Hload
  end.
  - eapply deref_addr_bytes; [reflexivity| |eassumption|eassumption|].
    + eapply bind_parameters_valid_blocks; [exact Hbind|].
      eapply parameter_allocations_valid_blocks; eauto.
    + intros position Hinside.
      apply (proj2 (bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind)).
      eapply parameter_allocations_permissions; [exact Halloc|]. eauto.
Qed.

Theorem mapped_parameter_preparation_memory_locations :
  forall bge bookkeeping initial m params callee allocated bookkeeping' values final
    cenv Sigma layout L,
  alloc_variables bge bookkeeping initial m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  typed_memory_layout cenv Sigma layout m ->
  memory_locations L layout m ->
  memory_locations L layout final.
Proof.
  intros bge bookkeeping initial m params callee allocated bookkeeping' values final
    cenv Sigma layout L Halloc Hnames Hbind Hmemory Hlocations.
  intros b ofs ty chunk Hentry v Hread.
  destruct (typed_memory_cell_read cenv empty_context Sigma m b ofs ty chunk
    (Hmemory _ _ _ _ Hentry)) as [old [Hreadold Htyped]].
  assert (v = old).
  { eapply deref_full_deterministic; [exact Hread |].
    eapply mapped_parameter_preparation_read_frame; eauto. }
  subst v. eapply Hlocations; eauto.
Qed.

Theorem mapped_call_parameter_storage_preparation :
  forall bge cenv Sigma L initial m layout params values,
  NoDup (map fst params) ->
  call_parameter_values cenv Sigma L params values ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma initial m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' initialized /\
    typed_memory_layout cenv Sigma' layout initialized /\
    (forall id ty b, In (id, ty) params -> PTree.get id callee = Some (b, ty) ->
      scalar_parameter_type ty ->
      typed_memory_cell cenv Sigma' initialized b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
      (forall loaded, deref_addr ty initialized b Ptrofs.zero Full loaded -> value_locations L loaded ty)) /\
    (forall b, parameter_binding_target callee params b -> ~ Mem.valid_block m b).
Proof.
  intros bge cenv Sigma L initial m layout params values Hnames Hvalues Hblocks Hmemory.
  destruct (alloc_variables_total bge params Sigma initial m)
    as [callee [allocated [Sigma' Halloc]]].
  destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
    as [Hslots Hdistinct].
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hblocks)
    as [Hext Hblocks_allocated].
  assert (Hvalues' : call_parameter_values cenv Sigma' L params values).
  { eapply call_parameter_values_extend; [exact Hext | |exact Hvalues]. intros b ofs ty H; exact H. }
  assert (Hinputs : call_parameter_inputs cenv Sigma' L callee allocated params values).
  { eapply allocated_call_parameter_inputs; eauto. }
  destruct (bind_call_parameters_initialized bge cenv Sigma' L callee allocated params values
    Hinputs Hdistinct) as [initialized [Hbind Hcells]].
  assert (Hfresh : forall b, parameter_binding_target callee params b -> ~ Mem.valid_block m b).
  { intros b [id [ty [Hin Hget]]].
    destruct (Hslots id ty Hin) as [target [Hlookup [Hfresh Hrest]]].
    assert (target = b) by congruence. subst target. exact Hfresh. }
  exists callee, allocated, initialized, Sigma'.
  split; [exact Halloc |]. split; [exact Hbind |]. split; [exact Hext |]. split.
  - intros b ty Hentry. eapply bind_parameters_valid_blocks; [exact Hbind |].
    eapply Hblocks_allocated; eauto.
  - split.
    + eapply bind_parameters_layout_frame; [exact Hbind | |].
      * eapply typed_memory_layout_context_extension; [|exact Hext].
        eapply alloc_variables_typed_memory_frame; eauto.
      * intros b ofs ty chunk Hentry Htarget. apply (Hfresh b Htarget).
        eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
          [exact (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hentry)) | constructor].
    + split; assumption.
Qed.


Print Assumptions mapped_call_parameter_storage_preparation.

Require Import BeePL_scalar_object_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_layout_coherence.
Theorem mapped_initialized_object_parameter_preparation :
  forall ge Sigma initial m objects cells params values,
  NoDup (map fst params) ->
  call_parameter_values ge.(genv_cenv) Sigma (descriptor_heap_locations ge cells objects) params values ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  exists callee allocated final Sigma',
    alloc_variables ge Sigma initial m params callee allocated Sigma' /\
    bind_variables ge callee allocated params values final /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final objects
      (extended_parameter_call_layout cells callee params).
Proof.
  intros ge Sigma initial m objects cells params values Hnames Hvalues Hblocks
    [Hobjects Hcoverage Hmemory Hlocations HscalarCoherence].
  destruct (mapped_call_parameter_storage_preparation ge ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge cells objects) initial m cells params values
    Hnames Hvalues Hblocks Hmemory)
    as [callee [allocated [final [Sigma'
      [Halloc [Hbind [Hext [Hblocks' [Hmemory' [Hcells Hfresh]]]]]]]]]].
  assert (Hinc : location_context_includes (descriptor_heap_locations ge cells objects)
    (descriptor_heap_locations ge (extended_parameter_call_layout cells callee params) objects)).
  { apply descriptor_heap_locations_monotone; [intros; left; assumption |auto]. }
  assert (Hstored : memory_locations (descriptor_heap_locations ge cells objects) cells final).
  { eapply mapped_parameter_preparation_memory_locations; eauto. }
  exists callee, allocated, final, Sigma'.
  split; [exact Halloc|]. split; [exact Hbind|]. split; [exact Hext|]. split; [exact Hblocks'|].
  constructor.
  - eapply parameter_preparation_preserves_descriptors; eauto.
  - eapply object_coverage_layout_extension; [exact Hcoverage|]. intros; left; assumption.
  - intros b ofs ty chunk [Hold | [Hscalar [id [Hin [Hget [Hofs Hchunk]]]]]].
    + apply Hmemory'; exact Hold.
    + subst ofs chunk. exact (proj1 (Hcells id ty b Hin Hget Hscalar)).
  - intros b ofs ty chunk Hentry loaded Hread.
    eapply value_locations_monotone; [exact Hinc|].
    destruct Hentry as [Hold | [Hscalar [id [Hin [Hget [Hofs Hchunk]]]]]].
    + eapply Hstored; eauto.
    + subst ofs chunk. eapply (proj2 (Hcells id ty b Hin Hget Hscalar)); exact Hread.
  - eapply scalar_object_coherence_fresh_cells; [exact Hobjects|exact HscalarCoherence|].
    intros b ofs ty chunk [Hold | [Hscalar [id [Hin [Hget Hrest]]]]].
    + left; exact Hold.
    + right. apply Hfresh. exists id, ty. split; assumption.
Qed.


Print Assumptions mapped_initialized_object_parameter_preparation.
