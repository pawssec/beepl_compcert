(* Actual parameter allocation and binding retain initialized aggregate objects.
   Parameter cells contain scalars/references; they are not aggregate copies. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_scalar_object_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initializer_frames.
Require Import BeePL_call_memory BeePL_call_bindings BeePL_parameter_allocations.
Require Import BeePL_scalar_parameters BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_parameter_call_preparation.
Import ListNotations.

Lemma parameter_binding_preserves_permissions : forall ge callee m params values final,
  bind_variables ge callee m params values final ->
  forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm final b ofs k p.
Proof.
  intros ge callee m params values final Hbind. induction Hbind; intros; auto.
  apply IHHbind. eapply assignment_preserves_permissions; eauto.
Qed.

Theorem parameter_preparation_preserves_descriptors :
  forall ge cenv Sigma Sigma' vm m params callee allocated values final objects,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  bind_variables ge callee allocated params values final ->
  store_context_extends Sigma Sigma' -> aggregate_objects_valid cenv Sigma m objects ->
  aggregate_objects_valid cenv Sigma' final objects.
Proof.
  intros ge cenv Sigma Sigma' vm m params callee allocated values final objects
    Halloc Hbind Hext Hobjects.
  eapply aggregate_objects_valid_frame; [exact Hobjects |exact Hext | |].
  - intros b Hvalid. eapply bind_parameters_valid_blocks; [exact Hbind |].
    eapply parameter_allocations_block_frame; eauto.
  - intros b ofs k p Hperm. eapply parameter_binding_preserves_permissions; [exact Hbind |].
    eapply variable_allocation_preserves_permissions; eauto.
Qed.

Theorem initialized_object_parameter_preparation :
  forall ge Sigma m objects cells params values,
  NoDup (map fst params) ->
  call_parameter_values ge.(genv_cenv) Sigma (descriptor_heap_locations ge cells objects) params values ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  exists callee allocated final Sigma',
    alloc_variables ge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables ge callee allocated params values final /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final objects
      (extended_parameter_call_layout cells callee params).
Proof.
  intros ge Sigma m objects cells params values Hnames Hvalues Hblocks
    [Hobjects Hcoverage Hmemory Hlocations HscalarCoherence].
  destruct (call_parameter_storage_preparation ge ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge cells objects) m cells params values
    Hnames Hvalues Hblocks Hmemory)
    as [callee [allocated [final [Sigma'
      [Halloc [Hbind [Hext [Hblocks' [Hmemory' [Hcells Hfresh]]]]]]]]]].
  assert (Hinc : location_context_includes (descriptor_heap_locations ge cells objects)
    (descriptor_heap_locations ge (extended_parameter_call_layout cells callee params) objects)).
  { apply descriptor_heap_locations_monotone; [intros; left; assumption |auto]. }
  assert (Hstored : memory_locations (descriptor_heap_locations ge cells objects) cells final).
  { eapply parameter_preparation_memory_locations; eauto. }
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

Print Assumptions parameter_binding_preserves_permissions.
Print Assumptions parameter_preparation_preserves_descriptors.
Print Assumptions initialized_object_parameter_preparation.
