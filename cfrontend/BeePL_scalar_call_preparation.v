(* Actual preparation of scalar/reference parameters preserves the old heap
   and the locations stored in both old cells and new pointer slots. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_call_memory BeePL_allocation_proofs BeePL_call_bindings.
Require Import BeePL_scalar_parameters BeePL_scalar_arguments BeePL_scalar_parameter_allocations.
Require Import BeePL_scalar_parameter_bindings BeePL_scalar_call_layout.
Import ListNotations.

Theorem scalar_call_storage_preparation :
  forall bge cenv Sigma L m layout params values,
  NoDup (map fst params) ->
  scalar_parameter_values cenv Sigma L params values ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' initialized /\
    typed_memory_layout cenv Sigma' layout initialized /\
    (forall id ty b, In (id, ty) params -> PTree.get id callee = Some (b, ty) ->
      typed_memory_cell cenv Sigma' initialized b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
      (forall loaded, deref_addr ty initialized b Ptrofs.zero Full loaded -> value_locations L loaded ty)) /\
    (forall b, parameter_binding_target callee params b -> ~ Mem.valid_block m b).
Proof.
  intros bge cenv Sigma L m layout params values Hnames Hvalues Hblocks Hmemory.
  assert (Htypes : Forall (fun param => scalar_parameter_type (snd param)) params).
  { clear - Hvalues. induction Hvalues; constructor; tauto. }
  destruct (scalar_parameters_allocate bge Sigma m params Hnames Htypes)
    as [callee [allocated [Sigma' [Halloc [Hslots Hdistinct]]]]].
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hblocks)
    as [Hext Hblocks_allocated].
  assert (Hvalues' : scalar_parameter_values cenv Sigma' L params values).
  { eapply scalar_parameter_values_extend; [exact Hext | |exact Hvalues]. intros b ofs ty H; exact H. }
  assert (Hinputs : scalar_parameter_inputs cenv Sigma' L callee allocated params values).
  { assert (Hbuild : forall ps vs,
      scalar_parameter_values cenv Sigma' L ps vs ->
      (forall param, In param ps -> In param params) ->
      scalar_parameter_inputs cenv Sigma' L callee allocated ps vs).
    { intros ps vs Hfacts. induction Hfacts; intros Hincluded; constructor.
      - destruct x as [id ty]. destruct H as [Hscalar [Htyped Hlocated]].
        destruct (Hslots id ty (Hincluded _ (or_introl eq_refl)))
          as [b [Hget [Hfresh [Hvalid Haccess]]]].
        exists b. simpl in *. split; [exact Hget |]. split; [exact Hscalar |].
        split; [exact Htyped |]. split; assumption.
      - apply IHHfacts. intros param Hin. apply Hincluded. right; exact Hin. }
    apply Hbuild; [exact Hvalues' | auto]. }
  destruct (bind_scalar_parameters_initialized bge cenv Sigma' L callee allocated params values
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

Theorem scalar_callable_state_preparation :
  forall bge Gamma globals Sigma caller m layout params values,
  NoDup (map fst params) ->
  scalar_parameter_values bge.(genv_cenv) Sigma (callable_heap_locations bge layout) params values ->
  callable_heap_state Gamma Sigma bge caller m layout ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\
    callable_heap_state Gamma Sigma' bge caller initialized
      (extended_scalar_call_layout layout callee params) /\
    callable_heap_state (bind_vars globals params) Sigma' bge callee initialized
      (extended_scalar_call_layout layout callee params).
Proof.
  intros bge Gamma globals Sigma caller m layout params values Hnames Hvalues
    [Hblocks Hmemory Hcontents Hbindings] Hglobals.
  destruct (scalar_call_storage_preparation bge bge.(genv_cenv) Sigma
    (callable_heap_locations bge layout) m layout params values Hnames Hvalues Hblocks Hmemory)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hblocks' [Hmemory' [Hcells Hfresh]]]]]]]]]].
  assert (Htypes : Forall (fun param => scalar_parameter_type (snd param)) params).
  { clear - Hvalues. induction Hvalues; constructor; tauto. }
  assert (Hmemory_all : typed_memory_layout bge.(genv_cenv) Sigma'
    (extended_scalar_call_layout layout callee params) initialized).
  { intros b ofs ty chunk [Hold | [id [Hin [Hget [Hofs Hchunk]]]]].
    - apply Hmemory'; exact Hold.
    - subst ofs chunk. exact (proj1 (Hcells id ty b Hin Hget)). }
  assert (Hcontents_old : memory_locations (callable_heap_locations bge layout) layout initialized).
  { eapply parameter_preparation_memory_locations; eauto. }
  assert (Hinc : location_context_includes (callable_heap_locations bge layout)
    (callable_heap_locations bge (extended_scalar_call_layout layout callee params))).
  { apply callable_heap_locations_monotone. intros b ofs ty chunk Hentry. left; exact Hentry. }
  assert (Hcontents_all : memory_locations
    (callable_heap_locations bge (extended_scalar_call_layout layout callee params))
    (extended_scalar_call_layout layout callee params) initialized).
  { intros b ofs ty chunk Hentry loaded Hread.
    eapply value_locations_monotone; [exact Hinc |].
    destruct Hentry as [Hold | [id [Hin [Hget [Hofs Hchunk]]]]].
    - eapply Hcontents_old; eauto.
    - subst ofs chunk. eapply (proj2 (Hcells id ty b Hin Hget)); exact Hread. }
  exists callee, allocated, initialized, Sigma'.
  split; [exact Halloc |]. split; [exact Hbind |]. split; [exact Hext |]. split.
  - constructor; try assumption. eapply caller_scalar_callable_variable_layout_extended; eauto.
  - constructor; try assumption. eapply callee_scalar_callable_variable_layout; eauto.
Qed.

Print Assumptions scalar_call_storage_preparation.
Print Assumptions scalar_callable_state_preparation.
