Require Import BeePL_heap_extents BeePL_block_extents.
(* Primitive references allocate an actual fresh initialized cell. Existing
   descriptors, covered leaves and pointer payloads survive the allocation. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_scalar_object_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_runtime.
Require Import BeePL_layout_coherence BeePL_coherent_configurations.
Require Import BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.

Lemma fresh_scalar_layout_coherent : forall cells fresh ofs ty chunk,
  coherent_layout cells -> (forall off t ch, ~ cells fresh off t ch) ->
  coherent_layout (extend_scalar_layout cells fresh ofs ty chunk).
Proof.
  intros cells fresh ofs ty chunk Hcoherent Hfresh b off t ch Hentry b' off' t' ch' Hother.
  destruct Hentry as [Hold | [Hb [Ho [Ht Hc]]]];
    destruct Hother as [Hold' | [Hb' [Ho' [Ht' Hc']]]].
  - eapply Hcoherent; eauto.
  - subst b' off' t' ch'. right; left. intro Heq. subst b. eapply Hfresh; eauto.
  - subst b off t ch. right; left. intro Heq. subst b'. eapply Hfresh; eauto.
  - subst. left; repeat split; reflexivity.
Qed.

Lemma located_primitive_allocation :
  forall cenv Sigma Sigma' cells L L' m allocated final fresh pt cc cv,
  typed_memory_layout cenv Sigma cells m -> memory_locations L cells m ->
  location_context_includes L L' ->
  Mem.alloc m 0 (sizeof_ptype pt) = (allocated, fresh) ->
  Mem.store cc allocated fresh 0 cv = Some final ->
  typed_memory_layout cenv Sigma'
    (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) final ->
  memory_locations L'
    (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) final.
Proof.
  intros cenv Sigma Sigma' cells L L' m allocated final fresh pt cc cv
    Htyped Hlocations Hinc Halloc Hstore Hfinal b ofs ty chunk Hentry v Hread.
  destruct Hentry as [Hold | [Hb [Hofs [Ht Hchunk]]]].
  - destruct (typed_memory_cell_read cenv empty_context Sigma m b ofs ty chunk
      (Htyped _ _ _ _ Hold)) as [old [Hreadold Hvalue]].
    assert (v = old) by (eapply deref_full_deterministic; [exact Hread |];
      eapply full_read_alloc_store_frame; eauto).
    subst v. eapply value_locations_monotone; [exact Hinc |]. eapply Hlocations; eauto.
  - subst b ofs ty chunk. apply primitive_value_locations.
    eapply declarative_value_shape with (Gamma := empty_context). eapply typed_memory_cell_read_preservation;
      [apply Hfinal; right; repeat split; reflexivity | exact Hread].
Qed.

Theorem coherent_primitive_reference_progress :
  forall ge Gamma Sigma vm m objects cells packets p pt pa v ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val v (Vtype pt)] (Ptrtype (Reftype (Bprim pt) pa))) ef (Ptrtype (Reftype (Bprim pt) pa)) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val v (Vtype pt)] (Ptrtype (Reftype (Bprim pt) pa)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa))) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype (Bprim pt) pa)) Sigma) final objects
      (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) packets /\
    coherent_runtime_configuration ge Gamma
      (PTree.set fresh (Ptrtype (Reftype (Bprim pt) pa)) Sigma) vm final objects
      (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) packets
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa))) nil (Ptrtype (Reftype (Bprim pt) pa)).
Proof.
  intros ge Gamma Sigma vm m objects cells packets p pt pa v ef
    [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyping Hlocations Hframes] Hcoherent].
  assert (Hvolatile : type_is_volatile (transBeePL_type (Vtype pt)) = false).
  { inversion Htyping; subst; assumption. }
  assert (Hshape : typeof_value v (Vtype pt)).
  { inversion Htyping; subst. eapply type_rel_typeof_val; eauto. }
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocated HscalarCoherence].
  destruct (typed_layout_allocate_primitive ge.(genv_cenv) Sigma cells m pt pa v
    Hcells Hblocks Hshape Hvolatile)
    as [allocated [final [fresh [Halloc [Hstore [Hfresh [Hext Hcells']]]]]]].
  set (Sigma' := PTree.set fresh (Ptrtype (Reftype (Bprim pt) pa)) Sigma).
  set (cells' := extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)).
  assert (Hblocks' : store_blocks_valid Sigma' final) by (eapply store_blocks_valid_allocate; eauto).
  assert (Hmemory' : initialized_object_memory ge Sigma' final objects cells').
  { constructor.
    - eapply aggregate_objects_valid_frame; [exact Hobjects | exact Hext | |].
      + intros. eapply Mem.store_valid_block_1; [exact Hstore |]. eapply Mem.valid_block_alloc; eauto.
      + intros. eapply Mem.perm_store_1; [exact Hstore |]. eapply Mem.perm_alloc_1; eauto.
    - eapply object_coverage_layout_extension; [exact Hcoverage |]. intros; left; assumption.
    - exact Hcells'.
    - eapply located_primitive_allocation; eauto.
      apply descriptor_heap_locations_monotone; [intros; left; assumption |auto].
    - eapply scalar_object_coherence_fresh_cells; [exact Hobjects|exact HscalarCoherence|].
      intros b ofs ty chunk [Hold|[Hb Hrest]]; [left; exact Hold|].
      subst b. right. eapply Mem.fresh_block_alloc; exact Halloc. }
  assert (Hcoherent' : coherent_layout cells').
  { apply fresh_scalar_layout_coherent; [exact Hcoherent |]. intros ofs ty chunk Hentry.
    assert (Hvalid : Mem.valid_block m fresh).
    { eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. apply Hcells; exact Hentry. }
    eapply Mem.fresh_block_alloc; eauto. }
  assert (Hpackets' : packet_heap_invariant ge Sigma' final objects cells' packets).
  { eapply packet_heap_fresh_store; [exact Hpackets|exact Hext|exact Halloc|exact Hstore|].
    intros b ofs ty chunk [Hold|[Hb Hrest]]; [left; exact Hold|right; exact Hb]. }
  assert (Hextents' : heap_block_extents Sigma' final objects cells' packets).
  { eapply heap_extents_store; [|exact Hstore].
    eapply heap_extents_allocation; [exact Hextents|exact Halloc| |].
    - destruct pt as [|sz sg a|sg a]; try destruct sz; vm_compute; intuition discriminate.
    - eapply tracked_data_block_same_block_extension.
      + intros; eapply store_set_lookup_origin; eauto.
      + intros; left; assumption.
      + intros b ofs ty chunk [Hold|[Hb Hrest]]; [left; exact Hold|right; exact Hb].
      + intros; left; assumption. }
  exists final, fresh. split.
  - eapply ssem_ref2 with (ml := (allocated, fresh)) (chunk := chunk_of_ptype pt)
      (bt := Bprim pt) (a := pa) (v := v) (l := fresh) (Sigma := Sigma) (Sigma' := Sigma').
    + exact Halloc.
    + reflexivity.
    + simpl. rewrite Ptrofs.unsigned_zero. exact Hstore.
    + reflexivity.
  - split.
    + constructor; auto. intros; left; assumption.
    + split; [|exact Hcoherent']. constructor.
      * constructor; try assumption. eapply packet_variable_layout_extend with (cells := cells); eauto.
        intros; left; assumption.
      * constructor. apply PTree.gss.
      * left. change (descriptor_heap_locations ge cells' objects fresh Ptrofs.zero (Ptrtype (Reftype (Bprim pt) pa))).
        left. left. exists (Reftype (Bprim pt) pa), (chunk_of_ptype pt).
        split; [reflexivity |]. right; repeat split; reflexivity.
      * exact I.
Qed.

Theorem coherent_primitive_reference_preservation :
  forall ge Gamma Sigma vm m objects cells packets p pt pa v ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val v (Vtype pt)] (Ptrtype (Reftype (Bprim pt) pa))) ef (Ptrtype (Reftype (Bprim pt) pa)) ->
  ssem_expr ge p vm m (Prim Ref [Val v (Vtype pt)] (Ptrtype (Reftype (Bprim pt) pa))) final vm' e' ->
  exists fresh,
    vm' = vm /\ e' = Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa)) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype (Bprim pt) pa)) Sigma) final objects
      (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) packets /\
    coherent_runtime_configuration ge Gamma
      (PTree.set fresh (Ptrtype (Reftype (Bprim pt) pa)) Sigma) vm' final objects
      (extend_scalar_layout cells fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) packets
      e' nil (Ptrtype (Reftype (Bprim pt) pa)).
Proof.
  intros ge Gamma Sigma vm m objects cells packets p pt pa v ef final vm' e' Hconfig Hstep.
  destruct (coherent_primitive_reference_progress ge Gamma Sigma vm m objects cells packets p pt pa v ef Hconfig)
    as [expected [fresh [Hexpected [Hevolve Hfinal]]]].
  destruct (primitive_reference_step_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep Hexpected)
    as [Hm [Hvm He]]. subst final vm' e'. exists fresh.
  split; [reflexivity |]. split; [reflexivity |]. split; assumption.
Qed.

Print Assumptions fresh_scalar_layout_coherent.
Print Assumptions located_primitive_allocation.
Print Assumptions coherent_primitive_reference_progress.
Print Assumptions coherent_primitive_reference_preservation.
