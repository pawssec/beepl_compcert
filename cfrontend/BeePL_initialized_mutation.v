Require Import BeePL_heap_extents BeePL_block_extents.
(* Mutation requires pre-state alias compatibility. Initialized scalar contents
   alone do not imply it: a nullable-reference/word overlap counterexample below
   demonstrates the missing invariant. No post-store validity is assumed. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initialization_proofs BeePL_structure_proofs.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_runtime.
Require Import BeePL_packet_heap.
Import ListNotations.
Local Open Scope Z_scope.

Lemma initialized_primitive_store : forall ge Sigma objects cells m final b ofs pt v,
  initialized_object_memory ge Sigma m objects cells ->
  cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  layout_write_compatible cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  typeof_value v (Vtype pt) ->
  Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) m b (Ptrofs.unsigned ofs)
    (trans_bvalue_cvalue v) = Some final ->
  initialized_object_memory ge Sigma final objects cells.
Proof.
  intros ge Sigma objects cells m final b ofs pt v
    [Hobjects Hcoverage Htyped Hlocated HscalarCoherence] Hentry Hcompatible Hshape Hactual.
  destruct (primitive_store_normalization _ _ Hshape) as [stored [Hdecode Hstored]].
  assert (HstoredTyped : type_expr ge.(genv_cenv) empty_context Sigma (Val stored (Vtype pt)) nil (Vtype pt)).
  { apply primitive_value_typing; exact Hstored. }
  destruct (typed_memory_layout_store ge.(genv_cenv) Sigma cells m b ofs (Vtype pt) (chunk_of_ptype pt)
    (trans_bvalue_cvalue v) stored Htyped Hentry Hcompatible Hdecode HstoredTyped)
    as [expected [Hstore Htyped']].
  assert (final = expected) by congruence. subst final. constructor.
  - eapply aggregate_objects_valid_store; eauto.
  - exact Hcoverage.
  - exact Htyped'.
  - eapply memory_locations_store with (m := m) (cenv := ge.(genv_cenv)) (Sigma := Sigma)
      (b := b) (ofs := ofs) (t := Vtype pt) (chunk := chunk_of_ptype pt)
      (cv := trans_bvalue_cvalue v) (stored := stored); eauto.
    apply primitive_value_locations; exact Hstored.
  - exact HscalarCoherence.
Qed.

Lemma evaluated_primitive_assignment_shape : forall ge Gamma Sigma b ofs pt pa v ef,
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype ->
  typeof_value v (Vtype pt).
Proof.
  intros ge Gamma Sigma b ofs pt pa v ef Htyped. inversion Htyped; subst.
  eapply type_rel_typeof_val; eassumption.
Qed.

Theorem initialized_primitive_assignment_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype ->
  cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  layout_write_compatible cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype)
    final vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil Utype /\
  sub_effect nil ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef final vm' e'
    [[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes] Hentry Hcompatible Hstep.
  pose proof (evaluated_primitive_assignment_shape _ _ _ _ _ _ _ _ _ Htyped) as Hshape.
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hstore : Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) m b (Ptrofs.unsigned ofs)
      (trans_bvalue_cvalue v) = Some final).
  { eapply primitive_assignment_to_store; eauto. }
  assert (Hmemory' : initialized_object_memory ge Sigma final objects cells).
  { eapply initialized_primitive_store; eauto. }
  assert (Hblocks' : store_blocks_valid Sigma final).
  { intros old ty Hget. eapply Mem.store_valid_block_1; [exact Hstore |]. eapply Hblocks; eauto. }
  assert (Hpackets' : packet_heap_invariant ge Sigma final objects cells packets).
  { eapply packet_heap_scalar_store; eauto. }
  assert (Hextents' : heap_block_extents Sigma final objects cells packets).
  { eapply heap_extents_store; [exact Hextents|exact Hstore]. }
  split; [reflexivity |]. split; [reflexivity |]. split.
  - constructor; auto using store_context_extends_refl.
  - split; [|destruct ef; reflexivity]. constructor.
    + constructor; assumption.
    + constructor.
    + exact I.
    + exact I.
Qed.

Theorem initialized_primitive_assignment_progress :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype ->
  cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  layout_write_compatible cells b ofs (Vtype pt) (chunk_of_ptype pt) ->
  exists final,
    ssem_expr ge p vm m
      (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype)
      final vm (Val Vunit Utype) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    initialized_runtime_configuration ge Gamma Sigma vm final objects cells packets (Val Vunit Utype) nil Utype.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef Hconfig Hentry Hcompatible.
  destruct Hconfig as [[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes].
  pose proof (evaluated_primitive_assignment_shape _ _ _ _ _ _ _ _ _ Htyped) as Hshape.
  pose proof (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hentry) as Hcell.
  destruct (initialize_primitive_cell ge m b ofs pt v Hshape
    (typed_cell_nonvolatile _ _ _ _ _ _ _ Hcell) (typed_cell_permission _ _ _ _ _ _ _ Hcell))
    as [final [Hstore [Hassign Hnewcell]]].
  assert (Hstep : ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype)
    final vm (Val Vunit Utype)).
  { apply ssem_massgn3. exact Hassign. }
  assert (Hconfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype).
  { constructor; [constructor; assumption | assumption | assumption | assumption]. }
  destruct (initialized_primitive_assignment_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfig Hentry Hcompatible Hstep) as [_ [_ [Hevolve [Hfinal Heffect]]]].
  exists final. split; [exact Hstep |]. split; assumption.
Qed.

Definition overlapping_word_type : type := Vtype (Tlong Unsigned noattr).
Definition overlapping_optional_type : type :=
  Ptrtype (Otype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)).
Definition overlapping_word_optional (block : Values.block) : scalar_layout :=
  fun b ofs ty chunk => b = block /\ ofs = Ptrofs.zero /\ chunk = BMint64 /\
    (ty = overlapping_word_type \/ ty = overlapping_optional_type).

Theorem initialized_contents_do_not_prevent_alias_corruption : forall ge,
  Archi.ptr64 = true ->
  exists allocated before after block,
    Mem.alloc Mem.empty 0 8 = (allocated, block) /\
    Mem.store Mint64 allocated block 0 (Values.Vlong Int64.zero) = Some before /\
    Mem.store Mint64 before block 0 (Values.Vlong Int64.one) = Some after /\
    initialized_object_memory ge empty_stcontext before (fun _ _ _ => False)
      (overlapping_word_optional block) /\
    ~ typed_memory_layout ge.(genv_cenv) empty_stcontext (overlapping_word_optional block) after /\
    ~ layout_write_compatible (overlapping_word_optional block) block Ptrofs.zero overlapping_word_type BMint64.
Proof.
  intros ge Harch.
  destruct (Mem.alloc Mem.empty 0 8) as [allocated block] eqn:Halloc.
  assert (Hfree : Mem.valid_access allocated Mint64 block 0 Freeable).
  { eapply Mem.valid_access_alloc_same; [exact Halloc | lia | simpl; lia |]. exists 0; lia. }
  assert (Hwrite : Mem.valid_access allocated Mint64 block 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [exact Hfree | constructor]. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vlong Int64.zero) Hwrite) as [before Hzero].
  assert (Hfree0 : Mem.valid_access before Mint64 block 0 Freeable).
  { eapply Mem.store_valid_access_1; eauto. }
  assert (Hwrite0 : Mem.valid_access before Mint64 block 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [exact Hfree0 | constructor]. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vlong Int64.one) Hwrite0) as [after Hone].
  assert (Hload0 : Mem.load Mint64 before block 0 = Some (Values.Vlong Int64.zero)).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hzero). }
  assert (Hload1 : Mem.load Mint64 after block 0 = Some (Values.Vlong Int64.one)).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hone). }
  assert (Hdecode0 : decode_memory_value overlapping_optional_type (Values.Vlong Int64.zero) = OK (Voption None)).
  { unfold overlapping_optional_type, decode_memory_value, decode_optional_pointer.
    simpl. rewrite Harch. reflexivity. }
  assert (Hmode : access_mode_type overlapping_optional_type = By_value Mint64).
  { unfold overlapping_optional_type, access_mode_type, Mptr. rewrite Harch. reflexivity. }
  assert (Hword : typed_memory_cell ge.(genv_cenv) empty_stcontext before block Ptrofs.zero overlapping_word_type BMint64).
  { constructor; try reflexivity.
    - exact Hfree0.
    - exists (Values.Vlong Int64.zero), (Vint64 Int64.zero).
      split; [exact Hload0 |]. split; [reflexivity | constructor]. }
  assert (Hoption : typed_memory_cell ge.(genv_cenv) empty_stcontext before block Ptrofs.zero overlapping_optional_type BMint64).
  { constructor.
    - exact Hmode.
    - reflexivity.
    - exact Hfree0.
    - exists (Values.Vlong Int64.zero), (Voption None).
      split; [exact Hload0 |]. split; [exact Hdecode0 |].
      apply ty_valo; [reflexivity | intros; discriminate]. }
  assert (Hmemory : initialized_object_memory ge empty_stcontext before (fun _ _ _ => False)
      (overlapping_word_optional block)).
  { constructor.
    - constructor; intros; contradiction.
    - intros b base root H; contradiction.
    - intros b ofs ty chunk [-> [-> [-> [-> | ->]]]]; assumption.
    - intros b ofs ty chunk [-> [-> [-> [-> | ->]]]] v Hread.
      + assert (Heq : v = Vint64 Int64.zero).
        { eapply deref_full_deterministic; [exact Hread |].
          eapply deref_addr_value with (chunk := BMint64) (v := Values.Vlong Int64.zero);
            try reflexivity; exact Hload0. }
        subst v. exact I.
      + assert (Heq : v = Voption None).
        { eapply deref_full_deterministic; [exact Hread |].
          eapply deref_addr_value with (chunk := BMint64) (v := Values.Vlong Int64.zero);
            [exact Hmode | reflexivity | exact Hload0 | exact Hdecode0]. }
        subst v. exact I.
    - intros b base root H; contradiction. }
  exists allocated, before, after, block. split; [reflexivity |].
  split; [exact Hzero |]. split; [exact Hone |]. split; [exact Hmemory |]. split.
  - intro Htyped. assert (Hentry : overlapping_word_optional block block Ptrofs.zero overlapping_optional_type BMint64).
    { repeat split; auto. }
    destruct (typed_cell_contents _ _ _ _ _ _ _ (Htyped _ _ _ _ Hentry))
      as [cv [v [Hload [Hdecode Hvalue]]]].
    change (Mem.load Mint64 after block 0 = Some cv) in Hload.
    assert (cv = Values.Vlong Int64.one) by congruence. subst cv.
    unfold overlapping_optional_type, decode_memory_value, decode_optional_pointer in Hdecode.
    simpl in Hdecode. rewrite Harch in Hdecode. discriminate.
  - intro Hcompatible.
    assert (Hentry : overlapping_word_optional block block Ptrofs.zero overlapping_optional_type BMint64).
    { repeat split; auto. }
    destruct (Hcompatible _ _ _ _ Hentry) as [[_ [_ [Hbad _]]] | Haway]; [discriminate Hbad |].
    rewrite Ptrofs.unsigned_zero in Haway. simpl in Haway. intuition lia.
Qed.

Print Assumptions initialized_primitive_assignment_preservation.
Print Assumptions initialized_primitive_assignment_progress.
Print Assumptions initialized_contents_do_not_prevent_alias_corruption.
