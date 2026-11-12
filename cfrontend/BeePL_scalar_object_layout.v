(* Hereditary declared-cell layout, independent of initialized heap records. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_copy_cells BeePL_fresh_copy.
Local Open Scope Z_scope.

Definition scalar_object_region_coherent cenv (cells : scalar_layout) block start root : Prop :=
  forall b ofs ty chunk, cells b ofs ty chunk ->
    (b <> block \/ Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= start \/
       start + sizeof_type cenv root <= Ptrofs.unsigned ofs) \/
    exists delta, scalar_object_leaf cenv root delta ty chunk /\ b = block /\
      Ptrofs.unsigned ofs = start + delta.

Definition scalar_object_coherence cenv (objects : aggregate_object_context) cells : Prop :=
  forall block base root, objects block base root -> forall delta child,
    object_path cenv root delta child ->
    scalar_object_region_coherent cenv cells block (Ptrofs.unsigned base + delta) child.

Lemma scalar_object_coherence_root : forall cenv objects cells b base root,
  scalar_object_coherence cenv objects cells -> objects b base root ->
  0 <= sizeof_type cenv root -> scalar_object_region_coherent cenv cells b (Ptrofs.unsigned base) root.
Proof.
  intros cenv objects cells b base root Hcoherent Hobject Hsize.
  replace (Ptrofs.unsigned base) with (Ptrofs.unsigned base + 0) by lia.
  eapply Hcoherent; [exact Hobject|constructor; exact Hsize].
Qed.

Theorem scalar_object_coherence_subobject_extension : forall cenv objects cells b base root delta child result,
  scalar_object_coherence cenv objects cells -> objects b base root ->
  object_path cenv root delta child -> Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  scalar_object_coherence cenv (add_aggregate_descriptor objects b result child) cells.
Proof.
  intros cenv objects cells b base root delta child result Hcoherent Hobject Hpath Hresult
    block ofs ty [Hold|[Hb [Hofs Hty]]] offset leaf Hleaf.
  - eapply Hcoherent; eauto.
  - subst. rewrite Hresult. replace (Ptrofs.unsigned base + delta + offset)
      with (Ptrofs.unsigned base + (delta + offset)) by lia.
    eapply Hcoherent; [exact Hobject|]. eapply object_path_compose; eauto.
Qed.

Theorem scalar_object_coherence_fresh_copy :
  forall cenv Sigma m allocated objects cells source base root fresh,
  aggregate_objects_valid cenv Sigma m objects -> objects source base root ->
  typed_memory_layout cenv Sigma cells m -> scalar_object_coherence cenv objects cells ->
  Mem.alloc m 0 (sizeof_type cenv root) = (allocated, fresh) ->
  scalar_object_coherence cenv
    (add_aggregate_descriptor objects fresh Ptrofs.zero root)
    (fresh_copy_layout cells source (Ptrofs.unsigned base) (sizeof_type cenv root) fresh).
Proof.
  intros cenv Sigma m allocated objects cells source base root fresh Hobjects Hsource Hmemory Hcoherent Ha.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Ha) as Hfresh.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource) as [_ [Hsize [Hextent Hrest]]].
  assert (Htotal : sizeof_type cenv root <= Ptrofs.modulus)
    by (pose proof (Ptrofs.unsigned_range base); lia).
  assert (HcellFresh : forall b ofs ty chunk, cells b ofs ty chunk -> b <> fresh).
  { intros b ofs ty chunk Hin Heq. subst b. apply Hfresh.
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. exact (Hmemory _ _ _ _ Hin). }
  assert (HobjectFresh : forall b ofs ty, objects b ofs ty -> b <> fresh).
  { intros b ofs ty Hin Heq. subst b. apply Hfresh.
    destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hin) as [_ [_ [_ [Hv _]]]]. exact Hv. }
  intros b object_base object_type Hobject delta child Hpath block offset ty chunk Hcell.
  destruct Hobject as [HoldObject|[Hb [Hbase Hroot]]];
    destruct Hcell as [HoldCell|[Hblock [old_offset [cellDelta [HsourceCell [HsourceOffset [Hdelta [Hlimit Hoffset]]]]]]]].
  - exact (Hcoherent _ _ _ HoldObject _ _ Hpath _ _ _ _ HoldCell).
  - subst block. left; left. intro Heq. symmetry in Heq. eapply HobjectFresh; eauto.
  - subst b. left; left. eapply HcellFresh; exact HoldCell.
  - subst b object_base object_type block offset.
    assert (HcellDelta : 0 <= cellDelta <= Ptrofs.max_unsigned).
    { pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)). unfold Ptrofs.max_unsigned; lia. }
    rewrite Ptrofs.unsigned_zero, Z.add_0_l, Ptrofs.unsigned_repr by exact HcellDelta.
    destruct (Hcoherent _ _ _ Hsource _ _ Hpath _ _ _ _ HsourceCell)
      as [Haway|[relative [Hleaf [Hsame Hposition]]]].
    + left. rewrite HsourceOffset in Haway. intuition lia.
    + right. exists relative. split; [exact Hleaf|]. split; [reflexivity|].
      rewrite HsourceOffset in Hposition. lia.
Qed.


(* New storage cannot alias any object already valid in the old memory. *)
Lemma scalar_object_coherence_fresh_cells : forall cenv Sigma m objects cells cells',
  aggregate_objects_valid cenv Sigma m objects ->
  scalar_object_coherence cenv objects cells ->
  (forall b ofs ty chunk, cells' b ofs ty chunk ->
     cells b ofs ty chunk \/ ~ Mem.valid_block m b) ->
  scalar_object_coherence cenv objects cells'.
Proof.
  intros cenv Sigma m objects cells cells' Hobjects Hcoherent Horigin
    b base root Hobject delta child Hpath block ofs ty chunk Hcell.
  destruct (Horigin _ _ _ _ Hcell) as [Hold | Hfresh].
  - eapply Hcoherent; eauto.
  - left; left. intro Heq; subst block. apply Hfresh.
    destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
      as [_ [_ [_ [Hvalid _]]]]. exact Hvalid.
Qed.

Lemma scalar_object_coherence_fresh_descriptor : forall cenv Sigma m objects cells fresh base root,
  typed_memory_layout cenv Sigma cells m ->
  scalar_object_coherence cenv objects cells ->
  ~ Mem.valid_block m fresh ->
  scalar_object_coherence cenv (add_aggregate_descriptor objects fresh base root) cells.
Proof.
  intros cenv Sigma m objects cells fresh base root Htyped Hcoherent Hfresh
    b ofs ty [Hold|[Hb [Hofs Hty]]] delta child Hpath block offset cell chunk Hentry.
  - eapply Hcoherent; eauto.
  - subst b ofs ty. left; left. intro Heq; subst block. apply Hfresh.
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure.
    exact (Htyped _ _ _ _ Hentry).
Qed.
