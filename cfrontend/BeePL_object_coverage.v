(* Every scalar leaf of a certified aggregate has an initialized typed cell.
   Paths traverse embedded objects, but stop at pointer-valued leaves. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_fresh_copy.
Require Import BeePL_scalar_object_layout.
Local Open Scope Z_scope.

Definition initialized_object_coverage (cenv : bcomposite_env)
    (objects : aggregate_object_context) (cells : scalar_layout) : Prop :=
  forall b base root, objects b base root ->
  forall delta ty chunk, scalar_object_leaf cenv root delta ty chunk ->
    exists stored_chunk,
      cells b (Ptrofs.repr (Ptrofs.unsigned base + delta)) ty stored_chunk /\
      transl_bchunk_cchunk stored_chunk = transl_bchunk_cchunk chunk.

Record initialized_object_memory (ge : genv) (Sigma : store_context) (m : Mem.mem)
    (objects : aggregate_object_context) (cells : scalar_layout) : Prop := {
  initialized_object_descriptors : aggregate_objects_valid ge.(genv_cenv) Sigma m objects;
  initialized_object_leaves : initialized_object_coverage ge.(genv_cenv) objects cells;
  initialized_object_cells : typed_memory_layout ge.(genv_cenv) Sigma cells m;
  initialized_object_locations : memory_locations (descriptor_heap_locations ge cells objects) cells m;
  initialized_object_scalar_coherence : scalar_object_coherence ge.(genv_cenv) objects cells
}.

Lemma object_coverage_layout_extension : forall cenv objects cells cells',
  initialized_object_coverage cenv objects cells ->
  (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) ->
  initialized_object_coverage cenv objects cells'.
Proof. intros cenv objects cells cells' Hcoverage Hext b base root Hobject delta ty chunk Hleaf.
  destruct (Hcoverage _ _ _ Hobject _ _ _ Hleaf) as [stored [Hcell Hchunk]].
  exists stored. split; [apply Hext; exact Hcell | exact Hchunk]. Qed.

Lemma covered_leaf_offset_no_wrap : forall cenv Sigma m objects b base root delta ty chunk,
  aggregate_objects_valid cenv Sigma m objects -> objects b base root ->
  scalar_object_leaf cenv root delta ty chunk ->
  Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned base + delta)) = Ptrofs.unsigned base + delta.
Proof.
  intros cenv Sigma m objects b base root delta ty chunk Hobjects Hobject Hleaf.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [Hkind [Hsize [Hextent Hrest]]].
  pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as Hbounds.
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
  pose proof (Ptrofs.unsigned_range base).
  apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. lia.
Qed.

Theorem covered_scalar_leaf_read :
  forall ge Sigma Gamma m objects cells b base root delta ty chunk,
  initialized_object_memory ge Sigma m objects cells -> objects b base root ->
  scalar_object_leaf ge.(genv_cenv) root delta ty chunk ->
  exists v,
    deref_addr ty m b (Ptrofs.repr (Ptrofs.unsigned base + delta)) Full v /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    value_locations (descriptor_heap_locations ge cells objects) v ty.
Proof.
  intros ge Sigma Gamma m objects cells b base root delta ty chunk
    [Hobjects Hcoverage Htyped Hlocations HscalarCoherence] Hobject Hleaf.
  destruct (Hcoverage _ _ _ Hobject _ _ _ Hleaf) as [stored [Hentry Hchunk]].
  destruct (typed_memory_cell_read ge.(genv_cenv) Gamma Sigma m b
    (Ptrofs.repr (Ptrofs.unsigned base + delta)) ty stored (Htyped _ _ _ _ Hentry))
    as [v [Hread Hvalue]].
  exists v. split; [exact Hread |]. split; [exact Hvalue |]. eapply Hlocations; eauto.
Qed.

Theorem object_coverage_subobject_extension :
  forall cenv objects cells b base root delta child result,
  initialized_object_coverage cenv objects cells -> objects b base root ->
  object_path cenv root delta child ->
  Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  initialized_object_coverage cenv (add_aggregate_descriptor objects b result child) cells.
Proof.
  intros cenv objects cells b base root delta child result Hcoverage Hobject Hpath Hresult
    block offset ty [Hold | [Hb [Hoffset Hty]]] leafDelta leafTy chunk Hleaf.
  - eapply Hcoverage; eauto.
  - subst block offset ty. destruct Hleaf as [HleafPath Hmode].
    assert (Hcombined : scalar_object_leaf cenv root (delta + leafDelta) leafTy chunk).
    { split; [eapply object_path_compose; eauto | exact Hmode]. }
    pose proof (Hcoverage _ _ _ Hobject _ _ _ Hcombined) as Hentry.
    rewrite Hresult. replace (Ptrofs.unsigned base + delta + leafDelta)
      with (Ptrofs.unsigned base + (delta + leafDelta)) by lia. exact Hentry.
Qed.

Theorem fresh_copy_object_coverage :
  forall cenv Sigma m objects cells src base root fresh,
  aggregate_objects_valid cenv Sigma m objects ->
  initialized_object_coverage cenv objects cells -> objects src base root ->
  initialized_object_coverage cenv
    (add_aggregate_descriptor objects fresh Ptrofs.zero root)
    (fresh_copy_layout cells src (Ptrofs.unsigned base) (sizeof_type cenv root) fresh).
Proof.
  intros cenv Sigma m objects cells src base root fresh Hobjects Hcoverage Hsource
    b offset ty [Hold | [Hb [Hoffset Hty]]] delta leaf chunk Hleaf.
  - destruct (Hcoverage _ _ _ Hold _ _ _ Hleaf) as [stored [Hcell Hchunk]].
    exists stored. split; [left; exact Hcell | exact Hchunk].
  - subst b offset ty.
    destruct (Hcoverage _ _ _ Hsource _ _ _ Hleaf) as [stored [Hcell Hchunk]].
    exists stored. split; [|exact Hchunk]. right. split; [reflexivity |].
    exists (Ptrofs.repr (Ptrofs.unsigned base + delta)), delta.
    split; [exact Hcell |]. split.
    + eapply covered_leaf_offset_no_wrap; eauto.
    + pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as Hbounds.
      split; [lia |]. split; [rewrite Hchunk; lia |]. rewrite Ptrofs.unsigned_zero. reflexivity.
Qed.

Print Assumptions covered_scalar_leaf_read.
Print Assumptions object_coverage_subobject_extension.
Print Assumptions fresh_copy_object_coverage.

Theorem initialized_object_subobject_extension :
  forall ge Sigma m objects cells b base root delta child result,
  initialized_object_memory ge Sigma m objects cells -> objects b base root ->
  object_path ge.(genv_cenv) root delta child -> is_aggregate_type child = true ->
  Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  initialized_object_memory ge Sigma m
    (add_aggregate_descriptor objects b result child) cells.
Proof.
  intros ge Sigma m objects cells b base root delta child result
    [Hobjects Hcoverage Htyped Hlocations HscalarCoherence] Hobject Hpath Hkind Hresult.
  pose proof (object_path_bounds _ _ _ _ Hpath) as Hbounds.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [HrootKind [HrootSize [HrootExtent [Hblock Hreadable]]]].
  constructor.
  - constructor; intros block offset ty [Hold | [Hb [Hofs Hty]]].
    + eapply aggregate_object_typing; eauto.
    + subst block offset ty. rewrite Hresult. eapply object_path_typing; [exact Hpath |].
      eapply aggregate_object_typing; eauto.
    + eapply aggregate_object_readable; eauto.
    + subst block offset ty. unfold aggregate_readable. rewrite Hresult.
      split; [exact Hkind |]. split; [lia |]. split; [lia |].
      split; [exact Hblock |]. intros offset Hin. apply Hreadable. lia.
    + eapply aggregate_object_address_bound; eauto.
    + subst block offset ty. rewrite Hresult.
      pose proof (aggregate_object_address_bound _ _ _ _ Hobjects _ _ _ Hobject). lia.
  - eapply object_coverage_subobject_extension; eauto.
  - exact Htyped.
  - intros block offset ty chunk Hentry v Hread.
    eapply value_locations_monotone with (L := descriptor_heap_locations ge cells objects).
    + eapply descriptor_heap_locations_monotone.
      * intros; assumption.
      * intros; left; assumption.
    + eapply Hlocations; eauto.
  - eapply scalar_object_coherence_subobject_extension; eauto.
Qed.

Print Assumptions initialized_object_subobject_extension.
