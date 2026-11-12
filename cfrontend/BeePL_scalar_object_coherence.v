(* Scalar cells that intersect an object must be declared leaves, including
   when the intersection lies in padding. The relation is hereditary under
   object paths and independent of operations or successor-state contents. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_copy_cells BeePL_fresh_copy BeePL_packet_alignment.
Require Export BeePL_scalar_object_layout.
Local Open Scope Z_scope.

Lemma source_chunk_translation_injective : forall first second,
  transl_bchunk_cchunk first = transl_bchunk_cchunk second -> first = second.
Proof. destruct first, second; simpl; congruence. Qed.

Theorem coherent_objects_scalar_copy_plan : forall cenv Sigma m objects cells source source_base destination target root,
  aggregate_objects_valid cenv Sigma m objects -> initialized_object_coverage cenv objects cells ->
  typed_memory_layout cenv Sigma cells m -> scalar_object_coherence cenv objects cells ->
  objects source source_base root -> objects destination target root ->
  scalar_copy_plan cells cells source (Ptrofs.unsigned source_base) destination
    (Ptrofs.unsigned target) (sizeof_type cenv root).
Proof.
  intros cenv Sigma m objects cells source source_base destination target root
    Hobjects Hcoverage Hmemory Hcoherent Hsource Htarget b ofs ty chunk Hcell.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Htarget) as [_ [Hsize Hrest]].
  destruct (scalar_object_coherence_root _ _ _ _ _ _ Hcoherent Htarget Hsize _ _ _ _ Hcell)
    as [Haway|[delta [Hleaf [Hb Hofs]]]].
  - left; split; assumption.
  - right. split; [exact Hb|]. exists delta, (Ptrofs.repr (Ptrofs.unsigned source_base + delta)).
    destruct (Hcoverage _ _ _ Hsource _ _ _ Hleaf) as [stored [HsourceCell Hchunk]].
    assert (stored = chunk) by (apply source_chunk_translation_injective; exact Hchunk). subst stored.
    pose proof (covered_leaf_offset_no_wrap _ _ _ _ _ _ _ _ _ _ Hobjects Hsource Hleaf) as Hoffset.
    destruct (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hdelta [HscalarSize Hinside]].
    split; [exact HsourceCell|]. split; [exact Hdelta|]. split; [exact Hinside|].
    split; [exact Hoffset|]. split; [exact Hofs|].
    exact (proj2 (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell))).
Qed.

Lemma scalar_chunk_natural_alignment : forall env ty chunk,
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  align_chunk (transl_bchunk_cchunk chunk) = natural_object_alignment env ty.
Proof.
  intros env ty chunk Hmode. destruct ty; try discriminate.
  - destruct p as [|size sign attr|sign attr]; try destruct size; try destruct sign;
      destruct chunk; simpl in Hmode |- *; try discriminate; reflexivity.
  - unfold access_mode_type in Hmode. unfold Mptr in Hmode.
    simpl. destruct Archi.ptr64; destruct chunk; simpl in Hmode |- *; try discriminate; reflexivity.
Qed.

Lemma scalar_chunk_alignment_power : forall chunk,
  exists n, align_chunk (transl_bchunk_cchunk chunk) = two_power_nat n.
Proof.
  destruct chunk; simpl; first [exists 0%nat; reflexivity|exists 1%nat; reflexivity|
    exists 2%nat; reflexivity|exists 3%nat; reflexivity].
Qed.

Theorem program_scalar_object_leaf_alignment : forall p root delta ty chunk,
  scalar_object_leaf p.(prog_comp_env) root delta ty chunk ->
  (align_chunk (transl_bchunk_cchunk chunk) | delta).
Proof.
  intros p root delta ty chunk [Hpath Hmode].
  assert (Hnatural : align_chunk (transl_bchunk_cchunk chunk) <= natural_object_alignment p.(prog_comp_env) ty).
  { rewrite (scalar_chunk_natural_alignment p.(prog_comp_env) _ _ Hmode). lia. }
  exact (proj1 (program_object_path_alignment _ _ _ _ Hpath
    (align_chunk (transl_bchunk_cchunk chunk)) (scalar_chunk_alignment_power chunk) Hnatural)).
Qed.

Theorem coherent_object_relative_copy_alignment : forall p objects cells source base root,
  scalar_object_coherence p.(prog_comp_env) objects cells -> objects source base root ->
  0 <= sizeof_type p.(prog_comp_env) root ->
  relative_copy_alignment cells source (Ptrofs.unsigned base) (sizeof_type p.(prog_comp_env) root).
Proof.
  intros p objects cells source base root Hcoherent Hobject Hsize ofs ty chunk delta Hcell Hofs Hdelta Hbound.
  destruct (scalar_object_coherence_root _ _ _ _ _ _ Hcoherent Hobject Hsize _ _ _ _ Hcell)
    as [Haway|[actual [Hleaf [Hb Hposition]]]].
  - pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)); intuition lia.
  - assert (actual = delta) by lia. subst. eapply program_scalar_object_leaf_alignment; exact Hleaf.
Qed.

Theorem coherent_object_copy_preserves_cells :
  forall cenv Sigma L m final objects cells source base destination target root bytes,
  aggregate_objects_valid cenv Sigma m objects -> initialized_object_coverage cenv objects cells ->
  typed_memory_layout cenv Sigma cells m -> memory_locations L cells m ->
  scalar_object_coherence cenv objects cells ->
  objects source base root -> objects destination target root ->
  Mem.loadbytes m source (Ptrofs.unsigned base) (sizeof_type cenv root) = Some bytes ->
  Mem.storebytes m destination (Ptrofs.unsigned target) bytes = Some final ->
  typed_memory_layout cenv Sigma cells final /\ memory_locations L cells final /\
  scalar_object_coherence cenv objects cells.
Proof.
  intros cenv Sigma L m final objects cells source base destination target root bytes
    Hobjects Hcoverage Hmemory Hlocations Hcoherent Hsource Htarget Hr Hw.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource) as [_ [Hsize Hrest]].
  pose proof (coherent_objects_scalar_copy_plan _ _ _ _ _ _ _ _ _ _
    Hobjects Hcoverage Hmemory Hcoherent Hsource Htarget) as Hplan.
  assert (Hlength : Z.of_nat (length bytes) = sizeof_type cenv root).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hr), Z2Nat.id by exact Hsize. reflexivity. }
  assert (Hcells : forall b ofs ty chunk, cells b ofs ty chunk ->
    typed_memory_cell cenv Sigma final b ofs ty chunk /\
    forall v, deref_addr ty final b ofs Full v -> value_locations L v ty).
  { intros b ofs ty chunk Hentry. destruct (Hplan _ _ _ _ Hentry)
      as [[Hold Haway]|[Hb [delta [sourceOffset [HsourceCell [Hdelta [Hbound [Hsrc [Hdst Halign]]]]]]]]].
    - assert (HawayBytes : b <> destination \/
        Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= Ptrofs.unsigned target \/
        Ptrofs.unsigned target + Z.of_nat (length bytes) <= Ptrofs.unsigned ofs)
        by (rewrite Hlength; exact Haway).
      split; [eapply typed_cell_storebytes_disjoint; eauto|].
      intros actual Hread.
      destruct (Hmemory _ _ _ _ Hold) as [Hmode Hvolatile Hperm [cv [v [Hload [Hdecode Htyped]]]]].
      assert (Hreadv : deref_addr ty final b ofs Full v).
      { eapply deref_addr_value with (chunk := chunk) (v := cv); eauto. simpl.
        rewrite (Mem.load_storebytes_other _ _ _ _ _ Hw); assumption. }
      assert (actual = v) by (eapply deref_full_deterministic; eauto). subst actual.
      eapply Hlocations; [exact Hold|]. eapply deref_addr_value; eauto.
    - subst b. eapply copied_typed_cell;
        [exact Hr|exact Hw|exact Hdelta|exact Hbound|exact Hsrc|exact Hdst|
         exact (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hentry))|
         exact (Hmemory _ _ _ _ HsourceCell)|].
      intros; eapply Hlocations; eauto. }
  split; [intros b ofs ty chunk Hin; exact (proj1 (Hcells _ _ _ _ Hin))|]. split; [|exact Hcoherent].
  intros b ofs ty chunk Hentry v Hread. exact (proj2 (Hcells _ _ _ _ Hentry) v Hread).
Qed.

Print Assumptions coherent_objects_scalar_copy_plan.
Print Assumptions coherent_object_relative_copy_alignment.
Print Assumptions scalar_object_coherence_subobject_extension.
Print Assumptions scalar_object_coherence_fresh_copy.

Print Assumptions coherent_object_copy_preserves_cells.
