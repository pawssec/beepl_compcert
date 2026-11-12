(* Copy plans follow from the shared object/cell relation. Primitive arrays
   represented by callable indexed cells do not need an additional descriptor. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_arrays BeePL_array_object_coverage.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_copy_cells BeePL_fresh_copy BeePL_runtime_locations BeePL_soundness_store.
Require Import BeePL_scalar_object_coherence BeePL_packet_bindings BeePL_packet_location_coherence.
Local Open Scope Z_scope.

Lemma located_basic_scalar_leaf : forall ge Sigma m objects cells packets b base basic delta ty chunk,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets b base (construct_type_btype basic) ->
  Ptrofs.unsigned base + sizeof_type ge.(genv_cenv) (construct_type_btype basic) <= Ptrofs.modulus ->
  scalar_object_leaf ge.(genv_cenv) (construct_type_btype basic) delta ty chunk ->
  cells b (Ptrofs.repr (Ptrofs.unsigned base + delta)) ty chunk.
Proof.
  intros ge Sigma m objects cells packets b base basic delta ty chunk Hmemory Hloc Hbound Hleaf.
  assert (HobjectCase : objects b base (construct_type_btype basic) ->
    cells b (Ptrofs.repr (Ptrofs.unsigned base + delta)) ty chunk).
  { intro Hobj. destruct (initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hobj _ _ _ Hleaf)
      as [stored [Hcell Hsame]]. apply source_chunk_translation_injective in Hsame. subst; exact Hcell. }
  destruct Hloc as [Hloc|[Hbytes Hpacket]]; [|destruct basic; discriminate Hbytes].
  destruct Hloc as [Hcall|[[Hkind Hobj]|[bt [pa [Heq Hobj]]]]]; [|auto|destruct basic; discriminate Heq].
  destruct basic as [primitive|sid structure_attr|primitive count array_attr]; simpl in *.
  - destruct Hcall as [[pt [stored [Heq Hcell]]]|[elem [len [a [Heq Hrest]]]]]; discriminate Heq.
  - destruct Hcall as [[pt [stored [Heq Hcell]]]|[elem [len [a [Heq Hrest]]]]]; discriminate Heq.
  - destruct Hcall as [[pt [stored [Heq Hcell]]]|[elem [len [a [Heq [Hlen Hcells]]]]]];
      [discriminate Heq|]. inversion Heq; subst elem len a.
    destruct (primitive_array_scalar_leaf _ _ _ _ _ _ _ Hleaf)
      as [i [Hi [Hd [Ht Hchunk]]]]. subst delta ty.
    assert (Hindex : (Z.to_nat i < Z.to_nat count)%nat) by (apply Z2Nat.inj_lt; lia).
    destruct (Hcells _ Hindex) as [stored Hcell].
    pose proof (typed_cell_access _ _ _ _ _ _ _
      (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
    rewrite primitive_chunk_access in Hmode.
    assert (stored=chunk) by (apply source_chunk_translation_injective; congruence). subst stored.
    rewrite Z2Nat.id in Hcell by lia.
    pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as Hbounds.
    pose proof (Ptrofs.unsigned_range base).
    pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
    rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in Hcell.
    + exact Hcell.
    + change (0 <= i * sizeof_ptype primitive <= Ptrofs.max_unsigned).
      destruct Hbounds as [Hnonnegative [Hsize Hextent]].
      change (i * sizeof_ptype primitive + size_chunk (transl_bchunk_cchunk chunk) <=
        sizeof_ptype primitive * Z.max 0 count) in Hextent.
      unfold Ptrofs.max_unsigned. lia.
Qed.

Theorem located_aggregate_scalar_copy_plan :
  forall ge Sigma m objects cells packets source base destination target basic attr,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets source base (construct_type_btype basic) ->
  packet_heap_locations ge cells objects packets destination target (Ptrtype (Reftype basic attr)) ->
  aggregate_copy_ready ge m (construct_type_btype basic) source base destination target ->
  scalar_copy_plan cells cells source (Ptrofs.unsigned base) destination
    (Ptrofs.unsigned target) (aggregate_copy_size ge (construct_type_btype basic)).
Proof.
  intros ge Sigma m objects cells packets source base destination target basic attr
    Hmemory Hsource Htarget Hready b ofs ty chunk Hcell.
  pose proof (located_aggregate_reference_object _ _ _ _ _ _ _ _ _ _ Hmemory
    (copy_kind _ _ _ _ _ _ _ Hready) Htarget) as Hobject.
  destruct (scalar_object_coherence_root _ _ _ _ _ _
    (initialized_object_scalar_coherence _ _ _ _ _ Hmemory) Hobject
    (copy_size_nonnegative _ _ _ _ _ _ _ Hready) _ _ _ _ Hcell)
    as [Haway|[delta [Hleaf [Hb Hofs]]]].
  - left; split; assumption.
  - right; split; [exact Hb|]. exists delta, (Ptrofs.repr (Ptrofs.unsigned base + delta)).
    pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Hs Hbnd]].
    pose proof (copy_source_bound _ _ _ _ _ _ _ Hready) as Hbound.
    pose proof (Ptrofs.unsigned_range base).
    pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
    split; [eapply located_basic_scalar_leaf; eauto|].
    split; [exact Hd|]. split; [exact Hbnd|].
    split; [apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; unfold aggregate_copy_size in *; lia|].
    split; [exact Hofs|].
    exact (proj2 (typed_cell_permission _ _ _ _ _ _ _
      (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell))).
Qed.

Require Import BeePL_layout_coherence BeePL_array_proofs.
Lemma callable_primitive_array_relative_alignment :
  forall cenv Sigma m cells source base pt count attr,
  typed_memory_layout cenv Sigma cells m -> coherent_layout cells ->
  array_reference_locations cenv cells source base (Atype (Vtype pt) count attr) ->
  relative_copy_alignment cells source (Ptrofs.unsigned base)
    (sizeof_type cenv (Atype (Vtype pt) count attr)).
Proof.
  intros cenv Sigma m cells source base pt count attr Hmemory Hcoherent
    [elem [len [a [Heq [Hlen Hcells]]]]] ofs ty chunk delta Hcell Hofs Hdelta Hinside.
  inversion Heq; subst elem len a.
  simpl in Hinside. rewrite Z.max_r in Hinside by exact Hlen.
  pose proof (primitive_size_positive pt) as Hsize.
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)) as Hpositive.
  pose proof (Ptrofs.unsigned_range ofs) as HofsRange.
  pose proof (Ptrofs.unsigned_range base) as HbaseRange.
  set (q := delta / sizeof_ptype pt).
  assert (Hq : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (Hqlt : q < count) by (unfold q; apply Z.div_lt_upper_bound; nia).
  assert (Hdecomp : delta = sizeof_ptype pt * q + delta mod sizeof_ptype pt)
    by (unfold q; apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound delta (sizeof_ptype pt) Hsize) as Hmod.
  assert (Hi : (Z.to_nat q < Z.to_nat count)%nat) by (apply Z2Nat.inj_lt; lia).
  destruct (Hcells _ Hi) as [stored Hcanonical].
  rewrite Z2Nat.id in Hcanonical by exact Hq.
  pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcanonical)) as Hmode.
  rewrite primitive_chunk_access in Hmode.
  assert (stored = chunk_of_ptype pt) by (apply source_chunk_translation_injective; congruence).
  subst stored.
  assert (Hrelative : 0 <= q * sizeof_ptype pt <= Ptrofs.max_unsigned)
    by (unfold Ptrofs.max_unsigned; nia).
  assert (Habsolute : 0 <= Ptrofs.unsigned base + q * sizeof_ptype pt <= Ptrofs.max_unsigned)
    by (unfold Ptrofs.max_unsigned; nia).
  change (cells source (Ptrofs.add base (Ptrofs.repr (q * sizeof_ptype pt)))
    (Vtype pt) (chunk_of_ptype pt)) in Hcanonical.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in Hcanonical by exact Hrelative.
  pose proof (Hcoherent _ _ _ _ Hcanonical _ _ _ _ Hcell) as Hcompatible.
  rewrite Ptrofs.unsigned_repr in Hcompatible by exact Habsolute.
  rewrite primitive_chunk_size in Hcompatible.
  destruct Hcompatible as [[Hb [He [Ht Hchunk]]]|[Hneq|[Hafter|Hbefore]]].
  - subst chunk. rewrite primitive_chunk_alignment. exists q.
    apply (f_equal Ptrofs.unsigned) in He. rewrite Ptrofs.unsigned_repr in He by exact Habsolute. nia.
  - contradiction.
  - nia.
  - nia.
Qed.

Theorem located_basic_relative_copy_alignment :
  forall ge p Sigma m objects cells packets source base basic,
  ge.(genv_cenv) = p.(prog_comp_env) ->
  initialized_object_memory ge Sigma m objects cells -> coherent_layout cells ->
  is_aggregate_type (construct_type_btype basic) = true ->
  packet_heap_locations ge cells objects packets source base (construct_type_btype basic) ->
  relative_copy_alignment cells source (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)).
Proof.
  intros ge p Sigma m objects cells packets source base basic Henv Hmemory Hcoherent Hkind Hloc.
  destruct Hloc as [Hloc|[Hbytes Hpacket]]; [|destruct basic; discriminate Hbytes].
  destruct Hloc as [Hcall|[[Haggregate Hobject]|[bt [pa [Htype Hrest]]]]].
  - destruct basic; simpl in Hkind; try discriminate.
    + destruct Hcall as [[pt [chunk [Hbad Hcell]]]|[elem [len [otherAttr [Hbad Hrest]]]]]; discriminate Hbad.
    + destruct Hcall as [[pt [chunk [Hbad Hcell]]]|Harray]; [discriminate Hbad|].
      eapply callable_primitive_array_relative_alignment;
        [exact (initialized_object_cells _ _ _ _ _ Hmemory)|exact Hcoherent|exact Harray].
  - pose proof (initialized_object_scalar_coherence _ _ _ _ _ Hmemory) as Hscalar.
    pose proof (aggregate_object_readable _ _ _ _
      (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobject) as Hreadable.
    rewrite Henv in Hscalar, Hreadable |- *.
    eapply coherent_object_relative_copy_alignment;
      [exact Hscalar|exact Hobject|exact (proj1 (proj2 Hreadable))].
  - destruct basic; discriminate Htype.
Qed.

Print Assumptions located_aggregate_scalar_copy_plan.
Print Assumptions located_basic_relative_copy_alignment.
Print Assumptions callable_primitive_array_relative_alignment.
