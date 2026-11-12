(* Callable indexed arrays retain their existing representation. Their actual
   source allocation profile supplies the whole readable extent. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_soundness_store.
Require Import BeePL_soundness_memory BeePL_soundness_arrays BeePL_runtime_locations.
Require Import BeePL_array_proofs BeePL_array_object_coverage BeePL_layout_coherence.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory.
Require Import BeePL_block_extents BeePL_heap_extents BeePL_scalar_location_coherence.
Require Import BeePL_scalar_object_layout BeePL_packet_heap BeePL_packet_object_layout.
Require Import BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_coverage.
Local Open Scope Z_scope.

Lemma typed_data_object_store_origin : forall env Sigma b offset ty,
  object_type_at env Sigma b offset ty -> is_funtype ty = false ->
  exists stored, PTree.get b Sigma = Some stored /\ is_funtype stored = false.
Proof.
  intros env Sigma b offset ty Hobject. induction Hobject; intro Hdata.
  - exists stored. split; [assumption|]. destruct stored; simpl in *; auto; discriminate.
  - apply IHHobject; reflexivity.
  - apply IHHobject; reflexivity.
Qed.

Lemma callable_primitive_array_readable : forall ge Sigma m objects cells packets b base pt len attr,
  initialized_object_memory ge Sigma m objects cells ->
  heap_block_extents Sigma m objects cells packets ->
  object_type_at ge.(genv_cenv) Sigma b (Ptrofs.unsigned base) (Atype (Vtype pt) len attr) ->
  array_reference_locations ge.(genv_cenv) cells b base (Atype (Vtype pt) len attr) ->
  aggregate_readable ge.(genv_cenv) m b base (Atype (Vtype pt) len attr) /\
  Ptrofs.unsigned base + sizeof_type ge.(genv_cenv) (Atype (Vtype pt) len attr) <= Ptrofs.max_unsigned.
Proof.
  intros * Hmemory Hextents Hobject Harray.
  assert (Htracked : tracked_data_block Sigma objects cells packets b).
  { left. eapply typed_data_object_store_origin; [exact Hobject|reflexivity]. }
  destruct (heap_extent_lookup _ _ _ _ _ _ Hextents Htracked) as [limit Hextent].
  assert (Hlen : 0 <= len).
  { destruct Harray as [e [n [a [Heq [Hn Hcells]]]]]; inversion Heq; subst; assumption. }
  pose proof (primitive_array_extent_representable _ _ _ _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory) Hextent Harray) as Hbound.
  assert (Hsize : sizeof_type ge.(genv_cenv) (Atype (Vtype pt) len attr) = len * sizeof_ptype pt).
  { simpl. rewrite Z.max_r by exact Hlen. ring. }
  split; [|rewrite Hsize; exact Hbound].
  unfold aggregate_readable. rewrite Hsize.
  split; [reflexivity|]. split; [pose proof (primitive_size_positive pt); nia|].
  split; [unfold Ptrofs.max_unsigned in Hbound; lia|].
  split; [exact (source_extent_valid _ _ _ Hextent)|].
  intros offset Hrange. destruct (Z.eq_dec len 0) as [->|Hpositive]; [lia|].
  pose proof (primitive_array_extent_bound _ _ _ _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory) Hextent Harray ltac:(lia)) as Hlimit.
  eapply Mem.perm_implies; [apply (source_extent_freeable _ _ _ Hextent); pose proof (Ptrofs.unsigned_range base); lia|constructor].
Qed.

(* Any nonempty interval overlapping a tiled, positive-length array overlaps
   one of its primitive cells. No global interval enumeration is needed. *)
Lemma primitive_tiling_overlap : forall start width count low high,
  0 < width -> 0 < count -> low < high -> start < high -> low < start + count * width ->
  exists i, 0 <= i < count /\ low < start + (i+1)*width /\ start+i*width < high.
Proof.
  intros start width count low high Hwidth Hcount Hinterval Hleft Hright.
  destruct (Z_lt_ge_dec low start) as [Hbefore|Hafter].
  - exists 0. repeat split; nia.
  - exists ((low-start)/width).
    pose proof (Z.div_pos (low-start) width ltac:(lia) ltac:(lia)) as Hnonnegative.
    assert (Hindex : (low-start)/width < count) by (apply Z.div_lt_upper_bound; nia).
    pose proof (Z.div_mod (low-start) width ltac:(lia)).
    pose proof (Z.mod_pos_bound (low-start) width Hwidth).
    repeat split; nia.
Qed.

Require Import BeePL_scalar_object_coherence BeePL_initializer_coherence.
Lemma callable_primitive_index_cell : forall env Sigma m cells b base pt len attr i,
  typed_memory_layout env Sigma cells m ->
  array_reference_locations env cells b base (Atype (Vtype pt) len attr) ->
  Ptrofs.unsigned base + len * sizeof_ptype pt <= Ptrofs.max_unsigned ->
  0 <= i < len ->
  cells b (Ptrofs.repr (Ptrofs.unsigned base + i * sizeof_ptype pt))
    (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros * Hmemory [elem [count [a [Heq [Hlen Hcells]]]]] Hbound Hi.
  inversion Heq; subst elem count a.
  destruct (Hcells (Z.to_nat i) ltac:(apply Z2Nat.inj_lt; lia)) as [chunk Hcell].
  rewrite Z2Nat.id in Hcell by lia.
  pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
  rewrite primitive_chunk_access in Hmode.
  assert (chunk=chunk_of_ptype pt) by (apply source_chunk_translation_injective; congruence). subst chunk.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in Hcell.
  - exact Hcell.
  - change (0 <= i * sizeof_ptype pt <= Ptrofs.max_unsigned).
    pose proof (primitive_size_positive pt). pose proof (Ptrofs.unsigned_range base). nia.
Qed.

Lemma primitive_array_index_leaf : forall env pt len attr i,
  0 <= i < len ->
  scalar_object_leaf env (Atype (Vtype pt) len attr) (i * sizeof_ptype pt)
    (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros * Hi. split; [|apply primitive_chunk_access].
  replace (i * sizeof_ptype pt) with (0 + i * sizeof_type env (Vtype pt)) by reflexivity.
  eapply path_array_element; [|exact Hi|pose proof (primitive_size_positive pt); simpl; lia].
  apply path_root, primitive_array_size_nonnegative.
Qed.

Lemma callable_primitive_array_scalar_region : forall env Sigma m cells b base pt len attr,
  typed_memory_layout env Sigma cells m -> coherent_layout cells ->
  array_reference_locations env cells b base (Atype (Vtype pt) len attr) ->
  0 < len -> Ptrofs.unsigned base + len * sizeof_ptype pt <= Ptrofs.max_unsigned ->
  scalar_object_region_coherent env cells b (Ptrofs.unsigned base) (Atype (Vtype pt) len attr).
Proof.
  intros * Hmemory Hcoherent Harray Hlen Hbound block ofs ty chunk Hcell.
  destruct (peq block b) as [Heq|Hneq]; [subst block|left; left; exact Hneq].
  destruct (Z_le_gt_dec (Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk)) (Ptrofs.unsigned base)) as [Hbefore|Hbefore].
  { left; right; left; exact Hbefore. }
  assert (Hsize : sizeof_type env (Atype (Vtype pt) len attr)=len*sizeof_ptype pt).
  { simpl. rewrite Z.max_r by lia. ring. }
  destruct (Z_le_gt_dec (Ptrofs.unsigned base + len*sizeof_ptype pt) (Ptrofs.unsigned ofs)) as [Hafter|Hafter].
  { left; right; right. rewrite Hsize; exact Hafter. }
  pose proof (primitive_size_positive pt) as Hwidth.
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)) as Hpositive.
  destruct (primitive_tiling_overlap (Ptrofs.unsigned base) (sizeof_ptype pt) len
    (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs+size_chunk (transl_bchunk_cchunk chunk))
    Hwidth Hlen ltac:(lia) ltac:(lia) ltac:(lia)) as [i [Hi [Hleft Hright]]].
  pose proof (callable_primitive_index_cell _ _ _ _ _ _ _ _ _ _ Hmemory Harray Hbound Hi) as Hcanonical.
  assert (Hrange : 0 <= Ptrofs.unsigned base+i*sizeof_ptype pt <= Ptrofs.max_unsigned)
    by (pose proof (Ptrofs.unsigned_range base); nia).
  pose proof (Hcoherent _ _ _ _ Hcanonical _ _ _ _ Hcell) as Hcompatible.
  rewrite Ptrofs.unsigned_repr in Hcompatible by exact Hrange.
  rewrite primitive_chunk_size in Hcompatible.
  destruct Hcompatible as [[Hb [Hofs [Hty Hchunk]]]|[Hneq|[Haway|Haway]]]; try contradiction; try nia.
  subst ofs ty chunk. right; exists (i*sizeof_ptype pt). split.
  - apply primitive_array_index_leaf; exact Hi.
  - split; [reflexivity|apply Ptrofs.unsigned_repr; exact Hrange].
Qed.

Lemma declared_scalar_region_hereditary : forall env cells block base root,
  scalar_object_region_coherent env cells block base root -> declared_leaf_separation env root ->
  forall delta child, object_path env root delta child ->
    scalar_object_region_coherent env cells block (base+delta) child.
Proof.
  intros * Hregion Hseparation delta child Hpath b ofs ty chunk Hcell.
  pose proof (object_path_bounds _ _ _ _ Hpath) as Hbounds.
  destruct (Hregion _ _ _ _ Hcell) as [Haway|[offset [Hleaf [Hb Ho]]]].
  - left. intuition lia.
  - destruct (Hseparation _ _ _ Hleaf _ _ Hpath) as [Haway|[relative [Hsub Hoffset]]].
    + left; right; intuition lia.
    + right; exists relative. split; [exact Hsub|]. split; [exact Hb|lia].
Qed.

Lemma tiled_packet_interval_separated : forall b start width count other low size,
  0 < width -> 0 < count -> 0 <= size ->
  (forall i, 0 <= i < count -> packet_interval_disjoint other low size b (start+i*width) width) ->
  packet_interval_disjoint other low size b start (count*width).
Proof.
  intros * Hwidth Hcount Hsize Htiles.
  destruct (Z.eq_dec size 0) as [Hzero|Hnonzero]; [left; exact Hzero|].
  destruct (peq other b) as [Heq|Hneq]; [subst other|right; left; exact Hneq].
  destruct (Z_le_gt_dec (low+size) start) as [Hbefore|Hbefore]; [right; right; left; exact Hbefore|].
  destruct (Z_le_gt_dec (start+count*width) low) as [Hafter|Hafter]; [right; right; right; exact Hafter|].
  destruct (primitive_tiling_overlap start width count low (low+size) Hwidth Hcount
    ltac:(lia) ltac:(lia) ltac:(lia)) as [i [Hi [Hl Hr]]].
  specialize (Htiles i Hi). unfold packet_interval_disjoint in Htiles. intuition nia.
Qed.

Require Import BeePL_packet BeePL_packet_location_coherence.
Lemma packet_disjoint_target_subrange : forall block start size target base width delta child,
  packet_interval_disjoint block start size target base width ->
  0 <= delta -> delta+child <= width ->
  packet_interval_disjoint block start size target (base+delta) child.
Proof. unfold packet_interval_disjoint; intros; intuition lia. Qed.

Lemma callable_primitive_array_packet_regions : forall env Sigma m cells packets b base pt len attr,
  typed_memory_layout env Sigma cells m -> packet_layout_separated m packets cells ->
  array_reference_locations env cells b base (Atype (Vtype pt) len attr) ->
  0 < len -> Ptrofs.unsigned base + len*sizeof_ptype pt <= Ptrofs.max_unsigned ->
  forall delta child, object_path env (Atype (Vtype pt) len attr) delta child ->
  packet_object_region_coherent env m packets b (Ptrofs.unsigned base+delta) child.
Proof.
  intros * Hmemory Hseparated Harray Hlen Hbound.
  assert (Htile : forall i, 0 <= i < len -> packet_write_separated m packets b
    (Ptrofs.unsigned base+i*sizeof_ptype pt) (sizeof_ptype pt)).
  { intros i Hi. pose proof (callable_primitive_index_cell _ _ _ _ _ _ _ _ _ _ Hmemory Harray Hbound Hi) as Hcell.
    pose proof (Hseparated _ _ _ _ Hcell) as Hsep.
    rewrite Ptrofs.unsigned_repr, primitive_chunk_size in Hsep.
    - exact Hsep.
    - pose proof (Ptrofs.unsigned_range base). pose proof (primitive_size_positive pt). nia. }
  assert (Hwhole : packet_write_separated m packets b (Ptrofs.unsigned base) (len*sizeof_ptype pt)).
  { intros descriptor offset Hin; split.
    - eapply tiled_packet_interval_separated; [apply primitive_size_positive|exact Hlen|pose proof packet_descriptor_size_positive; lia|].
      intros i Hi. exact (proj1 (Htile i Hi _ _ Hin)).
    - intros view Hview. eapply tiled_packet_interval_separated;
        [apply primitive_size_positive|exact Hlen| |].
      + destruct Hview as [_ [_ [Horder Hrest]]]; lia.
      + intros i Hi. exact (proj2 (Htile i Hi _ _ Hin) _ Hview). }
  intros delta child Hpath descriptor offset Hin.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hd [Hs Hinside]].
  assert (Hsize : sizeof_type env (Atype (Vtype pt) len attr)=len*sizeof_ptype pt).
  { simpl; rewrite Z.max_r by lia; ring. }
  rewrite Hsize in Hinside. split.
  - left. eapply packet_disjoint_target_subrange; [exact (proj1 (Hwhole _ _ Hin))|exact Hd|exact Hinside].
  - intros view Hview. eapply packet_disjoint_target_subrange;
      [exact (proj2 (Hwhole _ _ Hin) _ Hview)|exact Hd|exact Hinside].
Qed.

Theorem register_positive_callable_array : forall ge Sigma m objects cells packets b base pt len attr,
  initialized_object_memory ge Sigma m objects cells -> coherent_layout cells ->
  packet_heap_invariant ge Sigma m objects cells packets -> heap_block_extents Sigma m objects cells packets ->
  object_type_at ge.(genv_cenv) Sigma b (Ptrofs.unsigned base) (Atype (Vtype pt) len attr) ->
  array_reference_locations ge.(genv_cenv) cells b base (Atype (Vtype pt) len attr) ->
  0 < len ->
  let objects' := add_aggregate_descriptor objects b base (Atype (Vtype pt) len attr) in
  initialized_object_memory ge Sigma m objects' cells /\
  packet_heap_invariant ge Sigma m objects' cells packets /\
  heap_block_extents Sigma m objects' cells packets.
Proof.
  intros * Hmemory Hcoherent Hpackets Hextents Htype Harray Hlen objects'.
  destruct (callable_primitive_array_readable _ _ _ _ _ _ _ _ _ _ _ Hmemory Hextents Htype Harray)
    as [Hread Hbound].
  assert (Hsize : sizeof_type ge.(genv_cenv) (Atype (Vtype pt) len attr)=len*sizeof_ptype pt).
  { simpl; rewrite Z.max_r by lia; ring. }
  assert (Hnumeric : Ptrofs.unsigned base+len*sizeof_ptype pt<=Ptrofs.max_unsigned) by (rewrite <- Hsize; exact Hbound).
  assert (Hcells : typed_memory_layout ge.(genv_cenv) Sigma cells m)
    by exact (initialized_object_cells _ _ _ _ _ Hmemory).
  split.
  - constructor.
    + constructor; intros block offset ty [Hold|[Hb [Hofs Hty]]].
      * eapply aggregate_object_typing; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hold].
      * subst; exact Htype.
      * eapply aggregate_object_readable; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hold].
      * subst; exact Hread.
      * eapply aggregate_object_address_bound; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hold].
      * subst; exact Hbound.
    + intros block offset root [Hold|[Hb [Hofs Hty]]] delta ty chunk Hleaf.
      * eapply (initialized_object_leaves _ _ _ _ _ Hmemory); eauto.
      * subst block offset root. destruct (primitive_array_scalar_leaf _ _ _ _ _ _ _ Hleaf)
          as [i [Hi [Hd [Ht Hchunk]]]]. subst delta ty.
        exists (chunk_of_ptype pt); split; [eapply callable_primitive_index_cell; eauto|symmetry; exact Hchunk].
    + exact Hcells.
    + intros block offset ty chunk Hcell v Hloaded.
      eapply value_locations_monotone with (L := descriptor_heap_locations ge cells objects).
      * apply descriptor_heap_locations_monotone; [auto|intros; left; assumption].
      * eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto.
    + intros block offset root [Hold|[Hb [Hofs Hty]]] delta child Hpath.
      * eapply (initialized_object_scalar_coherence _ _ _ _ _ Hmemory); eauto.
      * subst block offset root. eapply declared_scalar_region_hereditary; [| |exact Hpath].
        -- eapply callable_primitive_array_scalar_region; eauto.
        -- replace len with (Z.of_nat (Z.to_nat len)) by (rewrite Z2Nat.id by lia; reflexivity).
           apply primitive_array_leaf_separation.
  - split.
    + destruct Hpackets as [Hv Ht Hcover Hsep HobjectCoherence]. constructor; try assumption.
      * intros block offset root [Hold|[Hb [Hofs Hty]]] delta Hpath.
        -- eapply Hcover; eauto.
        -- subst block offset root. exfalso. eapply callable_array_has_no_bytes_path; eauto.
      * intros block offset root [Hold|[Hb [Hofs Hty]]] delta child Hpath.
        -- eapply HobjectCoherence; eauto.
        -- subst block offset root. eapply callable_primitive_array_packet_regions; eauto.
    + eapply heap_extents_add_object; [exact Hextents|]. left.
      eapply typed_data_object_store_origin; [exact Htype|reflexivity].
Qed.

Print Assumptions callable_primitive_array_readable.
Print Assumptions register_positive_callable_array.
