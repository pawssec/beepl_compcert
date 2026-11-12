(* Indexed callable arrays may contain any inhabited scalar type, including
   references and options. Empty arrays need no scalar element witness. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_soundness_arrays.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory.
Require Import BeePL_block_extents BeePL_heap_extents BeePL_callable_array_objects.
Require Import BeePL_initializer_coherence BeePL_scalar_object_coherence BeePL_layout_coherence.
Local Open Scope Z_scope.

Lemma callable_array_scalar_witness : forall env Sigma m cells b base elem len attr,
 typed_memory_layout env Sigma cells m ->
 array_reference_locations env cells b base (Atype elem len attr) -> 0<len ->
 exists chunk, access_mode_type elem=By_value(transl_bchunk_cchunk chunk) /\
 0<sizeof_type env elem.
Proof.
 intros * Htyped [e [n [a [Heq [Hn Hcells]]]]] Hpositive.
 inversion Heq; subst e n a.
 destruct (Hcells O ltac:(apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; simpl; lia)) as [chunk Hcell].
 exists chunk. pose proof (typed_cell_access _ _ _ _ _ _ _ (Htyped _ _ _ _ Hcell)) as Hmode.
 split; [exact Hmode|]. rewrite <- (scalar_type_chunk_size env elem _ Hmode).
 pose proof(size_chunk_pos (transl_bchunk_cchunk chunk)); lia.
Qed.

Lemma callable_scalar_array_extent_bound : forall env Sigma m cells b base elem len attr limit,
 typed_memory_layout env Sigma cells m -> source_block_extent m b limit ->
 array_reference_locations env cells b base (Atype elem len attr) -> 0<len ->
 Ptrofs.unsigned base+len*sizeof_type env elem<=limit.
Proof.
 intros * Htyped Hextent Harray Hpositive.
 destruct (callable_array_scalar_witness _ _ _ _ _ _ _ _ _ Htyped Harray Hpositive) as [canonical [Hmode Hwidth]].
 destruct Harray as [e [n [a [Heq [Hn Hcells]]]]]; inversion Heq; subst e n a.
 eapply indexed_extent_nonwrapping; [exact Hextent|exact Hwidth|exact Hpositive|].
 intros i Hi. destruct (Hcells (Z.to_nat i) ltac:(apply Z2Nat.inj_lt; lia)) as [chunk Hcell].
 rewrite Z2Nat.id in Hcell by lia.
 pose proof (Htyped _ _ _ _ Hcell) as Htypedcell.
 pose proof (typed_cell_permission _ _ _ _ _ _ _ Htypedcell) as [Hperm Halign].
 rewrite (scalar_type_chunk_size env elem _ (typed_cell_access _ _ _ _ _ _ _ Htypedcell)) in Hperm.
 exact Hperm.
Qed.

Lemma callable_scalar_array_readable : forall ge Sigma m objects cells packets b base elem len attr,
 initialized_object_memory ge Sigma m objects cells -> heap_block_extents Sigma m objects cells packets ->
 object_type_at ge.(genv_cenv) Sigma b (Ptrofs.unsigned base) (Atype elem len attr) ->
 array_reference_locations ge.(genv_cenv) cells b base (Atype elem len attr) ->
 aggregate_readable ge.(genv_cenv) m b base (Atype elem len attr) /\
 Ptrofs.unsigned base+sizeof_type ge.(genv_cenv) (Atype elem len attr)<=Ptrofs.max_unsigned.
Proof.
 intros * Hmemory Hextents Hobject Harray.
 assert (Htracked:tracked_data_block Sigma objects cells packets b).
 { left. eapply typed_data_object_store_origin; [exact Hobject|reflexivity]. }
 destruct (heap_extent_lookup _ _ _ _ _ _ Hextents Htracked) as [limit Hextent].
 assert (Hlen:0<=len).
 { destruct Harray as [e [n [a [Heq [Hn Hcells]]]]]; inversion Heq; subst; assumption. }
 assert (Hsize:sizeof_type ge.(genv_cenv) (Atype elem len attr)=len*sizeof_type ge.(genv_cenv) elem).
 { simpl; rewrite Z.max_r by lia; ring. }
 destruct (Z.eq_dec len 0) as [Hzero|Hpositive].
 - split; [|rewrite Hsize, Hzero, Z.mul_0_l; pose proof(Ptrofs.unsigned_range_2 base); lia].
   unfold aggregate_readable; rewrite Hsize, Hzero, Z.mul_0_l.
   repeat split; try reflexivity; try lia.
   + pose proof(Ptrofs.unsigned_range base); lia.
   + exact (source_extent_valid _ _ _ Hextent).
   + unfold Mem.range_perm; intros offset Hrange; lia.
 - pose proof (callable_scalar_array_extent_bound _ _ _ _ _ _ _ _ _ _
     (initialized_object_cells _ _ _ _ _ Hmemory) Hextent Harray ltac:(lia)) as Hlimit.
   destruct (callable_array_scalar_witness _ _ _ _ _ _ _ _ _
     (initialized_object_cells _ _ _ _ _ Hmemory) Harray ltac:(lia)) as [chunk [Hmode Hwidth]].
   pose proof(source_extent_bound _ _ _ Hextent) as Hbounds.
   split; [|rewrite Hsize; lia]. unfold aggregate_readable; rewrite Hsize.
   split; [reflexivity|]. split; [nia|]. split; [unfold Ptrofs.max_unsigned in *; lia|].
   split; [exact(source_extent_valid _ _ _ Hextent)|].
   intros offset Hrange. eapply Mem.perm_implies.
   + apply(source_extent_freeable _ _ _ Hextent); pose proof(Ptrofs.unsigned_range base); lia.
   + constructor.
Qed.

Require Import BeePL_packet_location_coherence BeePL_object_separation.
Lemma callable_scalar_index_cell : forall env Sigma m cells b base elem len attr i,
 typed_memory_layout env Sigma cells m ->
 array_reference_locations env cells b base (Atype elem len attr) ->
 Ptrofs.unsigned base+len*sizeof_type env elem<=Ptrofs.max_unsigned -> 0<=i<len ->
 exists chunk, cells b (Ptrofs.repr(Ptrofs.unsigned base+i*sizeof_type env elem)) elem chunk /\
 access_mode_type elem=By_value(transl_bchunk_cchunk chunk).
Proof.
 intros * Hmemory Harray Hbound Hi.
 destruct (callable_array_scalar_witness _ _ _ _ _ _ _ _ _ Hmemory Harray ltac:(lia)) as [ch [Hm Hwidth]].
 destruct Harray as [e [n [a [Heq [Hn Hcells]]]]]; inversion Heq; subst e n a.
 destruct (Hcells (Z.to_nat i) ltac:(apply Z2Nat.inj_lt; lia)) as [chunk Hcell].
 rewrite Z2Nat.id in Hcell by lia.
 pose proof(typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
 exists chunk; split; [|exact Hmode].
 rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in Hcell.
 - exact Hcell.
 - pose proof(Ptrofs.unsigned_range base); nia.
Qed.

Lemma scalar_array_index_leaf : forall env elem len attr i chunk,
 access_mode_type elem=By_value(transl_bchunk_cchunk chunk) -> 0<=i<len ->
 scalar_object_leaf env (Atype elem len attr) (i*sizeof_type env elem) elem chunk.
Proof.
 intros * Hmode Hi. pose proof(size_chunk_pos (transl_bchunk_cchunk chunk)) as Hwidth.
 rewrite (scalar_type_chunk_size env elem _ Hmode) in Hwidth.
 split; [|exact Hmode].
 replace (i*sizeof_type env elem) with (0+i*sizeof_type env elem) by lia.
 eapply path_array_element; [|exact Hi|lia]. apply path_root.
 simpl; rewrite Z.max_r by lia; nia.
Qed.

Lemma callable_scalar_array_coverage : forall env Sigma m cells b base elem len attr,
 typed_memory_layout env Sigma cells m ->
 array_reference_locations env cells b base (Atype elem len attr) ->
 Ptrofs.unsigned base+sizeof_type env (Atype elem len attr)<=Ptrofs.max_unsigned ->
 forall delta ty chunk, scalar_object_leaf env (Atype elem len attr) delta ty chunk ->
 exists stored, cells b (Ptrofs.repr(Ptrofs.unsigned base+delta)) ty stored /\
 transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Proof.
 intros * Hmemory Harray Hbound delta ty chunk Hleaf.
 pose proof(scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Ht Hinside]].
 assert(Hlen:0<len).
 { destruct(Z_le_gt_dec len 0); [|lia]. simpl in Hinside; rewrite Z.max_l in Hinside by lia.
   pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)); nia. }
 destruct(callable_array_scalar_witness _ _ _ _ _ _ _ _ _ Hmemory Harray Hlen) as [ch [Hmode Hwidth]].
 destruct(by_value_array_object_paths _ _ _ _ _ _ _ Hmode (proj1 Hleaf)) as [[Hz Heq]|[i [Hi [Hz Heq]]]].
 - subst ty; discriminate (proj2 Hleaf).
 - subst delta ty. simpl in Hbound; rewrite Z.max_r in Hbound by lia.
   destruct(callable_scalar_index_cell _ _ _ _ _ _ _ _ _ _ Hmemory Harray ltac:(nia) Hi) as [stored [Hcell Hstored]].
   exists stored; split; [exact Hcell|]. pose proof(proj2 Hleaf); congruence.
Qed.

Lemma callable_scalar_array_scalar_region : forall env Sigma m cells b base elem len attr,
  typed_memory_layout env Sigma cells m -> coherent_layout cells ->
  array_reference_locations env cells b base (Atype elem len attr) ->
  0 < len -> Ptrofs.unsigned base + len * sizeof_type env elem <= Ptrofs.max_unsigned ->
  scalar_object_region_coherent env cells b (Ptrofs.unsigned base) (Atype elem len attr).
Proof.
  intros * Hmemory Hcoherent Harray Hlen Hbound block ofs ty chunk Hcell.
  destruct (peq block b) as [Heq|Hneq]; [subst block|left; left; exact Hneq].
  destruct (Z_le_gt_dec (Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk)) (Ptrofs.unsigned base)) as [Hbefore|Hbefore].
  { left; right; left; exact Hbefore. }
  assert (Hsize : sizeof_type env (Atype elem len attr)=len*sizeof_type env elem).
  { simpl. rewrite Z.max_r by lia. ring. }
  destruct (Z_le_gt_dec (Ptrofs.unsigned base + len*sizeof_type env elem) (Ptrofs.unsigned ofs)) as [Hafter|Hafter].
  { left; right; right. rewrite Hsize; exact Hafter. }
  destruct (callable_array_scalar_witness _ _ _ _ _ _ _ _ _ Hmemory Harray Hlen) as [witness [Hmode Hwidth]].
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)) as Hpositive.
  destruct (primitive_tiling_overlap (Ptrofs.unsigned base) (sizeof_type env elem) len
    (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs+size_chunk (transl_bchunk_cchunk chunk))
    Hwidth Hlen ltac:(lia) ltac:(lia) ltac:(lia)) as [i [Hi [Hleft Hright]]].
  destruct (callable_scalar_index_cell _ _ _ _ _ _ _ _ _ _ Hmemory Harray Hbound Hi) as [canonical [Hcanonical HcanonicalMode]].
  assert (Hrange : 0 <= Ptrofs.unsigned base+i*sizeof_type env elem <= Ptrofs.max_unsigned)
    by (pose proof (Ptrofs.unsigned_range base); nia).
  pose proof (Hcoherent _ _ _ _ Hcanonical _ _ _ _ Hcell) as Hcompatible.
  rewrite Ptrofs.unsigned_repr in Hcompatible by exact Hrange.
  rewrite (scalar_type_chunk_size env elem _ HcanonicalMode) in Hcompatible.
  destruct Hcompatible as [[Hb [Hofs [Hty Hchunk]]]|[Hneq|[Haway|Haway]]]; try contradiction; try nia.
  subst ofs ty chunk. right; exists (i*sizeof_type env elem). split.
  - apply scalar_array_index_leaf; assumption.
  - split; [reflexivity|apply Ptrofs.unsigned_repr; exact Hrange].
Qed.


Theorem callable_scalar_array_regions : forall p Sigma m cells b base elem len attr,
 typed_memory_layout p.(prog_comp_env) Sigma cells m -> coherent_layout cells ->
 array_reference_locations p.(prog_comp_env) cells b base (Atype elem len attr) ->
 0<sizeof_type p.(prog_comp_env) (Atype elem len attr) ->
 Ptrofs.unsigned base+sizeof_type p.(prog_comp_env) (Atype elem len attr)<=Ptrofs.max_unsigned ->
 forall delta child, object_path p.(prog_comp_env) (Atype elem len attr) delta child ->
 scalar_object_region_coherent p.(prog_comp_env) cells b (Ptrofs.unsigned base+delta) child.
Proof.
 intros * Hmemory Hcoherent Harray Hsize Hbound delta child Hpath.
 assert(Hlen:0<len).
 { destruct(Z_le_gt_dec len 0); [|lia]. simpl in Hsize; rewrite Z.max_l in Hsize by lia; nia. }
 eapply declared_scalar_region_hereditary; [| |exact Hpath].
 - eapply callable_scalar_array_scalar_region; eauto. simpl in Hbound; rewrite Z.max_r in Hbound by lia; nia.
 - unfold declared_leaf_separation. intros. eapply program_scalar_leaf_subobject; eauto.
Qed.

Print Assumptions callable_scalar_array_readable.
Print Assumptions callable_scalar_array_coverage.
Print Assumptions callable_scalar_array_regions.
