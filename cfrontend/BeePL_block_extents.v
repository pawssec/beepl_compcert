(* Source-owned allocations have uniform permissions and finite, nonwrapping
   extents. This is not an assertion about readonly CompCert global blocks. *)
Require Import Coqlib List ZArith Lia Integers AST Maps Memory Memdata Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_object_paths.
Require Import BeePL_soundness_arrays BeePL_array_proofs.
Local Open Scope Z_scope.

Record source_block_extent (m : Mem.mem) (b : Values.block) (limit : Z) : Prop := {
  source_extent_valid : Mem.valid_block m b;
  source_extent_bound : 0 <= limit <= Ptrofs.max_unsigned;
  source_extent_freeable : Mem.range_perm m b 0 limit Cur Freeable;
  source_extent_outside : forall ofs, ofs < 0 \/ limit <= ofs -> ~ Mem.perm m b ofs Cur Nonempty
}.

Definition block_extent_context := PTree.t Z.
Definition block_extents_valid (m : Mem.mem) (limits : block_extent_context) : Prop :=
  forall b limit, PTree.get b limits = Some limit -> source_block_extent m b limit.

Lemma source_block_extent_transport : forall m final b limit,
  source_block_extent m b limit -> Mem.valid_block final b ->
  (forall ofs, Mem.perm m b ofs Cur Freeable -> Mem.perm final b ofs Cur Freeable) ->
  (forall ofs, Mem.perm final b ofs Cur Nonempty -> Mem.perm m b ofs Cur Nonempty) ->
  source_block_extent final b limit.
Proof.
  intros m final b limit [Hv Hb Hfree Houtside] Hv' Hforward Hbackward.
  constructor; auto. intros ofs Hrange; auto. intros ofs Hrange Hperm.
  eapply Houtside; [exact Hrange|apply Hbackward; exact Hperm].
Qed.

Theorem allocated_source_block_extent : forall m final fresh limit,
  Mem.alloc m 0 limit = (final,fresh) -> 0 <= limit <= Ptrofs.max_unsigned ->
  source_block_extent final fresh limit.
Proof.
  intros m final fresh limit Ha Hbound. constructor.
  - eapply Mem.valid_new_block; eauto.
  - exact Hbound.
  - intros ofs Hrange; eapply Mem.perm_alloc_2; eauto.
  - intros ofs Houtside Hperm.
    pose proof (Mem.perm_alloc_3 _ _ _ _ _ Ha _ _ _ Hperm); lia.
Qed.

Theorem source_block_extent_alloc_frame : forall m final fresh low high b limit,
  Mem.alloc m low high = (final,fresh) -> source_block_extent m b limit ->
  source_block_extent final b limit.
Proof.
  intros m final fresh low high b limit Ha Hextent.
  assert (Hneq : b <> fresh).
  { intro Heq; subst b. eapply (Mem.fresh_block_alloc _ _ _ _ _ Ha).
    exact (source_extent_valid _ _ _ Hextent). }
  eapply source_block_extent_transport; [exact Hextent| | |].
  - eapply Mem.valid_block_alloc; [exact Ha|exact (source_extent_valid _ _ _ Hextent)].
  - intros; eapply Mem.perm_alloc_1; eauto.
  - intros; eapply Mem.perm_alloc_4; eauto.
Qed.

Theorem source_block_extent_store : forall chunk m written offset value final b limit,
  Mem.store chunk m written offset value = Some final -> source_block_extent m b limit ->
  source_block_extent final b limit.
Proof.
  intros chunk m written offset value final b limit Hstore Hextent.
  eapply source_block_extent_transport; [exact Hextent| | |].
  - eapply Mem.store_valid_block_1; [exact Hstore|exact (source_extent_valid _ _ _ Hextent)].
  - intros; eapply Mem.perm_store_1; eauto.
  - intros; eapply Mem.perm_store_2; eauto.
Qed.

Theorem source_block_extent_storebytes : forall m written offset bytes final b limit,
  Mem.storebytes m written offset bytes = Some final -> source_block_extent m b limit ->
  source_block_extent final b limit.
Proof.
  intros m written offset bytes final b limit Hstore Hextent.
  eapply source_block_extent_transport; [exact Hextent| | |].
  - eapply Mem.storebytes_valid_block_1; [exact Hstore|exact (source_extent_valid _ _ _ Hextent)].
  - intros; eapply Mem.perm_storebytes_1; eauto.
  - intros; eapply Mem.perm_storebytes_2; eauto.
Qed.

Theorem block_extents_allocation : forall m final fresh size limits,
  block_extents_valid m limits -> Mem.alloc m 0 size = (final,fresh) ->
  0 <= size <= Ptrofs.max_unsigned ->
  block_extents_valid final (PTree.set fresh size limits).
Proof.
  intros m final fresh size limits Hvalid Ha Hsize b limit Hget.
  rewrite PTree.gsspec in Hget. destruct (peq b fresh).
  - subst b; inversion Hget; subst limit. eapply allocated_source_block_extent; eauto.
  - eapply source_block_extent_alloc_frame; [exact Ha|apply Hvalid; exact Hget].
Qed.

Theorem block_extents_store : forall chunk m written offset value final limits,
  block_extents_valid m limits -> Mem.store chunk m written offset value = Some final ->
  block_extents_valid final limits.
Proof. intros * Hvalid Hstore b limit Hget. eapply source_block_extent_store; eauto. Qed.

Theorem block_extents_storebytes : forall m written offset bytes final limits,
  block_extents_valid m limits -> Mem.storebytes m written offset bytes = Some final ->
  block_extents_valid final limits.
Proof. intros * Hvalid Hstore b limit Hget. eapply source_block_extent_storebytes; eauto. Qed.

Lemma source_extent_readable_freeable : forall m b limit low high,
  source_block_extent m b limit -> Mem.range_perm m b low high Cur Readable ->
  Mem.range_perm m b low high Cur Freeable.
Proof.
  intros m b limit low high Hextent Hread ofs Hin.
  assert (Hperm : Mem.perm m b ofs Cur Nonempty).
  { eapply Mem.perm_implies; [apply Hread; exact Hin|constructor]. }
  apply (source_extent_freeable _ _ _ Hextent).
  destruct (Z_lt_ge_dec ofs 0); [exfalso; eapply (source_extent_outside _ _ _ Hextent ofs); eauto|].
  destruct (Z_le_gt_dec limit ofs); [exfalso; eapply (source_extent_outside _ _ _ Hextent ofs); eauto|lia].
Qed.

Theorem source_extent_readable_writable : forall m b limit low high,
  source_block_extent m b limit -> Mem.range_perm m b low high Cur Readable ->
  Mem.range_perm m b low high Cur Writable.
Proof.
  intros. eapply Mem.range_perm_implies; [eapply source_extent_readable_freeable; eauto|constructor].
Qed.

Theorem aggregate_extent_writable : forall env m b base ty limit,
  source_block_extent m b limit -> aggregate_readable env m b base ty ->
  Mem.valid_block m b /\ Mem.range_perm m b (Ptrofs.unsigned base)
    (Ptrofs.unsigned base + sizeof_type env ty) Cur Writable.
Proof.
  intros env m b base ty limit Hextent [_ [_ [_ [Hv Hread]]]]. split; [exact Hv|].
  eapply source_extent_readable_writable; eauto.
Qed.

(* A modular array address cannot skip the first forbidden byte: the element
   containing [limit] starts before wraparound and would grant permission there. *)
Lemma indexed_extent_nonwrapping : forall m b base limit width count,
  source_block_extent m b limit -> 0 < width -> 0 < count ->
  (forall i, 0 <= i < count ->
    Mem.range_perm m b
      (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr (i * width))))
      (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr (i * width))) + width)
      Cur Freeable) ->
  Ptrofs.unsigned base + count * width <= limit.
Proof.
  intros m b base limit width count Hextent Hwidth Hcount Hcells.
  pose proof (Ptrofs.unsigned_range_2 base) as Hbase.
  pose proof (source_extent_bound _ _ _ Hextent) as Hlimit.
  assert (Hzero : Ptrofs.add base (Ptrofs.repr (0 * width)) = base).
  { rewrite Z.mul_0_l. change (Ptrofs.add base Ptrofs.zero = base).
    apply Ptrofs.add_zero. }
  assert (Hstart : Ptrofs.unsigned base < limit).
  { pose proof (Hcells 0 ltac:(lia)) as Hfirst. rewrite Hzero in Hfirst.
    destruct (Z_lt_ge_dec (Ptrofs.unsigned base) limit); auto.
    exfalso. eapply (source_extent_outside _ _ _ Hextent (Ptrofs.unsigned base)); [lia|].
    eapply Mem.perm_implies; [apply Hfirst; lia|constructor]. }
  destruct (Z_le_gt_dec (Ptrofs.unsigned base + count*width) limit); auto.
  set (index := (limit - Ptrofs.unsigned base) / width).
  pose proof (Z.div_mod (limit-Ptrofs.unsigned base) width ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (limit-Ptrofs.unsigned base) width Hwidth) as Hmod.
  assert (Hi : 0 <= index < count).
  { unfold index. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; nia. }
  assert (Hraw : 0 <= Ptrofs.unsigned base + index*width <= Ptrofs.max_unsigned) by
    (unfold index; nia).
  assert (Hdecode : Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr (index*width))) =
                     Ptrofs.unsigned base + index*width).
  { rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr (index*width)) by nia.
    apply Ptrofs.unsigned_repr; exact Hraw. }
  specialize (Hcells index Hi). rewrite Hdecode in Hcells.
  exfalso. eapply (source_extent_outside _ _ _ Hextent limit); [lia|].
  eapply Mem.perm_implies; [apply Hcells; unfold index; nia|constructor].
Qed.

Theorem primitive_array_extent_bound : forall env Sigma layout m b base pt len attr limit,
  typed_memory_layout env Sigma layout m -> source_block_extent m b limit ->
  array_reference_locations env layout b base (Atype (Vtype pt) len attr) ->
  0 < len -> Ptrofs.unsigned base + len * sizeof_ptype pt <= limit.
Proof.
  intros env Sigma layout m b base pt len attr limit Htyped Hextent Harray Hpositive.
  destruct Harray as [elem [count [a [Heq [Hcount Hcells]]]]].
  inversion Heq; subst elem count a.
  eapply indexed_extent_nonwrapping; [exact Hextent|apply primitive_size_positive|exact Hpositive|].
  intros i Hi. destruct (Hcells (Z.to_nat i)) as [chunk Hcell].
  { apply Z2Nat.inj_lt; lia. }
  rewrite Z2Nat.id in Hcell by lia.
  pose proof (Htyped _ _ _ _ Hcell) as Htypedcell.
  pose proof (scalar_type_chunk_size env (Vtype pt) _
    (typed_cell_access _ _ _ _ _ _ _ Htypedcell)) as Hsize.
  pose proof (typed_cell_permission _ _ _ _ _ _ _ Htypedcell) as [Hperm Halign].
  simpl in Hsize, Hperm. rewrite Hsize in Hperm. exact Hperm.
Qed.

Theorem primitive_array_extent_representable : forall env Sigma layout m b base pt len attr limit,
  typed_memory_layout env Sigma layout m -> source_block_extent m b limit ->
  array_reference_locations env layout b base (Atype (Vtype pt) len attr) ->
  Ptrofs.unsigned base + len * sizeof_ptype pt <= Ptrofs.max_unsigned.
Proof.
  intros * Htyped Hextent Harray.
  assert (Hlen : 0 <= len).
  { destruct Harray as [e [n [a [H [Hn _]]]]]; inversion H; subst; auto. }
  destruct (Z.eq_dec len 0) as [->|Hnonzero].
  - pose proof (Ptrofs.unsigned_range_2 base); lia.
  - pose proof (primitive_array_extent_bound _ _ _ _ _ _ _ _ _ _ Htyped Hextent Harray ltac:(lia)).
    pose proof (source_extent_bound _ _ _ Hextent); lia.
Qed.
