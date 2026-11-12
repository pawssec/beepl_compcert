(* Memory foundation for repairing type soundness. No admitted BeePL proof
   modules are imported. This does not yet replace the legacy store invariant. *)
Require Import ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Local Open Scope Z_scope.

Record initialized_scalar_cell (m : Mem.mem) (b : Values.block) (ofs : ptrofs)
                              (t : type) (chunk : bmemory_chunk) : Prop := {
  cell_access : access_mode_type t = By_value (transl_bchunk_cchunk chunk);
  cell_nonvolatile : type_is_volatile (transBeePL_type t) = false;
  cell_permission : Mem.valid_access m (transl_bchunk_cchunk chunk)
                                    b (Ptrofs.unsigned ofs) Freeable;
  cell_contents : exists cv v,
    Mem.load (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) = Some cv /\
    decode_memory_value t cv = OK v /\ typeof_value v t
}.

Lemma initialized_scalar_read : forall m b ofs t chunk,
  initialized_scalar_cell m b ofs t chunk ->
  exists v, deref_addr t m b ofs Full v /\ typeof_value v t.
Proof.
  intros m b ofs t chunk [Hmode Hvolatile Hpermission Hcontents].
  destruct Hcontents as [cv [v [Hload [Hconvert Htype]]]].
  exists v. split; [|exact Htype].
  eapply deref_addr_value; eauto.
Qed.

Lemma primitive_value_typing : forall cenv Gamma Sigma v pt,
  typeof_value v (Vtype pt) ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma v pt Htype.
  destruct v; destruct pt; simpl in Htype; try contradiction; constructor.
Qed.

Lemma initialized_scalar_deref_progress : forall cenv Gamma Sigma bge p vm m b ofs pt a chunk,
  initialized_scalar_cell m b ofs (Vtype pt) chunk ->
  exists v,
    ssem_expr bge p vm m
      (Prim Deref ((Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a))) :: nil) (Vtype pt))
      m vm (Val v (Vtype pt)) /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma bge p vm m b ofs pt a chunk Hcell.
  destruct (initialized_scalar_read m b ofs (Vtype pt) chunk Hcell)
    as [v [Hread Htype]].
  exists v. split.
  - apply ssem_deref2. exact Hread.
  - apply primitive_value_typing. exact Htype.
Qed.

(* The conversion premise explicitly accounts for narrow-integer normalization
   by the memory chunk; it is not inferred from the permissive legacy ty_vali. *)
Lemma initialized_scalar_store : forall m b ofs t chunk cv v,
  initialized_scalar_cell m b ofs t chunk ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK v ->
  typeof_value v t ->
  exists m',
    Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' /\
    initialized_scalar_cell m' b ofs t chunk.
Proof.
  intros m b ofs t chunk cv v Hcell Hconvert Htype.
  destruct Hcell as [Hmode Hvolatile Hpermission Hcontents].
  assert (Hwritable : Mem.valid_access m (transl_bchunk_cchunk chunk)
           b (Ptrofs.unsigned ofs) Writable).
  { eapply Mem.valid_access_implies; [exact Hpermission | constructor]. }
  destruct (Mem.valid_access_store m (transl_bchunk_cchunk chunk) b
              (Ptrofs.unsigned ofs) cv Hwritable) as [m' Hstore].
  exists m'. split; [exact Hstore |].
  constructor; try assumption.
  - eapply Mem.store_valid_access_1; eauto.
  - exists (Values.Val.load_result (transl_bchunk_cchunk chunk) cv), v.
    split; [eapply Mem.load_store_same; eauto |].
    split; assumption.
Qed.

Lemma initialized_scalar_store_other_block : forall m m' b ofs t chunk cb co cc cv,
  initialized_scalar_cell m b ofs t chunk ->
  Mem.store cc m cb co cv = Some m' ->
  b <> cb ->
  initialized_scalar_cell m' b ofs t chunk.
Proof.
  intros m m' b ofs t chunk cb co cc cv [Hmode Hvolatile Hpermission Hcontents] Hstore Hneq.
  constructor; try assumption.
  - eapply Mem.store_valid_access_1; eauto.
  - destruct Hcontents as [loaded [v [Hload [Hconvert Htype]]]].
    exists loaded, v. split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); auto.
    + split; assumption.
Qed.

Print Assumptions initialized_scalar_read.
Print Assumptions primitive_value_typing.
Print Assumptions initialized_scalar_deref_progress.
Print Assumptions initialized_scalar_store.
Print Assumptions initialized_scalar_store_other_block.

(* Realizability: unlike the legacy well_formed_loc, this invariant is inhabited
   by an actual allocation and initialization, for every int32 payload. *)
Lemma allocate_initialized_int32 : forall m i,
  exists allocated m' b,
    Mem.alloc m 0 4 = (allocated, b) /\
    Mem.store Mint32 allocated b 0 (Values.Vint i) = Some m' /\
    initialized_scalar_cell m' b Ptrofs.zero
      (Vtype (Tint I32 Signed noattr)) BMint32.
Proof.
  intros m i.
  destruct (Mem.alloc m 0 4) as [allocated b] eqn:Halloc.
  assert (Hfree : Mem.valid_access allocated Mint32 b 0 Freeable).
  { eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
    exists 0. reflexivity. }
  assert (Hwrite : Mem.valid_access allocated Mint32 b 0 Writable).
  { eapply Mem.valid_access_implies; [exact Hfree | constructor]. }
  destruct (Mem.valid_access_store allocated Mint32 b 0 (Values.Vint i) Hwrite)
    as [m' Hstore].
  exists allocated, m', b. split; [reflexivity |].
  split; [exact Hstore |]. constructor; try reflexivity.
  - rewrite Ptrofs.unsigned_zero. eapply Mem.store_valid_access_1; eauto.
  - exists (Values.Vint i), (Vint i). split.
    + rewrite Ptrofs.unsigned_zero.
      exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
    + split; reflexivity.
Qed.

Lemma initialized_scalar_assignment_progress : forall bge p vm m b ofs pt a chunk cv v stored,
  initialized_scalar_cell m b ofs (Vtype pt) chunk ->
  trans_cvalue_bvalue cv = OK v ->
  decode_memory_value (Vtype pt) (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK stored ->
  typeof_value stored (Vtype pt) ->
  exists m',
    ssem_expr bge p vm m
      (Prim Massgn
        (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a)) :: Val v (Vtype pt) :: nil) Utype)
      m' vm (Val Vunit Utype) /\
    initialized_scalar_cell m' b ofs (Vtype pt) chunk.
Proof.
  intros bge p vm m b ofs pt a chunk cv v stored Hcell Hconvert Hnormalized Htype.
  destruct (initialized_scalar_store m b ofs (Vtype pt) chunk cv stored Hcell Hnormalized Htype)
    as [m' [Hstore Hcell']].
  exists m'. split; [|exact Hcell'].
  apply ssem_massgn3.
  destruct Hcell as [Hmode Hvolatile Hpermission Hcontents].
  eapply assign_addr_value; eauto.
  exact Hstore.
Qed.

Print Assumptions allocate_initialized_int32.
Print Assumptions initialized_scalar_assignment_progress.

(* Allocation must extend store typings without invalidating old locations. *)
Definition store_context_extends (before after : store_context) : Prop :=
  forall b t, PTree.get b before = Some t -> PTree.get b after = Some t.

Lemma store_context_extends_refl : forall Sigma,
  store_context_extends Sigma Sigma.
Proof. intros Sigma b t H; exact H. Qed.

Lemma store_context_extends_trans : forall S1 S2 S3,
  store_context_extends S1 S2 -> store_context_extends S2 S3 ->
  store_context_extends S1 S3.
Proof. intros S1 S2 S3 H12 H23 b t H; apply H23, H12, H. Qed.

Lemma store_context_extends_fresh : forall Sigma b t,
  PTree.get b Sigma = None ->
  store_context_extends Sigma (PTree.set b t Sigma).
Proof.
  intros Sigma b t Hfresh old ty Hentry.
  destruct (Pos.eq_dec old b) as [Heq | Hneq].
  - subst old. rewrite Hfresh in Hentry. discriminate.
  - rewrite PTree.gso; auto.
Qed.

Lemma object_type_at_store_extension : forall cenv Sigma block offset ty,
  object_type_at cenv Sigma block offset ty ->
  forall Sigma', store_context_extends Sigma Sigma' ->
  object_type_at cenv Sigma' block offset ty.
Proof.
  intros cenv Sigma block offset ty Hobject. induction Hobject; intros Sigma' Hextends.
  - eapply object_type_root; [eapply Hextends; eassumption | eassumption].
  - eapply object_type_field; eauto.
  - eapply object_type_array_element; eauto.
Qed.

Lemma typing_store_extension :
  (forall cenv Gamma Sigma es ef ts,
    type_exprs cenv Gamma Sigma es ef ts ->
    forall Sigma', store_context_extends Sigma Sigma' ->
    type_exprs cenv Gamma Sigma' es ef ts) /\
  (forall cenv Gamma Sigma e ef t,
    type_expr cenv Gamma Sigma e ef t ->
    forall Sigma', store_context_extends Sigma Sigma' ->
    type_expr cenv Gamma Sigma' e ef t).
Proof.
  apply type_exprs_type_expr_ind_mut;
    intros; econstructor; eauto using object_type_at_store_extension.
Qed.

Print Assumptions typing_store_extension.

Lemma value_has_no_small_step : forall bge p vm m v t m' vm' e',
  ~ ssem_expr bge p vm m (Val v t) m' vm' e'.
Proof. intros bge p vm m v t m' vm' e' H; inversion H. Qed.

Lemma reference_allocation_preserves_environment :
  forall bge p vm m v bt a m' vm' e',
  ssem_expr bge p vm m
    (Prim Ref (Val v (construct_type_btype bt) :: nil) (Ptrtype (Reftype bt a)))
    m' vm' e' -> vm' = vm.
Proof.
  intros bge p vm m v bt a m' vm' e' H.
  inversion H; subst; try reflexivity.
  exfalso. eapply value_has_no_small_step; eauto.
Qed.

(* A concrete allocation case of preservation with an extending store typing.
   Every block named in Sigma must already be allocated in m. *)
Lemma int32_reference_allocation : forall cenv Gamma Sigma bge p vm m i,
  (forall b t, PTree.get b Sigma = Some t -> Mem.valid_block m b) ->
  exists m' b Sigma',
    ssem_expr bge p vm m
      (Prim Ref (Val (Vint i) (Vtype (Tint I32 Signed noattr)) :: nil)
        (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)))
      m' vm (Val (Vloc b Ptrofs.zero)
        (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))) /\
    store_context_extends Sigma Sigma' /\
    type_expr cenv Gamma Sigma'
      (Val (Vloc b Ptrofs.zero)
        (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))) nil
      (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)) /\
    initialized_scalar_cell m' b Ptrofs.zero
      (Vtype (Tint I32 Signed noattr)) BMint32.
Proof.
  intros cenv Gamma Sigma bge p vm m i Hvalid.
  destruct (allocate_initialized_int32 m i)
    as [allocated [m' [b [Halloc [Hstore Hcell]]]]].
  set (rt := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)).
  assert (Hfresh : PTree.get b Sigma = None).
  { destruct (PTree.get b Sigma) as [t |] eqn:Hentry; auto.
    exfalso. eapply Mem.fresh_block_alloc; [exact Halloc |].
    eapply Hvalid; eauto. }
  exists m', b, (PTree.set b rt Sigma). split.
  - eapply ssem_ref2 with (ml := (allocated, b)) (chunk := BMint32)
      (bt := Bprim (Tint I32 Signed noattr)) (a := noattr) (v := Vint i)
      (l := b) (Sigma := Sigma) (Sigma' := PTree.set b rt Sigma).
    + exact Halloc.
    + reflexivity.
    + simpl. rewrite Ptrofs.unsigned_zero. exact Hstore.
    + reflexivity.
  - split.
    + apply store_context_extends_fresh. exact Hfresh.
    + split; [apply ty_valloc; apply PTree.gss | exact Hcell].
Qed.

Print Assumptions reference_allocation_preserves_environment.
Print Assumptions int32_reference_allocation.

Lemma initialized_scalar_alloc_frame : forall m allocated fresh lo hi b ofs t chunk,
  Mem.alloc m lo hi = (allocated, fresh) ->
  initialized_scalar_cell m b ofs t chunk ->
  initialized_scalar_cell allocated b ofs t chunk.
Proof.
  intros m allocated fresh lo hi b ofs t chunk Halloc
    [Hmode Hvolatile Hpermission Hcontents].
  constructor; try assumption.
  - eapply Mem.valid_access_alloc_other; eauto.
  - destruct Hcontents as [cv [v [Hload [Hconvert Htype]]]].
    exists cv, v. split.
    + eapply Mem.load_alloc_other; eauto.
    + split; assumption.
Qed.

Lemma initialized_scalar_alloc_store_frame :
  forall m allocated m' fresh lo hi cc co cv b ofs t chunk,
  Mem.alloc m lo hi = (allocated, fresh) ->
  Mem.store cc allocated fresh co cv = Some m' ->
  initialized_scalar_cell m b ofs t chunk ->
  initialized_scalar_cell m' b ofs t chunk.
Proof.
  intros m allocated m' fresh lo hi cc co cv b ofs t chunk Halloc Hstore Hcell.
  assert (Hvalid : Mem.valid_block m b).
  { destruct Hcell as [_ _ _ [loaded [v [Hload _]]]].
    eapply Mem.load_valid_access in Hload.
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact Hload | constructor]. }
  eapply initialized_scalar_store_other_block; [|exact Hstore|].
  - eapply initialized_scalar_alloc_frame; eauto.
  - intro Heq. subst b. eapply Mem.fresh_block_alloc; eauto.
Qed.

Print Assumptions initialized_scalar_alloc_frame.
Print Assumptions initialized_scalar_alloc_store_frame.

(* A layout enumerates the typed scalar cells of a whole store, including cells
   at nonzero offsets in aggregates. It is separate from source-level Sigma,
   which currently records neither offsets nor allocation extents. *)
Definition scalar_layout := Values.block -> ptrofs -> type -> bmemory_chunk -> Prop.

Definition initialized_layout (layout : scalar_layout) (m : Mem.mem) : Prop :=
  forall b ofs t chunk, layout b ofs t chunk ->
    initialized_scalar_cell m b ofs t chunk.

Definition extend_scalar_layout (layout : scalar_layout) b ofs t chunk : scalar_layout :=
  fun b' ofs' t' chunk' =>
    layout b' ofs' t' chunk' \/
    (b' = b /\ ofs' = ofs /\ t' = t /\ chunk' = chunk).

Lemma initialized_layout_empty : forall m,
  initialized_layout (fun _ _ _ _ => False) m.
Proof. intros m b ofs t chunk H; contradiction. Qed.

Lemma initialized_scalar_valid_block : forall m b ofs t chunk,
  initialized_scalar_cell m b ofs t chunk -> Mem.valid_block m b.
Proof.
  intros m b ofs t chunk [_ _ Hpermission _].
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [exact Hpermission | constructor].
Qed.

Lemma initialized_layout_allocation : forall layout m allocated fresh lo hi,
  initialized_layout layout m ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  initialized_layout layout allocated.
Proof.
  intros layout m allocated fresh lo hi Hlayout Halloc b ofs t chunk Hentry.
  eapply initialized_scalar_alloc_frame; eauto.
Qed.

Lemma initialized_layout_allocate_int32 : forall layout m i,
  initialized_layout layout m ->
  exists allocated m' b,
    Mem.alloc m 0 4 = (allocated, b) /\
    Mem.store Mint32 allocated b 0 (Values.Vint i) = Some m' /\
    (forall ofs t chunk, ~ layout b ofs t chunk) /\
    initialized_layout
      (extend_scalar_layout layout b Ptrofs.zero
        (Vtype (Tint I32 Signed noattr)) BMint32) m'.
Proof.
  intros layout m i Hlayout.
  destruct (allocate_initialized_int32 m i)
    as [allocated [m' [b [Halloc [Hstore Hcell]]]]].
  exists allocated, m', b. split; [exact Halloc |].
  split; [exact Hstore |]. split.
  - intros ofs t chunk Hentry.
    eapply Mem.fresh_block_alloc; [exact Halloc |].
    eapply initialized_scalar_valid_block; eauto.
  - intros old ofs t chunk [Hentry | [Hb [Hofs [Ht Hchunk]]]].
    + eapply initialized_scalar_alloc_store_frame; eauto.
    + subst. exact Hcell.
Qed.

(* Nonoverlapping cells in the same block must also survive writes. *)
Lemma initialized_scalar_store_disjoint : forall m m' b ofs t chunk cb co cc cv,
  initialized_scalar_cell m b ofs t chunk ->
  Mem.store cc m cb co cv = Some m' ->
  (b <> cb \/ co + size_chunk cc <= Ptrofs.unsigned ofs \/
    Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= co) ->
  initialized_scalar_cell m' b ofs t chunk.
Proof.
  intros m m' b ofs t chunk cb co cc cv
    [Hmode Hvolatile Hpermission Hcontents] Hstore Hdisjoint.
  constructor; try assumption.
  - eapply Mem.store_valid_access_1; eauto.
  - destruct Hcontents as [loaded [v [Hload [Hconvert Htype]]]].
    exists loaded, v. split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload | tauto].
    + split; assumption.
Qed.

Definition layout_write_compatible (layout : scalar_layout) b ofs t chunk : Prop :=
  forall old off ty ch, layout old off ty ch ->
    (old = b /\ off = ofs /\ ty = t /\ ch = chunk) \/
    old <> b \/
    Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= Ptrofs.unsigned off \/
    Ptrofs.unsigned off + size_chunk (transl_bchunk_cchunk ch) <= Ptrofs.unsigned ofs.

Lemma initialized_layout_store : forall layout m b ofs t chunk cv v,
  initialized_layout layout m ->
  layout b ofs t chunk ->
  layout_write_compatible layout b ofs t chunk ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK v ->
  typeof_value v t ->
  exists m',
    Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' /\
    initialized_layout layout m'.
Proof.
  intros layout m b ofs t chunk cv v Hlayout Hentry Hcompatible Hconvert Htype.
  destruct (initialized_scalar_store m b ofs t chunk cv v
    (Hlayout b ofs t chunk Hentry) Hconvert Htype) as [m' [Hstore Hcell]].
  exists m'. split; [exact Hstore |].
  intros old off ty ch Hold.
  destruct (Hcompatible old off ty ch Hold) as [[Hb [Hofs [Ht Hch]]] | Hdisjoint].
  - subst. exact Hcell.
  - eapply initialized_scalar_store_disjoint; eauto.
Qed.

Print Assumptions initialized_layout_allocate_int32.
Print Assumptions initialized_layout_store.

Lemma initialized_layout_assignment_progress :
  forall layout bge p vm m b ofs pt a chunk cv v stored cenv Gamma Sigma,
  initialized_layout layout m ->
  layout b ofs (Vtype pt) chunk ->
  layout_write_compatible layout b ofs (Vtype pt) chunk ->
  trans_cvalue_bvalue cv = OK v ->
  decode_memory_value (Vtype pt) (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK stored ->
  typeof_value stored (Vtype pt) ->
  exists m',
    ssem_expr bge p vm m
      (Prim Massgn
        (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a)) :: Val v (Vtype pt) :: nil) Utype)
      m' vm (Val Vunit Utype) /\
    initialized_layout layout m' /\
    type_expr cenv Gamma Sigma (Val Vunit Utype) nil Utype.
Proof.
  intros layout bge p vm m b ofs pt a chunk cv v stored cenv Gamma Sigma
    Hlayout Hentry Hcompatible Hconvert Hnormalized Htype.
  destruct (initialized_layout_store layout m b ofs (Vtype pt) chunk cv stored
    Hlayout Hentry Hcompatible Hnormalized Htype) as [m' [Hstore Hlayout']].
  exists m'. split.
  - apply ssem_massgn3.
    destruct (Hlayout b ofs (Vtype pt) chunk Hentry)
      as [Hmode Hvolatile Hpermission Hcontents].
    eapply assign_addr_value; eauto. exact Hstore.
  - split; [exact Hlayout' | constructor].
Qed.

Lemma initialized_layout_deref_progress :
  forall layout bge p vm m b ofs pt a chunk cenv Gamma Sigma,
  initialized_layout layout m ->
  layout b ofs (Vtype pt) chunk ->
  exists v,
    ssem_expr bge p vm m
      (Prim Deref (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a)) :: nil) (Vtype pt))
      m vm (Val v (Vtype pt)) /\
    initialized_layout layout m /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros layout bge p vm m b ofs pt a chunk cenv Gamma Sigma Hlayout Hentry.
  destruct (initialized_scalar_deref_progress cenv Gamma Sigma bge p vm m b ofs pt a chunk
    (Hlayout b ofs (Vtype pt) chunk Hentry)) as [v [Hstep Htyped]].
  exists v. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions initialized_layout_assignment_progress.
Print Assumptions initialized_layout_deref_progress.

Lemma deref_full_deterministic : forall t m b ofs v1 v2,
  deref_addr t m b ofs Full v1 -> deref_addr t m b ofs Full v2 -> v1 = v2.
Proof.
  intros t m b ofs v1 v2 H1 H2. inversion H1; inversion H2; subst; try discriminate; congruence.
Qed.

Lemma initialized_scalar_read_preservation : forall m b ofs pt chunk v cenv Gamma Sigma,
  initialized_scalar_cell m b ofs (Vtype pt) chunk ->
  deref_addr (Vtype pt) m b ofs Full v ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros m b ofs pt chunk v cenv Gamma Sigma Hcell Hread.
  destruct (initialized_scalar_read m b ofs (Vtype pt) chunk Hcell)
    as [v' [Hread' Htype]].
  assert (v = v') by (eapply deref_full_deterministic; eauto). subst v'.
  apply primitive_value_typing. exact Htype.
Qed.

Lemma aggregate_readable_not_by_value : forall cenv m b base ty chunk,
  access_mode_type ty = By_value chunk ->
  ~ aggregate_readable cenv m b base ty.
Proof.
  intros cenv m b base ty chunk Hmode [Hkind Hrest].
  destruct ty; simpl in Hkind; try discriminate; discriminate Hmode.
Qed.

Lemma initialized_scalar_deref_step_preservation :
  forall cenv Gamma Sigma bge p vm m b ofs pt a chunk m' vm' e',
  initialized_scalar_cell m b ofs (Vtype pt) chunk ->
  ssem_expr bge p vm m
    (Prim Deref (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a)) :: nil) (Vtype pt))
    m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma bge p vm m b ofs pt a chunk m' vm' e' Hcell Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - repeat split; auto. eapply initialized_scalar_read_preservation; eauto.
  - exfalso. eapply aggregate_readable_not_by_value;
      [exact (cell_access _ _ _ _ _ Hcell) | eassumption].
Qed.

Print Assumptions deref_full_deterministic.
Print Assumptions initialized_scalar_read_preservation.
Print Assumptions initialized_scalar_deref_step_preservation.

Lemma successful_value_conversion_injective : forall cv1 cv2 v,
  trans_cvalue_bvalue cv1 = OK v -> trans_cvalue_bvalue cv2 = OK v -> cv1 = cv2.
Proof.
  intros cv1 cv2 v H1 H2. destruct cv1; destruct cv2; simpl in *; congruence.
Qed.

Lemma by_value_type_not_aggregate : forall ty chunk,
  access_mode_type ty = By_value chunk -> is_aggregate_type ty = false.
Proof. intros ty chunk Hmode. destruct ty; simpl; try reflexivity; discriminate Hmode. Qed.

Lemma full_scalar_assignment_store : forall bge t m b ofs chunk cv v m',
  access_mode_type t = By_value (transl_bchunk_cchunk chunk) ->
  trans_cvalue_bvalue cv = OK v ->
  assign_addr bge t m b ofs Full v m' v ->
  Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m'.
Proof.
  intros bge t m b ofs chunk cv v m' Hmode Hconvert Hassign.
  inversion Hassign; subst; try congruence;
    try solve [destruct cv; discriminate];
    try solve [pose proof (by_value_type_not_aggregate _ _ Hmode); congruence].
  match goal with H : trans_cvalue_bvalue ?stored = OK v |- _ =>
    assert (Heq : stored = cv) by (eapply successful_value_conversion_injective; eauto);
    subst stored
  end.
  simpl in *. congruence.
Qed.

Lemma initialized_layout_assignment_step_preservation :
  forall layout cenv Gamma Sigma bge p vm m b ofs pt a chunk cv v stored m' vm' e',
  initialized_layout layout m ->
  layout b ofs (Vtype pt) chunk ->
  layout_write_compatible layout b ofs (Vtype pt) chunk ->
  trans_cvalue_bvalue cv = OK v ->
  decode_memory_value (Vtype pt) (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK stored ->
  typeof_value stored (Vtype pt) ->
  ssem_expr bge p vm m
    (Prim Massgn
      (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) a)) :: Val v (Vtype pt) :: nil) Utype)
    m' vm' e' ->
  vm' = vm /\ initialized_layout layout m' /\ type_expr cenv Gamma Sigma e' nil Utype.
Proof.
  intros layout cenv Gamma Sigma bge p vm m b ofs pt a chunk cv v stored m' vm' e'
    Hlayout Hentry Hcompatible Hconvert Hnormalized Htype Hstep.
  destruct (initialized_layout_store layout m b ofs (Vtype pt) chunk cv stored
    Hlayout Hentry Hcompatible Hnormalized Htype) as [expected [Hstore Hexpected]].
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hactual : Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m').
  { eapply full_scalar_assignment_store; eauto.
    exact (cell_access _ _ _ _ _ (Hlayout b ofs (Vtype pt) chunk Hentry)). }
  assert (m' = expected) by congruence. subst m'.
  split; [reflexivity |]. split; [exact Hexpected | constructor].
Qed.

Print Assumptions successful_value_conversion_injective.
Print Assumptions full_scalar_assignment_store.
Print Assumptions initialized_layout_assignment_step_preservation.

Lemma integer_cell_store_normalization : forall sz s a i chunk,
  access_mode_type (Vtype (Tint sz s a)) = By_value (transl_bchunk_cchunk chunk) ->
  exists stored,
    decode_memory_value (Vtype (Tint sz s a)) (Values.Val.load_result (transl_bchunk_cchunk chunk) (Values.Vint i)) = OK stored /\
    typeof_value stored (Vtype (Tint sz s a)).
Proof.
  intros sz s a i chunk Hmode.
  destruct sz, s, chunk; simpl in Hmode; try discriminate;
    eexists; split; reflexivity.
Qed.

Lemma long_cell_store_normalization : forall s a i chunk,
  access_mode_type (Vtype (Tlong s a)) = By_value (transl_bchunk_cchunk chunk) ->
  exists stored,
    decode_memory_value (Vtype (Tlong s a)) (Values.Val.load_result (transl_bchunk_cchunk chunk) (Values.Vlong i)) = OK stored /\
    typeof_value stored (Vtype (Tlong s a)).
Proof.
  intros s a i chunk Hmode.
  destruct s, chunk; simpl in Hmode; try discriminate;
    eexists; split; reflexivity.
Qed.

Lemma initialized_layout_integer_assignment_preservation :
  forall layout cenv Gamma Sigma bge p vm m b ofs sz s a pa chunk i m' vm' e',
  initialized_layout layout m ->
  layout b ofs (Vtype (Tint sz s a)) chunk ->
  layout_write_compatible layout b ofs (Vtype (Tint sz s a)) chunk ->
  ssem_expr bge p vm m
    (Prim Massgn
      (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim (Tint sz s a)) pa)) ::
       Val (Vint i) (Vtype (Tint sz s a)) :: nil) Utype) m' vm' e' ->
  vm' = vm /\ initialized_layout layout m' /\ type_expr cenv Gamma Sigma e' nil Utype.
Proof.
  intros layout cenv Gamma Sigma bge p vm m b ofs sz s a pa chunk i m' vm' e'
    Hlayout Hentry Hcompatible Hstep.
  destruct (integer_cell_store_normalization sz s a i chunk
    (cell_access _ _ _ _ _ (Hlayout b ofs _ chunk Hentry))) as [stored [Hnormalized Htype]].
  eapply initialized_layout_assignment_step_preservation with (cv := Values.Vint i) (stored := stored);
    eauto; reflexivity.
Qed.

Lemma initialized_layout_long_assignment_preservation :
  forall layout cenv Gamma Sigma bge p vm m b ofs s a pa chunk i m' vm' e',
  initialized_layout layout m ->
  layout b ofs (Vtype (Tlong s a)) chunk ->
  layout_write_compatible layout b ofs (Vtype (Tlong s a)) chunk ->
  ssem_expr bge p vm m
    (Prim Massgn
      (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim (Tlong s a)) pa)) ::
       Val (Vint64 i) (Vtype (Tlong s a)) :: nil) Utype) m' vm' e' ->
  vm' = vm /\ initialized_layout layout m' /\ type_expr cenv Gamma Sigma e' nil Utype.
Proof.
  intros layout cenv Gamma Sigma bge p vm m b ofs s a pa chunk i m' vm' e'
    Hlayout Hentry Hcompatible Hstep.
  destruct (long_cell_store_normalization s a i chunk
    (cell_access _ _ _ _ _ (Hlayout b ofs _ chunk Hentry))) as [stored [Hnormalized Htype]].
  eapply initialized_layout_assignment_step_preservation with (cv := Values.Vlong i) (stored := stored);
    eauto; reflexivity.
Qed.

Print Assumptions integer_cell_store_normalization.
Print Assumptions long_cell_store_normalization.
Print Assumptions initialized_layout_integer_assignment_preservation.
Print Assumptions initialized_layout_long_assignment_preservation.

Lemma allocate_initialized_boolean : forall m flag,
  exists allocated m' b,
    Mem.alloc m 0 1 = (allocated, b) /\
    Mem.store Mbool allocated b 0 (Values.Val.of_bool flag) = Some m' /\
    initialized_scalar_cell m' b Ptrofs.zero (Vtype Tbool) BMbool.
Proof.
  intros m flag. destruct (Mem.alloc m 0 1) as [allocated b] eqn:Halloc.
  assert (Hfree : Mem.valid_access allocated Mbool b 0 Freeable).
  { eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
    exists 0. reflexivity. }
  assert (Hwrite : Mem.valid_access allocated Mbool b 0 Writable).
  { eapply Mem.valid_access_implies; [exact Hfree | constructor]. }
  destruct (Mem.valid_access_store allocated Mbool b 0 (Values.Val.of_bool flag) Hwrite)
    as [m' Hstore].
  exists allocated, m', b. split; [reflexivity |]. split; [exact Hstore |].
  constructor; try reflexivity.
  - rewrite Ptrofs.unsigned_zero. eapply Mem.store_valid_access_1; eauto.
  - exists (Values.Val.load_result Mbool (Values.Val.of_bool flag)), (Vbool flag).
    split.
    + rewrite Ptrofs.unsigned_zero. eapply Mem.load_store_same; eauto.
    + split; [destruct flag; reflexivity | exact I].
Qed.

Lemma full_boolean_assignment_store : forall bge m b ofs flag m',
  assign_addr bge (Vtype Tbool) m b ofs Full (Vbool flag) m' (Vbool flag) ->
  Mem.store Mbool m b (Ptrofs.unsigned ofs) (Values.Val.of_bool flag) = Some m'.
Proof.
  intros bge m b ofs flag m' Hassign.
  inversion Hassign; subst; simpl in *; auto.
  match goal with H : trans_cvalue_bvalue ?cv = OK (Vbool _) |- _ =>
    destruct cv; discriminate
  end.
Qed.

Lemma initialized_layout_boolean_store : forall layout m b ofs chunk flag,
  initialized_layout layout m -> layout b ofs (Vtype Tbool) chunk ->
  layout_write_compatible layout b ofs (Vtype Tbool) chunk ->
  exists m', Mem.store Mbool m b (Ptrofs.unsigned ofs) (Values.Val.of_bool flag) = Some m' /\
    initialized_layout layout m'.
Proof.
  intros layout m b ofs chunk flag Hlayout Hentry Hcompatible.
  pose proof (cell_access _ _ _ _ _ (Hlayout b ofs _ chunk Hentry)) as Hmode.
  assert (Hchunk : transl_bchunk_cchunk chunk = Mbool) by (simpl in Hmode; congruence).
  assert (Hnormalize : decode_memory_value (Vtype Tbool)
    (Values.Val.load_result (transl_bchunk_cchunk chunk) (Values.Val.of_bool flag)) = OK (Vbool flag)).
  { rewrite Hchunk. destruct flag; reflexivity. }
  destruct (initialized_layout_store layout m b ofs (Vtype Tbool) chunk
    (Values.Val.of_bool flag) (Vbool flag) Hlayout Hentry Hcompatible Hnormalize I)
    as [m' [Hstore Hlayout']].
  exists m'. rewrite Hchunk in Hstore. split; assumption.
Qed.

Lemma initialized_layout_boolean_assignment_progress :
  forall layout bge p vm m b ofs chunk pa flag,
  initialized_layout layout m -> layout b ofs (Vtype Tbool) chunk ->
  layout_write_compatible layout b ofs (Vtype Tbool) chunk ->
  exists m', ssem_expr bge p vm m
    (Prim Massgn (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim Tbool) pa)) ::
      Val (Vbool flag) (Vtype Tbool) :: nil) Utype) m' vm (Val Vunit Utype) /\
    initialized_layout layout m'.
Proof.
  intros layout bge p vm m b ofs chunk pa flag Hlayout Hentry Hcompatible.
  destruct (initialized_layout_boolean_store layout m b ofs chunk flag Hlayout Hentry Hcompatible)
    as [m' [Hstore Hlayout']].
  exists m'. split; [|exact Hlayout'].
  apply ssem_massgn3. apply assign_addr_boolean; [reflexivity | exact Hstore].
Qed.

Lemma initialized_layout_boolean_assignment_preservation :
  forall layout cenv Gamma Sigma bge p vm m b ofs chunk pa flag m' vm' e',
  initialized_layout layout m -> layout b ofs (Vtype Tbool) chunk ->
  layout_write_compatible layout b ofs (Vtype Tbool) chunk ->
  ssem_expr bge p vm m
    (Prim Massgn (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim Tbool) pa)) ::
      Val (Vbool flag) (Vtype Tbool) :: nil) Utype) m' vm' e' ->
  vm' = vm /\ initialized_layout layout m' /\ type_expr cenv Gamma Sigma e' nil Utype.
Proof.
  intros layout cenv Gamma Sigma bge p vm m b ofs chunk pa flag m' vm' e'
    Hlayout Hentry Hcompatible Hstep.
  destruct (initialized_layout_boolean_store layout m b ofs chunk flag Hlayout Hentry Hcompatible)
    as [expected [Hstore Hexpected]].
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hactual : Mem.store Mbool m b (Ptrofs.unsigned ofs) (Values.Val.of_bool flag) = Some m').
  { eapply full_boolean_assignment_store; eauto. }
  assert (m' = expected) by congruence. subst m'.
  split; [reflexivity |]. split; [exact Hexpected | constructor].
Qed.

Print Assumptions allocate_initialized_boolean.
Print Assumptions initialized_layout_boolean_assignment_progress.
Print Assumptions initialized_layout_boolean_assignment_preservation.

Lemma primitive_chunk_access : forall pt,
  access_mode_type (Vtype pt) = By_value (transl_bchunk_cchunk (chunk_of_ptype pt)).
Proof. intros [|sz s a|s a]; try destruct sz; try destruct s; reflexivity. Qed.

Lemma primitive_chunk_size : forall pt,
  size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) = sizeof_ptype pt.
Proof. intros [|sz s a|s a]; try destruct sz; try destruct s; reflexivity. Qed.

Lemma primitive_store_normalization : forall pt v,
  typeof_value v (Vtype pt) ->
  exists stored,
    decode_memory_value (Vtype pt)
      (Values.Val.load_result (transl_bchunk_cchunk (chunk_of_ptype pt)) (trans_bvalue_cvalue v)) = OK stored /\
    typeof_value stored (Vtype pt).
Proof.
  intros [|sz s a|s a] v Htype; destruct v; simpl in Htype; try contradiction.
  - destruct b; eexists; split; reflexivity.
  - destruct sz, s; eexists; split; reflexivity.
  - destruct s; eexists; split; reflexivity.
Qed.

Lemma allocate_initialized_primitive : forall m pt v,
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_ptype pt) = (allocated, b) /\
    Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) allocated b 0 (trans_bvalue_cvalue v) = Some m' /\
    initialized_scalar_cell m' b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros m pt v Htype Hvolatile.
  destruct (Mem.alloc m 0 (sizeof_ptype pt)) as [allocated b] eqn:Halloc.
  assert (Hfree : Mem.valid_access allocated (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Freeable).
  { eapply Mem.valid_access_alloc_same; [exact Halloc | lia | |].
    - rewrite primitive_chunk_size. lia.
    - exists 0. lia. }
  assert (Hwrite : Mem.valid_access allocated (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Writable).
  { eapply Mem.valid_access_implies; [exact Hfree | constructor]. }
  destruct (Mem.valid_access_store allocated (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0
    (trans_bvalue_cvalue v) Hwrite) as [m' Hstore].
  destruct (primitive_store_normalization pt v Htype) as [stored [Hdecode Hstored]].
  exists allocated, m', b. split; [reflexivity |]. split; [exact Hstore |].
  constructor; [apply primitive_chunk_access | exact Hvolatile | |].
  - rewrite Ptrofs.unsigned_zero. eapply Mem.store_valid_access_1; eauto.
  - eexists; exists stored. split.
    + rewrite Ptrofs.unsigned_zero. eapply Mem.load_store_same; eauto.
    + split; eauto.
Qed.

Lemma primitive_reference_allocation_progress : forall bge p vm m pt pa v,
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  exists m' b,
    ssem_expr bge p vm m
      (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa))) /\
    initialized_scalar_cell m' b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros bge p vm m pt pa v Htype Hvolatile.
  destruct (allocate_initialized_primitive m pt v Htype Hvolatile)
    as [allocated [m' [b [Halloc [Hstore Hcell]]]]].
  exists m', b. split; [|exact Hcell].
  eapply ssem_ref2 with (ml := (allocated, b)) (chunk := chunk_of_ptype pt)
    (bt := Bprim pt) (a := pa) (v := v) (l := b)
    (Sigma := PTree.empty type)
    (Sigma' := PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) (PTree.empty type)).
  - exact Halloc.
  - reflexivity.
  - simpl. rewrite Ptrofs.unsigned_zero. exact Hstore.
  - reflexivity.
Qed.

Print Assumptions primitive_chunk_access.
Print Assumptions primitive_chunk_size.
Print Assumptions allocate_initialized_primitive.
Print Assumptions primitive_reference_allocation_progress.
