(* Runtime locations need offset/type evidence in addition to block membership.
   This invariant preserves arbitrary legitimate offsets; it does not identify
   every address in an allocated block as a well-formed reference. *)
Require Import List ZArith Lia AST Integers BeeTypes BeePL_values BeePL.
Import ListNotations.

Definition location_context := Values.block -> ptrofs -> type -> Prop.
Definition location_context_includes (L L' : location_context) : Prop :=
  forall b ofs t, L b ofs t -> L' b ofs t.

Fixpoint value_locations (L : location_context) (v : value) (t : type) : Prop :=
  match v with
  | Vloc b ofs => L b ofs t
  | Voption (Some payload) =>
      match t with
      | Ptrtype (Otype pt) => value_locations L payload (Ptrtype pt)
      | _ => False
      end
  | _ => True
  end.

Definition all_expr_locations (f : expr -> Prop) : list expr -> Prop :=
  fix loop es := match es with [] => True | e :: es => f e /\ loop es end.

Lemma all_expr_locations_Forall : forall f es,
  all_expr_locations f es <-> Forall f es.
Proof.
  intros f es. induction es; simpl.
  - split; intros; constructor.
  - rewrite IHes. split; intros H; [destruct H; constructor; assumption | inversion H; auto].
Qed.

Section RuntimeLocations.
Variable L : location_context.
Fixpoint runtime_locations (e : expr) : Prop :=
  match e with
  | Val v t => value_locations L v t
  | Addr l ofs t => L l.(lname) ofs t
  | App f es _ => runtime_locations f /\ all_expr_locations (runtime_locations) es
  | Prim _ es _ | Sinit _ _ es _ | Ebytes es _ | Ainit _ _ es _ =>
      all_expr_locations (runtime_locations) es
  | Bind _ _ e1 e2 _ => runtime_locations e1 /\ runtime_locations e2
  | Cond e1 e2 e3 _ | For e1 e2 _ e3 _ =>
      runtime_locations e1 /\ runtime_locations e2 /\ runtime_locations e3
  (* Captured variable-map validity is a separate invariant. This traversal
     only checks literal locations appearing in the suspended body. *)
  | CallFrame _ body _ => runtime_locations body
  | LoopFrame _ template active => runtime_locations template /\ runtime_locations active
  | Sfield e _ _ | Esome e _ => runtime_locations e
  | Match e _ es _ => runtime_locations e /\ all_expr_locations (runtime_locations) es
  | _ => True
  end.

End RuntimeLocations.

Lemma value_locations_monotone : forall L L', location_context_includes L L' ->
  forall v t, value_locations L v t -> value_locations L' v t.
Proof.
  intros L L' H. fix IH 1. intros v t.
  destruct v; simpl; auto.
  destruct o as [payload |]; simpl; auto.
  destruct t; simpl; try contradiction.
  destruct p; simpl; try contradiction. apply IH.
Qed.

Lemma runtime_locations_monotone : forall L L', location_context_includes L L' ->
  forall e, runtime_locations L e -> runtime_locations L' e.
Proof.
  intros L L' Hextends e. induction e using expr_ind_rec; intros; simpl in *;
    try solve [intuition eauto using value_locations_monotone];
    try solve [rewrite all_expr_locations_Forall, Forall_forall in *; eauto].
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto;
    rewrite all_expr_locations_Forall; apply Forall_forall; intros child Hin;
    match goal with IH : forall e, In e ?es -> _, Hall : all_expr_locations _ ?es |- _ =>
      apply IH; [exact Hin | rewrite all_expr_locations_Forall, Forall_forall in Hall; apply Hall; exact Hin]
    end.
Qed.

Lemma substs_runtime_locations : forall L x v t es,
  value_locations L v t -> all_expr_locations (runtime_locations L) es ->
  (forall e, In e es -> runtime_locations L e -> runtime_locations L (subst x (Val v t) e)) ->
  all_expr_locations (runtime_locations L) (substs subst x (Val v t) es).
Proof.
  intros L x v t es Hv. induction es as [|e es IH]; intros Hall Hstep; simpl; constructor.
  - apply Hstep; [left; reflexivity | destruct Hall; assumption].
  - apply IH; [destruct Hall; assumption |]. intros e' Hin. apply Hstep. right; exact Hin.
Qed.

Lemma match_substs_runtime_locations : forall L x v t es ps,
  value_locations L v t -> all_expr_locations (runtime_locations L) es ->
  (forall e, In e es -> runtime_locations L e -> runtime_locations L (subst x (Val v t) e)) ->
  all_expr_locations (runtime_locations L) (subst_match_branches subst x (Val v t) ps es).
Proof.
  intros L x v t es. induction es as [|e es IH]; intros ps Hv Hall Hstep; simpl; [constructor |].
  destruct ps as [|pat ps]; [exact Hall |]. simpl.
  destruct Hall as [Hhead Htail]. destruct (x_in_pattern x pat); constructor; auto.
  - apply IH; auto. intros e' Hin. apply Hstep. right; exact Hin.
  - apply Hstep; auto. left; reflexivity.
  - apply IH; auto. intros e' Hin. apply Hstep. right; exact Hin.
Qed.

Lemma value_substitution_runtime_locations : forall L x v t,
  value_locations L v t -> forall e,
  runtime_locations L e -> runtime_locations L (subst x (Val v t) e).
Proof.
  intros L x v t Hv e. induction e using expr_ind_rec; intros; cbn [subst runtime_locations] in *;
    try solve [intuition eauto using substs_runtime_locations, match_substs_runtime_locations].
  - destruct (Pos.eqb x x0); simpl; auto.
  - destruct (Pos.eqb x x0); simpl; intuition.
  - destruct (Pos.eqb x a); simpl; auto.
Qed.

Print Assumptions runtime_locations_monotone.
Print Assumptions value_substitution_runtime_locations.

Require Import Maps Memory Ctypes BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.

(* A scalar reference denotes precisely a cell at the given offset and type.
   Aggregate-object locations will require their own layout evidence, rather
   than pretending that a whole aggregate is a scalar load. *)
Definition scalar_reference_locations (layout : scalar_layout) : location_context :=
  fun b ofs t => exists pt chunk,
    t = Ptrtype pt /\ layout b ofs (get_data_type pt) chunk.

Definition memory_locations (L : location_context) (layout : scalar_layout) (m : Mem.mem) : Prop :=
  forall b ofs t chunk, layout b ofs t chunk ->
  forall v, deref_addr t m b ofs Full v -> value_locations L v t.

Lemma scalar_reference_locations_extend : forall layout b ofs t chunk,
  location_context_includes (scalar_reference_locations layout)
    (scalar_reference_locations (extend_scalar_layout layout b ofs t chunk)).
Proof.
  intros layout b ofs t chunk old off ty [pt [ch [Heq Hcell]]].
  exists pt, ch. split; [exact Heq | left; exact Hcell].
Qed.

Lemma primitive_value_locations : forall L v pt,
  typeof_value v (Vtype pt) -> value_locations L v (Vtype pt).
Proof. intros L v pt H; destruct pt, v; simpl in *; tauto. Qed.

Lemma scalar_reference_cell : forall layout b ofs pt,
  value_locations (scalar_reference_locations layout) (Vloc b ofs) (Ptrtype pt) ->
  exists chunk, layout b ofs (get_data_type pt) chunk.
Proof.
  intros layout b ofs pt [pt' [chunk [Heq Hcell]]].
  inversion Heq; subst pt'. exists chunk; exact Hcell.
Qed.

Lemma located_deref_progress : forall cenv Gamma Sigma layout bge p vm m b ofs pt,
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  runtime_locations (scalar_reference_locations layout) (Val (Vloc b ofs) (Ptrtype pt)) ->
  exists v,
    ssem_expr bge p vm m
      (Prim Deref (Val (Vloc b ofs) (Ptrtype pt) :: nil) (get_data_type pt))
      m vm (Val v (get_data_type pt)) /\
    type_expr cenv Gamma Sigma (Val v (get_data_type pt)) nil (get_data_type pt) /\
    runtime_locations (scalar_reference_locations layout) (Val v (get_data_type pt)).
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pt Hmemory Hlocations Href.
  destruct (scalar_reference_cell layout b ofs pt Href) as [chunk Hcell].
  destruct (typed_memory_cell_read cenv Gamma Sigma m b ofs (get_data_type pt) chunk
    (Hmemory b ofs _ chunk Hcell)) as [v [Hread Htyped]].
  exists v. split; [apply ssem_deref2; exact Hread |]. split; [exact Htyped |].
  simpl. eapply Hlocations; eauto.
Qed.

Lemma located_deref_preservation : forall cenv Gamma Sigma layout bge p vm m b ofs pt m' vm' e',
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  runtime_locations (scalar_reference_locations layout) (Val (Vloc b ofs) (Ptrtype pt)) ->
  ssem_expr bge p vm m
    (Prim Deref (Val (Vloc b ofs) (Ptrtype pt) :: nil) (get_data_type pt)) m' vm' e' ->
  m' = m /\ vm' = vm /\
    type_expr cenv Gamma Sigma e' nil (get_data_type pt) /\
    runtime_locations (scalar_reference_locations layout) e'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pt m' vm' e'
    Hmemory Hlocations Href Hstep.
  destruct (scalar_reference_cell layout b ofs pt Href) as [chunk Hcell].
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - split; [reflexivity |]. split; [reflexivity |]. split.
    + eapply typed_memory_cell_read_preservation; eauto.
    + simpl. eapply Hlocations; eauto.
  - exfalso. eapply aggregate_readable_not_by_value;
      [exact (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) | eassumption].
Qed.

Lemma located_bind_value_preservation : forall L bge p vm m x tx v body rt m' vm' e',
  runtime_locations L (Bind x tx (Val v tx) body rt) ->
  ssem_expr bge p vm m (Bind x tx (Val v tx) body rt) m' vm' e' ->
  runtime_locations L e'.
Proof.
  intros L bge p vm m x tx v body rt m' vm' e' [Hv Hbody] Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - match goal with H : SubstE _ _ _ _ |- _ =>
      apply substitution_relation_iff in H; subst
    end.
    eapply value_substitution_runtime_locations; eauto.
Qed.

Print Assumptions located_deref_progress.
Print Assumptions located_deref_preservation.
Print Assumptions located_bind_value_preservation.

Lemma primitive_layout_memory_locations : forall cenv Sigma layout m L,
  typed_memory_layout cenv Sigma layout m ->
  (forall b ofs t chunk, layout b ofs t chunk -> exists pt, t = Vtype pt) ->
  memory_locations L layout m.
Proof.
  intros cenv Sigma layout m L Hmemory Hprimitive b ofs t chunk Hcell v Hread.
  destruct (Hprimitive b ofs t chunk Hcell) as [pt Heq]. subst t.
  apply primitive_value_locations.
  eapply declarative_value_shape with (cenv := cenv) (Gamma := empty_context) (Sigma := Sigma).
  eapply typed_memory_cell_read_preservation; eauto.
Qed.

Lemma scalar_reference_at_cell : forall layout b ofs pt chunk,
  layout b ofs (get_data_type pt) chunk ->
  runtime_locations (scalar_reference_locations layout) (Val (Vloc b ofs) (Ptrtype pt)).
Proof. intros; exists pt, chunk; auto. Qed.

Lemma located_int32_rejects_unaligned : forall cenv Sigma layout m b,
  typed_memory_layout cenv Sigma layout m ->
  ~ runtime_locations (scalar_reference_locations layout)
    (Val (Vloc b (Ptrofs.repr 1))
      (Ptrtype (Reftype (Bprim (BeeTypes.Tint I32 Signed noattr)) noattr))).
Proof.
  intros cenv Sigma layout m b Hmemory Href.
  destruct (scalar_reference_cell _ _ _ _ Href) as [chunk Hcell].
  destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hvolatile [_ Halign] Hcontents].
  simpl in Hmode. injection Hmode as Hchunk.
  rewrite <- Hchunk in Halign.
  change (4 | 1)%Z in Halign. destruct Halign as [k Hk]. lia.
Qed.

Print Assumptions primitive_layout_memory_locations.
Print Assumptions located_int32_rejects_unaligned.

(* A read of an existing cell is unchanged by allocation and initialization of
   a fresh block. This preserves the actual pointer payload, not only its type. *)
Lemma full_read_alloc_store_frame : forall m allocated m' fresh lo hi cc co cv b ofs t v,
  Mem.alloc m lo hi = (allocated, fresh) ->
  Mem.store cc allocated fresh co cv = Some m' ->
  deref_addr t m b ofs Full v -> deref_addr t m' b ofs Full v.
Proof.
  intros m allocated m' fresh lo hi cc co cv b ofs t v Halloc Hstore Hread.
  inversion Hread; subst.
  - match goal with Hload : Mem.loadv _ _ _ = Some _ |- _ =>
    simpl in Hload;
    assert (Hvalid : Mem.valid_block m b) by
      (apply Mem.load_valid_access in Hload;
       eapply Mem.valid_access_valid_block;
       eapply Mem.valid_access_implies; [exact Hload | constructor])
  end.
  assert (Hneq : b <> fresh).
  { intro Heq. subst b. eapply Mem.fresh_block_alloc; eauto. }
  eapply deref_addr_value; eauto. simpl.
  rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [|left; exact Hneq].
  eapply Mem.load_alloc_other; eauto.
  - eapply deref_addr_bytes; [reflexivity| |eassumption|eassumption|].
    + eapply Mem.store_valid_block_1; [exact Hstore|]. eapply Mem.valid_block_alloc; eauto.
    + intros position Hinside. eapply Mem.perm_store_1; [exact Hstore|].
      eapply Mem.perm_alloc_1; [exact Halloc|]. eauto.
Qed.

Lemma memory_locations_primitive_allocation :
  forall cenv Sigma Sigma' layout m allocated m' fresh pt lo hi cc co cv,
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  Mem.store cc allocated fresh co cv = Some m' ->
  typed_memory_layout cenv Sigma'
    (extend_scalar_layout layout fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m' ->
  memory_locations
    (scalar_reference_locations
      (extend_scalar_layout layout fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)))
    (extend_scalar_layout layout fresh Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m'.
Proof.
  intros cenv Sigma Sigma' layout m allocated m' fresh pt lo hi cc co cv
    Hmemory Hlocations Halloc Hstore Hmemory' b ofs t chunk Hentry v Hread.
  destruct Hentry as [Hold | [Hb [Hofs [Ht Hchunk]]]].
  - destruct (typed_memory_cell_read cenv empty_context Sigma m b ofs t chunk
      (Hmemory b ofs t chunk Hold)) as [old [Hreadold Htyped]].
    assert (Hsame : v = old).
    { eapply deref_full_deterministic; [exact Hread |].
      eapply full_read_alloc_store_frame; eauto. }
    subst v. eapply value_locations_monotone.
    + apply scalar_reference_locations_extend.
    + eapply Hlocations; eauto.
  - subst b ofs t chunk. apply primitive_value_locations.
    eapply declarative_value_shape with (cenv := cenv) (Gamma := empty_context) (Sigma := Sigma').
    eapply typed_memory_cell_read_preservation; [apply Hmemory'; right; repeat split; reflexivity | exact Hread].
Qed.

Print Assumptions full_read_alloc_store_frame.
Print Assumptions memory_locations_primitive_allocation.

Lemma full_read_store_disjoint : forall m m' cb co cc cv b ofs t chunk v,
  Mem.store cc m cb co cv = Some m' ->
  access_mode_type t = By_value (transl_bchunk_cchunk chunk) ->
  (b <> cb \/ (co + size_chunk cc <= Ptrofs.unsigned ofs)%Z \/
    (Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= co)%Z) ->
  deref_addr t m b ofs Full v -> deref_addr t m' b ofs Full v.
Proof.
  intros m m' cb co cc cv b ofs t chunk v Hstore Hmode Hdisjoint Hread.
  inversion Hread; subst; try discriminate Hmode.
  assert (Hchunk : transl_bchunk_cchunk chunk0 = transl_bchunk_cchunk chunk) by congruence.
  eapply deref_addr_value; eauto. simpl.
  rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [assumption |].
  rewrite Hchunk. tauto.
Qed.

Lemma memory_locations_store : forall cenv Sigma L layout m m' b ofs t chunk cv stored,
  typed_memory_layout cenv Sigma layout m -> memory_locations L layout m ->
  layout b ofs t chunk -> layout_write_compatible layout b ofs t chunk ->
  Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = Errors.OK stored ->
  value_locations L stored t -> memory_locations L layout m'.
Proof.
  intros cenv Sigma L layout m m' b ofs t chunk cv stored
    Hmemory Hlocations Hentry Hcompatible Hstore Hdecode Hstored old off ty ch Hold v Hread.
  destruct (Hcompatible old off ty ch Hold) as [[Hb [Hofs [Ht Hch]]] | Hdisjoint].
  - subst old off ty ch.
    destruct (Hmemory b ofs t chunk Hentry) as [Hmode Hvolatile Hpermission Hcontents].
    assert (Hexpect : deref_addr t m' b ofs Full stored).
    { eapply deref_addr_value; [exact Hmode | exact Hvolatile | |exact Hdecode].
      simpl. eapply Mem.load_store_same; eauto. }
    assert (v = stored) by (eapply deref_full_deterministic; eauto).
    subst v. exact Hstored.
  - destruct (typed_memory_cell_read cenv empty_context Sigma m old off ty ch
      (Hmemory old off ty ch Hold)) as [before [Hbefore Htyped]].
    assert (Hsame : v = before).
    { eapply deref_full_deterministic; [exact Hread |].
      eapply full_read_store_disjoint; eauto.
      exact (typed_cell_access _ _ _ _ _ _ _ (Hmemory old off ty ch Hold)). }
    subst v. eapply Hlocations; eauto.
Qed.

Lemma located_layout_store : forall cenv Sigma layout m b ofs t chunk cv stored,
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  layout b ofs t chunk -> layout_write_compatible layout b ofs t chunk ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = Errors.OK stored ->
  type_expr cenv empty_context Sigma (Val stored t) nil t ->
  value_locations (scalar_reference_locations layout) stored t ->
  exists m',
    Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' /\
    typed_memory_layout cenv Sigma layout m' /\
    memory_locations (scalar_reference_locations layout) layout m'.
Proof.
  intros cenv Sigma layout m b ofs t chunk cv stored
    Hmemory Hlocations Hentry Hcompatible Hdecode Htyped Hstored.
  destruct (typed_memory_layout_store cenv Sigma layout m b ofs t chunk cv stored
    Hmemory Hentry Hcompatible Hdecode Htyped) as [m' [Hstore Hmemory']].
  exists m'. split; [exact Hstore |]. split; [exact Hmemory' |].
  eapply memory_locations_store with (m := m); eauto.
Qed.

Print Assumptions full_read_store_disjoint.
Print Assumptions memory_locations_store.
Print Assumptions located_layout_store.

Lemma located_primitive_reference_preservation :
  forall cenv Gamma Sigma layout bge p vm m pt pa v m' vm' e',
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  store_blocks_valid Sigma m ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  ssem_expr bge p vm m
    (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa))) m' vm' e' ->
  exists b Sigma',
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' nil (Ptrtype (Reftype (Bprim pt) pa)) /\
    typed_memory_layout cenv Sigma'
      (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m' /\
    memory_locations
      (scalar_reference_locations (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)))
      (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m' /\
    runtime_locations
      (scalar_reference_locations (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt))) e'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m pt pa v m' vm' e'
    Hmemory Hlocations Hvalid Htyped Hvolatile Hstep.
  destruct (typed_layout_allocate_primitive cenv Sigma layout m pt pa v
    Hmemory Hvalid (declarative_value_shape _ _ _ _ _ Htyped) Hvolatile)
    as [allocated [expected [b [Halloc [Hstore [Hfresh [Hextends Hmemory']]]]]]].
  assert (Hexpected : ssem_expr bge p vm m
    (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa)))
    expected vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa)))).
  { eapply ssem_ref2 with (ml := (allocated, b)) (chunk := chunk_of_ptype pt)
      (bt := Bprim pt) (a := pa) (v := v) (l := b) (Sigma := Sigma)
      (Sigma' := PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma).
    - exact Halloc.
    - reflexivity.
    - simpl. rewrite Ptrofs.unsigned_zero. exact Hstore.
    - reflexivity. }
  destruct (primitive_reference_step_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep Hexpected)
    as [Hm [Hvm He]]. subst m' vm' e'.
  exists b, (PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma).
  split; [reflexivity |]. split; [exact Hextends |]. split.
  - eapply store_blocks_valid_allocate; eauto.
  - split; [apply ty_valloc; apply PTree.gss |]. split; [exact Hmemory' |]. split.
    + eapply memory_locations_primitive_allocation with (m := m); eauto.
    + eapply scalar_reference_at_cell. right; repeat split; reflexivity.
Qed.

Print Assumptions located_primitive_reference_preservation.

Lemma located_assignment_preservation :
  forall cenv Gamma Sigma layout bge p vm m b ofs pt chunk cv v stored m' vm' e',
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  store_blocks_valid Sigma m ->
  layout b ofs (get_data_type pt) chunk ->
  layout_write_compatible layout b ofs (get_data_type pt) chunk ->
  trans_cvalue_bvalue cv = Errors.OK v ->
  decode_memory_value (get_data_type pt)
    (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = Errors.OK stored ->
  type_expr cenv empty_context Sigma (Val stored (get_data_type pt)) nil (get_data_type pt) ->
  value_locations (scalar_reference_locations layout) stored (get_data_type pt) ->
  ssem_expr bge p vm m
    (Prim Massgn
      (Val (Vloc b ofs) (Ptrtype pt) :: Val v (get_data_type pt) :: nil) Utype) m' vm' e' ->
  vm' = vm /\ store_blocks_valid Sigma m' /\
    typed_memory_layout cenv Sigma layout m' /\
    memory_locations (scalar_reference_locations layout) layout m' /\
    type_expr cenv Gamma Sigma e' nil Utype /\
    runtime_locations (scalar_reference_locations layout) e'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pt chunk cv v stored m' vm' e'
    Hmemory Hlocations Hvalid Hentry Hcompatible Hconvert Hdecode Htyped Hstored Hstep.
  destruct (located_layout_store cenv Sigma layout m b ofs (get_data_type pt) chunk cv stored
    Hmemory Hlocations Hentry Hcompatible Hdecode Htyped Hstored)
    as [expected [Hstore [Hmemory' Hlocations']]].
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hactual : Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m').
  { eapply full_scalar_assignment_store; eauto.
    exact (typed_cell_access _ _ _ _ _ _ _ (Hmemory b ofs _ chunk Hentry)). }
  assert (m' = expected) by congruence. subst m'.
  split; [reflexivity |]. split.
  - intros old ty Hold. eapply Mem.store_valid_block_1; [exact Hstore |]. eapply Hvalid; eauto.
  - split; [exact Hmemory' |]. split; [exact Hlocations' |].
    split; [constructor | exact I].
Qed.

Print Assumptions located_assignment_preservation.

Lemma located_boolean_assignment_preservation :
  forall cenv Gamma Sigma layout bge p vm m b ofs pa chunk flag m' vm' e',
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  store_blocks_valid Sigma m ->
  layout b ofs (Vtype Tbool) chunk ->
  layout_write_compatible layout b ofs (Vtype Tbool) chunk ->
  ssem_expr bge p vm m
    (Prim Massgn
      (Val (Vloc b ofs) (Ptrtype (Reftype (Bprim Tbool) pa)) ::
       Val (Vbool flag) (Vtype Tbool) :: nil) Utype) m' vm' e' ->
  vm' = vm /\ store_blocks_valid Sigma m' /\
    typed_memory_layout cenv Sigma layout m' /\
    memory_locations (scalar_reference_locations layout) layout m' /\
    type_expr cenv Gamma Sigma e' nil Utype /\
    runtime_locations (scalar_reference_locations layout) e'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pa chunk flag m' vm' e'
    Hmemory Hlocations Hvalid Hentry Hcompatible Hstep.
  pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory b ofs _ chunk Hentry)) as Hmode.
  assert (Hchunk : transl_bchunk_cchunk chunk = Mbool) by (simpl in Hmode; congruence).
  assert (Hdecode : decode_memory_value (Vtype Tbool)
    (Values.Val.load_result (transl_bchunk_cchunk chunk) (Values.Val.of_bool flag)) = Errors.OK (Vbool flag)).
  { rewrite Hchunk. destruct flag; reflexivity. }
  assert (Htyped : type_expr cenv empty_context Sigma (Val (Vbool flag) (Vtype Tbool)) nil (Vtype Tbool))
    by constructor.
  destruct (located_layout_store cenv Sigma layout m b ofs (Vtype Tbool) chunk
    (Values.Val.of_bool flag) (Vbool flag) Hmemory Hlocations Hentry Hcompatible Hdecode Htyped I)
    as [expected [Hstore [Hmemory' Hlocations']]].
  rewrite Hchunk in Hstore.
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hactual : Mem.store Mbool m b (Ptrofs.unsigned ofs) (Values.Val.of_bool flag) = Some m').
  { eapply full_boolean_assignment_store; eauto. }
  assert (m' = expected) by congruence. subst m'.
  split; [reflexivity |]. split.
  - intros old ty Hold. eapply Mem.store_valid_block_1; [exact Hstore |]. eapply Hvalid; eauto.
  - split; [exact Hmemory' |]. split; [exact Hlocations' |].
    split; [constructor | exact I].
Qed.

Print Assumptions located_boolean_assignment_preservation.

Lemma instantiate_field_values_runtime_locations : forall fields values L body body',
  List.Forall2 (fun field v => value_locations L v (snd field)) fields values ->
  runtime_locations L body ->
  instantiate_field_values fields values body = Errors.OK body' ->
  runtime_locations L body'.
Proof.
  induction fields as [|[name ty] fields IH]; intros values L body body' Hvalues Hbody Hinstantiate.
  - inversion Hvalues; subst. inversion Hinstantiate; subst. exact Hbody.
  - inversion Hvalues; subst. cbn [instantiate_field_values] in Hinstantiate.
    match goal with Htail : List.Forall2 _ fields ?tail |- _ =>
      destruct (instantiate_field_values fields tail body) as [nextBody | error] eqn:Htail_result;
      try discriminate;
      inversion Hinstantiate; subst;
      eapply value_substitution_runtime_locations; [eassumption |];
      eapply IH; eauto
    end.
Qed.

Lemma instantiate_bytes_header_runtime_locations :
  forall header schema fields headerValue fieldValues L body body',
  value_locations L headerValue schema ->
  List.Forall2 (fun field v => value_locations L v (snd field)) fields fieldValues ->
  runtime_locations L body ->
  instantiate_bytes_header header schema fields headerValue fieldValues body = Errors.OK body' ->
  runtime_locations L body'.
Proof.
  intros header schema fields headerValue fieldValues L body body' Hheader Hfields Hbody Hinstantiate.
  unfold instantiate_bytes_header in Hinstantiate.
  destruct (instantiate_field_values fields fieldValues body) as [nextBody | error] eqn:Hfields_result;
    try discriminate.
  inversion Hinstantiate; subst. apply value_substitution_runtime_locations; [exact Hheader |].
  eapply instantiate_field_values_runtime_locations; eassumption.
Qed.

Print Assumptions instantiate_field_values_runtime_locations.
Print Assumptions instantiate_bytes_header_runtime_locations.

Require Import BeePL_packet.

(* Only header locations backed by an actual preparation operation are added. *)
Definition packet_match_locations (L : location_context) (cenv : bcomposite_env)
    (before after : Mem.mem) (patterns : list pattern) : location_context :=
  fun block offset ty => L block offset ty \/
    exists sid header fields co bytes,
      In (Pbytes header (Stype sid noattr) fields) patterns /\
      PTree.get sid cenv = Some co /\
      prepare_packet_header (bcomposite_composite_env cenv) co.(BeeTypes.co_members) before bytes =
        Errors.OK (after, block) /\
      offset = Ptrofs.zero /\ ty = Stype sid noattr.

Lemma packet_match_locations_includes : forall L cenv before after patterns,
  location_context_includes L (packet_match_locations L cenv before after patterns).
Proof. intros L cenv before after patterns block offset ty H; left; exact H. Qed.

Lemma read_packet_scalar_runtime_locations : forall L m block offset pt v,
  read_packet_scalar m block offset pt = Errors.OK v -> value_locations L v (Vtype pt).
Proof.
  intros L m block offset pt v Hread. unfold read_packet_scalar in Hread.
  destruct (Mem.loadbytes m block offset (size_chunk (packet_scalar_chunk pt))) as [bytes |];
    try discriminate.
  unfold decode_packet_scalar in Hread.
  destruct pt; cbn [packet_scalar_chunk] in Hread;
    match type of Hread with context [Memdata.decode_val ?chunk bytes] =>
      destruct (Memdata.decode_val chunk bytes)
    end; simpl in Hread; try discriminate; inversion Hread; subst; exact I.
Qed.

Lemma read_packet_fields_runtime_locations : forall fields L env members m block values,
  read_packet_fields env members m block fields = Errors.OK values ->
  Forall2 (fun field v => value_locations L v (snd field)) fields values.
Proof.
  induction fields as [|[name ty] fields IH]; intros L env members m block values Hread.
  - inversion Hread; constructor.
  - destruct ty; cbn [read_packet_fields] in Hread; try discriminate.
    destruct (Ctypes.field_offset env name members) as [[offset bf] | error] eqn:Hoffset;
      try discriminate.
    destruct bf; try discriminate.
    destruct (read_packet_scalar m block offset p) as [v | error] eqn:Hscalar; try discriminate.
    destruct (read_packet_fields env members m block fields) as [rest | error] eqn:Hrest;
      try discriminate.
    inversion Hread; subst. constructor.
    + eapply read_packet_scalar_runtime_locations; exact Hscalar.
    + eapply IH; exact Hrest.
Qed.

Lemma located_match_value_preservation : forall L bge p vm m v t ps es rt m' vm' e',
  runtime_locations L (Match (Val v t) ps es rt) ->
  ssem_expr bge p vm m (Match (Val v t) ps es rt) m' vm' e' ->
  runtime_locations (packet_match_locations L bge.(genv_cenv) m m' ps) e'.
Proof.
  intros L bge p vm m v t ps es rt m' vm' e' Hlocations Hstep.
  pose proof (runtime_locations_monotone L
    (packet_match_locations L bge.(genv_cenv) m m' ps)
    (packet_match_locations_includes L bge.(genv_cenv) m m' ps)
    (Match (Val v t) ps es rt) Hlocations) as Hexpanded.
  clear Hlocations.
  inversion Hstep; subst; cbn [runtime_locations all_expr_locations value_locations] in Hexpanded;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  - destruct Hexpanded as [_ [Hfirst [Hsecond _]]].
    destruct (eq_pattern p1 Pnone); assumption.
  - destruct Hexpanded as [Hpayload [_ [Hsome _]]].
    eapply value_substitution_runtime_locations; eauto.
  - destruct Hexpanded as [Hpayload [Hsome _]].
    eapply value_substitution_runtime_locations; eauto.
  - destruct Hexpanded as [Hdescriptor [Hyes [Hno _]]].
    match goal with H : execute_packet_match _ _ _ _ _ _ _ _ _ _ = _ |- _ =>
      rename H into Hexecute end.
    unfold execute_packet_match in Hexecute.
    destruct (PTree.get sid (genv_cenv bge)) as [co |] eqn:Hco; try discriminate.
    destruct (read_packet_header m descriptor offset (BeeTypes.co_sizeof co)) as [result |] eqn:Hread;
      try discriminate.
    destruct result as [view bytes | view].
    + destruct (prepare_packet_header (bcomposite_composite_env (genv_cenv bge))
        (BeeTypes.co_members co) m bytes) as [[prepared block] | error] eqn:Hprepare; try discriminate.
      destruct (read_packet_fields (bcomposite_composite_env (genv_cenv bge))
        (bmembers_cmembers (BeeTypes.co_members co)) prepared block fields) as [values | error] eqn:Hfields;
        try discriminate.
      destruct (instantiate_bytes_header header (Stype sid noattr) fields
        (Vloc block Ptrofs.zero) values yes) as [body | error] eqn:Hinstantiate; try discriminate.
      inversion Hexecute; subst.
      eapply instantiate_bytes_header_runtime_locations; [| |exact Hyes |exact Hinstantiate].
      * right. exists sid, header, fields, co, bytes.
        split; [left; reflexivity |]. repeat split; assumption || reflexivity.
      * eapply read_packet_fields_runtime_locations; exact Hfields.
    + inversion Hexecute; subst. eapply value_substitution_runtime_locations; eauto.
Qed.

Print Assumptions located_match_value_preservation.

(* This says nothing about lookups in callee_vm: validating those requires
   the callee's typing context and its own variable-layout invariant. *)
Lemma callframe_literal_locations : forall L callee_vm body ty,
  runtime_locations L (CallFrame callee_vm body ty) <-> runtime_locations L body.
Proof. reflexivity. Qed.
