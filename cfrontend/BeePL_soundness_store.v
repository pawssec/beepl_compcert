(* Declarative typing of initialized memory contents. Unlike the shape-only
   invariant, this records store-context evidence for loaded references. *)
Require Import ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs.
Local Open Scope Z_scope.

Record typed_memory_cell (cenv : bcomposite_env) (Sigma : store_context)
    (m : Mem.mem) (b : Values.block) (ofs : ptrofs) (t : type) (chunk : bmemory_chunk) : Prop := {
  typed_cell_access : access_mode_type t = By_value (transl_bchunk_cchunk chunk);
  typed_cell_nonvolatile : type_is_volatile (transBeePL_type t) = false;
  typed_cell_permission : Mem.valid_access m (transl_bchunk_cchunk chunk) b (Ptrofs.unsigned ofs) Freeable;
  typed_cell_contents : exists cv v,
    Mem.load (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) = Some cv /\
    decode_memory_value t cv = OK v /\
    type_expr cenv empty_context Sigma (Val v t) nil t
}.

Definition typed_memory_layout cenv Sigma (layout : scalar_layout) m : Prop :=
  forall b ofs t chunk, layout b ofs t chunk -> typed_memory_cell cenv Sigma m b ofs t chunk.

Lemma declarative_value_shape : forall cenv Gamma Sigma v t,
  type_expr cenv Gamma Sigma (Val v t) nil t -> typeof_value v t.
Proof. intros cenv Gamma Sigma v t H; inversion H; subst; reflexivity. Qed.

Lemma typed_memory_cell_erasure : forall cenv Sigma m b ofs t chunk,
  typed_memory_cell cenv Sigma m b ofs t chunk -> initialized_scalar_cell m b ofs t chunk.
Proof.
  intros cenv Sigma m b ofs t chunk [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]].
  constructor; try assumption.
  exists cv, v. repeat split; auto. eapply declarative_value_shape; eauto.
Qed.

Lemma typed_memory_layout_erasure : forall cenv Sigma layout m,
  typed_memory_layout cenv Sigma layout m -> initialized_layout layout m.
Proof. intros cenv Sigma layout m H b ofs t chunk Hin; eapply typed_memory_cell_erasure; eauto. Qed.

Lemma typed_memory_cell_read : forall cenv Gamma Sigma m b ofs t chunk,
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  exists v, deref_addr t m b ofs Full v /\ type_expr cenv Gamma Sigma (Val v t) nil t.
Proof.
  intros cenv Gamma Sigma m b ofs t chunk
    [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]].
  exists v. split.
  - eapply deref_addr_value; eauto.
  - eapply value_typing_context_independent; eauto.
Qed.

Lemma typed_memory_cell_read_preservation : forall cenv Gamma Sigma m b ofs t chunk v,
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  deref_addr t m b ofs Full v -> type_expr cenv Gamma Sigma (Val v t) nil t.
Proof.
  intros cenv Gamma Sigma m b ofs t chunk v Hcell Hread.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b ofs t chunk Hcell)
    as [v' [Hread' Htyped]].
  assert (v = v') by (eapply deref_full_deterministic; eauto). subst v'. exact Htyped.
Qed.

Lemma typed_memory_cell_context_extension : forall cenv Sigma Sigma' m b ofs t chunk,
  typed_memory_cell cenv Sigma m b ofs t chunk -> store_context_extends Sigma Sigma' ->
  typed_memory_cell cenv Sigma' m b ofs t chunk.
Proof.
  intros cenv Sigma Sigma' m b ofs t chunk
    [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]] Hextends.
  constructor; try assumption. exists cv, v. repeat split; auto.
  eapply (proj2 typing_store_extension); eauto.
Qed.

Lemma typed_memory_cell_store : forall cenv Sigma m b ofs t chunk cv v,
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK v ->
  type_expr cenv empty_context Sigma (Val v t) nil t ->
  exists m', Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' /\
    typed_memory_cell cenv Sigma m' b ofs t chunk.
Proof.
  intros cenv Sigma m b ofs t chunk cv v Hcell Hdecode Htyped.
  destruct Hcell as [Hmode Hvolatile Hpermission Hcontents].
  assert (Hwrite : Mem.valid_access m (transl_bchunk_cchunk chunk) b (Ptrofs.unsigned ofs) Writable).
  { eapply Mem.valid_access_implies; [exact Hpermission | constructor]. }
  destruct (Mem.valid_access_store m (transl_bchunk_cchunk chunk) b (Ptrofs.unsigned ofs) cv Hwrite)
    as [m' Hstore].
  exists m'. split; [exact Hstore |]. constructor; try assumption.
  - eapply Mem.store_valid_access_1; eauto.
  - eexists; exists v. split; [eapply Mem.load_store_same; eauto |]. split; assumption.
Qed.

Lemma typed_memory_cell_store_disjoint : forall cenv Sigma m m' b ofs t chunk cb co cc cv,
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  Mem.store cc m cb co cv = Some m' ->
  (b <> cb \/ co + size_chunk cc <= Ptrofs.unsigned ofs \/
    Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= co) ->
  typed_memory_cell cenv Sigma m' b ofs t chunk.
Proof.
  intros cenv Sigma m m' b ofs t chunk cb co cc cv
    [Hmode Hvolatile Hpermission [loaded [v [Hload [Hdecode Htyped]]]]] Hstore Hdisjoint.
  constructor; try assumption.
  - eapply Mem.store_valid_access_1; eauto.
  - exists loaded, v. split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload | tauto].
    + split; assumption.
Qed.

Lemma typed_memory_layout_store : forall cenv Sigma layout m b ofs t chunk cv v,
  typed_memory_layout cenv Sigma layout m -> layout b ofs t chunk ->
  layout_write_compatible layout b ofs t chunk ->
  decode_memory_value t (Values.Val.load_result (transl_bchunk_cchunk chunk) cv) = OK v ->
  type_expr cenv empty_context Sigma (Val v t) nil t ->
  exists m', Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) cv = Some m' /\
    typed_memory_layout cenv Sigma layout m'.
Proof.
  intros cenv Sigma layout m b ofs t chunk cv v Hlayout Hentry Hcompatible Hdecode Htyped.
  destruct (typed_memory_cell_store cenv Sigma m b ofs t chunk cv v
    (Hlayout b ofs t chunk Hentry) Hdecode Htyped) as [m' [Hstore Hcell]].
  exists m'. split; [exact Hstore |]. intros old off ty ch Hold.
  destruct (Hcompatible old off ty ch Hold) as [[Hb [Hofs [Ht Hch]]] | Hdisjoint].
  - subst. exact Hcell.
  - eapply typed_memory_cell_store_disjoint; eauto.
Qed.

Print Assumptions typed_memory_cell_read_preservation.
Print Assumptions typed_memory_cell_context_extension.
Print Assumptions typed_memory_layout_store.

Lemma primitive_cell_declarative_typing : forall cenv Sigma m b ofs pt chunk,
  initialized_scalar_cell m b ofs (Vtype pt) chunk ->
  typed_memory_cell cenv Sigma m b ofs (Vtype pt) chunk.
Proof.
  intros cenv Sigma m b ofs pt chunk
    [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Hshape]]]]].
  constructor; try assumption. exists cv, v. repeat split; auto.
  apply primitive_value_typing. exact Hshape.
Qed.

Lemma typed_memory_cell_alloc_frame : forall cenv Sigma m allocated fresh lo hi b ofs t chunk,
  Mem.alloc m lo hi = (allocated, fresh) ->
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  typed_memory_cell cenv Sigma allocated b ofs t chunk.
Proof.
  intros cenv Sigma m allocated fresh lo hi b ofs t chunk Halloc
    [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]].
  constructor; try assumption.
  - eapply Mem.valid_access_alloc_other; eauto.
  - exists cv, v. split; [eapply Mem.load_alloc_other; eauto |]. split; assumption.
Qed.

Lemma typed_memory_cell_alloc_store_frame :
  forall cenv Sigma m allocated m' fresh lo hi cc co cv b ofs t chunk,
  Mem.alloc m lo hi = (allocated, fresh) ->
  Mem.store cc allocated fresh co cv = Some m' ->
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  typed_memory_cell cenv Sigma m' b ofs t chunk.
Proof.
  intros cenv Sigma m allocated m' fresh lo hi cc co cv b ofs t chunk Halloc Hstore Hcell.
  assert (Hvalid : Mem.valid_block m b).
  { eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure; eauto. }
  eapply typed_memory_cell_store_disjoint; [|exact Hstore|].
  - eapply typed_memory_cell_alloc_frame; eauto.
  - left. intro Heq. subst b. eapply Mem.fresh_block_alloc; eauto.
Qed.

Lemma typed_memory_layout_context_extension : forall cenv Sigma Sigma' layout m,
  typed_memory_layout cenv Sigma layout m -> store_context_extends Sigma Sigma' ->
  typed_memory_layout cenv Sigma' layout m.
Proof.
  intros cenv Sigma Sigma' layout m Hlayout Hextends b ofs t chunk Hin.
  eapply typed_memory_cell_context_extension; eauto.
Qed.

(* The allocation witness extends both store typing and the typed cell layout.
   Existing cells retain their declaratively typed contents in the new context. *)
Lemma typed_layout_allocate_primitive : forall cenv Sigma layout m pt pa v,
  typed_memory_layout cenv Sigma layout m ->
  (forall b t, PTree.get b Sigma = Some t -> Mem.valid_block m b) ->
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_ptype pt) = (allocated, b) /\
    Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) allocated b 0
      (trans_bvalue_cvalue v) = Some m' /\
    PTree.get b Sigma = None /\
    store_context_extends Sigma (PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma) /\
    typed_memory_layout cenv (PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma)
      (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m'.
Proof.
  intros cenv Sigma layout m pt pa v Hlayout Hvalid Hshape Hvolatile.
  destruct (allocate_initialized_primitive m pt v Hshape Hvolatile)
    as [allocated [m' [b [Halloc [Hstore Hcell]]]]].
  assert (Hfresh : PTree.get b Sigma = None).
  { destruct (PTree.get b Sigma) as [t |] eqn:Hentry; auto.
    exfalso. eapply Mem.fresh_block_alloc; [exact Halloc |]. eapply Hvalid; eauto. }
  assert (Hextends : store_context_extends Sigma
    (PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma)).
  { apply store_context_extends_fresh. exact Hfresh. }
  exists allocated, m', b. split; [exact Halloc |]. split; [exact Hstore |].
  split; [exact Hfresh |]. split; [exact Hextends |].
  intros old ofs t chunk [Hentry | [Hb [Hofs [Ht Hchunk]]]].
  - eapply typed_memory_cell_context_extension; [|exact Hextends].
    eapply typed_memory_cell_alloc_store_frame; eauto.
  - subst. apply primitive_cell_declarative_typing. exact Hcell.
Qed.

Lemma typed_primitive_reference_progress : forall cenv Gamma Sigma layout bge p vm m pt pa v,
  typed_memory_layout cenv Sigma layout m ->
  (forall b t, PTree.get b Sigma = Some t -> Mem.valid_block m b) ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  exists m' b Sigma',
    ssem_expr bge p vm m
      (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa))) /\
    store_context_extends Sigma Sigma' /\
    type_expr cenv Gamma Sigma'
      (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bprim pt) pa))) nil
      (Ptrtype (Reftype (Bprim pt) pa)) /\
    typed_memory_layout cenv Sigma'
      (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m pt pa v Hlayout Hvalid Htyped Hvolatile.
  pose proof (declarative_value_shape _ _ _ _ _ Htyped) as Hshape.
  destruct (typed_layout_allocate_primitive cenv Sigma layout m pt pa v
    Hlayout Hvalid Hshape Hvolatile)
    as [allocated [m' [b [Halloc [Hstore [Hfresh [Hextends Hlayout']]]]]]].
  exists m', b, (PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma).
  split.
  - eapply ssem_ref2 with (ml := (allocated, b)) (chunk := chunk_of_ptype pt)
      (bt := Bprim pt) (a := pa) (v := v) (l := b) (Sigma := Sigma)
      (Sigma' := PTree.set b (Ptrtype (Reftype (Bprim pt) pa)) Sigma).
    + exact Halloc.
    + reflexivity.
    + simpl. rewrite Ptrofs.unsigned_zero. exact Hstore.
    + reflexivity.
  - split; [exact Hextends |]. split; [apply ty_valloc; apply PTree.gss | exact Hlayout'].
Qed.

Print Assumptions typed_layout_allocate_primitive.
Print Assumptions typed_primitive_reference_progress.

Lemma primitive_reference_step_deterministic : forall bge p vm m pt pa v m1 vm1 e1 m2 vm2 e2,
  ssem_expr bge p vm m
    (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa))) m1 vm1 e1 ->
  ssem_expr bge p vm m
    (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa))) m2 vm2 e2 ->
  m1 = m2 /\ vm1 = vm2 /\ e1 = e2.
Proof.
  intros bge p vm m pt pa v m1 vm1 e1 m2 vm2 e2 H1 H2.
  inversion H1; subst; try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [simpl in *; discriminate].
  inversion H2; subst; try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [simpl in *; discriminate].
  simpl in *. repeat match goal with H : Some _ = Some _ |- _ => inversion H; clear H; subst end.
  repeat split; congruence.
Qed.

Definition store_blocks_valid (Sigma : store_context) (m : Mem.mem) : Prop :=
  forall b t, PTree.get b Sigma = Some t -> Mem.valid_block m b.

Lemma store_blocks_valid_allocate : forall Sigma m allocated m' b t lo hi chunk ofs cv,
  store_blocks_valid Sigma m -> Mem.alloc m lo hi = (allocated, b) ->
  Mem.store chunk allocated b ofs cv = Some m' ->
  store_blocks_valid (PTree.set b t Sigma) m'.
Proof.
  intros Sigma m allocated m' b t lo hi chunk ofs cv Hvalid Halloc Hstore old ty Hentry.
  eapply Mem.store_valid_block_1; [exact Hstore |].
  destruct (Pos.eq_dec old b) as [Heq | Hneq].
  - subst old. eapply Mem.valid_new_block; eauto.
  - rewrite PTree.gso in Hentry by exact Hneq.
    eapply Mem.valid_block_alloc; [exact Halloc |]. eapply Hvalid; eauto.
Qed.

(* Preservation is universal over actual successors, rather than only the
   witness produced by the allocation-progress lemma. *)
Lemma typed_primitive_reference_preservation :
  forall cenv Gamma Sigma layout bge p vm m pt pa v m' vm' e',
  typed_memory_layout cenv Sigma layout m -> store_blocks_valid Sigma m ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  ssem_expr bge p vm m
    (Prim Ref (Val v (Vtype pt) :: nil) (Ptrtype (Reftype (Bprim pt) pa))) m' vm' e' ->
  exists b Sigma',
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' nil (Ptrtype (Reftype (Bprim pt) pa)) /\
    typed_memory_layout cenv Sigma'
      (extend_scalar_layout layout b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt)) m'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m pt pa v m' vm' e'
    Hlayout Hvalid Htyped Hvolatile Hstep.
  destruct (typed_layout_allocate_primitive cenv Sigma layout m pt pa v
    Hlayout Hvalid (declarative_value_shape _ _ _ _ _ Htyped) Hvolatile)
    as [allocated [expected [b [Halloc [Hstore [Hfresh [Hextends Hlayout']]]]]]].
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
  - split; [apply ty_valloc; apply PTree.gss | exact Hlayout'].
Qed.

Print Assumptions primitive_reference_step_deterministic.
Print Assumptions typed_primitive_reference_preservation.

Lemma typed_layout_deref_progress : forall cenv Gamma Sigma layout bge p vm m b ofs pt chunk,
  typed_memory_layout cenv Sigma layout m -> layout b ofs (get_data_type pt) chunk ->
  exists v,
    ssem_expr bge p vm m
      (Prim Deref (Val (Vloc b ofs) (Ptrtype pt) :: nil) (get_data_type pt))
      m vm (Val v (get_data_type pt)) /\
    type_expr cenv Gamma Sigma (Val v (get_data_type pt)) nil (get_data_type pt).
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pt chunk Hlayout Hentry.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b ofs (get_data_type pt) chunk
    (Hlayout b ofs _ chunk Hentry)) as [v [Hread Htyped]].
  exists v. split; [apply ssem_deref2; exact Hread | exact Htyped].
Qed.

Lemma typed_layout_deref_preservation : forall cenv Gamma Sigma layout bge p vm m b ofs pt chunk m' vm' e',
  typed_memory_layout cenv Sigma layout m -> layout b ofs (get_data_type pt) chunk ->
  ssem_expr bge p vm m
    (Prim Deref (Val (Vloc b ofs) (Ptrtype pt) :: nil) (get_data_type pt)) m' vm' e' ->
  m' = m /\ vm' = vm /\ typed_memory_layout cenv Sigma layout m' /\
    type_expr cenv Gamma Sigma e' nil (get_data_type pt).
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs pt chunk m' vm' e' Hlayout Hentry Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - split; [reflexivity |]. split; [reflexivity |]. split; [exact Hlayout |].
    eapply typed_memory_cell_read_preservation; eauto.
  - exfalso. eapply aggregate_readable_not_by_value;
      [exact (typed_cell_access _ _ _ _ _ _ _ (Hlayout _ _ _ _ Hentry)) | eassumption].
Qed.

Print Assumptions typed_layout_deref_progress.
Print Assumptions typed_layout_deref_preservation.

(* Resolve each binding independently: a local binding shadows the global
   symbol, and local and global variables may coexist in one environment. *)
Definition variable_location (bge : genv) (vm : vmap) (x : ident) (t : type)
    (b : Values.block) : Prop :=
  PTree.get x vm = Some (b, t) \/
  (PTree.get x vm = None /\ Globalenvs.Genv.find_symbol bge x = Some b).

Definition variable_layout (Gamma : ty_context) (bge : genv) (vm : vmap)
    (layout : scalar_layout) : Prop :=
  forall x t, PTree.get x Gamma = Some t ->
  exists b chunk, variable_location bge vm x t b /\ layout b Ptrofs.zero t chunk.

Lemma variable_location_deterministic : forall bge vm x t b1 b2,
  variable_location bge vm x t b1 -> variable_location bge vm x t b2 -> b1 = b2.
Proof.
  intros bge vm x t b1 b2 [H1 | [H1 Hg1]] [H2 | [H2 Hg2]]; congruence.
Qed.

Lemma variable_layout_extend : forall Gamma bge vm layout b ofs t chunk,
  variable_layout Gamma bge vm layout ->
  variable_layout Gamma bge vm (extend_scalar_layout layout b ofs t chunk).
Proof.
  intros Gamma bge vm layout b ofs t chunk H x ty Hentry.
  destruct (H x ty Hentry) as [old [ch [Hlocation Hcell]]].
  exists old, ch. split; [exact Hlocation | left; exact Hcell].
Qed.

Lemma typed_variable_progress : forall cenv Gamma Sigma layout bge p vm m x t,
  variable_layout Gamma bge vm layout -> typed_memory_layout cenv Sigma layout m ->
  PTree.get x Gamma = Some t ->
  exists v, ssem_expr bge p vm m (Var x t) m vm (Val v t) /\
    type_expr cenv Gamma Sigma (Val v t) nil t.
Proof.
  intros cenv Gamma Sigma layout bge p vm m x t Hvars Hmemory Hentry.
  destruct (Hvars x t Hentry) as [b [chunk [Hlocation Hcell]]].
  destruct (typed_memory_cell_read cenv Gamma Sigma m b Ptrofs.zero t chunk
    (Hmemory b Ptrofs.zero t chunk Hcell)) as [v [Hread Htyped]].
  exists v. split; [|exact Htyped].
  destruct Hlocation as [Hlocal | [Hnotlocal Hglobal]].
  - eapply ssem_lvar; eauto.
  - eapply ssem_gbvar; eauto.
Qed.

Lemma typed_variable_preservation : forall cenv Gamma Sigma layout bge p vm m x t m' vm' e',
  variable_layout Gamma bge vm layout -> typed_memory_layout cenv Sigma layout m ->
  PTree.get x Gamma = Some t ->
  ssem_expr bge p vm m (Var x t) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil t.
Proof.
  intros cenv Gamma Sigma layout bge p vm m x t m' vm' e' Hvars Hmemory Hentry Hstep.
  destruct (Hvars x t Hentry) as [b [chunk [Hlocation Hcell]]].
  assert (Hmode := typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)).
  inversion Hstep; subst; try discriminate Hmode;
    split; [reflexivity | | reflexivity |]; split; [reflexivity | | reflexivity |].
  - assert (l = b).
    { eapply variable_location_deterministic; [left; eassumption | exact Hlocation]. }
    subst l. eapply typed_memory_cell_read_preservation; eauto.
  - assert (l = b).
    { eapply variable_location_deterministic; [right; split; eassumption | exact Hlocation]. }
    subst l. eapply typed_memory_cell_read_preservation; eauto.
Qed.

Print Assumptions typed_variable_progress.
Print Assumptions typed_variable_preservation.

(* Local rebinding is also sound when the layout contains the new binding's
   cell: the old typing entry and lookup are both overwritten together. *)
Lemma variable_layout_rebinding : forall Gamma bge vm layout x t b chunk,
  variable_layout Gamma bge vm layout -> layout b Ptrofs.zero t chunk ->
  variable_layout (PTree.set x t Gamma) bge (PTree.set x (b, t) vm) layout.
Proof.
  intros Gamma bge vm layout x t b chunk Hvars Hcell y ty Hentry.
  destruct (Pos.eq_dec y x) as [Heq | Hneq].
  - subst y. rewrite PTree.gss in Hentry. inversion Hentry; subst ty.
    exists b, chunk. split; [left; apply PTree.gss | exact Hcell].
  - rewrite PTree.gso in Hentry by exact Hneq.
    destruct (Hvars y ty Hentry) as [old [ch [Hlocation Hentry']]].
    exists old, ch. split; [|exact Hentry'].
    unfold variable_location in *. rewrite PTree.gso by exact Hneq. exact Hlocation.
Qed.

Print Assumptions variable_layout_rebinding.

(* Allocation-based operations may add cells while leaving every old block
   unchanged.  Preserve loaded-value typing as the store context grows. *)
Theorem typed_memory_layout_unchanged_old : forall cenv Sigma Sigma' layout m after,
  typed_memory_layout cenv Sigma layout m ->
  store_context_extends Sigma Sigma' ->
  Mem.unchanged_on (fun old _ => Mem.valid_block m old) m after ->
  typed_memory_layout cenv Sigma' layout after.
Proof.
  intros cenv Sigma Sigma' layout m after Hmemory Hextends Hunchanged b ofs t chunk Hcell.
  destruct (Hmemory b ofs t chunk Hcell)
    as [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]].
  assert (Hvalid : Mem.valid_block m b).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
      [exact Hpermission | constructor]. }
  constructor; [exact Hmode |exact Hvolatile | |].
  - destruct Hpermission as [Hrange Halign]. split; [|exact Halign].
    intros i Hi. eapply Mem.perm_unchanged_on; [exact Hunchanged |exact Hvalid |].
    apply Hrange; exact Hi.
  - exists cv, v. split.
    + eapply Mem.load_unchanged_on; [exact Hunchanged |intros; exact Hvalid |exact Hload].
    + split; [exact Hdecode |]. eapply (proj2 typing_store_extension); eauto.
Qed.

Print Assumptions typed_memory_layout_unchanged_old.


(* The legacy scalar-load-only variable invariant cannot describe an array
   variable. The array binding invariant supplies address/layout evidence. *)
Lemma legacy_array_variable_impossible : forall Gamma Sigma bge vm m x elem len a,
  PTree.get x Gamma = Some (Atype elem len a) ->
  ~ well_formed_var Gamma Sigma bge vm m.
Proof.
  intros Gamma Sigma bge vm m x elem len a Hentry Hvars.
  inversion Hvars as [Hlocal | Hglobal]; subst.
  - destruct (Hlocal x (Atype elem len a) Hentry)
      as [b [t [v [Hlookup [Heq [Hstore Hread]]]]]].
    inversion Hread; subst; discriminate.
  - destruct (Hglobal x (Atype elem len a) Hentry)
      as [b [v [Hmissing [Hsymbol [Hstore Hread]]]]].
    inversion Hread; subst; discriminate.
Qed.

Print Assumptions legacy_array_variable_impossible.
