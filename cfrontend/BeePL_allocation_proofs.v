(* Local allocation threads the extended store context through the remaining
   variables. Allocation alone does not initialize their contents. *)
Require Import List ZArith AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store.
Import ListNotations.

Lemma alloc_variables_total : forall bge vars Sigma vm m,
  exists vm' m' Sigma', alloc_variables bge Sigma vm m vars vm' m' Sigma'.
Proof.
  intros bge vars. induction vars as [|[x t] vars IH]; intros Sigma vm m.
  - exists vm, m, Sigma. constructor.
  - destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) t)) as [allocated b] eqn:Halloc.
    destruct (IH (PTree.set b t Sigma) (PTree.set x (b, t) vm) allocated)
      as [vm' [m' [Sigma' Htail]]].
    exists vm', m', Sigma'. eapply alloc_variables_con; [|exact Htail].
    unfold balloc. rewrite Halloc. reflexivity.
Qed.

Lemma alloc_variables_single : forall bge Sigma vm m x t,
  exists allocated b,
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) t) = (allocated, b) /\
    alloc_variables bge Sigma vm m [(x, t)]
      (PTree.set x (b, t) vm) allocated (PTree.set b t Sigma).
Proof.
  intros bge Sigma vm m x t.
  destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) t)) as [allocated b] eqn:Halloc.
  exists allocated, b. split; [reflexivity |].
  eapply alloc_variables_con; [unfold balloc; rewrite Halloc; reflexivity | constructor].
Qed.

Lemma balloc_store_extension : forall bge Sigma m t lo hi allocated b Sigma',
  store_blocks_valid Sigma m ->
  balloc bge Sigma m t lo hi = (allocated, b, Sigma') ->
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' allocated.
Proof.
  intros bge Sigma m t lo hi allocated b Sigma' Hvalid Halloc.
  unfold balloc in Halloc.
  destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) t)) as [m1 b1] eqn:Hmem.
  inversion Halloc; subst allocated b Sigma'.
  assert (Hfresh : PTree.get b1 Sigma = None).
  { destruct (PTree.get b1 Sigma) as [ty |] eqn:Hentry; auto.
    exfalso. eapply Mem.fresh_block_alloc; [exact Hmem |]. eapply Hvalid; eauto. }
  split; [apply store_context_extends_fresh; exact Hfresh |].
  intros old ty Hentry.
  destruct (Pos.eq_dec old b1) as [Heq | Hneq].
  - subst old. eapply Mem.valid_new_block; eauto.
  - rewrite PTree.gso in Hentry by exact Hneq.
    eapply Mem.valid_block_alloc; [exact Hmem |]. eapply Hvalid; eauto.
Qed.

Lemma alloc_variables_store_extension : forall bge Sigma vm m vars vm' m' Sigma',
  alloc_variables bge Sigma vm m vars vm' m' Sigma' ->
  store_blocks_valid Sigma m ->
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m'.
Proof.
  intros bge Sigma vm m vars vm' m' Sigma' Halloc.
  induction Halloc; intros Hvalid.
  - split; [apply store_context_extends_refl | exact Hvalid].
  - destruct (balloc_store_extension _ _ _ _ _ _ _ _ _ Hvalid H) as [Hfirst Hvalid1].
    destruct (IHHalloc Hvalid1) as [Hrest Hvalid2].
    split; [eapply store_context_extends_trans; eauto | exact Hvalid2].
Qed.

Lemma alloc_variables_typed_memory_frame : forall bge Sigma vm m vars vm' m' Sigma',
  alloc_variables bge Sigma vm m vars vm' m' Sigma' ->
  forall cenv stored layout,
    typed_memory_layout cenv stored layout m -> typed_memory_layout cenv stored layout m'.
Proof.
  intros bge Sigma vm m vars vm' m' Sigma' Halloc. induction Halloc;
    intros cenv stored layout Hmemory; [exact Hmemory |].
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) ty)) as [allocated b] eqn:Hmem.
  inversion H; subst.
  intros old ofs t chunk Hentry. eapply typed_memory_cell_alloc_frame; eauto.
Qed.

Lemma alloc_variables_preserves_typing : forall bge Sigma vm m vars vm' m' Sigma',
  alloc_variables bge Sigma vm m vars vm' m' Sigma' ->
  store_blocks_valid Sigma m ->
  forall cenv Gamma e ef t, type_expr cenv Gamma Sigma e ef t ->
    type_expr cenv Gamma Sigma' e ef t.
Proof.
  intros bge Sigma vm m vars vm' m' Sigma' Halloc Hvalid cenv Gamma e ef t Htyped.
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hvalid) as [Hextends _].
  eapply (proj2 typing_store_extension); eauto.
Qed.

Print Assumptions alloc_variables_total.
Print Assumptions alloc_variables_single.
Print Assumptions alloc_variables_store_extension.
Print Assumptions alloc_variables_typed_memory_frame.
Print Assumptions alloc_variables_preserves_typing.

Lemma alloc_variables_unshadowed_lookup : forall bge Sigma vm m vars vm' m' Sigma',
  alloc_variables bge Sigma vm m vars vm' m' Sigma' ->
  forall x, ~ In x (List.map fst vars) -> PTree.get x vm' = PTree.get x vm.
Proof.
  intros bge Sigma vm m vars vm' m' Sigma' Halloc. induction Halloc; intros x Hfresh.
  - reflexivity.
  - rewrite IHHalloc.
    + apply PTree.gso. intro Heq. subst x. apply Hfresh. left; reflexivity.
    + intro Hin. apply Hfresh. right; exact Hin.
Qed.

Lemma alloc_variables_variable_layout_frame : forall bge Sigma vm m vars vm' m' Sigma',
  alloc_variables bge Sigma vm m vars vm' m' Sigma' ->
  forall Gamma layout,
  variable_layout Gamma bge vm layout ->
  (forall x t, PTree.get x Gamma = Some t -> ~ In x (List.map fst vars)) ->
  variable_layout Gamma bge vm' layout.
Proof.
  intros bge Sigma vm m vars vm' m' Sigma' Halloc Gamma layout Hvars Hfresh x t Hentry.
  destruct (Hvars x t Hentry) as [b [chunk [Hlocation Hcell]]].
  exists b, chunk. split; [|exact Hcell].
  unfold variable_location in *.
  rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Halloc x (Hfresh x t Hentry)).
  exact Hlocation.
Qed.

Print Assumptions alloc_variables_unshadowed_lookup.
Print Assumptions alloc_variables_variable_layout_frame.

Lemma alloc_variables_preparation : forall bge Sigma vm m vars cenv Gamma layout,
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  variable_layout Gamma bge vm layout ->
  (forall x t, PTree.get x Gamma = Some t -> ~ In x (List.map fst vars)) ->
  exists vm' m' Sigma',
    alloc_variables bge Sigma vm m vars vm' m' Sigma' /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    typed_memory_layout cenv Sigma' layout m' /\ variable_layout Gamma bge vm' layout.
Proof.
  intros bge Sigma vm m vars cenv Gamma layout Hvalid Hmemory Hvars Hfresh.
  destruct (alloc_variables_total bge vars Sigma vm m) as [vm' [m' [Sigma' Halloc]]].
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hvalid)
    as [Hextends Hvalid'].
  exists vm', m', Sigma'. split; [exact Halloc |]. split; [exact Hextends |].
  split; [exact Hvalid' |]. split.
  - eapply typed_memory_layout_context_extension; [|exact Hextends].
    eapply alloc_variables_typed_memory_frame; eauto.
  - eapply alloc_variables_variable_layout_frame; eauto.
Qed.

Print Assumptions alloc_variables_preparation.
