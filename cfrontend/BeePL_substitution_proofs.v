(* Substitution metatheory without admitted BeePL proof dependencies. *)
Require Import ZArith List AST Ctypes Errors BeeTypes BeePL BeePL_substitution_freevars.

Lemma substitution_relation_function : forall x se,
  (forall e e', SubstE x se e e' -> subst x se e = e') /\
  (forall es es', SubstEs x se es es' -> substs subst x se es = es') /\
  (forall ps es es', SubstMatch x se ps es es' ->
    subst_match_branches subst x se ps es = es').
Proof.
  intros x se. apply Subst_all_mutind; intros; subst;
    cbn [subst substs subst_match_branches]; try rewrite Pos.eqb_refl;
    try match goal with
    | H : ?a <> ?b |- context [(?a =? ?b)%positive] =>
      assert (Heq : (a =? b)%positive = false) by (apply Pos.eqb_neq; exact H);
      rewrite Heq
    end;
    repeat match goal with
    | H : ?lhs = ?rhs |- context [?lhs] => progress rewrite H
    end; try reflexivity.
  destruct es; reflexivity.
Qed.

Lemma match_pattern_shadowing : forall x se scrutinee branch t,
  subst x se (Match scrutinee (Psome x :: nil) (branch :: nil) t) =
  Match (subst x se scrutinee) (Psome x :: nil) (branch :: nil) t.
Proof.
  intros. cbn [subst subst_match_branches x_in_pattern vars_bound_by x_in_xs].
  rewrite Pos.eqb_refl. reflexivity.
Qed.

Print Assumptions substitution_relation_function.
Print Assumptions match_pattern_shadowing.

Lemma substitution_list_from_members : forall x se es,
  (forall e, In e es -> SubstE x se e (subst x se e)) ->
  SubstEs x se es (substs subst x se es).
Proof.
  intros x se es. induction es as [|e es IH]; intros Hall; simpl.
  - constructor.
  - constructor.
    + apply Hall. left; reflexivity.
    + apply IH. intros e' Hin. apply Hall. right; exact Hin.
Qed.

Lemma substitution_branches_from_members : forall x se es ps,
  (forall e, In e es -> SubstE x se e (subst x se e)) ->
  SubstMatch x se ps es (subst_match_branches subst x se ps es).
Proof.
  intros x se es. induction es as [|e es IH]; intros ps Hall.
  - constructor.
  - destruct ps as [|p ps]; simpl.
    + constructor.
    + destruct (x_in_pattern x p) eqn:Hbound.
      * apply SM_bound; [exact Hbound |].
        apply IH. intros e' Hin. apply Hall. right; exact Hin.
      * apply SM_free; [exact Hbound | |].
        -- apply Hall. left; reflexivity.
        -- apply IH. intros e' Hin. apply Hall. right; exact Hin.
Qed.

Lemma substitution_function_relation : forall x se e,
  SubstE x se e (subst x se e).
Proof.
  intros x se. apply expr_ind_rec; intros; cbn [subst];
    try solve [constructor; auto using substitution_list_from_members,
      substitution_branches_from_members].
  all: match goal with
  | |- context [(?a =? ?b)%positive] =>
    destruct (Pos.eqb a b) eqn:Heq;
    [apply Pos.eqb_eq in Heq | apply Pos.eqb_neq in Heq];
    subst; constructor; auto using substitution_list_from_members
  end.
Qed.

Lemma substitution_relation_iff : forall x se e e',
  SubstE x se e e' <-> subst x se e = e'.
Proof.
  intros. split.
  - apply (proj1 (substitution_relation_function x se)).
  - intro H. subst e'. apply substitution_function_relation.
Qed.

Lemma substitution_relation_deterministic : forall x se e e1 e2,
  SubstE x se e e1 -> SubstE x se e e2 -> e1 = e2.
Proof.
  intros x se e e1 e2 H1 H2.
  apply substitution_relation_iff in H1.
  apply substitution_relation_iff in H2. congruence.
Qed.

Print Assumptions substitution_function_relation.
Print Assumptions substitution_relation_iff.
Print Assumptions substitution_relation_deterministic.

Require Import Maps BeePL_typesystem BeePL_sem BeePL_values.

Definition typing_context_includes (Gamma Gamma' : ty_context) : Prop :=
  forall x t, PTree.get x Gamma = Some t -> PTree.get x Gamma' = Some t.

Lemma typing_context_includes_update : forall Gamma Gamma' x t,
  typing_context_includes Gamma Gamma' ->
  typing_context_includes (extend_context Gamma x t) (extend_context Gamma' x t).
Proof.
  intros Gamma Gamma' x t H y ty Hy.
  unfold extend_context in *.
  destruct (Pos.eq_dec y x) as [Heq | Hneq].
  - subst y. rewrite PTree.gss in *. exact Hy.
  - rewrite PTree.gso in *; auto.
Qed.

Lemma typing_context_includes_updates : forall xs ts Gamma Gamma',
  typing_context_includes Gamma Gamma' ->
  typing_context_includes (extends_context Gamma xs ts) (extends_context Gamma' xs ts).
Proof.
  induction xs as [|x xs IH]; intros ts Gamma Gamma' H; destruct ts; simpl; auto.
  apply IH. apply typing_context_includes_update. exact H.
Qed.

Lemma typing_context_includes_pattern : forall Gamma Gamma' pat te,
  typing_context_includes Gamma Gamma' ->
  typing_context_includes (pattern_context Gamma pat te) (pattern_context Gamma' pat te).
Proof.
  intros Gamma Gamma' pat te H. destruct pat; simpl; auto.
  - destruct te; simpl; auto. destruct p; simpl; auto using typing_context_includes_update.
  - apply typing_context_includes_updates, typing_context_includes_update, H.
Qed.

Lemma typing_context_weakening :
  (forall cenv Gamma Sigma es ef ts,
    type_exprs cenv Gamma Sigma es ef ts ->
    forall Gamma', typing_context_includes Gamma Gamma' ->
    type_exprs cenv Gamma' Sigma es ef ts) /\
  (forall cenv Gamma Sigma e ef t,
    type_expr cenv Gamma Sigma e ef t ->
    forall Gamma', typing_context_includes Gamma Gamma' ->
    type_expr cenv Gamma' Sigma e ef t).
Proof.
  apply type_exprs_type_expr_ind_mut;
    intros; econstructor; eauto using typing_context_includes_update,
      typing_context_includes_updates, typing_context_includes_pattern.
Qed.

Lemma value_typing_context_independent : forall cenv Gamma Gamma' Sigma v annotation ef t,
  type_expr cenv Gamma Sigma (Val v annotation) ef t ->
  type_expr cenv Gamma' Sigma (Val v annotation) ef t.
Proof.
  intros cenv Gamma Gamma' Sigma v annotation ef t H.
  remember (Val v annotation) as e eqn:Heq in H.
  revert v annotation Heq Gamma'.
  induction H; intros; inversion Heq; subst; constructor; eauto.
Qed.

Print Assumptions typing_context_weakening.
Print Assumptions value_typing_context_independent.

Lemma match_some_returns_payload : forall bge p m vm pt v x enone,
  ssem_expr bge p vm m
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil)
      (enone :: Var x (Ptrtype pt) :: nil) (Ptrtype pt))
    m vm (Val v (Ptrtype pt)).
Proof.
  intros.
  pose proof (ssem_match_some bge p m vm pt v x enone
    (Var x (Ptrtype pt)) (Ptrtype pt)) as H.
  cbn [subst] in H. rewrite Pos.eqb_refl in H. exact H.
Qed.

Lemma match_some_first_returns_payload : forall bge p m vm pt v x enone,
  ssem_expr bge p vm m
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt)))
      (Psome x :: Pnone :: nil)
      (Var x (Ptrtype pt) :: enone :: nil) (Ptrtype pt))
    m vm (Val v (Ptrtype pt)).
Proof.
  intros.
  pose proof (ssem_match_some_first bge p m vm pt v x
    (Var x (Ptrtype pt)) enone (Ptrtype pt)) as H.
  cbn [subst] in H. rewrite Pos.eqb_refl in H. exact H.
Qed.

Lemma match_scrutinee_step_propagates_store :
  forall bge p vm m e m' vm' e' p1 p2 e1 e2 t,
  ssem_expr bge p vm m e m' vm' e' ->
  ssem_expr bge p vm m (Match e (p1 :: p2 :: nil) (e1 :: e2 :: nil) t)
    m' vm' (Match e' (p1 :: p2 :: nil) (e1 :: e2 :: nil) t).
Proof. intros; apply ssem_match_none1; assumption. Qed.

Print Assumptions match_some_returns_payload.
Print Assumptions match_some_first_returns_payload.
Print Assumptions match_scrutinee_step_propagates_store.

Lemma typed_none_branch : forall cenv Gamma Sigma pt x enone esome ef rt,
  type_expr cenv Gamma Sigma
    (Match (Val (Voption None) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) ef rt ->
  exists branch_effect, type_expr cenv Gamma Sigma enone branch_effect rt /\
    sub_effect branch_effect ef = true.
Proof.
  intros cenv Gamma Sigma pt x enone esome ef rt H.
  destruct (type_infer_match cenv Gamma Sigma rt
    (Val (Voption None) (Ptrtype (Otype pt))) ef
    (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt H)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  inversion Hscrut; subst. simpl.
  exists (effects O). split.
  - exact (Hbranches O Pnone enone eq_refl eq_refl).
  - apply Heffects. simpl; auto.
Qed.

Lemma typed_some_branch_context : forall cenv Gamma Sigma pt v x enone esome ef rt,
  type_expr cenv Gamma Sigma
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) ef rt ->
  exists branch_effect,
    type_expr cenv (extend_context Gamma x (Ptrtype pt)) Sigma esome branch_effect rt /\
    sub_effect branch_effect ef = true.
Proof.
  intros cenv Gamma Sigma pt v x enone esome ef rt H.
  destruct (type_infer_match cenv Gamma Sigma rt
    (Val (Voption (Some v)) (Ptrtype (Otype pt))) ef
    (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt H)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  inversion Hscrut; subst. simpl.
  exists (effects (S O)). split.
  - exact (Hbranches (S O) (Psome x) esome eq_refl eq_refl).
  - apply Heffects. simpl; auto.
Qed.

Lemma none_branch_cannot_use_some_binder : forall cenv Sigma pt x esome ef rt,
  ~ type_expr cenv (PTree.empty type) Sigma
    (Match (Val (Voption None) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (Var x rt :: esome :: nil) rt) ef rt.
Proof.
  intros cenv Sigma pt x esome ef rt H.
  apply typed_none_branch in H. destruct H as [branch_effect [H _]]. inversion H; subst.
  match goal with Hlookup : PTree.get _ (PTree.empty _) = Some _ |- _ =>
    rewrite PTree.gempty in Hlookup; discriminate
  end.
Qed.

Print Assumptions typed_none_branch.
Print Assumptions typed_some_branch_context.
Print Assumptions none_branch_cannot_use_some_binder.

Lemma none_match_step_preservation :
  forall cenv Gamma Sigma bge p vm m pt x enone esome ef rt m' vm' e',
  type_expr cenv Gamma Sigma
    (Match (Val (Voption None) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) ef rt ->
  ssem_expr bge p vm m
    (Match (Val (Voption None) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) m' vm' e' ->
  m' = m /\ vm' = vm /\
    exists branch_effect, type_expr cenv Gamma Sigma e' branch_effect rt /\
      sub_effect branch_effect ef = true.
Proof.
  intros cenv Gamma Sigma bge p vm m pt x enone esome ef rt m' vm' e' Htyped Hstep.
  inversion Hstep; subst.
  - match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end.
  - repeat split; auto. eapply typed_none_branch; eauto.
Qed.

Print Assumptions none_match_step_preservation.

Lemma typed_option_payload : forall cenv Gamma Sigma v pt ef,
  type_expr cenv Gamma Sigma (Val (Voption (Some v)) (Ptrtype (Otype pt))) ef
    (Ptrtype (Otype pt)) ->
  type_expr cenv Gamma Sigma (Val v (Ptrtype pt)) nil (Ptrtype pt).
Proof.
  intros cenv Gamma Sigma v pt ef H. inversion H; subst; eauto.
Qed.

Lemma some_constructor_result_typed : forall cenv Gamma Sigma v pt ef,
  type_expr cenv Gamma Sigma
    (Esome (Val v (Ptrtype pt)) (Ptrtype (Otype pt))) ef (Ptrtype (Otype pt)) ->
  type_expr cenv Gamma Sigma (Val (Voption (Some v)) (Ptrtype (Otype pt))) nil
    (Ptrtype (Otype pt)).
Proof.
  intros cenv Gamma Sigma v pt ef H. inversion H; subst.
  apply ty_valo; [assumption|]. intros payload Heq. inversion Heq; subst.
  eapply value_typing; eauto.
Qed.

Lemma some_constructor_step_preservation :
  forall cenv Gamma Sigma bge p vm m v pt ef m' vm' e',
  type_expr cenv Gamma Sigma
    (Esome (Val v (Ptrtype pt)) (Ptrtype (Otype pt))) ef (Ptrtype (Otype pt)) ->
  ssem_expr bge p vm m
    (Esome (Val v (Ptrtype pt)) (Ptrtype (Otype pt))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    type_expr cenv Gamma Sigma e' nil (Ptrtype (Otype pt)).
Proof.
  intros cenv Gamma Sigma bge p vm m v pt ef m' vm' e' Htyped Hstep.
  inversion Hstep; subst.
  - match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end.
  - repeat split; auto. eapply some_constructor_result_typed; eauto.
Qed.

Lemma option_int32_rejects_boolean_payload : forall cenv Gamma Sigma b ef,
  ~ type_expr cenv Gamma Sigma
    (Val (Voption (Some (Vbool b))) (Ptrtype (Otype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))))
    ef (Ptrtype (Otype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))).
Proof.
  intros cenv Gamma Sigma b ef H.
  apply typed_option_payload in H. inversion H.
Qed.

Print Assumptions typed_option_payload.
Print Assumptions some_constructor_result_typed.
Print Assumptions some_constructor_step_preservation.
Print Assumptions option_int32_rejects_boolean_payload.

Lemma structure_initializer_substitutes_fields : forall x se ids t field_type,
  subst x se (Sinit x ids (Var x field_type :: nil) t) =
    Sinit x ids (se :: nil) t.
Proof.
  intros. cbn [subst substs]. rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma typing_context_shadow : forall Gamma x t1 t2,
  extend_context (extend_context Gamma x t1) x t2 = extend_context Gamma x t2.
Proof. intros; unfold extend_context; apply PTree.set2. Qed.

Lemma typing_context_commute : forall Gamma x y tx ty,
  x <> y ->
  extend_context (extend_context Gamma x tx) y ty =
    extend_context (extend_context Gamma y ty) x tx.
Proof.
  intros Gamma x y tx ty Hneq. unfold extend_context.
  apply PTree.extensionality. intro z.
  destruct (Pos.eq_dec z x) as [Hzx | Hzx].
  - subst z. rewrite PTree.gso by exact Hneq. rewrite !PTree.gss. reflexivity.
  - destruct (Pos.eq_dec z y) as [Hzy | Hzy].
    + subst z. rewrite PTree.gss. rewrite PTree.gso by congruence. rewrite PTree.gss. reflexivity.
    + rewrite !PTree.gso by assumption. reflexivity.
Qed.

Print Assumptions structure_initializer_substitutes_fields.
Print Assumptions typing_context_shadow.
Print Assumptions typing_context_commute.

Lemma x_in_xs_spec : forall x xs, x_in_xs x xs = true <-> In x xs.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl.
  - split; [discriminate | contradiction].
  - destruct (Pos.eqb x y) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst. split; auto.
    + apply Pos.eqb_neq in Heq. rewrite IH. intuition congruence.
Qed.

Definition field_context (Gamma : ty_context) (fields : list (ident * type)) :=
  extends_context Gamma (seq.unzip1 fields) (seq.unzip2 fields).

Lemma field_context_commute : forall fields Gamma x tx,
  ~ In x (seq.unzip1 fields) ->
  field_context (extend_context Gamma x tx) fields =
    extend_context (field_context Gamma fields) x tx.
Proof.
  induction fields as [|[y ty] fields IH]; intros Gamma x tx Hfresh; simpl in *.
  - reflexivity.
  - change (field_context (extend_context (extend_context Gamma x tx) y ty) fields =
      extend_context (field_context (extend_context Gamma y ty) fields) x tx).
    rewrite typing_context_commute by (intuition congruence).
    apply IH. tauto.
Qed.

Lemma field_context_shadow : forall fields Gamma x tx,
  In x (seq.unzip1 fields) ->
  field_context (extend_context Gamma x tx) fields = field_context Gamma fields.
Proof.
  induction fields as [|[y ty] fields IH]; intros Gamma x tx Hbound; simpl in Hbound.
  - contradiction.
  - change (field_context (extend_context (extend_context Gamma x tx) y ty) fields =
      field_context (extend_context Gamma y ty) fields).
    destruct (Pos.eq_dec x y) as [Heq | Hneq].
    + subst. rewrite typing_context_shadow. reflexivity.
    + rewrite typing_context_commute by exact Hneq.
      apply IH. intuition congruence.
Qed.

Definition pattern_accepts_type (pat : pattern) (te : type) : Prop :=
  match pat, te with
  | Pnone, Ptrtype (Otype _) | Psome _, Ptrtype (Otype _) | Pbytes _ _ _, Bytes => True
  | _, _ => False
  end.

Lemma valid_match_pattern_member : forall te ps pat,
  valid_match_patterns te ps -> In pat ps -> pattern_accepts_type pat te.
Proof.
  intros te ps pat Hvalid Hin. destruct te; simpl in Hvalid; try contradiction.
  - destruct p; simpl in Hvalid; try contradiction.
    destruct Hvalid as [x [Heq | Heq]]; subst ps; simpl in Hin;
      destruct Hin as [Heq | [Heq | Hfalse]]; try contradiction;
      subst pat; exact I.
  - destruct Hvalid as [header [schema [fields [rest Heq]]]]. subst ps.
    simpl in Hin. destruct Hin as [Heq | [Heq | Hfalse]];
      try contradiction; subst pat; exact I.
Qed.

Lemma pattern_context_substitution_commute : forall Gamma x tx pat te,
  pattern_accepts_type pat te -> x_in_pattern x pat = false ->
  pattern_context (extend_context Gamma x tx) pat te =
    extend_context (pattern_context Gamma pat te) x tx.
Proof.
  intros Gamma x tx pat te Hvalid Hfree.
  assert (Hnot : ~ In x (vars_bound_by pat)).
  { intro Hin. apply x_in_xs_spec in Hin. unfold x_in_pattern in Hfree. congruence. }
  destruct pat; simpl in *.
  - reflexivity.
  - destruct te; simpl in Hvalid; try contradiction.
    destruct p; simpl in Hvalid; try contradiction.
    simpl. apply typing_context_commute. intuition congruence.
  - change (field_context (extend_context (extend_context Gamma x tx) i t) l =
      extend_context (field_context (extend_context Gamma i t) l) x tx).
    rewrite typing_context_commute by (intuition congruence).
    apply field_context_commute. tauto.
Qed.

Lemma pattern_context_substitution_shadow : forall Gamma x tx pat te,
  pattern_accepts_type pat te -> x_in_pattern x pat = true ->
  pattern_context (extend_context Gamma x tx) pat te = pattern_context Gamma pat te.
Proof.
  intros Gamma x tx pat te Hvalid Hbound.
  unfold x_in_pattern in Hbound. apply x_in_xs_spec in Hbound.
  destruct pat; simpl in *.
  - contradiction.
  - destruct Hbound as [Heq | Hfalse]; [subst i | contradiction].
    destruct te; simpl in Hvalid; try contradiction.
    destruct p; simpl in Hvalid; try contradiction.
    simpl. apply typing_context_shadow.
  - change (field_context (extend_context (extend_context Gamma x tx) i t) l =
      field_context (extend_context Gamma i t) l).
    destruct (Pos.eq_dec x i) as [Heq | Hneq].
    + subst. rewrite typing_context_shadow. reflexivity.
    + rewrite typing_context_commute by exact Hneq.
      apply field_context_shadow. intuition congruence.
Qed.

Print Assumptions pattern_context_substitution_commute.
Print Assumptions pattern_context_substitution_shadow.

Lemma substituted_branches_length : forall x se es ps,
  length (subst_match_branches subst x se ps es) = length es.
Proof.
  intros x se es. induction es as [|e es IH]; intros ps; destruct ps; simpl; auto.
Qed.

Lemma substituted_branch_lookup : forall x se es ps n pat branch',
  nth_error ps n = Some pat ->
  nth_error (subst_match_branches subst x se ps es) n = Some branch' ->
  exists branch, nth_error es n = Some branch /\
    branch' = if x_in_pattern x pat then branch else subst x se branch.
Proof.
  intros x se es. induction es as [|e es IH]; intros ps n pat branch' Hpat Hbranch;
    destruct ps as [|p ps]; destruct n; cbn [subst_match_branches nth_error] in *;
    try discriminate.
  - inversion Hpat; subst p. exists e. split; [reflexivity |].
    inversion Hbranch. reflexivity.
  - eapply IH; eauto.
Qed.

Lemma value_substitution_typing :
  (forall cenv Gamma Sigma es ef ts, type_exprs cenv Gamma Sigma es ef ts ->
   forall x v tx Gamma0, Gamma = extend_context Gamma0 x tx ->
   type_expr cenv Gamma0 Sigma (Val v tx) nil tx ->
   type_exprs cenv Gamma0 Sigma (substs subst x (Val v tx) es) ef ts) /\
  (forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
   forall x v tx Gamma0, Gamma = extend_context Gamma0 x tx ->
   type_expr cenv Gamma0 Sigma (Val v tx) nil tx ->
   type_expr cenv Gamma0 Sigma (subst x (Val v tx) e) ef t).
Proof.
  apply type_exprs_type_expr_ind_mut; intros; subst; cbn [subst substs];
    try solve [econstructor; eauto].
  - apply ty_valo; [assumption|]. intros payload Hp.
    eapply value_typing_context_independent; eauto.
  - destruct (Pos.eqb x0 x) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst x0.
      unfold extend_context in e. rewrite PTree.gss in e. inversion e; subst. assumption.
    + apply Pos.eqb_neq in Heq. apply ty_var.
      unfold extend_context in e. rewrite PTree.gso in e by congruence. exact e.
  - destruct (Pos.eqb x0 x) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst x0. apply ty_bind.
      * eapply H; eauto.
      * rewrite typing_context_shadow in t1. exact t1.
    + apply Pos.eqb_neq in Heq. apply ty_bind.
      * eapply H; eauto.
      * eapply H0.
        -- apply typing_context_commute. exact Heq.
        -- eapply value_typing_context_independent; eauto.
  - eapply ty_for; eauto using value_substitution_disjoint.
  - eapply ty_matcho with (te := te) (ef := ef) (efb := efb)
      (branch_effect := branch_effect).
    + eapply H; eauto.
    + exact v.
    + exact Hschemas.
    + rewrite substituted_branches_length. exact e0.
    + intros n pat branch' Hpat Hbranch'.
      destruct (substituted_branch_lookup x (Val v0 tx) es ps n pat branch' Hpat Hbranch')
        as [branch [Hbranch Heq]]. subst branch'.
      assert (Hvalid : pattern_accepts_type pat te).
      { eapply valid_match_pattern_member; [exact v |]. eapply nth_error_In; eauto. }
      destruct (x_in_pattern x pat) eqn:Hbound.
      * pose proof (t0 n pat branch Hpat Hbranch) as Htyped.
        rewrite pattern_context_substitution_shadow in Htyped; auto.
      * eapply H0; [exact Hpat | exact Hbranch | |].
        -- apply pattern_context_substitution_commute; assumption.
        -- eapply value_typing_context_independent; eauto.
    + rewrite substituted_branches_length. exact e1.
  - destruct (Pos.eqb x a) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame. subst a.
      match goal with
      | Hlookup : PTree.get x (extend_context Gamma0 x tx) = Some _ |- _ =>
          unfold extend_context in Hlookup; rewrite PTree.gss in Hlookup;
          inversion Hlookup; subst
      end.
      match goal with
      | Hbound : exists len attr, _ = Atype _ len attr /\ _ |- _ =>
          destruct Hbound as [len [attr [Harray Hbound]]]; subst
      end.
      eapply ty_arrayread; eauto.
    + apply Pos.eqb_neq in Hsame.
      eapply ty_aaccess; eauto.
      match goal with
      | Hlookup : PTree.get a (extend_context Gamma0 x tx) = Some _ |- _ =>
          unfold extend_context in Hlookup; rewrite PTree.gso in Hlookup by congruence;
          exact Hlookup
      end.

Qed.
Print Assumptions value_substitution_typing.


Lemma value_substitution_preserves_typing : forall cenv Gamma Sigma x v tx e ef t,
  type_expr cenv (extend_context Gamma x tx) Sigma e ef t ->
  type_expr cenv Gamma Sigma (Val v tx) nil tx ->
  type_expr cenv Gamma Sigma (subst x (Val v tx) e) ef t.
Proof.
  intros cenv Gamma Sigma x v tx e ef t He Hv.
  eapply (proj2 value_substitution_typing); eauto.
Qed.

Lemma typed_value_effect_nil : forall cenv Gamma Sigma v annotation ef t,
  type_expr cenv Gamma Sigma (Val v annotation) ef t -> ef = nil.
Proof. intros cenv Gamma Sigma v annotation ef t H; inversion H; reflexivity. Qed.

Lemma bind_value_step_preservation :
  forall cenv Gamma Sigma bge p vm m x v tx body rt ef m' vm' e',
  type_expr cenv Gamma Sigma (Bind x tx (Val v tx) body rt) ef rt ->
  ssem_expr bge p vm m (Bind x tx (Val v tx) body rt) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' ef rt.
Proof.
  intros cenv Gamma Sigma bge p vm m x v tx body rt ef m' vm' e' Htyped Hstep.
  inversion Hstep; subst.
  - match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end.
  - inversion Htyped; subst.
    match goal with H : type_expr _ _ _ (Val _ _) _ _ |- _ =>
      pose proof (typed_value_effect_nil _ _ _ _ _ _ _ H) as Hnil; subst
    end.
    repeat split; auto.
    match goal with H : SubstE _ _ _ _ |- _ =>
      apply substitution_relation_iff in H; subst
    end.
    eapply value_substitution_preserves_typing; eauto using value_typing.
Qed.

Lemma some_match_step_preservation :
  forall cenv Gamma Sigma bge p vm m pt v x enone esome ef rt m' vm' e',
  type_expr cenv Gamma Sigma
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) ef rt ->
  ssem_expr bge p vm m
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt)))
      (Pnone :: Psome x :: nil) (enone :: esome :: nil) rt) m' vm' e' ->
  m' = m /\ vm' = vm /\
    exists branch_effect, type_expr cenv Gamma Sigma e' branch_effect rt /\
      sub_effect branch_effect ef = true.
Proof.
  intros cenv Gamma Sigma bge p vm m pt v x enone esome ef rt m' vm' e' Htyped Hstep.
  pose proof (typed_some_branch_context _ _ _ _ _ _ _ _ _ _ Htyped) as Hbranch.
  assert (Hpayload : type_expr cenv Gamma Sigma (Val v (Ptrtype pt)) nil (Ptrtype pt)).
  { inversion Htyped; subst.
    match goal with H : type_expr _ _ _ (Val (Voption _) _) _ _ |- _ =>
      inversion H; subst; eauto
    end. }
  inversion Hstep; subst.
  - match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end.
  - repeat split; auto. destruct Hbranch as [branch_effect [Hbranch Hsub]].
    exists branch_effect. split; [|exact Hsub].
    eapply value_substitution_preserves_typing; eauto.
Qed.

Print Assumptions value_substitution_preserves_typing.
Print Assumptions bind_value_step_preservation.
Print Assumptions some_match_step_preservation.

Lemma typed_option_match_shape : forall cenv Gamma Sigma o pt ps es ef rt,
  type_expr cenv Gamma Sigma
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es rt) ef rt ->
  exists x enone esome efn efs,
    ((ps = (Pnone :: Psome x :: nil) /\ es = (enone :: esome :: nil)) \/
     (ps = (Psome x :: Pnone :: nil) /\ es = (esome :: enone :: nil))) /\
    type_expr cenv Gamma Sigma enone efn rt /\
    type_expr cenv (extend_context Gamma x (Ptrtype pt)) Sigma esome efs rt /\
    sub_effect efn ef = true /\ sub_effect efs ef = true.
Proof.
  intros cenv Gamma Sigma o pt ps es ef rt Htyped.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  inversion Hscrut; subst.
  destruct Hpatterns as [x [Horder | Horder]]; subst ps;
    destruct es as [|a [|b [|extra rest]]]; simpl in Hlength; try discriminate.
  - exists x, a, b, (effects O), (effects (S O)). split.
    + left. split; reflexivity.
    + split; [exact (Hbranches O Pnone a eq_refl eq_refl) |].
      split; [exact (Hbranches (S O) (Psome x) b eq_refl eq_refl) |].
      split; apply Heffects; reflexivity.
  - exists x, b, a, (effects (S O)), (effects O). split.
    + right. split; reflexivity.
    + split; [exact (Hbranches (S O) Pnone b eq_refl eq_refl) |].
      split; [exact (Hbranches O (Psome x) a eq_refl eq_refl) |].
      split; apply Heffects; reflexivity.
Qed.

Lemma typed_some_match_payload : forall cenv Gamma Sigma v pt ps es ef rt,
  type_expr cenv Gamma Sigma
    (Match (Val (Voption (Some v)) (Ptrtype (Otype pt))) ps es rt) ef rt ->
  type_expr cenv Gamma Sigma (Val v (Ptrtype pt)) nil (Ptrtype pt).
Proof.
  intros cenv Gamma Sigma v pt ps es ef rt Htyped.
  inversion Htyped; subst.
  match goal with H : type_expr _ _ _ (Val (Voption _) _) _ _ |- _ =>
    inversion H; subst; eauto
  end.
Qed.

Lemma option_match_value_progress : forall cenv Gamma Sigma bge p vm m o pt ps es ef rt,
  type_expr cenv Gamma Sigma
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es rt) ef rt ->
  exists e', ssem_expr bge p vm m
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es rt) m vm e'.
Proof.
  intros cenv Gamma Sigma bge p vm m o pt ps es ef rt Htyped.
  destruct (typed_option_match_shape _ _ _ _ _ _ _ _ _ Htyped)
    as [x [enone [esome [efn [efs [Horder Hbranches]]]]]].
  destruct Horder as [[Hp He] | [Hp He]]; subst ps es; destruct o.
  - eexists. apply ssem_match_some.
  - eexists. apply ssem_match_none2.
  - eexists. apply ssem_match_some_first.
  - eexists. apply ssem_match_none2.
Qed.

Lemma option_match_value_preservation :
  forall cenv Gamma Sigma bge p vm m o pt ps es ef rt m' vm' e',
  type_expr cenv Gamma Sigma
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es rt) ef rt ->
  ssem_expr bge p vm m
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es rt) m' vm' e' ->
  m' = m /\ vm' = vm /\
    exists ef', type_expr cenv Gamma Sigma e' ef' rt /\ sub_effect ef' ef = true.
Proof.
  intros cenv Gamma Sigma bge p vm m o pt ps es ef rt m' vm' e' Htyped Hstep.
  destruct (typed_option_match_shape _ _ _ _ _ _ _ _ _ Htyped)
    as [x [enone [esome [efn [efs [Horder [Hnone [Hsome [Hfn Hfs]]]]]]]]].
  destruct Horder as [[Hp He] | [Hp He]]; subst ps es; destruct o;
    inversion Hstep; subst;
    try solve [match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end];
    repeat split; auto.
  - exists efs. split; [|exact Hfs].
    eapply value_substitution_preserves_typing; [exact Hsome |].
    eapply typed_some_match_payload; eauto.
  - exists efn. split; assumption.
  - exists efs. split; [|exact Hfs].
    eapply value_substitution_preserves_typing; [exact Hsome |].
    eapply typed_some_match_payload; eauto.
  - exists efn. split; assumption.
Qed.

Print Assumptions option_match_value_progress.
Print Assumptions option_match_value_preservation.

Require Import BeePL_soundness_memory BeePL_auxlemmas.

Lemma match_scrutinee_typing_preservation :
  forall cenv Gamma Sigma Sigma' e e' ps es ef rt,
  type_expr cenv Gamma Sigma (Match e ps es rt) ef rt ->
  store_context_extends Sigma Sigma' ->
  (forall scrutinee_effect scrutinee_type,
    type_expr cenv Gamma Sigma e scrutinee_effect scrutinee_type ->
    exists effect', type_expr cenv Gamma Sigma' e' effect' scrutinee_type /\
      sub_effect effect' scrutinee_effect = true) ->
  exists ef', type_expr cenv Gamma Sigma' (Match e' ps es rt) ef' rt /\
    sub_effect ef' ef = true.
Proof.
  intros cenv Gamma Sigma Sigma' e e' ps es ef rt Htyped Hextends Hscrutinee.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  subst ef.
  destruct (Hscrutinee efe te Hscrut) as [efe' [Hscrut' Hsub]].
  exists (efe' ++ efb). split.
  - eapply ty_matcho with (te := te) (branch_effect := effects); eauto.
    intros n pat branch Hpat Hbranch.
    eapply (proj2 typing_store_extension); [eapply Hbranches; eauto | exact Hextends].
  - apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
Qed.

Print Assumptions match_scrutinee_typing_preservation.

(* Shared list case of preservation. Q can package the memory and runtime-map
   invariants needed by a particular expression proof. *)
Theorem argument_list_preservation_from_expressions :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bge p cenv Gamma Sigma vm m es ef ts vm' m' es',
  Q Sigma vm m -> type_exprs cenv Gamma Sigma es ef ts ->
  (forall e, In e es -> forall effect ty,
    type_expr cenv Gamma Sigma e effect ty ->
    forall next_vm next_m next_e,
      ssem_expr bge p vm m e next_m next_vm next_e ->
      exists next_Sigma next_effect,
        store_context_extends Sigma next_Sigma /\ Q next_Sigma next_vm next_m /\
        type_expr cenv Gamma next_Sigma next_e next_effect ty /\
        sub_effect next_effect effect = true) ->
  ssem_exprs bge p vm m es m' vm' es' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_exprs cenv Gamma Sigma' es' ef' ts /\ sub_effect ef' ef = true.
Proof.
  intros Q bge p cenv Gamma Sigma vm m es.
  induction es as [|head tail IH]; intros ef ts vm' m' es' Hstate Htyped Hlocal Hstep.
  - inversion Htyped; subst. inversion Hstep; subst.
    exists Sigma, nil. split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [constructor | reflexivity].
  - inversion Htyped as [|c G S h tl hef tef ht tts Hhead Htail]; subst.
    inversion Hstep; subst.
    + match goal with Hs : ssem_expr bge p vm m _ _ _ _ |- _ =>
        destruct (Hlocal _ (or_introl eq_refl) _ _ Hhead _ _ _ Hs)
          as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
      end.
      exists nextSigma, (nextEffect ++ tef). split; [exact Hext |].
      split; [exact Hstate' |]. split.
      * econstructor; [exact Htyped' |]. eapply (proj1 typing_store_extension); eauto.
      * apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
    + match goal with Hs : ssem_exprs bge p vm m tail _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ Hstate Htail
          ltac:(intros e Hin; apply Hlocal; right; exact Hin) Hs)
          as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
      end.
      exists nextSigma, (hef ++ nextEffect). split; [exact Hext |].
      split; [exact Hstate' |]. split.
      * econstructor; [| exact Htyped']. eapply (proj2 typing_store_extension); eauto.
      * apply sub_effect_concat; [apply sub_effect_refl | exact Hsub].
Qed.

Print Assumptions argument_list_preservation_from_expressions.

Lemma conditional_typing_components : forall cenv Gamma Sigma guard yes no ef ty,
  type_expr cenv Gamma Sigma (Cond guard yes no ty) ef ty ->
  exists guard_effect branch_effect yes_effect no_effect,
    ef = guard_effect ++ branch_effect /\
    type_expr cenv Gamma Sigma guard guard_effect (Vtype Tbool) /\
    type_expr cenv Gamma Sigma yes yes_effect ty /\
    type_expr cenv Gamma Sigma no no_effect ty /\
    sub_effect yes_effect branch_effect = true /\
    sub_effect no_effect branch_effect = true.
Proof. intros; inversion H; subst; eauto 12. Qed.

Theorem conditional_preservation_from_guard :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bge p cenv Gamma Sigma vm m guard yes no ef ty vm' m' e',
  Q Sigma vm m -> type_expr cenv Gamma Sigma (Cond guard yes no ty) ef ty ->
  (forall guard_effect, type_expr cenv Gamma Sigma guard guard_effect (Vtype Tbool) ->
    forall next_vm next_m next_guard,
      ssem_expr bge p vm m guard next_m next_vm next_guard ->
      exists next_Sigma next_effect,
        store_context_extends Sigma next_Sigma /\ Q next_Sigma next_vm next_m /\
        type_expr cenv Gamma next_Sigma next_guard next_effect (Vtype Tbool) /\
        sub_effect next_effect guard_effect = true) ->
  ssem_expr bge p vm m (Cond guard yes no ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q bge p cenv Gamma Sigma vm m guard yes no ef ty vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [guard_effect [branch_effect [yes_effect [no_effect [Heffect [Hguard [Hyes [Hno [Hyes_sub Hno_sub]]]]]]]]]. subst ef.
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m guard _ _ _ |- _ =>
      destruct (Hlocal _ Hguard _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, (nextEffect ++ branch_effect). split; [exact Hext |].
    split; [exact Hstate' |]. split.
    + eapply ty_cond; [exact Htyped' | | |exact Hyes_sub |exact Hno_sub]; eapply (proj2 typing_store_extension); eauto.
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
  - pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hguard) as Hef. subst guard_effect.
    exists Sigma, yes_effect. split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [exact Hyes | exact Hyes_sub].
  - pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hguard) as Hef. subst guard_effect.
    exists Sigma, no_effect. split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [exact Hno | exact Hno_sub].
Qed.

Lemma typed_boolean_value_canonical : forall cenv Gamma Sigma v annotation ef,
  type_expr cenv Gamma Sigma (Val v annotation) ef (Vtype Tbool) ->
  exists b, v = Vbool b /\ annotation = Vtype Tbool.
Proof. intros; inversion H; subst; eauto. Qed.

Theorem conditional_progress_from_guard :
  forall bge p cenv Gamma Sigma vm m guard yes no ef ty,
  type_expr cenv Gamma Sigma (Cond guard yes no ty) ef ty ->
  ((exists v annotation, guard = Val v annotation) \/
    exists next_m next_vm next_guard, ssem_expr bge p vm m guard next_m next_vm next_guard) ->
  exists m' vm' e', ssem_expr bge p vm m (Cond guard yes no ty) m' vm' e'.
Proof.
  intros bge p cenv Gamma Sigma vm m guard yes no ef ty Htyped Hprogress.
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [guard_effect [branch_effect [yes_effect [no_effect [Heffect [Hguard [Hyes [Hno [Hyes_sub Hno_sub]]]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hyes) as Hyes_type.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hno) as Hno_type.
  destruct Hprogress as [[v [annotation He]] | [next_m [next_vm [next_guard Hstep]]]].
  - subst guard. destruct (typed_boolean_value_canonical _ _ _ _ _ _ Hguard) as [b [Hv Ha]].
    subst v annotation. destruct b.
    + rewrite <- Hyes_type. do 3 eexists. apply ssem_ctrue.
    + rewrite <- Hno_type. do 3 eexists. apply ssem_cfalse.
  - rewrite <- Hyes_type. do 3 eexists. apply ssem_cond. exact Hstep.
Qed.

Print Assumptions conditional_preservation_from_guard.
Print Assumptions conditional_progress_from_guard.

Lemma bind_typing_components : forall cenv Gamma Sigma x tx init body ef ty,
  type_expr cenv Gamma Sigma (Bind x tx init body ty) ef ty ->
  exists init_effect body_effect,
    ef = init_effect ++ body_effect /\
    type_expr cenv Gamma Sigma init init_effect tx /\
    type_expr cenv (extend_context Gamma x tx) Sigma body body_effect ty.
Proof. intros; inversion H; subst; eauto 8. Qed.

Theorem bind_preservation_from_initializer :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bge p cenv Gamma Sigma vm m x tx init body ef ty vm' m' e',
  Q Sigma vm m -> type_expr cenv Gamma Sigma (Bind x tx init body ty) ef ty ->
  (forall init_effect, type_expr cenv Gamma Sigma init init_effect tx ->
    forall next_vm next_m next_init,
      ssem_expr bge p vm m init next_m next_vm next_init ->
      exists next_Sigma next_effect,
        store_context_extends Sigma next_Sigma /\ Q next_Sigma next_vm next_m /\
        type_expr cenv Gamma next_Sigma next_init next_effect tx /\
        sub_effect next_effect init_effect = true) ->
  ssem_expr bge p vm m (Bind x tx init body ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q bge p cenv Gamma Sigma vm m x tx init body ef ty vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (bind_typing_components _ _ _ _ _ _ _ _ _ Htyped)
    as [init_effect [body_effect [Heffect [Hinit Hbody]]]]. subst ef.
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m init _ _ _ |- _ =>
      destruct (Hlocal _ Hinit _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, (nextEffect ++ body_effect). split; [exact Hext |].
    split; [exact Hstate' |]. split.
    + apply ty_bind; [exact Htyped' |]. eapply (proj2 typing_store_extension); eauto.
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
  - edestruct bind_value_step_preservation as [_ [_ Hvalue]];
      [exact Htyped | exact Hstep |].
    exists Sigma, (init_effect ++ body_effect). split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [exact Hvalue | apply sub_effect_refl].
Qed.

Theorem bind_progress_from_initializer :
  forall bge p cenv Gamma Sigma vm m x tx init body ef ty,
  type_expr cenv Gamma Sigma (Bind x tx init body ty) ef ty ->
  ((exists v annotation, init = Val v annotation) \/
    exists next_m next_vm next_init, ssem_expr bge p vm m init next_m next_vm next_init) ->
  exists m' vm' e', ssem_expr bge p vm m (Bind x tx init body ty) m' vm' e'.
Proof.
  intros bge p cenv Gamma Sigma vm m x tx init body ef ty Htyped Hprogress.
  destruct (bind_typing_components _ _ _ _ _ _ _ _ _ Htyped)
    as [init_effect [body_effect [Heffect [Hinit Hbody]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hbody) as Hbody_type.
  destruct Hprogress as [[v [annotation He]] | [next_m [next_vm [next_init Hstep]]]].
  - subst init. pose proof (type_rel_typeof _ _ _ _ _ _ Hinit) as Hannotation.
    simpl in Hannotation. subst annotation. rewrite <- Hbody_type.
    do 3 eexists. apply ssem_bind2. apply substitution_function_relation.
  - rewrite <- Hbody_type. do 3 eexists. apply ssem_bind1. exact Hstep.
Qed.

Print Assumptions bind_preservation_from_initializer.
Print Assumptions bind_progress_from_initializer.

Lemma some_typing_components : forall cenv Gamma Sigma operand ef ty,
  type_expr cenv Gamma Sigma (Esome operand ty) ef ty ->
  exists pt, ty = Ptrtype (Otype pt) /\
    type_expr cenv Gamma Sigma operand ef (Ptrtype pt).
Proof.
  intros cenv Gamma Sigma operand ef ty Htyped. inversion Htyped; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Theorem none_progress_preservation : forall bge p cenv Gamma Sigma vm m ty ef,
  type_expr cenv Gamma Sigma (Enone ty) ef ty ->
  ssem_expr bge p vm m (Enone ty) m vm (Val (Voption None) ty) /\
    type_expr cenv Gamma Sigma (Val (Voption None) ty) nil ty.
Proof.
  intros bge p cenv Gamma Sigma vm m ty ef Htyped. split; [apply ssem_none |].
  inversion Htyped; subst. apply ty_valo; [assumption|]. intros; discriminate.
Qed.

Theorem none_step_preservation : forall bge p cenv Gamma Sigma vm m ty ef m' vm' e',
  type_expr cenv Gamma Sigma (Enone ty) ef ty ->
  ssem_expr bge p vm m (Enone ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros bge p cenv Gamma Sigma vm m ty ef m' vm' e' Htyped Hstep.
  pose proof (proj2 (none_progress_preservation bge p cenv Gamma Sigma vm m ty ef Htyped)) as Hresult.
  inversion Hstep; subst. repeat split; try reflexivity; exact Hresult.
Qed.

Theorem some_value_step_preservation :
  forall bge p cenv Gamma Sigma vm m v annotation ty ef m' vm' e',
  type_expr cenv Gamma Sigma (Esome (Val v annotation) ty) ef ty ->
  ssem_expr bge p vm m (Esome (Val v annotation) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros bge p cenv Gamma Sigma vm m v annotation ty ef m' vm' e' Htyped Hstep.
  destruct (some_typing_components _ _ _ _ _ _ Htyped) as [pt [Hty Hvalue]]. subst ty.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation.
  simpl in Hannotation. subst annotation.
  pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hef. subst ef.
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  repeat split; try reflexivity. apply ty_valo.
  - inversion Htyped; subst; assumption.
  - intros payload Heq.
  inversion Heq; subst. exact Hvalue.
Qed.

Theorem some_progress_from_operand :
  forall bge p cenv Gamma Sigma vm m operand ef ty,
  type_expr cenv Gamma Sigma (Esome operand ty) ef ty ->
  ((exists v annotation, operand = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m operand m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m (Esome operand ty) m' vm' e'.
Proof.
  intros bge p cenv Gamma Sigma vm m operand ef ty Htyped Hprogress.
  destruct Hprogress as [[v [annotation He]] | [nextM [nextVm [nextOperand Hstep]]]].
  - subst operand. do 3 eexists. apply ssem_some2.
  - do 3 eexists. apply ssem_some1. exact Hstep.
Qed.

Theorem some_preservation_from_operand :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bge p cenv Gamma Sigma vm m operand ef ty m' vm' e',
  Q Sigma vm m -> type_expr cenv Gamma Sigma (Esome operand ty) ef ty ->
  (forall operandTy, type_expr cenv Gamma Sigma operand ef operandTy ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect operandTy /\ sub_effect nextEffect ef = true) ->
  ssem_expr bge p vm m (Esome operand ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q bge p cenv Gamma Sigma vm m operand ef ty m' vm' e' Hstate Htyped Hlocal Hstep.
  destruct (some_typing_components _ _ _ _ _ _ Htyped) as [pt [Hty Hoperand]]. subst ty.
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m operand _ _ _ |- _ =>
      destruct (Hlocal _ Hoperand _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, nextEffect. split; [exact Hext |].
    split; [exact Hstate' |]. split; [|exact Hsub].
    eapply ty_some; [exact Htyped' | | reflexivity].
    inversion Htyped; subst; assumption.
  - edestruct some_value_step_preservation as [_ [_ Hvalue]];
      [exact Htyped | exact Hstep |].
    exists Sigma, nil. split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [exact Hvalue | apply sub_effect_nil].
Qed.

Print Assumptions none_progress_preservation.
Print Assumptions none_step_preservation.
Print Assumptions some_value_step_preservation.
Print Assumptions some_progress_from_operand.
Print Assumptions some_preservation_from_operand.

Lemma typed_option_value_canonical : forall cenv Gamma Sigma v annotation ef pt,
  type_expr cenv Gamma Sigma (Val v annotation) ef (Ptrtype (Otype pt)) ->
  exists o, v = Voption o /\ annotation = Ptrtype (Otype pt).
Proof. intros; inversion H; subst; eauto. Qed.

Lemma option_match_typing_components : forall cenv Gamma Sigma scrutinee pt ps es ef rt,
  typeof_expr scrutinee = Ptrtype (Otype pt) ->
  type_expr cenv Gamma Sigma (Match scrutinee ps es rt) ef rt ->
  exists efe efb effects,
    ef = efe ++ efb /\
    type_expr cenv Gamma Sigma scrutinee efe (Ptrtype (Otype pt)) /\
    valid_match_patterns (Ptrtype (Otype pt)) ps /\ length ps = length es /\
    (forall n pat branch, List.nth_error ps n = Some pat -> List.nth_error es n = Some branch ->
      type_expr cenv (pattern_context Gamma pat (Ptrtype (Otype pt))) Sigma branch (effects n) rt) /\
    (forall n, is_true (ssrnat.leq (S n) (length es)) -> sub_effect (effects n) efb = true).
Proof.
  intros cenv Gamma Sigma scrutinee pt ps es ef rt Hoption Htyped.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hscrut) as Htype.
  rewrite Hoption in Htype. subst te. exists efe, efb, effects.
  repeat split; assumption.
Qed.

Theorem option_match_progress_from_scrutinee :
  forall bge p cenv Gamma Sigma vm m scrutinee pt ps es ef rt,
  typeof_expr scrutinee = Ptrtype (Otype pt) ->
  type_expr cenv Gamma Sigma (Match scrutinee ps es rt) ef rt ->
  ((exists v annotation, scrutinee = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m scrutinee m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m (Match scrutinee ps es rt) m' vm' e'.
Proof.
  intros bge p cenv Gamma Sigma vm m scrutinee pt ps es ef rt Hoption Htyped Hprogress.
  destruct (option_match_typing_components _ _ _ _ _ _ _ _ _ Hoption Htyped)
    as [efe [efb [effects [Heffect [Hscrut [Hpatterns [Hlength Hbranches]]]]]]].
  destruct Hprogress as [[v [annotation He]] | [nextM [nextVm [nextScrutinee Hstep]]]].
  - subst scrutinee.
    destruct (typed_option_value_canonical _ _ _ _ _ _ _ Hscrut) as [o [Hv Ha]]. subst v annotation.
    destruct (option_match_value_progress _ _ _ bge p vm m _ _ _ _ _ _ Htyped) as [e' Hs]. eauto.
  - destruct Hpatterns as [x [Hps | Hps]]; subst ps;
      destruct es as [|a [|b [|extra rest]]]; simpl in Hlength; try discriminate;
      do 3 eexists; apply ssem_match_none1; exact Hstep.
Qed.

Theorem option_match_preservation_from_scrutinee :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bge p cenv Gamma Sigma vm m scrutinee pt ps es ef rt m' vm' e',
  Q Sigma vm m -> typeof_expr scrutinee = Ptrtype (Otype pt) ->
  type_expr cenv Gamma Sigma (Match scrutinee ps es rt) ef rt ->
  (forall scrutineeEffect,
    type_expr cenv Gamma Sigma scrutinee scrutineeEffect (Ptrtype (Otype pt)) ->
    forall nextVm nextM nextScrutinee,
      ssem_expr bge p vm m scrutinee nextM nextVm nextScrutinee ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextScrutinee nextEffect (Ptrtype (Otype pt)) /\
        sub_effect nextEffect scrutineeEffect = true) ->
  ssem_expr bge p vm m (Match scrutinee ps es rt) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' rt /\ sub_effect ef' ef = true.
Proof.
  intros Q bge p cenv Gamma Sigma vm m scrutinee pt ps es ef rt m' vm' e'
    Hstate Hoption Htyped Hlocal Hstep.
  destruct (option_match_typing_components _ _ _ _ _ _ _ _ _ Hoption Htyped)
    as [efe [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]].
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  subst ef. inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m scrutinee _ _ _ |- _ =>
      destruct (Hlocal _ Hscrut _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, (nextEffect ++ efb). split; [exact Hext |].
    split; [exact Hstate' |]. split.
    + eapply ty_matcho with (te := Ptrtype (Otype pt)) (branch_effect := effects); eauto.
      intros n pat branch Hpat Hbranch.
      eapply (proj2 typing_store_extension); [eapply Hbranches; eauto | exact Hext].
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
  all: try solve [
    cbn [typeof_expr] in Hoption; inversion Hoption; subst;
    edestruct option_match_value_preservation as [_ [_ [resultEffect [Hresult Hsub]]]];
      [exact Htyped | exact Hstep |];
    exists Sigma, resultEffect; split; [apply store_context_extends_refl |];
    split; [exact Hstate |]; split; assumption].
  destruct Hpatterns as [x [Hbad | Hbad]]; discriminate.
Qed.

Print Assumptions typed_option_value_canonical.
Print Assumptions option_match_progress_from_scrutinee.
Print Assumptions option_match_preservation_from_scrutinee.

Definition typed_field_values cenv Gamma Sigma (fields : list (ident * type)) (values : list value) :=
  List.Forall2 (fun field v => type_expr cenv Gamma Sigma (Val v (snd field)) nil (snd field)) fields values.

Lemma typed_field_values_context_independent : forall cenv Gamma Gamma' Sigma fields values,
  typed_field_values cenv Gamma Sigma fields values ->
  typed_field_values cenv Gamma' Sigma fields values.
Proof.
  intros cenv Gamma Gamma' Sigma fields values Hvalues.
  induction Hvalues; constructor; auto.
  eapply value_typing_context_independent; eassumption.
Qed.

Theorem instantiate_field_values_preserves_typing :
  forall fields values cenv Gamma Sigma body ef rt,
  typed_field_values cenv Gamma Sigma fields values ->
  type_expr cenv (field_context Gamma fields) Sigma body ef rt ->
  exists body', instantiate_field_values fields values body = OK body' /\
    type_expr cenv Gamma Sigma body' ef rt.
Proof.
  induction fields as [|[name ty] fields IH];
    intros values cenv Gamma Sigma body ef rt Hvalues Hbody.
  - inversion Hvalues; subst. exists body. split; [reflexivity | exact Hbody].
  - inversion Hvalues; subst.
    change (type_expr cenv (field_context (extend_context Gamma name ty) fields) Sigma body ef rt) in Hbody.
    match goal with Htail : List.Forall2 _ fields ?tail |- _ =>
      assert (Htail' : typed_field_values cenv (extend_context Gamma name ty) Sigma fields tail)
        by (eapply typed_field_values_context_independent; exact Htail);
      destruct (IH tail cenv (extend_context Gamma name ty) Sigma body ef rt Htail' Hbody)
        as [nextBody [Hinstantiate Htyped]]
    end.
    eexists. split.
    + cbn [instantiate_field_values]. rewrite Hinstantiate. reflexivity.
    + eapply value_substitution_preserves_typing; eassumption.
Qed.

Theorem instantiate_bytes_header_preserves_typing :
  forall cenv Gamma Sigma header schema fields headerValue fieldValues body ef rt,
  type_expr cenv Gamma Sigma (Val headerValue schema) nil schema ->
  typed_field_values cenv Gamma Sigma fields fieldValues ->
  type_expr cenv (pattern_context Gamma (Pbytes header schema fields) Bytes) Sigma body ef rt ->
  exists body', instantiate_bytes_header header schema fields headerValue fieldValues body = OK body' /\
    type_expr cenv Gamma Sigma body' ef rt.
Proof.
  intros cenv Gamma Sigma header schema fields headerValue fieldValues body ef rt Hheader Hfields Hbody.
  change (type_expr cenv (field_context (extend_context Gamma header schema) fields) Sigma body ef rt) in Hbody.
  assert (Hfields' : typed_field_values cenv (extend_context Gamma header schema) Sigma fields fieldValues)
    by (eapply typed_field_values_context_independent; exact Hfields).
  destruct (instantiate_field_values_preserves_typing fields fieldValues cenv
    (extend_context Gamma header schema) Sigma body ef rt Hfields' Hbody)
    as [nextBody [Hinstantiate Htyped]].
  eexists. split.
  - unfold instantiate_bytes_header. rewrite Hinstantiate. reflexivity.
  - eapply value_substitution_preserves_typing; eassumption.
Qed.

Lemma instantiate_field_values_rejects_arity : forall fields values body,
  List.length fields <> List.length values ->
  exists error, instantiate_field_values fields values body = Error error.
Proof.
  induction fields as [|[name ty] fields IH]; intros values body Hlength;
    destruct values as [|v values]; try solve [exfalso; apply Hlength; reflexivity].
  - eexists; reflexivity.
  - eexists; reflexivity.
  - assert (Htail : List.length fields <> List.length values) by (intro Heq; apply Hlength; simpl; congruence).
    destruct (IH values body Htail) as [error Herr]. cbn [instantiate_field_values]. rewrite Herr. eauto.
Qed.

Print Assumptions instantiate_field_values_preserves_typing.
Print Assumptions instantiate_bytes_header_preserves_typing.
Print Assumptions instantiate_field_values_rejects_arity.

(* Context extension gives the last occurrence of a field name precedence. *)
Lemma instantiate_field_values_last_binding_wins : forall name ty first last,
  instantiate_field_values ((name, ty) :: (name, ty) :: nil)
    (first :: last :: nil) (Var name ty) = OK (Val last ty).
Proof.
  intros. cbn [instantiate_field_values subst]. rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma instantiate_bytes_field_shadows_header : forall name ty headerValue fieldValue,
  instantiate_bytes_header name ty ((name, ty) :: nil) headerValue (fieldValue :: nil)
    (Var name ty) = OK (Val fieldValue ty).
Proof.
  intros. cbn [instantiate_bytes_header instantiate_field_values subst]. rewrite Pos.eqb_refl. reflexivity.
Qed.

Print Assumptions instantiate_field_values_last_binding_wins.
Print Assumptions instantiate_bytes_field_shadows_header.

(* The captured callee environment closes a suspended call with respect to
   substitutions in its caller. The body is intentionally left untouched. *)
Lemma callframe_substitution_identity : forall x replacement callee_vm body ty,
  subst x replacement (CallFrame callee_vm body ty) = CallFrame callee_vm body ty.
Proof. reflexivity. Qed.
