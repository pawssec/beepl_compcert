(* Substituting a value preserves captured frame validity: substitutions stop
   at a call-frame scope boundary and values contain no nested expressions. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_runtime_locations BeePL_callable_locations.
Require Import BeePL_runtime_frames.
Import ListNotations.

Lemma substs_runtime_frames : forall bge Sigma m layout x v ty es,
  all_expr_locations (runtime_frames bge Sigma m layout) es ->
  (forall e, In e es -> runtime_frames bge Sigma m layout e ->
    runtime_frames bge Sigma m layout (subst x (Val v ty) e)) ->
  all_expr_locations (runtime_frames bge Sigma m layout) (substs subst x (Val v ty) es).
Proof.
  intros bge Sigma m layout x v ty es. induction es; intros Hall Hstep; simpl; constructor.
  - apply Hstep; [left; reflexivity | destruct Hall; assumption].
  - apply IHes; [destruct Hall; assumption |]. intros e Hin. apply Hstep. right; exact Hin.
Qed.

Lemma match_substs_runtime_frames : forall bge Sigma m layout x v ty es ps,
  all_expr_locations (runtime_frames bge Sigma m layout) es ->
  (forall e, In e es -> runtime_frames bge Sigma m layout e ->
    runtime_frames bge Sigma m layout (subst x (Val v ty) e)) ->
  all_expr_locations (runtime_frames bge Sigma m layout)
    (subst_match_branches subst x (Val v ty) ps es).
Proof.
  intros bge Sigma m layout x v ty es. induction es; intros ps Hall Hstep; simpl; [constructor |].
  destruct ps as [|pat ps]; [exact Hall |]. simpl. destruct Hall as [Hhead Htail].
  destruct (x_in_pattern x pat); constructor; auto.
  - apply IHes; auto. intros e Hin. apply Hstep. right; exact Hin.
  - apply Hstep; auto. left; reflexivity.
  - apply IHes; auto. intros e Hin. apply Hstep. right; exact Hin.
Qed.

Theorem value_substitution_runtime_frames : forall bge Sigma m layout x v ty e,
  runtime_frames bge Sigma m layout e ->
  runtime_frames bge Sigma m layout (subst x (Val v ty) e).
Proof.
  intros bge Sigma m layout x v ty e. induction e using expr_ind_rec;
    intros Hframes; cbn [subst runtime_frames] in *;
    try solve [intuition eauto using substs_runtime_frames, match_substs_runtime_frames].
  - destruct (Pos.eqb x x0); simpl; auto.
  - destruct (Pos.eqb x x0); simpl; intuition.
  - destruct (Pos.eqb x a); simpl; auto.
Qed.

Theorem runtime_bind_value_preservation :
  forall bge Gamma Sigma p vm m layout x v tx body rt ef m' vm' e',
  runtime_configuration bge Gamma Sigma vm m layout (Bind x tx (Val v tx) body rt) ef rt ->
  ssem_expr bge p vm m (Bind x tx (Val v tx) body rt) m' vm' e' ->
  m' = m /\ vm' = vm /\ runtime_configuration bge Gamma Sigma vm' m' layout e' ef rt.
Proof.
  intros bge Gamma Sigma p vm m layout x v tx body rt ef m' vm' e'
    [Hheap Htyped Hlocations Hframes] Hstep.
  destruct (bind_value_step_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htyped Hstep)
    as [Hm [Hvm Htyped']]. subst m' vm'.
  split; [reflexivity |]. split; [reflexivity |]. constructor; try assumption.
  - eapply located_bind_value_preservation; eauto.
  - inversion Hstep; subst.
    + match goal with H : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion H end.
    + match goal with H : SubstE _ _ _ _ |- _ =>
        apply substitution_relation_iff in H; subst
      end.
      eapply value_substitution_runtime_frames. destruct Hframes; assumption.
Qed.

Print Assumptions value_substitution_runtime_frames.
Print Assumptions runtime_bind_value_preservation.
