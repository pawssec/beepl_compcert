(* Structural pattern arity, independent of memories and replacement values. *)
Require Import List Bool ZArith Lia AST.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_substitution_freevars.
Require Import BeePL_typed_substitution_freevars.
Import ListNotations.

Fixpoint match_arity (e : expr) : bool :=
  match e with
  | App f es _ => match_arity f && forallb (fun b=>b) (List.map match_arity es)
  | Prim _ es _ | Sinit _ _ es _ | Ainit _ _ es _ | Ebytes es _ => forallb (fun b=>b) (List.map match_arity es)
  | Bind _ _ first body _ => match_arity first && match_arity body
  | Cond a b c _ | For a b _ c _ => match_arity a && (match_arity b && match_arity c)
  | Sfield e _ _ | Esome e _ => match_arity e
  | Match e ps es _ => match_arity e && (Nat.eqb (length ps) (length es) && forallb (fun b=>b) (List.map match_arity es))
  | LoopFrame _ template active => match_arity template && match_arity active
  | _ => true
  end.

Lemma match_arity_list_spec : forall es,
  forallb (fun b=>b) (List.map match_arity es)=true <-> forall e, In e es -> match_arity e=true.
Proof.
  intros es. rewrite forallb_forall. split.
  - intros H e Hin. apply H. apply in_map; exact Hin.
  - intros H b Hin. apply in_map_iff in Hin as [e [He Hin]]. subst b. apply H; exact Hin.
Qed.

Lemma match_arity_substs : forall x v ty es,
  (forall e, In e es -> match_arity (subst x (Val v ty) e)=match_arity e) ->
  List.map match_arity (substs subst x (Val v ty) es)=List.map match_arity es.
Proof.
  intros x v ty es; induction es as [|e es IH]; intros H; simpl; auto.
  rewrite H by (left; reflexivity). rewrite IH; auto. intros child Hin; apply H; right; exact Hin.
Qed.

Lemma match_arity_branches : forall x v ty es ps,
  (forall e, In e es -> match_arity (subst x (Val v ty) e)=match_arity e) ->
  List.map match_arity (subst_match_branches subst x (Val v ty) ps es)=List.map match_arity es.
Proof.
  intros x v ty es; induction es as [|e es IH]; intros ps H; destruct ps; simpl; auto.
  destruct (x_in_pattern x p); simpl; rewrite IH; auto.
  - intros child Hin; apply H; right; exact Hin.
  - rewrite H by (left; reflexivity); reflexivity.
  - intros child Hin; apply H; right; exact Hin.
Qed.

Lemma subst_match_branches_length : forall x replacement ps es,
  length (subst_match_branches subst x replacement ps es)=length es.
Proof.
  intros x replacement ps es; revert ps; induction es as [|e es IH]; intros ps; destruct ps; simpl; auto.
Qed.

Theorem value_substitution_preserves_match_arity : forall x v ty e,
  match_arity (subst x (Val v ty) e)=match_arity e.
Proof.
  intros x v ty e; induction e using expr_ind_rec; cbn [subst match_arity];
    try solve [reflexivity];
    try solve [congruence];
    try solve [rewrite match_arity_substs by assumption; congruence].
  - destruct (Pos.eqb x x0); reflexivity.
  - destruct (Pos.eqb x x0); cbn [match_arity]; congruence.
  - rewrite subst_match_branches_length. rewrite match_arity_branches by assumption. congruence.
  - destruct (Pos.eqb x a); reflexivity.
Qed.

Lemma notin_seq_cat : forall x (xs ys : list ident),
  ~In x xs -> ~In x ys -> ~In x (seq.cat xs ys).
Proof. intros x xs ys Hx Hy. change (~In x (List.app xs ys)). rewrite in_app_iff; tauto. Qed.

Lemma list_substitution_notin : forall es x v ty,
  (forall e, In e es -> ~In x (free_variables (subst x (Val v ty) e))) ->
  ~In x (expression_list_variables (substs subst x (Val v ty) es)).
Proof.
  induction es as [|e es IH]; intros x v ty H; [simpl; tauto|].
  change (~In x (free_variables (subst x (Val v ty) e) ++ expression_list_variables(substs subst x (Val v ty) es))).
  rewrite in_app_iff; intros [Hin|Hin].
  - exact (H e (or_introl eq_refl) Hin).
  - eapply IH; [|exact Hin]. intros child Hchild; apply H; right; exact Hchild.
Qed.

Theorem match_arity_value_substitution_notin : forall e,
  match_arity e=true -> forall x v ty, ~In x (free_variables (subst x (Val v ty) e)).
Proof.
  intros e; induction e using expr_ind_rec; intros Hvalid target replacement annotation;
    cbn [match_arity] in Hvalid; cbn [subst free_variables];
    try solve [simpl; tauto];
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    try solve [eauto].
  all: repeat match goal with
    | IH : match_arity ?child = true -> forall x v ty, _, Hv : match_arity ?child = true |- _ =>
      let Hnot := fresh "Hnot" in pose proof (IH Hv target replacement annotation) as Hnot; clear IH
    end.
  all: try solve [repeat rewrite in_app_iff; intuition].
  all: try solve [
    match goal with |- ~In _ (seq.flatten (seq.map _ (substs _ _ _ ?es))) =>
      change (~In target (expression_list_variables (substs subst target (Val replacement annotation) es)));
      apply list_substitution_notin; intros child Hin;
      match goal with IH : forall child, In child es -> _, Hv : forallb _ (List.map match_arity es)=true |- _ =>
        apply IH; [exact Hin|apply (proj1 (match_arity_list_spec es) Hv); exact Hin] end end].
  all: try solve [eauto using notin_seq_cat].
  - destruct (Pos.eqb target x) eqn:Heq; simpl; [tauto|].
    apply Pos.eqb_neq in Heq; intuition congruence.
  - apply notin_seq_cat; [assumption|].
    change (~In target (expression_list_variables (substs subst target (Val replacement annotation) es))).
    apply list_substitution_notin; intros child Hin.
    match goal with IH : forall child, In child es -> _, Hv : forallb _ (List.map match_arity es)=true |- _ =>
      apply IH; [exact Hin|apply (proj1 (match_arity_list_spec es) Hv); exact Hin] end.
  - destruct (Pos.eqb target x) eqn:Heq; cbn [free_variables]; apply notin_seq_cat; try assumption;
      intro Hin; apply in_remove in Hin as [Hin Hneq].
    + apply Pos.eqb_eq in Heq; subst; contradiction.
    + contradiction.
  - apply notin_seq_cat; [assumption|].
    eapply substituted_scoped_branches_notin.
    + apply Nat.eqb_eq; eassumption.
    + intros n pat branch Hp Hb.
      match goal with IH : forall child, In child es -> _, Hv : forallb _ (List.map match_arity es)=true |- _ =>
        apply IH; [eapply nth_error_In; exact Hb|apply (proj1 (match_arity_list_spec es) Hv); eapply nth_error_In; exact Hb] end.
  - destruct (Pos.eqb target a) eqn:Heq; simpl; [tauto|].
    apply Pos.eqb_neq in Heq; intuition congruence.
Qed.

Lemma typed_match_arity_mutual :
  (forall env Gamma Sigma es ef ts, type_exprs env Gamma Sigma es ef ts ->
    forallb (fun b=>b) (List.map match_arity es)=true) /\
  (forall env Gamma Sigma e ef ty, type_expr env Gamma Sigma e ef ty -> match_arity e=true).
Proof.
  apply type_exprs_type_expr_ind_mut; intros;
    cbn [match_arity List.map forallb];
    repeat rewrite andb_true_iff; try solve [intuition].
  split; [assumption|]. split.
  - apply Nat.eqb_eq; assumption.
  - apply match_arity_list_spec. intros branch Hin.
    apply In_nth_error in Hin as [n Hnth].
    match goal with Hlen : length ?ps = length ?es |- _ =>
      assert (Hbound : (n < length ps)%nat) by
        (rewrite Hlen; apply nth_error_Some; rewrite Hnth; discriminate);
      destruct (nth_error ps n) as [pat|] eqn:Hpat;
      [|apply nth_error_None in Hpat; lia]
    end.
    eauto.
Qed.

Theorem typed_match_arity : forall env Gamma Sigma e ef ty,
  type_expr env Gamma Sigma e ef ty -> match_arity e=true.
Proof. exact (proj2 typed_match_arity_mutual). Qed.

Theorem arity_value_substitution_removes_variable : forall e x v ty,
  match_arity e=true ->
  incl (free_variables (subst x (Val v ty) e)) (remove ident_eq x (free_variables e)).
Proof.
  intros * Hvalid y Hin. apply in_in_remove.
  - intro Heq; subst y. eapply match_arity_value_substitution_notin; eauto.
  - eapply value_substitution_free_variables; exact Hin.
Qed.
Print Assumptions typed_match_arity.
Print Assumptions arity_value_substitution_removes_variable.
