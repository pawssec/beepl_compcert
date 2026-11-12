(* Finite graph reachability using every listed vertex as an intermediate.
   The recursion bound is the graph's vertex list, not guessed path fuel. *)
Require Import List Bool.
Import ListNotations.
Section FiniteReachability.
Context {A : Type}.
Variable same : forall x y : A, {x = y} + {x <> y}.
Variable edge : A -> A -> bool.

Inductive finite_walk : A -> A -> Prop :=
| finite_walk_refl : forall x, finite_walk x x
| finite_walk_cons : forall x y z, edge x y = true -> finite_walk y z -> finite_walk x z.

Lemma finite_walk_trans : forall x y z,
  finite_walk x y -> finite_walk y z -> finite_walk x z.
Proof. intros x y z Hxy Hyz; induction Hxy; eauto using finite_walk_cons. Qed.

Fixpoint finite_reach (vertices : list A) (x y : A) : bool :=
  match vertices with
  | [] => if same x y then true else edge x y
  | middle :: rest => finite_reach rest x y ||
      (finite_reach rest x middle && finite_reach rest middle y)
  end.

Lemma finite_reach_refl : forall vertices x, finite_reach vertices x x = true.
Proof.
  induction vertices; intro x; simpl.
  - destruct (same x x); congruence.
  - rewrite IHvertices; reflexivity.
Qed.

Lemma finite_reach_edge : forall vertices x y,
  edge x y = true -> finite_reach vertices x y = true.
Proof.
  induction vertices; intros x y H; simpl.
  - destruct (same x y); auto.
  - rewrite IHvertices by exact H; reflexivity.
Qed.

Lemma finite_reach_sound : forall vertices x y,
  finite_reach vertices x y = true -> finite_walk x y.
Proof.
  induction vertices as [|middle rest IH]; intros x y H; simpl in H.
  - destruct (same x y); subst; eauto using finite_walk_refl, finite_walk_cons.
  - apply orb_true_iff in H as [Hdirect|Hvia].
    + apply IH; exact Hdirect.
    + apply andb_true_iff in Hvia as [Hleft Hright].
      eapply finite_walk_trans; eauto.
Qed.

Lemma finite_reach_through_member : forall vertices middle x y,
  In middle vertices -> finite_reach vertices x middle = true ->
  finite_reach vertices middle y = true -> finite_reach vertices x y = true.
Proof.
  induction vertices as [|head rest IH]; intros middle x y Hin Hleft Hright; [contradiction|].
  simpl in Hin, Hleft, Hright |- *.
  destruct Hin as [Heq|Hin].
  - subst middle. rewrite finite_reach_refl in Hleft, Hright.
    rewrite andb_true_r, orb_diag in Hleft.
    rewrite andb_true_l, orb_diag in Hright.
    apply orb_true_iff; right. apply andb_true_iff; auto.
  - apply orb_true_iff in Hleft as [Hleft|Hleft];
      apply orb_true_iff in Hright as [Hright|Hright].
    + apply orb_true_iff; left. eapply IH; eauto.
    + apply andb_true_iff in Hright as [Hmh Hhy].
      apply orb_true_iff; right. apply andb_true_iff; split; [eapply IH; eauto|exact Hhy].
    + apply andb_true_iff in Hleft as [Hxh Hhm].
      apply orb_true_iff; right. apply andb_true_iff; split; [exact Hxh|eapply IH; eauto].
    + apply andb_true_iff in Hleft as [Hxh Hhm].
      apply andb_true_iff in Hright as [Hmh Hhy].
      apply orb_true_iff; right. apply andb_true_iff; auto.
Qed.

Theorem finite_reach_complete : forall vertices,
  (forall x y, In x vertices -> edge x y = true -> In y vertices) ->
  forall x y, In x vertices -> finite_walk x y -> finite_reach vertices x y = true.
Proof.
  intros vertices Hclosed x y Hin Hwalk. revert Hin.
  induction Hwalk; intro Hin.
  - apply finite_reach_refl.
  - assert (Hmiddle : In y vertices) by (eapply Hclosed; eauto).
    eapply finite_reach_through_member with (middle := y); eauto using finite_reach_edge.
Qed.

Theorem finite_walk_decidable : forall vertices,
  (forall x y, In x vertices -> edge x y = true -> In y vertices) ->
  forall x y, In x vertices -> {finite_walk x y} + {~ finite_walk x y}.
Proof.
  intros vertices Hclosed x y Hin.
  destruct (finite_reach vertices x y) eqn:Hreach.
  - left. eapply finite_reach_sound; eauto.
  - right. intro Hwalk. pose proof (finite_reach_complete vertices Hclosed x y Hin Hwalk). congruence.
Qed.
End FiniteReachability.
Print Assumptions finite_walk_decidable.
