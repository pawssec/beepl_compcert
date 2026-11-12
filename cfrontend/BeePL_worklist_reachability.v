(* Executable reachability with a visited worklist. The finite universe occurs
   only in the proof: callers may supply an arithmetic cardinality bound. *)
Require Import List Bool Lia.
Require Import BeePL_finite_reachability.
Import ListNotations.
Section Worklist.
Context {A : Type}.
Variable same : forall x y : A, {x = y} + {x <> y}.
Variable successors : A -> list A.

Definition successor_edge (x y : A) : bool :=
  if in_dec same y (successors x) then true else false.

Definition pending_without (seen pending : list A) : list A :=
  filter (fun x => if in_dec same x seen then false else true) pending.

Lemma pending_without_in : forall seen pending x,
  In x (pending_without seen pending) <-> In x pending /\ ~ In x seen.
Proof.
  intros. unfold pending_without. rewrite filter_In.
  destruct (in_dec same x seen); simpl; intuition discriminate.
Qed.

Fixpoint worklist_search (fuel : nat) (seen pending : list A) : list A * list A :=
  match fuel, pending with
  | _, [] => (seen, [])
  | O, _ => (seen, pending)
  | S rest, x :: xs =>
      worklist_search rest (x :: seen)
        (pending_without (x :: seen) (xs ++ successors x))
  end.

Definition worklist_reach (bound : nat) (start target : A) : bool :=
  if in_dec same target (fst (worklist_search bound [] [start])) then true else false.

Lemma successor_edge_spec : forall x y,
  successor_edge x y = true <-> In y (successors x).
Proof. intros; unfold successor_edge; destruct (in_dec same y (successors x)); intuition discriminate. Qed.

Lemma worklist_discovered_step : forall seen x pending y,
  In y ((x :: seen) ++ pending_without (x :: seen) (pending ++ successors x)) <->
  In y (seen ++ x :: pending) \/ In y (successors x).
Proof.
  intros. repeat rewrite in_app_iff. rewrite pending_without_in, in_app_iff.
  simpl. destruct (in_dec same y (x :: seen)); simpl in *; intuition congruence.
Qed.

Record worklist_invariant (universe : list A) (start : A)
    (seen pending : list A) : Prop := {
  worklist_seen_unique : NoDup seen;
  worklist_separate : forall x, In x pending -> ~ In x seen;
  worklist_domain : incl (seen ++ pending) universe;
  worklist_start : In start (seen ++ pending);
  worklist_sound : forall y, In y (seen ++ pending) -> finite_walk successor_edge start y;
  worklist_closed : forall x y, In x seen -> In y (successors x) -> In y (seen ++ pending)
}.

Lemma worklist_invariant_step : forall universe start seen x pending,
  (forall a b, In a universe -> In b (successors a) -> In b universe) ->
  worklist_invariant universe start seen (x :: pending) ->
  worklist_invariant universe start (x :: seen)
    (pending_without (x :: seen) (pending ++ successors x)).
Proof.
  intros universe start seen x pending Hclosed Hinv.
  destruct Hinv as [Hunique Hseparate Hdomain Hstart Hsound Hfrontier].
  assert (Hx : In x (seen ++ x :: pending)) by (apply in_app_iff; right; simpl; auto).
  constructor.
  - constructor; [apply Hseparate; simpl; auto|exact Hunique].
  - intros y Hin. apply pending_without_in in Hin; tauto.
  - intros y Hin. apply worklist_discovered_step in Hin as [Hin|Hin].
    + apply Hdomain; exact Hin.
    + eapply Hclosed; [apply Hdomain; exact Hx|exact Hin].
  - apply worklist_discovered_step; auto.
  - intros y Hin. apply worklist_discovered_step in Hin as [Hin|Hin].
    + apply Hsound; exact Hin.
    + eapply finite_walk_trans; [apply Hsound; exact Hx|].
      eapply finite_walk_cons; [apply successor_edge_spec; exact Hin|constructor].
  - intros a b [Heq|Hin] Hnext.
    + subst a. apply worklist_discovered_step; auto.
    + apply worklist_discovered_step. left. eapply Hfrontier; eauto.
Qed.

Lemma worklist_search_preserves : forall fuel universe start seen pending,
  (forall a b, In a universe -> In b (successors a) -> In b universe) ->
  worklist_invariant universe start seen pending ->
  worklist_invariant universe start
    (fst (worklist_search fuel seen pending)) (snd (worklist_search fuel seen pending)).
Proof.
  induction fuel; intros universe start seen pending Hclosed Hinv; destruct pending;
    simpl; try exact Hinv.
  apply IHfuel; [exact Hclosed|]. apply worklist_invariant_step; assumption.
Qed.

Lemma worklist_bound_exhausts : forall fuel universe start seen pending,
  (forall a b, In a universe -> In b (successors a) -> In b universe) ->
  worklist_invariant universe start seen pending ->
  length universe <= length seen + fuel ->
  snd (worklist_search fuel seen pending) = [].
Proof.
  induction fuel; intros universe start seen pending Hclosed Hinv Hbound.
  - destruct pending as [|x pending]; [reflexivity|].
    destruct Hinv as [Hunique Hseparate Hdomain Hstart Hsound Hfrontier].
    assert (Hnew : NoDup (x :: seen)) by (constructor; [apply Hseparate; simpl; auto|assumption]).
    assert (Hincl : incl (x :: seen) universe).
    { intros y [Heq|Hin]; apply Hdomain; apply in_app_iff;
        [right; simpl; auto|left; exact Hin]. }
    pose proof (NoDup_incl_length Hnew Hincl). simpl in *. lia.
  - destruct pending as [|x pending]; [reflexivity|]. simpl.
    apply IHfuel with (universe := universe) (start := start).
    + exact Hclosed.
    + apply worklist_invariant_step; assumption.
    + simpl; lia.
Qed.

Lemma worklist_initial : forall universe start,
  In start universe -> worklist_invariant universe start [] [start].
Proof.
  intros universe start Hin. constructor; simpl.
  - constructor.
  - intuition.
  - intros y [Heq|Hfalse]; [subst; assumption|contradiction].
  - auto.
  - intros y [Heq|Hfalse]; [subst; constructor|contradiction].
  - contradiction.
Qed.

Theorem worklist_reach_correct : forall universe bound start target,
  (forall a b, In a universe -> In b (successors a) -> In b universe) ->
  In start universe -> length universe <= bound ->
  (worklist_reach bound start target = true <-> finite_walk successor_edge start target).
Proof.
  intros universe bound start target Hclosed Hstart Hbound.
  pose proof (worklist_initial universe start Hstart) as Hinitial.
  pose proof (worklist_search_preserves bound universe start [] [start] Hclosed Hinitial) as Hfinal.
  pose proof (worklist_bound_exhausts bound universe start [] [start] Hclosed Hinitial Hbound) as Hempty.
  destruct (worklist_search bound [] [start]) as [seen pending] eqn:Hsearch.
  simpl in Hfinal, Hempty. subst pending.
  destruct Hfinal as [Hunique Hseparate Hdomain Hroot Hsound Hfrontier].
  rewrite app_nil_r in Hroot, Hsound, Hfrontier.
  assert (Hcomplete : forall x y, In x seen -> finite_walk successor_edge x y -> In y seen).
  { intros x y Hin Hwalk. revert Hin. induction Hwalk; intro Hin; [assumption|].
    apply IHHwalk. eapply Hfrontier; [exact Hin|]. apply successor_edge_spec; assumption. }
  unfold worklist_reach. rewrite Hsearch. simpl.
  destruct (in_dec same target seen) as [Hin|Hmissing].
  - split; [intros; apply Hsound; assumption|reflexivity].
  - split; [discriminate|]. intro Hwalk. exfalso. apply Hmissing. eapply Hcomplete; eauto.
Qed.

Theorem worklist_walk_decidable : forall universe bound start target,
  (forall a b, In a universe -> In b (successors a) -> In b universe) ->
  In start universe -> length universe <= bound ->
  {finite_walk successor_edge start target} + {~ finite_walk successor_edge start target}.
Proof.
  intros. destruct (worklist_reach bound start target) eqn:Hreach.
  - left. eapply worklist_reach_correct; eauto.
  - right. intro Hwalk. apply (proj2 (worklist_reach_correct universe bound start target H H0 H1)) in Hwalk.
    congruence.
Qed.
End Worklist.
Print Assumptions worklist_reach_correct.
Print Assumptions worklist_walk_decidable.
