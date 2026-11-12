(* Value substitution preserves initialized captured environments; CallFrame
   boundaries retain their callee scope. No value-type restriction is imposed. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas.
Require Import BeePL_substitution_proofs BeePL_runtime_locations BeePL_aggregate_memory.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_initialized_runtime.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Lemma substs_initialized_runtime_frames : forall bge Sigma layout objects packets x v ty es,
  all_expr_locations (initialized_runtime_frames bge Sigma layout objects packets) es ->
  (forall e, In e es -> initialized_runtime_frames bge Sigma layout objects packets e ->
    initialized_runtime_frames bge Sigma layout objects packets (subst x (Val v ty) e)) ->
  all_expr_locations (initialized_runtime_frames bge Sigma layout objects packets) (substs subst x (Val v ty) es).
Proof.
  intros bge Sigma layout objects packets x v ty es. induction es; intros Hall Hstep; simpl; constructor.
  - apply Hstep; [left; reflexivity | destruct Hall; assumption].
  - apply IHes; [destruct Hall; assumption |]. intros e Hin. apply Hstep. right; exact Hin.
Qed.

Lemma match_substs_initialized_runtime_frames : forall bge Sigma layout objects packets x v ty es ps,
  all_expr_locations (initialized_runtime_frames bge Sigma layout objects packets) es ->
  (forall e, In e es -> initialized_runtime_frames bge Sigma layout objects packets e ->
    initialized_runtime_frames bge Sigma layout objects packets (subst x (Val v ty) e)) ->
  all_expr_locations (initialized_runtime_frames bge Sigma layout objects packets)
    (subst_match_branches subst x (Val v ty) ps es).
Proof.
  intros bge Sigma layout objects packets x v ty es. induction es; intros ps Hall Hstep; simpl; [constructor |].
  destruct ps as [|pat ps]; [exact Hall |]. simpl. destruct Hall as [Hhead Htail].
  destruct (x_in_pattern x pat); constructor; auto.
  - apply IHes; auto. intros e Hin. apply Hstep. right; exact Hin.
  - apply Hstep; auto. left; reflexivity.
  - apply IHes; auto. intros e Hin. apply Hstep. right; exact Hin.
Qed.

Theorem value_substitution_initialized_runtime_frames : forall bge Sigma layout objects packets x v ty e,
  initialized_runtime_frames bge Sigma layout objects packets e ->
  initialized_runtime_frames bge Sigma layout objects packets (subst x (Val v ty) e).
Proof.
  intros bge Sigma layout objects packets x v ty e. induction e using expr_ind_rec;
    intros Hframes; cbn [subst initialized_runtime_frames] in *;
    try solve [intuition eauto using substs_initialized_runtime_frames, match_substs_initialized_runtime_frames].
  - destruct (Pos.eqb x x0); simpl; auto.
  - destruct (Pos.eqb x x0); simpl; intuition.
  - destruct (Pos.eqb x a); simpl; auto.
Qed.

Theorem initialized_bind_value_preservation :
  forall bge Gamma Sigma p vm m objects layout packets x v tx body rt ef m' vm' e',
  initialized_runtime_configuration bge Gamma Sigma vm m objects layout packets (Bind x tx (Val v tx) body rt) ef rt ->
  ssem_expr bge p vm m (Bind x tx (Val v tx) body rt) m' vm' e' ->
  m' = m /\ vm' = vm /\ initialized_runtime_configuration bge Gamma Sigma vm' m' objects layout packets e' ef rt.
Proof.
  intros bge Gamma Sigma p vm m objects layout packets x v tx body rt ef m' vm' e'
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
      eapply value_substitution_initialized_runtime_frames. destruct Hframes; assumption.
Qed.

Print Assumptions value_substitution_initialized_runtime_frames.
Print Assumptions initialized_bind_value_preservation.

Theorem initialized_bind_value_progress :
  forall ge Gamma Sigma p vm m objects cells packets x v tx body rt ef,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Bind x tx (Val v tx) body rt) ef rt ->
  ssem_expr ge p vm m (Bind x tx (Val v tx) body rt) m vm (subst x (Val v tx) body) /\
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (subst x (Val v tx) body) ef rt.
Proof.
  intros ge Gamma Sigma p vm m objects cells packets x v tx body rt ef Hconfig.
  destruct Hconfig as [Hheap Htyped Hlocations Hframes].
  destruct (bind_typing_components _ _ _ _ _ _ _ _ _ Htyped)
    as [ei [eb [Hef [Hinit Hbody]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hbody) as Hannotation.
  assert (Hstep : ssem_expr ge p vm m (Bind x tx (Val v tx) body rt) m vm (subst x (Val v tx) body)).
  { rewrite <- Hannotation. apply ssem_bind2. apply substitution_function_relation. }
  split; [exact Hstep|].
  eapply (proj2 (proj2 (initialized_bind_value_preservation ge Gamma Sigma p vm m objects cells packets
    x v tx body rt ef m vm (subst x (Val v tx) body) ltac:(constructor; assumption) Hstep))).
Qed.

(* Conditional context lifting: the initializer's preservation/evolution is
   supplied by the recursive case of the eventual whole-language theorem. *)
Theorem initialized_bind_initializer_step :
  forall ge Gamma Sigma p vm m objects cells packets x tx init body rt ei eb
    Sigma' vm' m' objects' cells' packets' init' ei',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Bind x tx init body rt) (ei ++ eb) rt ->
  type_expr ge.(genv_cenv) Gamma Sigma init ei tx ->
  type_expr ge.(genv_cenv) (extend_context Gamma x tx) Sigma body eb rt ->
  ssem_expr ge p vm m init m' vm' init' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' init' ei' tx ->
  sub_effect ei' ei = true ->
  ssem_expr ge p vm m (Bind x tx init body rt) m' vm' (Bind x tx init' body rt) /\
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Bind x tx init' body rt) (ei' ++ eb) rt /\
  sub_effect (ei' ++ eb) (ei ++ eb) = true.
Proof.
  intros ge Gamma Sigma p vm m objects cells packets x tx init body rt ei eb
    Sigma' vm' m' objects' cells' packets' init' ei' [Hheap Htyped [Hinitloc Hbodyloc] [Hinitframes Hbodyframes]]
    Hinit Hbody Hstep Hupdate [Hheap' Hinit' Hinitloc' Hinitframes'] Hsub.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hbody) as Hannotation.
  destruct Hupdate as [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents].
  split.
  - rewrite <- Hannotation. apply ssem_bind1. exact Hstep.
  - split.
    + constructor.
      * exact Hheap'.
      * apply ty_bind; [exact Hinit'|]. eapply (proj2 typing_store_extension); eauto.
      * split; [exact Hinitloc'|]. eapply runtime_locations_monotone; [|exact Hbodyloc].
        eapply packet_heap_locations_monotone; eauto.
      * split; [exact Hinitframes'|]. eapply initialized_runtime_frames_evolve; eauto.
    + apply sub_effect_concat; [exact Hsub|apply sub_effect_refl].
Qed.

Print Assumptions initialized_bind_value_progress.
Print Assumptions initialized_bind_initializer_step.
