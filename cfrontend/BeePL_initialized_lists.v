(* Expression lists share the initialized heap and preserve suspended arguments
   across a child step. The expression case is an explicit induction hypothesis. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_auxlemmas BeePL_runtime_locations.
Require Import BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_aggregate_memory BeePL_initialized_runtime.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Record initialized_list_configuration (ge : genv) (Gamma : ty_context) (Sigma : store_context)
    (vm : vmap) (m : Mem.mem) (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations)
    (es : list expr) (ef : effect) (ts : list type) : Prop := {
  initialized_list_heap : initialized_heap_state ge Gamma Sigma vm m objects cells packets;
  initialized_list_typing : type_exprs ge.(genv_cenv) Gamma Sigma es ef ts;
  initialized_list_locations : all_expr_locations (runtime_locations (packet_heap_locations ge cells objects packets)) es;
  initialized_list_frames : all_expr_locations (initialized_runtime_frames ge Sigma cells objects packets) es
}.

Lemma initialized_configuration_reframe :
  forall ge Gamma Sigma vm m objects cells packets e ef ty Sigma' vm' m' objects' cells' packets',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_heap_state ge Gamma Sigma' vm' m' objects' cells' packets' ->
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' e ef ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets e ef ty Sigma' vm' m' objects' cells' packets' Hconfig Hupdate Hheap.
  destruct (initialized_runtime_configuration_evolve _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hupdate)
    as [Hheap0 Htyping Hlocations Hframes]. constructor; assumption.
Qed.

Lemma initialized_list_configuration_reframe :
  forall ge Gamma Sigma vm m objects cells packets es ef ts Sigma' vm' m' objects' cells' packets',
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_heap_state ge Gamma Sigma' vm' m' objects' cells' packets' ->
  initialized_list_configuration ge Gamma Sigma' vm' m' objects' cells' packets' es ef ts.
Proof.
  intros ge Gamma Sigma vm m objects cells packets es ef ts Sigma' vm' m' objects' cells' packets'
    [Hheap Htyping Hlocations Hframes] [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents] Hheap'.
  constructor; [exact Hheap' | | |].
  - eapply (proj1 typing_store_extension); eauto.
  - rewrite all_expr_locations_Forall, Forall_forall in *. intros e Hin.
    eapply runtime_locations_monotone; [|apply Hlocations; exact Hin].
    apply packet_heap_locations_monotone; assumption.
  - rewrite all_expr_locations_Forall, Forall_forall in *. intros e Hin.
    eapply initialized_runtime_frames_evolve; eauto.
Qed.

Lemma initialized_list_cons : forall ge Gamma Sigma vm m objects cells packets e es ef efs ty ts,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty ->
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets es efs ts ->
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets (e :: es) (ef ++ efs) (ty :: ts).
Proof.
  intros ge Gamma Sigma vm m objects cells packets e es ef efs ty ts
    [Hheap Htyped Hlocations Hframes] [Hheap' Htyped' Hlocations' Hframes'].
  constructor; simpl; auto. econstructor; eauto.
Qed.

Theorem initialized_list_preservation_from_expressions :
  forall ge Gamma Sigma vm m objects cells packets p es ef ts final vm' es',
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts ->
  (forall e, In e es -> forall effect ty,
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect ty ->
    forall nextM nextVm next,
    ssem_expr ge p vm m e nextM nextVm next ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      initialized_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' ty /\
      sub_effect effect' effect = true) ->
  ssem_exprs ge p vm m es final vm' es' ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    initialized_list_configuration ge Gamma Sigma' vm' final objects' cells' packets' es' ef' ts /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p es. induction es as [|e es IH];
    intros ef ts final vm' es' Hconfig Hlocal Hstep.
  - destruct Hconfig as [Hheap Htyped Hloc Hframes]. inversion Htyped; subst.
    inversion Hstep; subst. exists Sigma, objects, cells, packets, []. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [constructor; assumption || constructor | apply sub_effect_refl].
  - destruct Hconfig as [Hheap Htyped [Heloc HtailLoc] [Heframes HtailFrames]].
    inversion Htyped; subst.
    match goal with
    | Hh : type_expr _ _ _ e ?he ?ht,
      Ht : type_exprs _ _ _ es ?te ?tt |- _ =>
      assert (Hhead : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e he ht)
        by (constructor; assumption);
      assert (Htail : initialized_list_configuration ge Gamma Sigma vm m objects cells packets es te tt)
        by (constructor; assumption)
    end.
    inversion Hstep; subst.
    + match goal with Hchild : ssem_expr _ _ _ _ e _ _ _ |- _ =>
        destruct (Hlocal e (or_introl eq_refl) _ _ Hhead _ _ _ Hchild)
          as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [Hnew Hsub]]]]]]]
      end.
      pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
      pose proof (initialized_list_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Htail Hupdate Hheap') as Htail'.
      eexists; eexists; eexists; eexists; eexists. split; [exact Hupdate |]. split.
      * eapply initialized_list_cons; eauto.
      * apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
    + match goal with HtailStep : ssem_exprs _ _ _ _ es _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ Htail ltac:(intros child Hin; apply Hlocal; right; exact Hin) HtailStep)
          as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [Hnew Hsub]]]]]]]
      end.
      pose proof (initialized_list_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
      pose proof (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hhead Hupdate Hheap') as Hhead'.
      eexists; eexists; eexists; eexists; eexists. split; [exact Hupdate |]. split.
      * eapply initialized_list_cons; eauto.
      * apply sub_effect_concat; [apply sub_effect_refl | exact Hsub].
Qed.

Theorem initialized_list_progress_from_expressions :
  forall ge Gamma Sigma vm m objects cells packets p es ef ts,
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts ->
  (forall e, In e es -> forall effect ty,
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect ty ->
    (exists v annotation, e = Val v annotation) \/
    exists final vm' e', ssem_expr ge p vm m e final vm' e') ->
  exists final vm' es', ssem_exprs ge p vm m es final vm' es'.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p es. induction es as [|e es IH]; intros ef ts Hconfig Hlocal.
  - exists m, vm, []. constructor.
  - destruct Hconfig as [Hheap Htyped [Heloc HtailLoc] [Heframes HtailFrames]].
    inversion Htyped; subst.
    match goal with Hh : type_expr _ _ _ e ?he ?ht, Ht : type_exprs _ _ _ es ?te ?tt |- _ =>
      assert (Hhead : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e he ht)
        by (constructor; assumption);
      assert (Htail : initialized_list_configuration ge Gamma Sigma vm m objects cells packets es te tt)
        by (constructor; assumption)
    end.
    destruct (Hlocal e (or_introl eq_refl) _ _ Hhead) as [[v [annotation He]] | [final [vm' [e' Hstep]]]].
    + subst e. destruct (IH _ _ Htail ltac:(intros child Hin; apply Hlocal; right; exact Hin))
        as [final [vm' [es' Hstep]]].
      exists final, vm', (Val v annotation :: es'). apply ssem_cons2; exact Hstep.
    + exists final, vm', (e' :: es). apply ssem_cons1; exact Hstep.
Qed.

Print Assumptions initialized_list_preservation_from_expressions.
Print Assumptions initialized_list_progress_from_expressions.
