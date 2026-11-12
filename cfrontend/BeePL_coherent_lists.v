(* List evaluation retains the coherent layout produced by the actual child
   step. The child premise is the structural induction hypothesis, quantified
   over the expression members, not an assumption that the parent is safe. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_auxlemmas BeePL_runtime_locations.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_aggregate_memory.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Require Import BeePL_layout_coherence BeePL_packet_state BeePL_packet_bindings.
Import ListNotations.

Definition coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts : Prop :=
  initialized_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts /\ coherent_layout cells.

Theorem coherent_list_preservation_from_expressions :
  forall ge Gamma Sigma vm m objects cells packets p es ef ts final vm' es',
  coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts ->
  (forall e, In e es -> forall effect ty,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect ty ->
    forall nextM nextVm next,
    ssem_expr ge p vm m e nextM nextVm next ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' ty /\
      sub_effect effect' effect = true) ->
  ssem_exprs ge p vm m es final vm' es' ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_list_configuration ge Gamma Sigma' vm' final objects' cells' packets' es' ef' ts /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p es. induction es as [|e es IH];
    intros ef ts final vm' es' [Hconfig Hcoherent] Hlocal Hstep.
  - destruct Hconfig as [Hheap Htyped Hloc Hframes]. inversion Htyped; subst.
    inversion Hstep; subst. exists Sigma, objects, cells, packets, []. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [split; [constructor; assumption || constructor |exact Hcoherent] | apply sub_effect_refl].
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
        destruct (Hlocal e (or_introl eq_refl) _ _ (conj Hhead Hcoherent) _ _ _ Hchild)
          as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
      end.
      pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
      pose proof (initialized_list_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Htail Hupdate Hheap') as Htail'.
      eexists; eexists; eexists; eexists; eexists. split; [exact Hupdate |]. split.
      * split; [eapply initialized_list_cons; eauto |exact Hcoherent'].
      * apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
    + match goal with HtailStep : ssem_exprs _ _ _ _ es _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ (conj Htail Hcoherent) ltac:(intros child Hin; apply Hlocal; right; exact Hin) HtailStep)
          as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
      end.
      pose proof (initialized_list_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
      pose proof (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hhead Hupdate Hheap') as Hhead'.
      eexists; eexists; eexists; eexists; eexists. split; [exact Hupdate |]. split.
      * split; [eapply initialized_list_cons; eauto |exact Hcoherent'].
      * apply sub_effect_concat; [apply sub_effect_refl | exact Hsub].
Qed.

Theorem coherent_list_progress_from_expressions :
  forall ge Gamma Sigma vm m objects cells packets p es ef ts,
  coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts ->
  (forall e, In e es -> forall effect ty,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect ty ->
    (exists v annotation, e = Val v annotation) \/
    exists final vm' e', ssem_expr ge p vm m e final vm' e') ->
  exists final vm' es', ssem_exprs ge p vm m es final vm' es'.
Proof.
  intros * [Hconfig Hcoherent] Hlocal.
  eapply initialized_list_progress_from_expressions; [exact Hconfig |].
  intros e Hin effect ty Hchild. apply (Hlocal e Hin effect ty); split; assumption.
Qed.

Print Assumptions coherent_list_preservation_from_expressions.
Print Assumptions coherent_list_progress_from_expressions.
