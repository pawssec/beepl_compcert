(* The structure-field expression case uses the actual program layout at its
   evaluated head and the structural operand hypothesis in its context. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_type_equality.
Require Import BeePL_runtime_locations BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_fields BeePL_coherent_memory_contexts.
Import ListNotations.

Lemma field_typing_operand : forall env Gamma Sigma operand field result ef,
  type_expr env Gamma Sigma (Sfield operand field result) ef result ->
  exists receiver, type_expr env Gamma Sigma operand ef receiver.
Proof. intros * Htyped; inversion Htyped; subst; eauto. Qed.

Lemma typed_field_value_address : forall env Gamma Sigma v annotation field result ef,
  type_expr env Gamma Sigma (Sfield (Val v annotation) field result) ef result ->
  exists b offset, v = Vloc b offset.
Proof.
  intros * Htyped. inversion Htyped; subst.
  match goal with Hshape : _ \/ _ |- _ =>
    destruct Hshape as [Hshape|Hshape]; apply eq_type_sound in Hshape; subst end.
  all: match goal with Hvalue : type_expr _ _ _ (Val _ _) _ _ |- _ =>
    inversion Hvalue; subst; eauto end.
Qed.

Theorem coherent_field_progress_from_operand :
  forall p Gamma Sigma vm m objects cells packets operand field result ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sfield operand field result) ef result ->
  (forall receiver,
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets operand ef receiver ->
    (exists v annotation, operand = Val v annotation) \/
    exists final vm' next, ssem_expr (globalenv p) p vm m operand final vm' next) ->
  exists final vm' next, ssem_expr (globalenv p) p vm m (Sfield operand field result) final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (field_typing_operand _ _ _ _ _ _ _ Htyped) as [receiver Hoperand].
  assert (HoperandConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    operand ef receiver) by (split; [constructor; assumption |exact Hcoherent]).
  destruct (Hchild receiver HoperandConfig) as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst operand. destruct (typed_field_value_address _ _ _ _ _ _ _ _ Htyped) as [b [offset Hv]]. subst v.
    destruct (coherent_field_read_progress (globalenv p) p Gamma Sigma vm m objects cells packets b offset annotation field result ef eq_refl Hconfig)
      as [objects' [value [Hstep Hrest]]]. do 3 eexists; exact Hstep.
  - do 3 eexists. apply ssem_sfield1; exact Hstep.
Qed.

Theorem coherent_field_preservation_from_operand :
  forall p Gamma Sigma vm m objects cells packets operand field result ef final vm' next,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sfield operand field result) ef result ->
  (forall receiver,
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets operand ef receiver ->
    forall nextM nextVm child,
    ssem_expr (globalenv p) p vm m operand nextM nextVm child ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration (globalenv p) Gamma Sigma' nextVm nextM objects' cells' packets' child effect' receiver /\
      sub_effect effect' ef = true) ->
  ssem_expr (globalenv p) p vm m (Sfield operand field result) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets' next ef' result /\
    sub_effect ef' ef = true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (field_typing_operand _ _ _ _ _ _ _ Htyped) as [receiver Hoperand].
  assert (HoperandConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    operand ef receiver) by (split; [constructor; assumption |exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ operand _ _ _ |- _ =>
      destruct (Hchild receiver HoperandConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [Hnew Hsub]]]]]]];
      destruct (coherent_field_operand_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hoperand Hs Hevolve Hnew Hsub) as [_ [Hfinal HsubFinal]]
    end.
    exists Sigma', objects', cells', packets', effect'. split; [exact Hevolve |]. split; assumption.
  all: destruct (coherent_field_read_preservation (globalenv p) p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl Hconfig Hstep)
      as [Hm [Hvm [objects' [Hevolve Hfinal]]]];
    do 4 eexists; exists []; split; [exact Hevolve |]; split; [exact Hfinal |apply sub_effect_nil].
Qed.

Print Assumptions coherent_field_progress_from_operand.
Print Assumptions coherent_field_preservation_from_operand.
