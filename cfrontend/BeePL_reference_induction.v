(* The Ref case of the whole-expression induction: the only recursive
   hypothesis concerns its proper operand; evaluated heads are proved. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_general_reference_heads BeePL_coherent_memory_contexts.
Import ListNotations.

Lemma reference_typing_components : forall env Gamma Sigma operand basic attr ef,
  type_expr env Gamma Sigma (Prim Ref [operand] (Ptrtype (Reftype basic attr))) ef
    (Ptrtype (Reftype basic attr)) ->
  exists child_effect,
    ef = child_effect ++ [Alloc] /\
    type_expr env Gamma Sigma operand child_effect (construct_type_btype basic).
Proof. intros * Htyped; inversion Htyped; subst; eauto. Qed.

Theorem coherent_reference_progress_from_operand :
  forall p Gamma Sigma vm m objects cells packets operand basic attr ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [operand] (Ptrtype (Reftype basic attr))) ef (Ptrtype (Reftype basic attr)) ->
  (forall effect,
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
      operand effect (construct_type_btype basic) ->
    (exists v annotation, operand = Val v annotation) \/
    exists final vm' next, ssem_expr (globalenv p) p vm m operand final vm' next) ->
  exists final vm' next,
    ssem_expr (globalenv p) p vm m (Prim Ref [operand] (Ptrtype (Reftype basic attr))) final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [Hloc Hnil] [Hframes HnilFrames]] Hcoherent].
  destruct (reference_typing_components _ _ _ _ _ _ _ Htyped) as [effect [Hef Hoperand]].
  assert (HoperandConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    operand effect (construct_type_btype basic)) by (split; [constructor; assumption |exact Hcoherent]).
  destruct (Hchild effect HoperandConfig) as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst operand.
    destruct (coherent_general_reference_head_progress p Gamma Sigma vm m objects cells packets v annotation basic attr ef Hconfig)
      as [final [fresh [Sigma' [objects' [cells' [packets' [Hstep Hrest]]]]]]].
    do 3 eexists; exact Hstep.
  - do 3 eexists. apply ssem_ref1; exact Hstep.
Qed.

Theorem coherent_reference_preservation_from_operand :
  forall p Gamma Sigma vm m objects cells packets operand basic attr ef final vm' next,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [operand] (Ptrtype (Reftype basic attr))) ef (Ptrtype (Reftype basic attr)) ->
  (forall effect,
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
      operand effect (construct_type_btype basic) ->
    forall nextM nextVm child,
    ssem_expr (globalenv p) p vm m operand nextM nextVm child ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration (globalenv p) Gamma Sigma' nextVm nextM objects' cells' packets'
        child effect' (construct_type_btype basic) /\ sub_effect effect' effect = true) ->
  ssem_expr (globalenv p) p vm m
    (Prim Ref [operand] (Ptrtype (Reftype basic attr))) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets'
      next ef' (Ptrtype (Reftype basic attr)) /\ sub_effect ef' ef = true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hloc Hnil] [Hframes HnilFrames]] Hcoherent].
  destruct (reference_typing_components _ _ _ _ _ _ _ Htyped) as [effect [Hef Hoperand]]. subst ef.
  assert (HoperandConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    operand effect (construct_type_btype basic)) by (split; [constructor; assumption |exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ operand _ _ _ |- _ =>
      destruct (Hchild effect HoperandConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [Hnew Hsub]]]]]]];
      destruct (coherent_reference_operand_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hs Hevolve Hnew Hsub) as [_ [Hfinal HsubFinal]]
    end.
    exists Sigma', objects', cells', packets', (effect' ++ [Alloc]).
    split; [exact Hevolve |]. split; assumption.
  all: destruct (coherent_general_reference_head_preservation _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ Hconfig Hstep)
    as [Sigma' [objects' [cells' [packets' [Hevolve [Hfinal Hsub]]]]]];
    exists Sigma', objects', cells', packets', []; split; [exact Hevolve |]; split; assumption.
Qed.

Print Assumptions coherent_reference_progress_from_operand.
Print Assumptions coherent_reference_preservation_from_operand.
