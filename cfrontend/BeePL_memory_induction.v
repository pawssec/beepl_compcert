(* Dereference and assignment cases of the expression induction. Evaluated
   memory operations are discharged by the general checked head theorems. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_general_memory_heads BeePL_coherent_memory_contexts.
Import ListNotations.

Theorem coherent_dereference_progress_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p operand result ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [operand] result) ef result ->
  (forall pt effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand effect (Ptrtype pt) ->
    (exists v annotation, operand = Val v annotation) \/
    exists final vm' next, ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next, ssem_expr ge p vm m (Prim Deref [operand] result) final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [Hloc Hnil] [Hframes HnilFrames]] Hcoherent].
  destruct (dereference_typing_components _ _ _ _ _ _ Htyped)
    as [pt [effect [Hresult [Hef [Hoperand Hoption]]]]].
  assert (HoperandConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    operand effect (Ptrtype pt)) by (split; [constructor; assumption |exact Hcoherent]).
  destruct (Hchild pt effect HoperandConfig) as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst operand.
    destruct (coherent_general_dereference_head_progress ge Gamma Sigma vm m objects cells packets p v annotation result ef Hconfig)
      as [value [Hstep Hrest]]. do 3 eexists; exact Hstep.
  - do 3 eexists. apply ssem_deref1; exact Hstep.
Qed.

Theorem coherent_dereference_preservation_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p operand result ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [operand] result) ef result ->
  (forall pt effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand effect (Ptrtype pt) ->
    forall nextM nextVm child,
    ssem_expr ge p vm m operand nextM nextVm child ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' child effect' (Ptrtype pt) /\
      sub_effect effect' effect = true) ->
  ssem_expr ge p vm m (Prim Deref [operand] result) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' result /\
    sub_effect ef' ef = true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hloc Hnil] [Hframes HnilFrames]] Hcoherent].
  destruct (dereference_typing_components _ _ _ _ _ _ Htyped)
    as [pt [effect [Hresult [Hef [Hoperand Hoption]]]]]. subst result ef.
  assert (HoperandConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    operand effect (Ptrtype pt)) by (split; [constructor; assumption |exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ operand _ _ _ |- _ =>
      destruct (Hchild pt effect HoperandConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [Hnew Hsub]]]]]]];
      destruct (coherent_dereference_operand_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hoperand Hs Hevolve Hnew Hsub) as [_ [Hfinal HsubFinal]]
    end.
    exists Sigma', objects', cells', packets', (effect' ++ [Read]).
    split; [exact Hevolve |]. split; assumption.
  all: pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation;
    simpl in Hannotation; inversion Hannotation; subst.
  all: destruct (coherent_general_dereference_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [Hm [Hvm [Hevolve Hfinal]]];
    do 4 eexists; exists []; split; [exact Hevolve |]; split; [exact Hfinal |apply sub_effect_nil].
Qed.

Theorem coherent_assignment_progress_from_operands :
  forall p Gamma Sigma vm m objects cells packets left right ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [left; right] Utype) ef Utype ->
  (forall operand effect ty, (operand = left \/ operand = right) ->
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets operand effect ty ->
    (exists v annotation, operand = Val v annotation) \/
    exists final vm' next, ssem_expr (globalenv p) p vm m operand final vm' next) ->
  exists final vm' next, ssem_expr (globalenv p) p vm m (Prim Massgn [left; right] Utype) final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [HleftLoc [HrightLoc Hnil]] [HleftFrames [HrightFrames HnilFrames]]] Hcoherent].
  destruct (assignment_typing_components _ _ _ _ _ _ Htyped)
    as [pt [ef1 [ef2 [Hef [Hleft [Hright Hoption]]]]]].
  assert (HleftConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    left ef1 (Ptrtype pt)) by (split; [constructor; assumption |exact Hcoherent]).
  assert (HrightConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    right ef2 (get_data_type pt)) by (split; [constructor; assumption |exact Hcoherent]).
  destruct (Hchild left ef1 (Ptrtype pt) (or_introl eq_refl) HleftConfig)
    as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst left. destruct (typed_nonoption_pointer_value _ _ _ _ _ _ _ Hleft Hoption)
      as [basic [attr [b [offset [Hpt [Hv Hannotation]]]]]]. subst pt v annotation.
    destruct (Hchild right ef2 (get_data_type (Reftype basic attr)) (or_intror eq_refl) HrightConfig)
      as [[value [annotation He]] | [final [vm' [next Hstep]]]].
    + subst right.
      destruct (coherent_general_assignment_head_progress p Gamma Sigma vm m objects cells packets
        _ _ value annotation ef Hconfig) as [final [Hstep Hrest]]. do 3 eexists; exact Hstep.
    + do 3 eexists. apply ssem_massgn2; exact Hstep.
  - do 3 eexists. apply ssem_massgn1; exact Hstep.
Qed.

Theorem coherent_assignment_preservation_from_operands :
  forall p Gamma Sigma vm m objects cells packets left right ef final vm' next,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [left; right] Utype) ef Utype ->
  (forall operand effect ty, (operand = left \/ operand = right) ->
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets operand effect ty ->
    forall nextM nextVm child,
    ssem_expr (globalenv p) p vm m operand nextM nextVm child ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration (globalenv p) Gamma Sigma' nextVm nextM objects' cells' packets' child effect' ty /\
      sub_effect effect' effect = true) ->
  ssem_expr (globalenv p) p vm m (Prim Massgn [left; right] Utype) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets' next ef' Utype /\
    sub_effect ef' ef = true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [HleftLoc [HrightLoc Hnil]] [HleftFrames [HrightFrames HnilFrames]]] Hcoherent].
  destruct (assignment_typing_components _ _ _ _ _ _ Htyped)
    as [pt [ef1 [ef2 [Hef [Hleft [Hright Hoption]]]]]]. subst ef.
  assert (HleftConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    left ef1 (Ptrtype pt)) by (split; [constructor; assumption |exact Hcoherent]).
  assert (HrightConfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    right ef2 (get_data_type pt)) by (split; [constructor; assumption |exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ left _ _ _ |- _ =>
      destruct (Hchild left ef1 (Ptrtype pt) (or_introl eq_refl) HleftConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [Hnew Hsub]]]]]]];
      destruct (coherent_assignment_left_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hleft Hright Hs Hevolve Hnew Hsub) as [_ [Hfinal HsubFinal]]
    end.
    exists Sigma', objects', cells', packets', (effect' ++ ef2 ++ [Write]).
    split; [exact Hevolve |]. split; assumption.
  - pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hleft) as Hef1. subst ef1.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Hannotation.
    simpl in Hannotation. inversion Hannotation; subst.
    match goal with Hs : ssem_expr _ _ _ _ right _ _ _ |- _ =>
      destruct (Hchild right ef2 _ (or_intror eq_refl) HrightConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [Hnew Hsub]]]]]]];
      destruct (coherent_assignment_right_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hleft Hs Hevolve Hnew Hsub) as [_ [Hfinal HsubFinal]]
    end.
    exists Sigma', objects', cells', packets', (effect' ++ [Write]).
    split; [exact Hevolve |]. split; assumption.
  - destruct (coherent_general_assignment_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [Hvm [He [Hevolve [Hfinal Hsub]]]].
    do 4 eexists; exists []; split; [exact Hevolve |]. split; [exact Hfinal |exact Hsub].
Qed.

Print Assumptions coherent_dereference_progress_from_operand.
Print Assumptions coherent_dereference_preservation_from_operand.
Print Assumptions coherent_assignment_progress_from_operands.
Print Assumptions coherent_assignment_preservation_from_operands.
