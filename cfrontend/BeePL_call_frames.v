(* Internal calls preserve the surrounding caller environment. These lemmas
   expose the remaining callee-body typing/progress obligations explicitly. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_call_bindings.
Import ListNotations.

Lemma call_frame_step_cases : forall bge p caller callee m body t m' caller' e',
  ssem_expr bge p caller m (CallFrame callee body t) m' caller' e' ->
  caller' = caller /\
  ((exists callee' body', e' = CallFrame callee' body' t /\
      ssem_expr bge p callee m body m' callee' body') \/
   (exists v, body = Val v t /\ m' = m /\ e' = Val v t)).
Proof.
  intros bge p caller callee m body t m' caller' e' Hstep. inversion Hstep; subst.
  - split; [reflexivity |]. left. do 2 eexists; split; [reflexivity | eassumption].
  - split; [reflexivity |]. right. eexists; repeat split; reflexivity.
Qed.

Lemma call_frame_preserves_caller : forall bge p caller callee m body t m' caller' e',
  ssem_expr bge p caller m (CallFrame callee body t) m' caller' e' -> caller' = caller.
Proof. intros. eapply (proj1 (call_frame_step_cases _ _ _ _ _ _ _ _ _ _ H)); eauto. Qed.

Theorem call_frame_progress_from_body :
  forall bge cenv callee_Gamma Sigma p caller callee m body ef t,
  type_expr cenv callee_Gamma Sigma body ef t ->
  (is_value body = true \/ exists m' callee' body',
    ssem_expr bge p callee m body m' callee' body') ->
  exists m' e', ssem_expr bge p caller m (CallFrame callee body t) m' caller e'.
Proof.
  intros bge cenv callee_Gamma Sigma p caller callee m body ef t Htyped Hprogress.
  destruct Hprogress as [Hvalue | [m' [callee' [body' Hstep]]]].
  - destruct body; simpl in Hvalue; try discriminate.
    pose proof (type_rel_typeof _ _ _ _ _ _ Htyped) as Hannotation.
    simpl in Hannotation. subst. do 2 eexists. apply ssem_call_frame_return.
  - do 2 eexists. apply ssem_call_frame_step. exact Hstep.
Qed.

Theorem call_frame_typing_preservation_from_body :
  forall bge cenv Gamma callee_Gamma Sigma p caller callee m body ef t m' caller' e',
  type_expr cenv callee_Gamma Sigma body ef t ->
  (forall next_m next_vm next_body,
    ssem_expr bge p callee m body next_m next_vm next_body ->
    exists next_Gamma next_Sigma next_ef,
      store_context_extends Sigma next_Sigma /\
      type_expr cenv next_Gamma next_Sigma next_body next_ef t /\
      sub_effect next_ef ef = true) ->
  ssem_expr bge p caller m (CallFrame callee body t) m' caller' e' ->
  exists Sigma' ef', caller' = caller /\ store_context_extends Sigma Sigma' /\
    type_expr cenv Gamma Sigma' e' ef' t /\ sub_effect ef' ef = true.
Proof.
  intros bge cenv Gamma callee_Gamma Sigma p caller callee m body ef t m' caller' e'
    Htyped Hbody Hstep.
  destruct (call_frame_step_cases _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hcaller [[callee' [body' [He Hinner]]] | [v [Hval [Hm He]]]]].
  - subst e'. destruct (Hbody _ _ _ Hinner)
      as [Gamma' [Sigma' [ef' [Hext [Hresult Heffect]]]]].
    exists Sigma', ef'. split; [exact Hcaller |]. split; [exact Hext |].
    split; [eapply ty_callframe; exact Hresult | exact Heffect].
  - subst body e' m'.
    pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Htyped) as Hef. subst ef.
    exists Sigma, nil. split; [exact Hcaller |]. split; [apply store_context_extends_refl |].
    split; [eapply value_typing_context_independent; exact Htyped | reflexivity].
Qed.

Theorem initialized_parameter_frame_returns :
  forall bge cenv Gamma Sigma p caller callee allocated initialized id pt input b,
  bind_variables bge callee allocated [(id, Vtype pt)] [input] initialized ->
  PTree.get id callee = Some (b, Vtype pt) ->
  typeof_value input (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  Mem.valid_access allocated (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Freeable ->
  exists result,
    ssem_closure bge p caller initialized
      (CallFrame callee (Var id (Vtype pt)) (Vtype pt)) 2%nat
      initialized caller (Val result (Vtype pt)) /\
    type_expr cenv Gamma Sigma (Val result (Vtype pt)) nil (Vtype pt).
Proof.
  intros bge cenv Gamma Sigma p caller callee allocated initialized id pt input b
    Hbind Hlookup Hshape Hvolatile Haccess.
  pose proof (bind_primitive_parameter_initialized _ _ _ _ _ _ _ _ cenv Sigma
    Hbind Hlookup Hshape Hvolatile Haccess) as Hcell.
  destruct (typed_memory_cell_read cenv Gamma Sigma initialized b Ptrofs.zero
    (Vtype pt) (chunk_of_ptype pt) Hcell) as [result [Hread Htyped]].
  exists result. split; [|exact Htyped].
  eapply ssem_multi with (n := 1%nat).
  - apply ssem_call_frame_step. eapply ssem_lvar; eauto.
  - apply ssem_one. apply ssem_call_frame_return.
Qed.

Print Assumptions call_frame_preserves_caller.
Print Assumptions call_frame_progress_from_body.
Print Assumptions call_frame_typing_preservation_from_body.
Print Assumptions initialized_parameter_frame_returns.
