(* Checked frame cases. Body-step lifting is conditional on the body induction
   hypothesis; it does not assert whole-language preservation. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_runtime_frames.
Import ListNotations.

Theorem frame_return_configuration :
  forall bge Gamma Sigma caller callee m layout v ty ef,
  runtime_configuration bge Gamma Sigma caller m layout
    (CallFrame callee (Val v ty) ty) ef ty ->
  runtime_configuration bge Gamma Sigma caller m layout (Val v ty) ef ty.
Proof.
  intros bge Gamma Sigma caller callee m layout v ty ef
    [Hheap Htyping Hlocations Hframes].
  constructor.
  - exact Hheap.
  - inversion Htyping; subst. eapply value_typing_context_independent; eauto.
  - exact Hlocations.
  - exact I.
Qed.

Theorem frame_return_step_configuration :
  forall bge p Gamma Sigma caller callee m layout v ty ef,
  runtime_configuration bge Gamma Sigma caller m layout
    (CallFrame callee (Val v ty) ty) ef ty ->
  ssem_expr bge p caller m (CallFrame callee (Val v ty) ty)
    m caller (Val v ty) /\
  runtime_configuration bge Gamma Sigma caller m layout (Val v ty) ef ty.
Proof.
  intros. split; [apply ssem_call_frame_return |].
  eapply frame_return_configuration; eauto.
Qed.

(* The successor body configuration is the explicit preservation induction
   hypothesis, including the validity of any nested captured environments. *)
Theorem frame_body_step_configuration_from_body :
  forall bge p Gamma callee_Gamma Sigma caller callee m layout body ef ty
    Sigma' callee' m' layout' body' ef',
  runtime_configuration bge Gamma Sigma caller m layout
    (CallFrame callee body ty) ef ty ->
  ssem_expr bge p callee m body m' callee' body' ->
  runtime_configuration bge callee_Gamma Sigma' callee' m' layout' body' ef' ty ->
  callable_heap_evolution bge Sigma layout Sigma' m' layout' ->
  sub_effect ef' ef = true ->
  ssem_expr bge p caller m (CallFrame callee body ty)
    m' caller (CallFrame callee' body' ty) /\
  runtime_configuration bge Gamma Sigma' caller m' layout'
    (CallFrame callee' body' ty) ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros bge p Gamma callee_Gamma Sigma caller callee m layout body ef ty
    Sigma' callee' m' layout' body' ef'
    [Hcaller Htyped Hlocations Hframes] Hstep
    [Hcallee Hbody Hbodylocations Hbodyframes] Hupdate Heffect.
  split; [eapply ssem_call_frame_step; exact Hstep |].
  split; [|exact Heffect]. constructor.
  - eapply callable_state_evolve; eauto.
  - eapply ty_callframe; exact Hbody.
  - exact Hbodylocations.
  - simpl. exists callee_Gamma, ef'. split; [exact Hcallee |]. split; assumption.
Qed.

Print Assumptions frame_return_configuration.
Print Assumptions frame_body_step_configuration_from_body.

Require Import BeePL_context_retyping.

(* The frame typing derivation and captured-environment witness may choose
   different effects. Retyping transfers the former effect without requiring
   effect uniqueness. *)
Theorem frame_configuration_body :
  forall bge Gamma Sigma caller callee m layout body ef ty,
  runtime_configuration bge Gamma Sigma caller m layout
    (CallFrame callee body ty) ef ty ->
  exists callee_Gamma,
    runtime_configuration bge callee_Gamma Sigma callee m layout body ef ty.
Proof.
  intros bge Gamma Sigma caller callee m layout body ef ty
    [Hcaller Htyping Hlocations Hframes].
  simpl in Hframes. destruct Hframes as [callee_Gamma [bodyef [Hcallee [Hbody Hnested]]]].
  exists callee_Gamma. constructor; try assumption.
  inversion Htyping; subst.
  eapply expression_context_retyping; [eassumption | exact Hbody].
Qed.

Print Assumptions frame_configuration_body.
