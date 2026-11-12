(* Runtime-frame validity is inhabited and rules out captured environments
   that raw expression typing alone cannot reject. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_callable_locations BeePL_callable_variables BeePL_callable_state.
Require Import BeePL_runtime_frames BeePL_frame_configurations.

Definition empty_frame_layout : scalar_layout := fun _ _ _ _ => False.

Lemma callable_frame_state_empty : forall bge,
  callable_heap_state empty_context empty_stcontext bge empty_vmap Mem.empty empty_frame_layout.
Proof.
  intros. constructor.
  - intros b ty Hget. rewrite PTree.gempty in Hget. discriminate.
  - intros b ofs ty chunk Hcell. contradiction.
  - intros b ofs ty chunk Hcell. contradiction.
  - intros x ty Hget. rewrite PTree.gempty in Hget. discriminate.
Qed.

Lemma empty_unit_configuration : forall bge,
  runtime_configuration bge empty_context empty_stcontext empty_vmap Mem.empty
    empty_frame_layout (Val Vunit Utype) nil Utype.
Proof.
  intros. constructor.
  - apply callable_frame_state_empty.
  - apply ty_valu.
  - exact I.
  - exact I.
Qed.

Lemma empty_frame_configuration_wrap : forall bge body ef ty,
  runtime_configuration bge empty_context empty_stcontext empty_vmap Mem.empty
    empty_frame_layout body ef ty ->
  runtime_configuration bge empty_context empty_stcontext empty_vmap Mem.empty
    empty_frame_layout (CallFrame empty_vmap body ty) ef ty.
Proof.
  intros bge body ef ty [Hheap Htyping Hlocations Hframes]. constructor.
  - exact Hheap.
  - eapply ty_callframe; exact Htyping.
  - exact Hlocations.
  - simpl. exists empty_context, ef. split; [exact Hheap|]. split; assumption.
Qed.

Theorem nested_unit_frames_execute : forall bge p,
  runtime_configuration bge empty_context empty_stcontext empty_vmap Mem.empty
    empty_frame_layout
    (CallFrame empty_vmap (CallFrame empty_vmap (Val Vunit Utype) Utype) Utype)
    nil Utype /\
  ssem_closure bge p empty_vmap Mem.empty
    (CallFrame empty_vmap (CallFrame empty_vmap (Val Vunit Utype) Utype) Utype)
    2%nat Mem.empty empty_vmap (Val Vunit Utype) /\
  runtime_configuration bge empty_context empty_stcontext empty_vmap Mem.empty
    empty_frame_layout (Val Vunit Utype) nil Utype.
Proof.
  intros. split.
  - apply empty_frame_configuration_wrap. apply empty_frame_configuration_wrap.
    apply empty_unit_configuration.
  - split; [|apply empty_unit_configuration].
    eapply ssem_multi with (n := 1%nat).
    + apply ssem_call_frame_step. apply ssem_call_frame_return.
    + apply ssem_one. apply ssem_call_frame_return.
Qed.

Lemma missing_captured_binding_rejects_frames :
  forall (bge : genv) Sigma m layout callee x ty,
  PTree.get x callee = None -> Genv.find_symbol bge x = None ->
  ~ runtime_frames bge Sigma m layout (CallFrame callee (Var x ty) ty).
Proof.
  intros bge Sigma m layout callee x ty Hmissing Hnosymbol
    [Gamma [ef [[Hblocks Hmemory Hcontents Hbindings] [Htyped Hnested]]]].
  inversion Htyped; subst.
  assert (Hbinding : callable_variable_binding bge Sigma callee layout x ty).
  { eapply Hbindings; eassumption. }
  destruct Hbinding as [b Hlocation Hheap Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
  - destruct Hlocation as [Hlocal|[Hnone Hsymbol]]; congruence.
  - congruence.
  - congruence.
Qed.

(* The raw frame typing rule can choose a context unrelated to the captured
   map. The runtime invariant above supplies the missing connection. *)
Lemma missing_captured_binding_raw_typing : forall cenv Gamma Sigma callee x ty,
  type_expr cenv Gamma Sigma (CallFrame callee (Var x ty) ty) nil ty.
Proof.
  intros. eapply ty_callframe with (callee_Gamma := extend_context empty_context x ty).
  apply ty_var. unfold extend_context. apply PTree.gss.
Qed.

Print Assumptions nested_unit_frames_execute.
Print Assumptions missing_captured_binding_rejects_frames.
Print Assumptions missing_captured_binding_raw_typing.
