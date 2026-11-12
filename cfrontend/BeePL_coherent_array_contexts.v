(* Evaluation-context lifting. The successor child/list configurations below
   are precisely the recursive preservation conclusions; no head-read or
   initialization safety is assumed. *)
Require Import List Bool Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Require Import BeePL_coherent_lists BeePL_type_equality BeePL_callable_entry.
Import ListNotations.

Theorem coherent_array_read_operand_context :
  forall ge Gamma Sigma vm m objects cells packets p operand elem len attr n ef
    Sigma' vm' m' objects' cells' packets' operand' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [operand] elem) ef elem ->
  type_expr ge.(genv_cenv) Gamma Sigma operand ef (Atype elem len attr) ->
  ssem_expr ge p vm m operand m' vm' operand' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    operand' ef' (Atype elem len attr) ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [operand] elem)
    m' vm' (Prim (ArrayRead n) [operand'] elem) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Prim (ArrayRead n) [operand'] elem) ef' elem /\ sub_effect ef' ef = true.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hoperand Hstep Hevolve
    [[Hheap' Hoperand' Hloc' Hframes'] Hcoherent'] Hsub.
  split; [apply ssem_array_read_context; exact Hstep|]. split; [|exact Hsub].
  split; [|exact Hcoherent']. constructor; simpl; auto.
  inversion Htyped; subst.
  match goal with Hother : type_expr _ _ _ operand _ (Atype _ _ _) |- _ =>
    pose proof (type_rel_typeof _ _ _ _ _ _ Hother) as Hannotation
  end.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation'.
  assert (Hsame : forall t, type_expr ge.(genv_cenv) Gamma Sigma operand ef t ->
    t = Atype elem len attr).
  { intros t Ht. pose proof (type_rel_typeof _ _ _ _ _ _ Ht); congruence. }
  match goal with H : type_expr _ _ _ operand _ (Atype _ _ _) |- _ =>
    specialize (Hsame _ H); inversion Hsame; subst end.
  eapply ty_arrayread; eauto.
Qed.

Lemma typed_array_head_annotation : forall env Gamma Sigma arr ty v annotation tail ef,
  type_expr env Gamma Sigma (Ainit arr ty (Val v annotation :: tail) ty) ef ty ->
  get_array_elm_ty ty = Errors.OK annotation.
Proof.
  intros * Htyped. inversion Htyped; subst.
  match goal with Hargs : type_exprs _ _ _ (_ :: _) _ _ |- _ => inversion Hargs; subst end.
  match goal with Hsame : is_true (all_eq_type _ (_ :: _)) |- _ =>
    simpl in Hsame; apply andb_true_iff in Hsame as [Heq Hrest];
    apply eq_type_sound in Heq; subst end.
  match goal with Hvalue : type_expr _ _ _ (Val _ _) _ _ |- _ =>
    pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
    simpl in Hannotation; subst end.
  assumption.
Qed.

Lemma typed_array_arguments_step : forall ge Gamma Sigma vm m p arr ty es ef final vm' es',
  type_expr ge.(genv_cenv) Gamma Sigma (Ainit arr ty es ty) ef ty ->
  is_values es = false -> ssem_exprs ge p vm m es final vm' es' ->
  ssem_expr ge p vm m (Ainit arr ty es ty) final vm' (Ainit arr ty es' ty).
Proof.
  intros * Htyped Hguard Hstep. inversion Hstep; subst; try discriminate.
  - apply ssem_array_init1; assumption.
  - eapply ssem_array_init2; [exact Hguard|eapply typed_array_head_annotation; exact Htyped|eassumption].
Qed.

Theorem coherent_array_arguments_context :
  forall ge Gamma Sigma vm m objects cells packets p arr ty es ef types
    Sigma' vm' m' objects' cells' packets' es' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Ainit arr ty es ty) ef ty ->
  type_exprs ge.(genv_cenv) Gamma Sigma es ef types ->
  is_values es = false ->
  ssem_exprs ge p vm m es m' vm' es' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_list_configuration ge Gamma Sigma' vm' m' objects' cells' packets' es' ef' types ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Ainit arr ty es ty) m' vm' (Ainit arr ty es' ty) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Ainit arr ty es' ty) ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hargs Hnonvalues Hstep Hevolve
    [[Hheap' Hargs' Hloc' Hframes'] Hcoherent'] Hsub.
  split; [eapply typed_array_arguments_step; eauto|]. split; [|exact Hsub].
  split; [|exact Hcoherent']. constructor; try assumption.
  inversion Htyped; subst.
  match goal with Hother : type_exprs _ _ _ es _ ?other |- _ =>
    assert (Heq : other = types) by
      (pose proof (typed_arguments_annotations _ _ _ _ _ _ Hother);
       pose proof (typed_arguments_annotations _ _ _ _ _ _ Hargs); congruence)
  end.
  subst. eapply ty_ainit; eauto.
Qed.

Print Assumptions coherent_array_read_operand_context.
Print Assumptions coherent_array_arguments_context.
