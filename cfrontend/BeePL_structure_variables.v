(* Direct structure variables denote their allocated object, without a scalar
   load. Object typing is required separately for preservation. *)
Require Import List AST Integers Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.

Lemma structure_full_deref_impossible : forall id attr m b ofs v,
  ~ deref_addr (Stype id attr) m b ofs Full v.
Proof. intros id attr m b ofs v H; inversion H; subst; discriminate. Qed.

Theorem local_structure_variable_progress : forall (ge : genv) p vm m x id attr b,
  PTree.get x vm = Some (b, Stype id attr) ->
  ssem_expr ge p vm m (Var x (Stype id attr)) m vm
    (Val (Vloc b Ptrofs.zero) (Stype id attr)).
Proof. intros; apply ssem_lvar_struct; assumption. Qed.

Theorem global_structure_variable_progress : forall (ge : genv) p vm m x id attr b,
  PTree.get x vm = None -> Genv.find_symbol ge x = Some b ->
  ssem_expr ge p vm m (Var x (Stype id attr)) m vm
    (Val (Vloc b Ptrofs.zero) (Stype id attr)).
Proof. intros; apply ssem_gbvar_struct; assumption. Qed.

Lemma local_structure_variable_step_exact :
  forall (ge : genv) p vm m x id attr b m' vm' e',
  PTree.get x vm = Some (b, Stype id attr) ->
  ssem_expr ge p vm m (Var x (Stype id attr)) m' vm' e' ->
  m' = m /\ vm' = vm /\ e' = Val (Vloc b Ptrofs.zero) (Stype id attr).
Proof.
  intros ge p vm m x id attr b m' vm' e' Hlocal Hstep.
  inversion Hstep; subst;
    try solve [exfalso; eapply structure_full_deref_impossible; eauto].
  all: repeat split; congruence.
Qed.

Lemma global_structure_variable_step_exact :
  forall (ge : genv) p vm m x id attr b m' vm' e',
  PTree.get x vm = None -> Genv.find_symbol ge x = Some b ->
  ssem_expr ge p vm m (Var x (Stype id attr)) m' vm' e' ->
  m' = m /\ vm' = vm /\ e' = Val (Vloc b Ptrofs.zero) (Stype id attr).
Proof.
  intros ge p vm m x id attr b m' vm' e' Hmissing Hsymbol Hstep.
  inversion Hstep; subst;
    try solve [exfalso; eapply structure_full_deref_impossible; eauto].
  all: repeat split; congruence.
Qed.

Theorem structure_variable_value_typed : forall cenv Gamma Sigma b id attr,
  object_type_at cenv Sigma b (Ptrofs.unsigned Ptrofs.zero) (Stype id attr) ->
  type_expr cenv Gamma Sigma (Val (Vloc b Ptrofs.zero) (Stype id attr)) nil (Stype id attr).
Proof. intros; apply ty_valstruct; assumption. Qed.

Print Assumptions local_structure_variable_step_exact.
Print Assumptions global_structure_variable_step_exact.
Print Assumptions structure_variable_value_typed.
