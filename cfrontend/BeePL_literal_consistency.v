(* Literal checking and execution, including the Const(ConsBool) shape
   emitted by beepl_transformer.ml for source Boolean constants. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_typechecker BeePL_type_equality.
Import ListNotations.

Theorem checked_constant_typing : forall env Gamma Sigma c annotation result effects,
  type_check_expr env Gamma Sigma (Const c annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Const c annotation) effects result.
Proof.
  intros env Gamma Sigma c annotation result effects Hcheck.
  destruct c; destruct annotation; try discriminate;
    try (destruct p; try discriminate);
    inversion Hcheck; subst; constructor.
Qed.

Theorem checked_unit_typing : forall env Gamma Sigma annotation result effects,
  type_check_expr env Gamma Sigma (Unit annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Unit annotation) effects result.
Proof.
  intros env Gamma Sigma annotation result effects Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (eq_type annotation Utype) eqn:Heq; try discriminate.
  apply eq_type_sound in Heq; subst.
  inversion Hcheck; subst; constructor.
Qed.

Theorem typed_constant_progress : forall ge p vm m Gamma Sigma c annotation ef ty,
  type_expr ge.(genv_cenv) Gamma Sigma (Const c annotation) ef ty ->
  exists v,
    ssem_expr ge p vm m (Const c annotation) m vm (Val v ty) /\
    bsem_expr ge p vm m (Const c annotation) m vm v /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) nil ty.
Proof.
  intros ge p vm m Gamma Sigma c annotation ef ty Htyped.
  inversion Htyped; subst; eexists; repeat split; constructor.
Qed.

Theorem typed_constant_preservation : forall ge p vm m Gamma Sigma c annotation ef ty final vm' result,
  type_expr ge.(genv_cenv) Gamma Sigma (Const c annotation) ef ty ->
  ssem_expr ge p vm m (Const c annotation) final vm' result ->
  final = m /\ vm' = vm /\
  exists v, result = Val v ty /\ type_expr ge.(genv_cenv) Gamma Sigma result nil ty.
Proof.
  intros ge p vm m Gamma Sigma c annotation ef ty final vm' result Htyped Hstep.
  inversion Hstep; subst; inversion Htyped; subst.
  all: split; [reflexivity |].
  all: split; [reflexivity |].
  all: eexists; split; [reflexivity |].
  all: eauto using ty_vali, ty_vall, ty_valu, ty_valb.
Qed.

Theorem typed_unit_progress : forall ge p vm m Gamma Sigma annotation ef ty,
  type_expr ge.(genv_cenv) Gamma Sigma (Unit annotation) ef ty ->
  ssem_expr ge p vm m (Unit annotation) m vm (Val Vunit Utype) /\
  bsem_expr ge p vm m (Unit annotation) m vm Vunit.
Proof. intros; match goal with H : type_expr _ _ _ _ _ _ |- _ => inversion H; subst end; split; constructor. Qed.

Theorem typed_unit_preservation : forall ge p vm m Gamma Sigma annotation ef ty final vm' result,
  type_expr ge.(genv_cenv) Gamma Sigma (Unit annotation) ef ty ->
  ssem_expr ge p vm m (Unit annotation) final vm' result ->
  final = m /\ vm' = vm /\ result = Val Vunit Utype /\ ty = Utype /\
  type_expr ge.(genv_cenv) Gamma Sigma result nil ty.
Proof. intros; match goal with H : ssem_expr _ _ _ _ _ _ _ _ |- _ => inversion H; subst end;
  match goal with H : type_expr _ _ _ _ _ _ |- _ => inversion H; subst end;
  repeat split; constructor. Qed.

Definition literal_check := type_check_expr (PTree.empty _) empty_context empty_stcontext.
Definition literal_rejected (r : res (type * effect)) := match r with Error _ => True | OK _ => False end.
Example bool_source_literal_accepted : literal_check (Const (ConsBool true) (Vtype Tbool)) = OK (Vtype Tbool, []).
Proof. vm_compute; reflexivity. Qed.
Example bool_source_literal_executes : forall ge p vm m,
  ssem_expr ge p vm m (Const (ConsBool true) (Vtype Tbool)) m vm (Val (Vbool true) (Vtype Tbool)).
Proof. intros; constructor. Qed.
Example integer_as_bool_rejected : literal_rejected (literal_check (Const (ConsInt Int.zero) (Vtype Tbool))).
Proof. vm_compute; exact I. Qed.
Example bool_as_integer_rejected : literal_rejected (literal_check (Const (ConsBool true) (Vtype (Tint I32 Signed noattr)))).
Proof. vm_compute; exact I. Qed.
Example long_as_integer_rejected : literal_rejected (literal_check (Const (ConsLong Int64.zero) (Vtype (Tint I32 Signed noattr)))).
Proof. vm_compute; exact I. Qed.
Example unit_constant_as_bool_rejected : literal_rejected (literal_check (Const ConsUnit (Vtype Tbool))).
Proof. vm_compute; exact I. Qed.
Example unit_expression_as_bool_rejected : literal_rejected (literal_check (Unit (Vtype Tbool))).
Proof. vm_compute; exact I. Qed.
Example unit_expression_accepted : literal_check (Unit Utype) = OK (Utype, []).
Proof. vm_compute; reflexivity. Qed.
Print Assumptions checked_constant_typing.
Print Assumptions checked_unit_typing.
Print Assumptions typed_constant_progress.
Print Assumptions typed_constant_preservation.
Print Assumptions typed_unit_progress.
Print Assumptions typed_unit_preservation.
