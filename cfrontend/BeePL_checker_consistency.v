(* Local checker-to-typing bridges: child-check soundness is an explicit
   induction hypothesis, not an assumed whole-checker correctness theorem. *)
Require Import String List Bool ZArith Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker BeePL_type_equality.
Require Import BeePL_value_checker.
Require Import BeePL_storage_types.
Import ListNotations.

Theorem checked_value_typing : forall env Gamma Sigma v annotation result effects,
  type_check_expr env Gamma Sigma (Val v annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Val v annotation) effects result.
Proof.
  intros env Gamma Sigma v annotation result effects Hcheck.
  change ((if value_type_check env Sigma v annotation then OK (annotation, [])
    else Error (msg "TYPE ERROR: Runtime value does not match its type or storage"%string)) =
    OK (result, effects)) in Hcheck.
  destruct (value_type_check env Sigma v annotation) eqn:Hvalue; try discriminate.
  inversion Hcheck; subst. apply value_type_check_sound. exact Hvalue.
Qed.

Theorem typed_value_checker_accepts : forall env Gamma Sigma v ty,
  type_expr env Gamma Sigma (Val v ty) [] ty ->
  type_check_expr env Gamma Sigma (Val v ty) = OK (ty, []).
Proof.
  intros env Gamma Sigma v ty Htyped.
  change ((if value_type_check env Sigma v ty then OK (ty, ([] : effect))
    else Error (msg "TYPE ERROR: Runtime value does not match its type or storage"%string)) = OK (ty, [])).
  rewrite (value_type_check_complete _ _ _ _ _ Htyped). reflexivity.
Qed.

Lemma checked_assignment_typing : forall env Gamma Sigma lhs rhs annotation result effects,
  (forall ty ef, type_check_expr env Gamma Sigma lhs = OK (ty, ef) ->
    type_expr env Gamma Sigma lhs ef ty) ->
  (forall ty ef, type_check_expr env Gamma Sigma rhs = OK (ty, ef) ->
    type_expr env Gamma Sigma rhs ef ty) ->
  type_check_expr env Gamma Sigma (Prim Massgn [lhs; rhs] annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Prim Massgn [lhs; rhs] annotation) effects result.
Proof.
  intros env Gamma Sigma lhs rhs annotation result effects Hlhs Hrhs Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_expr env Gamma Sigma lhs) as [[leftType leftEffects]|err] eqn:Hleft;
    cbn in Hcheck; try discriminate.
  destruct leftType as [|prim|pt|sid attr|elem len attr|args eff rt va|]; try discriminate.
  destruct (type_check_expr env Gamma Sigma rhs) as [[rightType rightEffects]|err] eqn:Hright;
    cbn in Hcheck; try discriminate.
  destruct (eq_type (get_data_type pt) rightType && eq_type annotation Utype) eqn:Htypes;
    try discriminate.
  apply andb_true_iff in Htypes as [Hsource Hunit].
  apply eq_type_sound in Hsource. apply eq_type_sound in Hunit. subst.
  destruct (is_option_ptr_type pt) eqn:Hoption; cbn in Hcheck; try discriminate.
  destruct (type_is_volatile (transBeePL_type (get_data_type pt))) eqn:Hvolatile;
    try discriminate.
  inversion Hcheck; subst. eapply ty_massgn; eauto.
Qed.

Lemma checked_array_initializer_typing : forall env Gamma Sigma name annotation es resultAnnotation result effects,
  (forall ts ef, type_check_exprs type_check_expr env Gamma Sigma es = OK (ts, ef) ->
    type_exprs env Gamma Sigma es ef ts) ->
  type_check_expr env Gamma Sigma (Ainit name annotation es resultAnnotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Ainit name annotation es resultAnnotation) effects result.
Proof.
  intros env Gamma Sigma name annotation es resultAnnotation result effects Hchildren Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_exprs type_check_expr env Gamma Sigma es) as [[ts ef]|err] eqn:Hargs;
    cbn in Hcheck; try discriminate.
  destruct annotation as [|prim|pt|sid attr|elem len attr|args eff rt va|]; try discriminate.
  destruct (eq_type (Atype elem len attr) resultAnnotation &&
    Z.eqb len (Z.of_nat (List.length ts)) && all_eq_type elem ts) eqn:Hguard; try discriminate.
  destruct (storage_type_check env (Atype elem len attr)) eqn:Hstorage; try discriminate.
  apply andb_true_iff in Hguard as [Hshape Htypes].
  apply andb_true_iff in Hshape as [Hequal Hlength].
  apply eq_type_sound in Hequal. apply Z.eqb_eq in Hlength. subst.
  inversion Hcheck; subst. eapply ty_ainit with (aty := elem) (ts := ts).
  - eapply Hchildren; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eauto.
  - exact Htypes.
  - exact Hstorage.
Qed.

Lemma checked_source_member_types_length : forall fields members types,
  source_member_types fields members = OK types ->
  List.length fields = List.length types.
Proof.
  induction fields as [|field fields IH]; intros members types Hcheck; simpl in Hcheck.
  - inversion Hcheck; reflexivity.
  - destruct (source_member_type field members); try discriminate.
    destruct (source_member_types fields members) eqn:Hrest; try discriminate.
    inversion Hcheck; subst. simpl. f_equal. eapply IH; exact Hrest.
Qed.

Theorem checked_structure_initializer_typing :
  forall env Gamma Sigma name fields es annotation result effects,
  (forall ts ef, type_check_exprs type_check_expr env Gamma Sigma es = OK (ts, ef) ->
    type_exprs env Gamma Sigma es ef ts) ->
  type_check_expr env Gamma Sigma (Sinit name fields es annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Sinit name fields es annotation) effects result.
Proof.
  intros env Gamma Sigma name fields es annotation result effects Hchildren Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_exprs type_check_expr env Gamma Sigma es) as [[ts ef]|err] eqn:Hargs;
    cbn in Hcheck; try discriminate.
  destruct annotation as [|pt|ptr|id a|elem len a|params eff rt va|]; try discriminate.
  all: try (destruct ptr as [basic pa|inner|params eff rt va]; try discriminate;
    destruct basic as [pt|id a|pt count a]; try discriminate).
  all: destruct (ident_eq name id) as [Hname|Hname]; try discriminate; subst name.
  all: destruct (PTree.get id env) as [co|] eqn:Hco; try discriminate.
  all: match type of Hcheck with context [list_eq_dec ident_eq ?actualFields ?declared] =>
    destruct (list_eq_dec ident_eq actualFields declared) as [Hfields|Hfields]; try discriminate
  end.
  all: destruct (source_member_types fields (co_members co)) as [bts|err] eqn:Hmembers;
    cbn in Hcheck; try discriminate.
  all: destruct (eq_types eq_type ts bts) eqn:Htypes; try discriminate.
  all: destruct (storage_type_check env (Stype id a)) eqn:Hstorage; try discriminate.
  all: apply eq_types_sound in Htypes; subst bts; inversion Hcheck; subst result effects.
  all: eapply ty_sinit with (id := id) (a := a) (co := co) (bts := ts);
    try reflexivity; try assumption.
  all: try solve [left; reflexivity | right; eexists; reflexivity].
  all: try (eapply Hchildren; reflexivity).
  all: eapply checked_source_member_types_length; exact Hmembers.
Qed.

Definition consistency_int := Vtype (Tint I32 Signed noattr).
Definition consistency_ref := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr).
Definition consistency_zero := Const (ConsInt Int.zero) consistency_int.
Definition consistency_pointer := Val (Vloc 1%positive Ptrofs.zero) consistency_ref.
Definition consistency_store := PTree.set 1%positive consistency_ref empty_stcontext.
Definition consistency_check := type_check_expr (PTree.empty _) empty_context consistency_store.
Definition checker_rejects (r : res (type * effect)) := match r with Error _ => True | OK _ => False end.

Example assignment_matching_source_accepted :
  consistency_check (Prim Massgn [consistency_pointer; consistency_zero] Utype) = OK (Utype, [Write]).
Proof. vm_compute; reflexivity. Qed.
Example assignment_unregistered_reference_rejected :
  checker_rejects (type_check_expr (PTree.empty _) empty_context empty_stcontext
    (Prim Massgn [consistency_pointer; consistency_zero] Utype)).
Proof. vm_compute; exact I. Qed.
Example assignment_mismatched_source_rejected :
  checker_rejects (consistency_check (Prim Massgn [consistency_pointer; Const ConsUnit Utype] Utype)).
Proof. vm_compute; exact I. Qed.
Example assignment_mismatched_result_rejected :
  checker_rejects (consistency_check (Prim Massgn [consistency_pointer; consistency_zero] consistency_int)).
Proof. vm_compute; exact I. Qed.
Example array_exact_shape_accepted :
  consistency_check (Ainit 1%positive (Atype consistency_int 2 noattr)
    [consistency_zero; consistency_zero] (Atype consistency_int 2 noattr)) =
  OK (Atype consistency_int 2 noattr, []).
Proof. vm_compute; reflexivity. Qed.
Example array_result_mismatch_rejected :
  checker_rejects (consistency_check (Ainit 1%positive (Atype consistency_int 2 noattr)
    [consistency_zero; consistency_zero] (Atype consistency_int 3 noattr))).
Proof. vm_compute; exact I. Qed.
Example array_length_mismatch_rejected :
  checker_rejects (consistency_check (Ainit 1%positive (Atype consistency_int 2 noattr)
    [consistency_zero] (Atype consistency_int 2 noattr))).
Proof. vm_compute; exact I. Qed.
Example array_element_mismatch_rejected :
  checker_rejects (consistency_check (Ainit 1%positive (Atype consistency_int 1 noattr)
    [Const ConsUnit Utype] (Atype consistency_int 1 noattr))).
Proof. vm_compute; exact I. Qed.

Example array_unit_elements_accepted :
  consistency_check (Ainit 1%positive (Atype Utype 2 noattr)
    [Const ConsUnit Utype; Const ConsUnit Utype] (Atype Utype 2 noattr)) =
  OK (Atype Utype 2 noattr, []).
Proof. vm_compute; reflexivity. Qed.

Example array_reference_elements_accepted :
  consistency_check (Ainit 1%positive (Atype consistency_ref 1 noattr)
    [consistency_pointer] (Atype consistency_ref 1 noattr)) =
  OK (Atype consistency_ref 1 noattr, []).
Proof. vm_compute; reflexivity. Qed.

Example array_nested_elements_accepted :
  consistency_check
    (Ainit 1%positive (Atype (Atype consistency_int 1 noattr) 1 noattr)
      [Ainit 2%positive (Atype consistency_int 1 noattr)
        [consistency_zero] (Atype consistency_int 1 noattr)]
      (Atype (Atype consistency_int 1 noattr) 1 noattr)) =
  OK (Atype (Atype consistency_int 1 noattr) 1 noattr, []).
Proof. vm_compute; reflexivity. Qed.

(* This checks the source storage kind, not packet-memory initialization. *)
Example array_bytes_slot_accepted :
  type_check_expr (PTree.empty _) (PTree.set 1%positive Bytes empty_context) empty_stcontext
    (Ainit 2%positive (Atype Bytes 1 noattr) [Var 1%positive Bytes] (Atype Bytes 1 noattr)) =
  OK (Atype Bytes 1 noattr, []).
Proof. vm_compute; reflexivity. Qed.

Definition consistency_volatile_int :=
  Vtype (Tint I32 Signed {| attr_volatile := true; attr_alignas := None |}).

Example array_volatile_element_rejected :
  checker_rejects (consistency_check
    (Ainit 1%positive (Atype consistency_volatile_int 1 noattr)
      [Const (ConsInt Int.zero) consistency_volatile_int]
      (Atype consistency_volatile_int 1 noattr))).
Proof. vm_compute; exact I. Qed.

Definition consistency_oversized_array :=
  Atype (Vtype (Tlong Signed noattr)) Ptrofs.max_unsigned noattr.

Example array_oversized_inline_element_rejected :
  checker_rejects
    (type_check_expr (PTree.empty _)
      (PTree.set 1%positive consistency_oversized_array empty_context) empty_stcontext
      (Ainit 2%positive (Atype consistency_oversized_array 1 noattr)
        [Var 1%positive consistency_oversized_array]
        (Atype consistency_oversized_array 1 noattr))).
Proof. vm_compute; exact I. Qed.
Print Assumptions checked_assignment_typing.
Print Assumptions checked_array_initializer_typing.
Print Assumptions checked_structure_initializer_typing.
Print Assumptions checked_value_typing.
Print Assumptions typed_value_checker_accepts.

(* This result is deliberately about the outer annotation. check_fun_ptr_fun
   additionally permits a function-pointer/function argument coercion that the
   current declarative ty_app rule does not express. *)
Lemma checked_application_result_annotation : forall env Gamma Sigma fn args annotation result effects,
  type_check_expr env Gamma Sigma (App fn args annotation) = OK (result, effects) ->
  annotation = result.
Proof.
  intros env Gamma Sigma fn args annotation result effects Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_expr env Gamma Sigma fn) as [[ft fe]|err]; cbn in Hcheck; try discriminate.
  destruct (type_check_exprs type_check_expr env Gamma Sigma args) as [[ts ae]|err]; cbn in Hcheck; try discriminate.
  destruct ft as [|prim|pt|sid attr|elem len attr|params eff rt va|]; try discriminate.
  - destruct pt as [bt attr|inner|params eff rt va]; try discriminate.
    destruct (check_fun_ptr_fun params ts && eq_type annotation rt) eqn:Hguard; try discriminate.
    apply andb_true_iff in Hguard as [_ Heq]. apply eq_type_sound in Heq.
    inversion Hcheck; subst; reflexivity.
  - destruct (check_fun_ptr_fun params ts && eq_type annotation rt) eqn:Hguard; try discriminate.
    apply andb_true_iff in Hguard as [_ Heq]. apply eq_type_sound in Heq.
    inversion Hcheck; subst; reflexivity.
Qed.
Definition consistency_function := Val (Vloc 1%positive Ptrofs.zero) (Ftype [] [] consistency_int false).
Example application_matching_result_accepted :
  consistency_check (App consistency_function [] consistency_int) = OK (consistency_int, []).
Proof. vm_compute; reflexivity. Qed.
Example application_result_mismatch_rejected :
  checker_rejects (consistency_check (App consistency_function [] Utype)).
Proof. vm_compute; exact I. Qed.
Print Assumptions checked_application_result_annotation.
