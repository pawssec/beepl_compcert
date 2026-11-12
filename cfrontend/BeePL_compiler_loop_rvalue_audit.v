(* Regression for actual generated loop guards after the RV repair.
   The historical bare-comparison impossibility remains as a boundary fact. *)
Require Import List String ZArith Integers AST Maps Events Memory SimplExpr Ctypes Csyntax Csem Cstrategy.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_compiler_bindings.
Import ListNotations.

Definition loop_audit_type : BeeTypes.type :=
  Vtype (BeeTypes.Tint I32 Signed noattr).
Definition loop_audit_source (direction : dir) : BeePL.expr :=
  For (Const (ConsInt Int.zero) loop_audit_type)
      (Const (ConsInt Int.one) loop_audit_type) direction (Unit Utype) Utype.
Definition loop_audit_context : bcompiler_ctx :=
 {| arg_ctx := []; benv := PTree.empty _; reserved_identifiers := [];
    lexical_bindings := empty_compiler_bindings |}.
Definition loop_audit_generated (direction : dir) :=
  transBeePL_expr_st (PTree.empty _) (loop_audit_source direction) [] loop_audit_context
    (mkgenerator 1%positive []).

Definition loop_outer_guard (statement : Csyntax.statement) : option Csyntax.expr :=
  match statement with
  | Ssequence _ (Sifthenelse guard _ _) => Some guard
  | _ => None
  end.
Definition loop_audit_guard (direction : dir) : option Csyntax.expr :=
  match loop_audit_generated direction with
  | Res (statement, _, _) _ _ => loop_outer_guard statement
  | Err _ => None
  end.
Definition loop_audit_ctype := Ctypes.Tint I32 Signed noattr.
Definition loop_audit_read (id : ident) :=
  Evalof (Evar id loop_audit_ctype) loop_audit_ctype.
Definition loop_audit_comparison (direction : dir) :=
  match direction with Up => Cop.Ole | Down => Cop.Oge end.
Definition loop_audit_result (direction : dir) :=
  match direction with Up => Values.Vint Int.one | Down => Values.Vint Int.zero end.

Lemma actual_loop_translation_reads_bounds : forall direction,
  exists low high,
  loop_audit_guard direction = Some
    (Ebinop (loop_audit_comparison direction)
      (loop_audit_read low) (loop_audit_read high) loop_audit_ctype).
Proof. destruct direction; vm_compute; eexists; eexists; reflexivity. Qed.

Definition bare_comparison (expression : Csyntax.expr) : bool :=
  match expression with
  | Ebinop _ (Evar _ _) (Evar _ _) _ => true
  | _ => false
  end.

Lemma bare_comparison_cannot_evaluate : forall guard,
  bare_comparison guard = true ->
  forall ge env m trace final value,
  ~ Cstrategy.eval_expression ge env m guard trace final value.
Proof.
  intros guard Hshape ge env m trace final value Heval.
  destruct guard; simpl in Hshape; try discriminate.
  destruct guard1; simpl in Hshape; try discriminate.
  destruct guard2; simpl in Hshape; try discriminate.
  inversion Heval; subst.
  match goal with H : Cstrategy.eval_expr _ _ _ RV (Ebinop _ _ _ _) _ _ _ |- _ => inversion H; subst end.
  match goal with H : Cstrategy.eval_expr _ _ _ RV (Evar _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma loop_audit_read_value : forall ge env m id block value,
  PTree.get id env = Some (block, loop_audit_ctype) ->
  Mem.load Mint32 m block 0 = Some value ->
  eval_simple_rvalue ge env m (loop_audit_read id) value.
Proof.
  intros ge env m id block value Henv Hload.
  unfold loop_audit_read.
  eapply esr_rvalof; [apply esl_var_local; exact Henv|reflexivity|reflexivity|].
  eapply deref_loc_value; [reflexivity|reflexivity|].
  simpl. rewrite Ptrofs.unsigned_zero. exact Hload.
Qed.

Lemma loop_audit_guard_evaluates : forall direction low high ge env m low_block high_block,
  PTree.get low env = Some (low_block, loop_audit_ctype) ->
  PTree.get high env = Some (high_block, loop_audit_ctype) ->
  Mem.load Mint32 m low_block 0 = Some (Values.Vint Int.zero) ->
  Mem.load Mint32 m high_block 0 = Some (Values.Vint Int.one) ->
  eval_expression ge env m
    (Ebinop (loop_audit_comparison direction)
      (loop_audit_read low) (loop_audit_read high) loop_audit_ctype)
    Events.E0 m (loop_audit_result direction).
Proof.
  intros direction low high ge env m low_block high_block Hlow Hhigh Llow Lhigh.
  eapply eval_expression_intro.
  - change Events.E0 with (Events.E0 ** Events.E0).
    eapply eval_binop; apply eval_valof; [reflexivity|constructor|reflexivity|constructor].
  - eapply esr_binop.
    + eapply loop_audit_read_value; eauto.
    + eapply loop_audit_read_value; eauto.
    + destruct direction; reflexivity.
Qed.

(* Actual successful compiler output, from target bindings and actual loads;
   there is no premise asserting evaluation of the generated expression. *)
Theorem actual_loop_guard_execution : forall direction,
  exists low high guard,
    loop_audit_guard direction = Some guard /\
    forall ge env m low_block high_block,
      PTree.get low env = Some (low_block, loop_audit_ctype) ->
      PTree.get high env = Some (high_block, loop_audit_ctype) ->
      Mem.load Mint32 m low_block 0 = Some (Values.Vint Int.zero) ->
      Mem.load Mint32 m high_block 0 = Some (Values.Vint Int.one) ->
      eval_expression ge env m guard Events.E0 m (loop_audit_result direction).
Proof.
  intros direction.
  destruct (actual_loop_translation_reads_bounds direction) as [low [high H]].
  exists low, high, (Ebinop (loop_audit_comparison direction)
      (loop_audit_read low) (loop_audit_read high) loop_audit_ctype).
  split; [exact H|]. intros. eapply loop_audit_guard_evaluates; eauto.
Qed.
Print Assumptions actual_loop_guard_execution.

(* Comparisons produce Vint booleans even when their operands are longs.
   The generated comparison result must therefore be int, not bound type. *)
Lemma long_bound_comparison_returns_int : forall m,
  Cop.sem_binary_operation (PTree.empty _) Cop.Ole
    (Values.Vlong Int64.zero) (Ctypes.Tlong Signed noattr)
    (Values.Vlong Int64.one) (Ctypes.Tlong Signed noattr) m =
  Some (Values.Vint Int.one).
Proof. intros; reflexivity. Qed.

Lemma long_annotated_comparison_cannot_test : forall m,
  Cop.bool_val (Values.Vint Int.one) (Ctypes.Tlong Signed noattr) m = None.
Proof. intros; reflexivity. Qed.

Definition loop_audit_long_type : BeeTypes.type := Vtype (BeeTypes.Tlong Signed noattr).
Definition loop_audit_long_source (direction : dir) : BeePL.expr :=
  For (Const (ConsLong Int64.zero) loop_audit_long_type)
      (Const (ConsLong Int64.one) loop_audit_long_type) direction (Unit Utype) Utype.
Definition loop_audit_long_guard (direction : dir) : option Csyntax.expr :=
  match transBeePL_expr_st (PTree.empty _) (loop_audit_long_source direction)
    [] loop_audit_context (mkgenerator 1%positive []) with
  | Res (statement, _, _) _ _ => loop_outer_guard statement
  | Err _ => None
  end.
Definition loop_audit_long_ctype := Ctypes.Tlong Signed noattr.
Definition loop_audit_long_read (id : ident) :=
  Evalof (Evar id loop_audit_long_ctype) loop_audit_long_ctype.

Lemma actual_long_loop_guard_reads_bounds : forall direction,
  exists low high,
    loop_audit_long_guard direction = Some
      (Ebinop (loop_audit_comparison direction)
        (loop_audit_long_read low) (loop_audit_long_read high) loop_audit_ctype).
Proof. destruct direction; vm_compute; eexists; eexists; reflexivity. Qed.

Lemma loop_audit_long_read_value : forall ge env m id block value,
  PTree.get id env = Some (block, loop_audit_long_ctype) ->
  Mem.load Mint64 m block 0 = Some value ->
  eval_simple_rvalue ge env m (loop_audit_long_read id) value.
Proof.
  intros ge env m id block value Henv Hload.
  unfold loop_audit_long_read.
  eapply esr_rvalof; [apply esl_var_local; exact Henv|reflexivity|reflexivity|].
  eapply deref_loc_value; [reflexivity|reflexivity|].
  simpl. rewrite Ptrofs.unsigned_zero. exact Hload.
Qed.

Theorem actual_long_loop_guard_execution : forall direction,
  exists low high guard,
    loop_audit_long_guard direction = Some guard /\
    forall ge env m low_block high_block,
      PTree.get low env = Some (low_block, loop_audit_long_ctype) ->
      PTree.get high env = Some (high_block, loop_audit_long_ctype) ->
      Mem.load Mint64 m low_block 0 = Some (Values.Vlong Int64.zero) ->
      Mem.load Mint64 m high_block 0 = Some (Values.Vlong Int64.one) ->
      eval_expression ge env m guard Events.E0 m (loop_audit_result direction) /\
      Cop.bool_val (loop_audit_result direction) (Csyntax.typeof guard) m =
        Some (match direction with Up => true | Down => false end).
Proof.
  intros direction.
  destruct (actual_long_loop_guard_reads_bounds direction) as [low [high Hguard]].
  exists low, high, (Ebinop (loop_audit_comparison direction)
      (loop_audit_long_read low) (loop_audit_long_read high) loop_audit_ctype).
  split; [exact Hguard|].
  intros ge env m low_block high_block Hlow Hhigh Llow Lhigh; split.
  - eapply eval_expression_intro.
    + change Events.E0 with (Events.E0 ** Events.E0).
      eapply eval_binop; apply eval_valof; [reflexivity|constructor|reflexivity|constructor].
    + eapply esr_binop.
      * eapply loop_audit_long_read_value; eauto.
      * eapply loop_audit_long_read_value; eauto.
      * destruct direction; reflexivity.
  - destruct direction; reflexivity.
Qed.
Print Assumptions actual_long_loop_guard_execution.
