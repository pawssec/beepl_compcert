(* Audit only. These contradictions must NOT be used to fill legacy soundness
   admissions: they show why those statements need replacement. No legacy
   proof module or admitted project theorem is imported. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Import ListNotations.

Theorem legacy_well_formed_function_uninhabited : forall env Gamma Sigma ge vm m,
  ~ well_formed_function env Gamma Sigma ge vm m.
Proof.
  intros env Gamma Sigma ge vm m [Hcontract].
  assert (Hunit : type_expr env Gamma Sigma
    (Val(Vloc 1%positive Ptrofs.zero)(Ftype [] [] Utype false)) [] (Ftype [] [] Utype false)) by constructor.
  assert (Hbool : type_expr env Gamma Sigma
    (Val(Vloc 1%positive Ptrofs.zero)(Ftype [] [] (Vtype Tbool) false)) [] (Ftype [] [] (Vtype Tbool) false)) by constructor.
  destruct(Hcontract 1%positive Ptrofs.zero [] (Ftype [] [] Utype false) [] [] Utype false [] []
    Hunit eq_refl (ty_nil env Gamma Sigma)) as [fnUnit [HfindUnit [_ [_ [_ HreturnUnit]]]]].
  destruct(Hcontract 1%positive Ptrofs.zero [] (Ftype [] [] (Vtype Tbool) false) [] [] (Vtype Tbool) false [] []
    Hbool eq_refl (ty_nil env Gamma Sigma)) as [fnBool [HfindBool [_ [_ [_ HreturnBool]]]]].
  rewrite HfindUnit in HfindBool. inversion HfindBool; subst fnBool.
  congruence.
Qed.

Theorem legacy_store_well_typed_uninhabited : forall env Gamma Sigma ge vm m,
  ~ store_well_typed env Gamma Sigma ge vm m.
Proof.
  intros env Gamma Sigma ge vm m [_ [_ Hfunction]].
  eapply legacy_well_formed_function_uninhabited; exact Hfunction.
Qed.

(* The legacy classifier calls even [] stateful. Its disjunction recursion
   therefore returns true for EVERY effect list, independently of execution. *)
Theorem legacy_stateful_effect_classifier_constant : forall effects,
  is_stateful_effect effects=true.
Proof. induction effects as [|label rest IH]; simpl; [reflexivity|]. rewrite IH. apply orb_true_r. Qed.

(* The old normalization statement additionally requires its INPUT expression
   to be a value. Even a well-typed Unit expression disproves that standalone
   requirement; the impossible store premise merely hides the problem. *)
Example typed_nonvalue_unit : forall env Gamma Sigma,
  type_expr env Gamma Sigma (Unit Utype) [] Utype /\ is_value(Unit Utype)=false.
Proof. intros; split; [constructor|reflexivity]. Qed.

Theorem typed_input_need_not_be_value :
  ~ (forall env Gamma Sigma e effects ty,
       type_expr env Gamma Sigma e effects ty -> is_value e=true).
Proof.
  intros H. specialize(H (PTree.empty _) empty_context empty_stcontext (Unit Utype) [] Utype
    (ty_unit (PTree.empty _) empty_context empty_stcontext)). discriminate.
Qed.

(* Required replacements (specification discussion, not asserted theorems):

   - Source one-step/multistep safety uses program_runtime_configuration and
     initialized_heap_evolution. It quantifies over an ACTUAL transition or
     reachable state, existentially chooses the extended Sigma/objects/cells/
     packets and remaining effect, and preserves the result type. It cannot
     retain the old fixed-Sigma preservation statement across allocations.

   - Callable value validity is supplied by internal_code_locations plus the
     program code contract and packet location invariant. A shape-only
     ty_valfun premise cannot by itself demand that every arbitrary block have
     every syntactically possible signature.

   - Remaining expression effects may SHRINK when a read/write/allocation
     executes: sub_effect successor_effect source_effect is the safety claim.
     A theorem about performed effects needs a labeled trace or event history
     and an explicit interpretation of effect labels. Keeping a stateful label
     on a resulting value is not the current residual-effect semantics.

   - Normalization, if intended, must existentially quantify the final state,
     value, and step count and test is_value on the RESULT. It needs a separate
     well-founded-call/termination argument; finite-step type safety and
     bounded For iteration alone do not establish termination of recursion.
     No legacy admitted theorem is discharged from the contradictions above.
 *)

Print Assumptions legacy_well_formed_function_uninhabited.
Print Assumptions legacy_store_well_typed_uninhabited.
Print Assumptions legacy_stateful_effect_classifier_constant.
Print Assumptions typed_input_need_not_be_value.
