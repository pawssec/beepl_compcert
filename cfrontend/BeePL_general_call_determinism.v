(* Runtime uniqueness for all call parameter kinds.  Allocation store contexts
   are proof bookkeeping and need not agree between the two derivations. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_call_determinism BeePL_initializer_determinism.
Require Import BeePL_function_parameters BeePL_strict_progress BeePL_soundness_memory.
Import ListNotations.

Theorem full_parameter_binding_unique : forall ge vm m params values first,
  bind_variables ge vm m params values first ->
  forall second, bind_variables ge vm m params values second -> second = first.
Proof.
  intros * Hfirst. induction Hfirst; intros second Hsecond;
    inversion Hsecond; subst; auto.
  - repeat match goal with
    | H1 : PTree.get ?id ?vm = Some (?b1, ?ty),
      H2 : PTree.get ?id ?vm = Some (?b2, ?ty) |- _ =>
      assert (b1 = b2) by congruence; first [progress subst | clear H2]
    end.
    match goal with
    | H1 : assign_addr _ _ _ _ _ Full _ ?m1 _,
      H2 : assign_addr _ _ _ _ _ Full _ ?m2 _ |- _ =>
      destruct (full_assignment_unique _ _ _ _ _ _ _ _ _ _ H1 H2) as [Hm _]; subst m2
    end.
    eapply IHHfirst; eauto.
  - exfalso; eapply unit_full_assignment_impossible; eauto.
  - exfalso; eapply unit_full_assignment_impossible; eauto.
Qed.

Theorem general_evaluated_application_step_unique :
  forall (ge : genv) p caller m b offset annotation es ret first caller1 e1,
  Forall (fun e => exists v ty, e = Val v ty) es ->
  ssem_expr ge p caller m (App (Val (Vloc b offset) annotation) es ret) first caller1 e1 ->
  forall second caller2 e2,
  ssem_expr ge p caller m (App (Val (Vloc b offset) annotation) es ret) second caller2 e2 ->
  second = first /\ caller2 = caller1 /\ e2 = e1.
Proof.
  intros * Hvalues Hfirst second caller2 e2 Hsecond.
  pose proof (all_value_arguments_is_values es Hvalues) as Hready.
  inversion Hfirst; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto]; try congruence;
    inversion Hsecond; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto]; try congruence.
  all: repeat match goal with
  | H1 : Genv.find_funct ?ge ?v = Some (Internal ?f1),
    H2 : Genv.find_funct ?ge ?v = Some (Internal ?f2) |- _ =>
    assert (f1 = f2) by congruence; first [progress subst | clear H2]
  end.
  all: try solve [exfalso; eapply function_parameters_cannot_use_data_binding; eauto].
  all: try match goal with
  | H1 : function_parameter_partition _ _ _ _ _ _,
    H2 : function_parameter_partition _ _ _ _ _ _ |- _ =>
    destruct (function_partition_unique _ _ _ _ _ _ H1 _ _ _ H2)
      as [Hcodes [Hparams Hvals]]; subst
  end.
  all: try match goal with
  | H1 : alloc_variables _ _ _ _ _ ?vm1 ?m1 _,
    H2 : alloc_variables _ _ _ _ _ ?vm2 ?m2 _ |- _ =>
    destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ H1 _ _ _ _ H2)
      as [Hmap Hmem]; subst vm2 m2
  end.
  all: try match goal with
  | H1 : bind_variables _ _ _ _ _ ?m1,
    H2 : bind_variables _ _ _ _ _ ?m2 |- _ =>
    pose proof (full_parameter_binding_unique _ _ _ _ _ _ H1 _ H2) as Hmem;
    subst m2
  end.
  all: repeat split; reflexivity.
Qed.

Print Assumptions full_parameter_binding_unique.
Print Assumptions general_evaluated_application_step_unique.
