(* Unit parameters have real scope bindings and zero-size allocation, but no
   stored payload. These are semantic regressions, not kernel/compiler tests. *)
Require Import List ZArith AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem.
Import ListNotations.

Lemma unit_has_no_full_memory_read : forall m b ofs v,
  ~ deref_addr Utype m b ofs Full v.
Proof. intros m b ofs v Hread. inversion Hread; subst; discriminate. Qed.

Lemma unit_has_no_full_memory_assignment : forall bge m b ofs v m' result,
  ~ assign_addr bge Utype m b ofs Full v m' result.
Proof. intros bge m b ofs v m' result Hassign. inversion Hassign; subst; discriminate. Qed.

Theorem unit_parameter_allocation_binding_read : forall bge Sigma p m x,
  exists allocated b Sigma' callee,
    Mem.alloc m 0 0 = (allocated, b) /\
    alloc_variables bge Sigma empty_vmap m [(x, Utype)] callee allocated Sigma' /\
    bind_variables bge callee allocated [(x, Utype)] [Vunit] allocated /\
    ssem_expr bge p callee allocated (Var x Utype) allocated callee (Val Vunit Utype) /\
    bsem_expr bge p callee allocated (Var x Utype) allocated callee Vunit.
Proof.
  intros bge Sigma p m x. destruct (Mem.alloc m 0 0) as [allocated b] eqn:Halloc.
  exists allocated, b, (PTree.set b Utype Sigma), (PTree.set x (b, Utype) empty_vmap).
  split; [reflexivity |]. split.
  - eapply alloc_variables_con; [unfold balloc; simpl; rewrite Halloc; reflexivity | constructor].
  - split; [eapply bind_variables_unit; [apply PTree.gss | constructor] |].
    split; [apply ssem_lvar_unit with (b := b) | apply bsem_lvar_unit with (b := b)]; apply PTree.gss.
Qed.

Lemma unit_parameter_binding_memory_identity : forall bge vm m x m',
  bind_variables bge vm m [(x, Utype)] [Vunit] m' -> m' = m.
Proof.
  intros bge vm m x m' Hbind. inversion Hbind; subst.
  - exfalso. eapply unit_has_no_full_memory_assignment; eauto.
  - match goal with Hnil : bind_variables _ _ _ [] [] _ |- _ => inversion Hnil; reflexivity end.
Qed.

Lemma unit_variable_step_memory_identity : forall bge p vm m x m' vm' e',
  ssem_expr bge p vm m (Var x Utype) m' vm' e' ->
  m' = m /\ vm' = vm /\ e' = Val Vunit Utype.
Proof.
  intros bge p vm m x m' vm' e' Hstep. inversion Hstep; subst;
    try solve [exfalso; eapply unit_has_no_full_memory_read; eauto];
    repeat split; reflexivity.
Qed.

Print Assumptions unit_parameter_allocation_binding_read.
Print Assumptions unit_parameter_binding_memory_identity.
Print Assumptions unit_variable_step_memory_identity.
