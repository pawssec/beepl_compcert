(* Aggregate dereference produces a typed address descriptor. Initialized field
   contents and whole-program heap validity remain separate obligations. *)
Require Import List AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_runtime_locations BeePL_aggregate_memory.
Import ListNotations.

Lemma aggregate_descriptor_value_typed : forall cenv Gamma Sigma m objects b base ty,
  aggregate_objects_valid cenv Sigma m objects -> objects b base ty ->
  type_expr cenv Gamma Sigma (Val (Vloc b base) ty) nil ty.
Proof.
  intros cenv Gamma Sigma m objects b base ty Hvalid Hobject.
  pose proof (aggregate_object_typing _ _ _ _ Hvalid _ _ _ Hobject) as Htyped.
  pose proof (aggregate_object_readable _ _ _ _ Hvalid _ _ _ Hobject) as Hreadable.
  destruct Hreadable as [Hkind Hrest]. destruct ty; simpl in Hkind; try discriminate;
    constructor; exact Htyped.
Qed.

Lemma aggregate_descriptor_no_scalar_read : forall cenv m b base ty v,
  aggregate_readable cenv m b base ty -> ~ deref_addr ty m b base Full v.
Proof.
  intros cenv m b base ty v [Hkind Hrest] Hread.
  destruct ty; simpl in Hkind; try discriminate; inversion Hread; subst; discriminate.
Qed.

Theorem aggregate_descriptor_dereference_progress :
  forall bge Gamma Sigma p vm m cells objects b base basic attr,
  aggregate_objects_valid bge.(genv_cenv) Sigma m objects ->
  objects b base (construct_type_btype basic) ->
  ssem_expr bge p vm m
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic))
    m vm (Val (Vloc b base) (construct_type_btype basic)) /\
  type_expr bge.(genv_cenv) Gamma Sigma
    (Val (Vloc b base) (construct_type_btype basic)) nil (construct_type_btype basic) /\
  runtime_locations (descriptor_heap_locations bge cells objects)
    (Val (Vloc b base) (construct_type_btype basic)).
Proof.
  intros bge Gamma Sigma p vm m cells objects b base basic attr Hvalid Hobject.
  pose proof (aggregate_object_readable _ _ _ _ Hvalid _ _ _ Hobject) as Hreadable.
  split; [apply ssem_deref_aggregate; exact Hreadable |]. split.
  - eapply aggregate_descriptor_value_typed; eauto.
  - apply aggregate_descriptor_direct; [exact (proj1 Hreadable) | exact Hobject].
Qed.

Theorem aggregate_descriptor_dereference_preservation :
  forall bge Gamma Sigma p vm m cells objects b base basic attr m' vm' e',
  aggregate_objects_valid bge.(genv_cenv) Sigma m objects ->
  objects b base (construct_type_btype basic) ->
  ssem_expr bge p vm m
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic)) m' vm' e' ->
  m' = m /\ vm' = vm /\ e' = Val (Vloc b base) (construct_type_btype basic) /\
  type_expr bge.(genv_cenv) Gamma Sigma e' nil (construct_type_btype basic) /\
  runtime_locations (descriptor_heap_locations bge cells objects) e'.
Proof.
  intros bge Gamma Sigma p vm m cells objects b base basic attr m' vm' e'
    Hvalid Hobject Hstep.
  pose proof (aggregate_object_readable _ _ _ _ Hvalid _ _ _ Hobject) as Hreadable.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - exfalso. eapply aggregate_descriptor_no_scalar_read; eauto.
  - repeat split; try reflexivity.
    + eapply aggregate_descriptor_value_typed; eauto.
    + apply aggregate_descriptor_direct; [exact (proj1 Hreadable) | exact Hobject].
Qed.

Print Assumptions aggregate_descriptor_dereference_progress.
Print Assumptions aggregate_descriptor_dereference_preservation.
