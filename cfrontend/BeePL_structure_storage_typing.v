(* Source struct typing establishes storage conditions for actual declared
   members. This does not replace layout/alignment/distinctness evidence. *)
Require Import List ZArith Lia Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL BeePL_sem BeePL_typesystem BeePL_storage_types.
Require Import BeePL_initialization_proofs BeePL_layout_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma structure_result_attribute_unique : forall sid first second result,
  structure_result_type sid first result -> structure_result_type sid second result -> first = second.
Proof.
  intros sid first second result Hfirst Hsecond.
  destruct Hfirst as [Hfirst|[pa Hfirst]]; destruct Hsecond as [Hsecond|[pb Hsecond]];
    rewrite Hfirst in Hsecond; inversion Hsecond; reflexivity.
Qed.

Lemma typed_structure_storage_admissible : forall env Gamma Sigma sid ids es result ef attr,
  type_expr env Gamma Sigma (Sinit sid ids es result) ef result ->
  structure_result_type sid attr result ->
  storage_type_check env (Stype sid attr) = true.
Proof.
  intros env Gamma Sigma sid ids es result ef attr Htyped Hshape.
  inversion Htyped; subst.
  match goal with
  | Hstorage : storage_type_check ?environment (Stype ?name ?other) = true,
    Hother : structure_result_type ?name ?other ?output
    |- storage_type_check ?environment (Stype ?name ?wanted) = true =>
      assert (Heq : other = wanted) by (eapply structure_result_attribute_unique; eauto);
      rewrite <- Heq; exact Hstorage
  end.
Qed.

Lemma typed_structure_planned_member : forall env Gamma Sigma sid fs result ef co,
  type_expr env Gamma Sigma (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  env ! sid = Some co ->
  forall field, In field fs ->
    source_member_type (planned_field field) (co_members co) = OK (Vtype (planned_type field)).
Proof.
  intros env Gamma Sigma sid fs result ef co Htyped Hco.
  inversion Htyped; subst.
  match goal with Hargs : type_exprs _ _ _ (planned_expressions fs) _ _ |- _ =>
    destruct (typed_planned_arguments _ _ _ _ _ _ Hargs) as [Htypes Hvalues]
  end.
  subst bts. assert (co0 = co) by congruence. subst co0.
  intros field Hin. eapply source_planned_member_types; eauto.
Qed.

Theorem typed_primitive_structure_storage_conditions :
  forall env Gamma Sigma sid attr pa result fs ef co,
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  type_expr env Gamma Sigma (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  env ! sid = Some co ->
  co_sizeof co <= Ptrofs.max_unsigned /\
  (forall field, In field fs -> type_is_volatile (transBeePL_type (Vtype (planned_type field))) = false).
Proof.
  intros env Gamma Sigma sid attr pa result fs ef co Hresult Htyped Hco.
  assert (Hshape : structure_result_type sid attr result).
  { destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity]. }
  pose proof (typed_structure_storage_admissible _ _ _ _ _ _ _ _ _ Htyped Hshape) as Hstorage.
  split.
  - pose proof (storage_type_size_bounds _ _ Hstorage) as [_ Hbound]. simpl in Hbound.
    rewrite Hco in Hbound. exact Hbound.
  - intros field Hin. eapply storage_type_member_nonvolatile; [exact Hstorage|exact Hco|].
    eapply typed_structure_planned_member; eauto.
Qed.
Print Assumptions typed_structure_storage_admissible.
Print Assumptions typed_structure_planned_member.
Print Assumptions typed_primitive_structure_storage_conditions.
