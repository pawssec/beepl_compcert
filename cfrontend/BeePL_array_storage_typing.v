(* Source typing supplies allocation storage conditions. These projections do
   not claim that primitive-array initialization proves nested/ref/Bytes cases:
   storage admissibility remains a separate, general type predicate. *)
Require Import List ZArith Lia Integers AST Maps Ctypes.
Require Import BeeTypes BeePL BeePL_typesystem BeePL_storage_types BeePL_array_proofs.
Local Open Scope Z_scope.

Lemma typed_array_storage_admissible : forall env Gamma Sigma arr ty es result ef,
  type_expr env Gamma Sigma (Ainit arr ty es result) ef result ->
  storage_type_check env ty = true.
Proof. intros env Gamma Sigma arr ty es result ef Htyped; inversion Htyped; subst; assumption. Qed.

Theorem typed_primitive_array_storage_conditions : forall env Gamma Sigma arr pt len attr es ef,
  type_expr env Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false /\
  sizeof_ptype pt * len <= Ptrofs.max_unsigned.
Proof.
  intros env Gamma Sigma arr pt len attr es ef Htyped.
  pose proof (typed_array_storage_admissible _ _ _ _ _ _ _ _ Htyped) as Hstorage.
  split.
  - eapply array_storage_element_nonvolatile; exact Hstorage.
  - pose proof (storage_type_size_bounds _ _ Hstorage) as [Hlower Hupper].
    pose proof (typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped) as [_ [elem [a Hextent]]].
    inversion Hextent; subst. simpl in Hupper.
    rewrite Z.max_r in Hupper by lia. exact Hupper.
Qed.

Print Assumptions typed_array_storage_admissible.
Print Assumptions typed_primitive_array_storage_conditions.
