(* Primitive arrays have exactly their indexed scalar leaves. Chunk equality
   is interpreted through the actual CompCert memory chunk, so bool's byte
   representation does not require duplicate cells for chunk aliases. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_aggregate_memory BeePL_object_paths.
Require Import BeePL_object_coverage BeePL_array_proofs.
Local Open Scope Z_scope.

Lemma primitive_array_object_paths : forall cenv pt len attr delta ty,
  object_path cenv (Atype (Vtype pt) len attr) delta ty ->
  (delta = 0 /\ ty = Atype (Vtype pt) len attr) \/
  exists index, 0 <= index < len /\ delta = index * sizeof_ptype pt /\ ty = Vtype pt.
Proof.
  intros cenv pt len attr delta ty Hpath.
  remember (Atype (Vtype pt) len attr) as root eqn:Hroot.
  induction Hpath.
  - left; auto.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent] | [index [Hindex [Hbase Hparent]]]];
      discriminate Hparent.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent] | [other [Hother [Hbase Hparent]]]].
    + inversion Hparent; subst. right. exists index. simpl. repeat split; auto; lia.
    + discriminate Hparent.
Qed.

Theorem primitive_array_scalar_leaf : forall cenv pt len attr delta ty chunk,
  scalar_object_leaf cenv (Atype (Vtype pt) len attr) delta ty chunk ->
  exists index, 0 <= index < len /\ delta = index * sizeof_ptype pt /\
    ty = Vtype pt /\
    transl_bchunk_cchunk chunk = transl_bchunk_cchunk (chunk_of_ptype pt).
Proof.
  intros cenv pt len attr delta ty chunk [Hpath Hmode].
  destruct (primitive_array_object_paths _ _ _ _ _ _ Hpath)
    as [[Hdelta Hty] | [index [Hindex [Hdelta Hty]]]].
  - subst ty. discriminate Hmode.
  - subst ty. exists index. split; [exact Hindex |]. split; [exact Hdelta |].
    split; [reflexivity |]. rewrite primitive_chunk_access in Hmode. congruence.
Qed.

Theorem primitive_array_descriptor_coverage : forall cenv objects cells b pt count attr,
  initialized_object_coverage cenv objects cells ->
  initialized_object_coverage cenv
    (add_aggregate_descriptor objects b Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr))
    (extend_array_layout cells b pt count).
Proof.
  intros cenv objects cells b pt count attr Hcoverage block base root Hobject delta ty chunk Hleaf.
  destruct Hobject as [Hold | [Hblock [Hbase Hroot]]].
  - destruct (Hcoverage _ _ _ Hold _ _ _ Hleaf) as [stored [Hcell Heq]].
    exists stored. split; [left; exact Hcell | exact Heq].
  - subst block base root.
    destruct (primitive_array_scalar_leaf _ _ _ _ _ _ _ Hleaf)
      as [index [Hindex [Hdelta [Hty Hchunk]]]].
    exists (chunk_of_ptype pt). split; [|symmetry; exact Hchunk].
    right. exists (Z.to_nat index).
    assert (Hnat : (Z.to_nat index < count)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    split; [exact Hnat |]. split; [reflexivity |]. split.
    + rewrite Ptrofs.unsigned_zero, Z.add_0_l, Hdelta, Z2Nat.id by lia. reflexivity.
    + split; [exact Hty | reflexivity].
Qed.

Corollary primitive_array_root_coverage : forall cenv cells b pt count attr,
  initialized_object_coverage cenv
    (fun block base root => block = b /\ base = Ptrofs.zero /\
      root = Atype (Vtype pt) (Z.of_nat count) attr)
    (extend_array_layout cells b pt count).
Proof.
  intros cenv cells b pt count attr block base root Hroot delta ty chunk Hleaf.
  eapply (primitive_array_descriptor_coverage cenv (fun _ _ _ => False) cells b pt count attr).
  - intros x y z Hfalse; contradiction.
  - right; exact Hroot.
  - exact Hleaf.
Qed.

Print Assumptions primitive_array_scalar_leaf.
Print Assumptions primitive_array_descriptor_coverage.
Print Assumptions primitive_array_root_coverage.
