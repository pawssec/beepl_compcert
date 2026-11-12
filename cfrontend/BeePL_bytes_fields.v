Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_fields.
Local Open Scope Z_scope.

(* Bytes are readable descriptors, unlike aggregate values. Their scalar-read
   alternative therefore needs the same actual field-layout evidence as the
   descriptor-read rule; aggregate kind alone is insufficient. *)
Theorem bytes_field_value_preservation :
  forall bge p Gamma Sigma vm m b ofs base_type f result m' vm' e',
  aggregate_field_access bge.(genv_cenv) m b ofs base_type f Bytes result ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    object_type_at bge.(genv_cenv) Sigma b (Ptrofs.unsigned ofs) (Stype sid attr)) ->
  ssem_expr bge p vm m (Sfield (Val (Vloc b ofs) base_type) f Bytes) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr bge.(genv_cenv) Gamma Sigma e' nil Bytes.
Proof.
  intros bge p Gamma Sigma vm m b ofs base_type f result m' vm' e'
    Haccess Hbase Hstep.
  inversion Hstep; subst.
  - exfalso; eapply value_has_no_small_step; eauto.
  - inversion Haccess; subst.
    match goal with Hshape : _ = Stype _ _ \/ _ = Ptrtype _ |- _ =>
      destruct Hshape as [Hshape | Hshape]; inversion Hshape; subst end.
    match goal with Ha : PTree.get ?id ?env = Some ?a,
      Hb : PTree.get ?id ?env = Some ?b |- _ =>
      assert (a = b) by congruence; subst end.
    match goal with Ha : field_offset _ _ _ = OK (?da, ?bf),
      Hb : field_offset _ _ _ = OK (?db, Full) |- _ =>
      assert (Hoffsets : da = db /\ bf = Full) by (split; congruence);
      destruct Hoffsets as [? ?]; subst end.
    match goal with Hr : deref_addr Bytes _ _ _ Full _ |- _ =>
      inversion Hr; subst; try discriminate end.
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (Ptrofs.unsigned_range ofs).
    rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr by lia.
    eapply aggregate_field_access_typed_result; eauto.
  - inversion Haccess; subst.
    match goal with Hshape : _ = Stype _ _ \/ _ = Ptrtype _ |- _ =>
      destruct Hshape as [Hshape | Hshape]; inversion Hshape; subst end.
    match goal with Ha : PTree.get ?id ?env = Some ?a,
      Hb : PTree.get ?id ?env = Some ?b |- _ =>
      assert (a = b) by congruence; subst end.
    match goal with Ha : field_offset _ _ _ = OK (?da, ?bf),
      Hb : field_offset _ _ _ = OK (?db, Full) |- _ =>
      assert (Hoffsets : da = db /\ bf = Full) by (split; congruence);
      destruct Hoffsets as [? ?]; subst end.
    match goal with Hr : deref_addr Bytes _ _ _ Full _ |- _ =>
      inversion Hr; subst; try discriminate end.
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (Ptrofs.unsigned_range ofs).
    rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr by lia.
    eapply aggregate_field_access_typed_result; eauto.
  - split; [reflexivity|]. split; [reflexivity|].
    eapply aggregate_field_access_typed_result; eauto.
Qed.
Print Assumptions bytes_field_value_preservation.
