(* Initialization of primitive and ordinary-reference parameters. Reference
   payloads retain their exact target, offset and declarative store evidence. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_initialization_proofs BeePL_option_representation.

Definition scalar_parameter_type (ty : type) : Prop :=
  ((exists pt, ty = Vtype pt) \/ (exists bt a, ty = Ptrtype (Reftype bt a)) \/
    (exists bt a, ty = Ptrtype (Otype (Reftype bt a)))) /\
  type_is_volatile (transBeePL_type ty) = false.

Definition scalar_parameter_chunk (ty : type) : bmemory_chunk :=
  match ty with
  | Vtype pt => chunk_of_ptype pt
  | Ptrtype (Reftype _ _) | Ptrtype (Otype (Reftype _ _)) =>
      if Archi.ptr64 then BMint64 else BMint32
  | _ => BMbool
  end.

Lemma scalar_parameter_chunk_access : forall ty,
  scalar_parameter_type ty ->
  access_mode_type ty = By_value (transl_bchunk_cchunk (scalar_parameter_chunk ty)).
Proof.
  intros ty [[ [pt Hty] | [[bt [a Hty]] | [bt [a Hty]]]] Hvolatile]; subst ty.
  - apply primitive_chunk_access.
  - simpl. unfold Mptr. destruct Archi.ptr64; reflexivity.
  - simpl. unfold Mptr. destruct Archi.ptr64; reflexivity.
Qed.

Lemma scalar_parameter_chunk_size : forall cenv ty,
  scalar_parameter_type ty ->
  size_chunk (transl_bchunk_cchunk (scalar_parameter_chunk ty)) = sizeof_type cenv ty.
Proof.
  intros cenv ty [[ [pt Hty] | [[bt [a Hty]] | [bt [a Hty]]]] Hvolatile]; subst ty.
  - apply primitive_chunk_size.
  - simpl. destruct Archi.ptr64; reflexivity.
  - simpl. destruct Archi.ptr64; reflexivity.
Qed.

Lemma ordinary_reference_store_normalization : forall bt a target offset,
  decode_memory_value (Ptrtype (Reftype bt a))
    (Values.Val.load_result
      (transl_bchunk_cchunk (scalar_parameter_chunk (Ptrtype (Reftype bt a))))
      (Values.Vptr target offset)) = OK (Vloc target offset).
Proof. intros. simpl. destruct Archi.ptr64 eqn:Harch; simpl; rewrite ?Harch; reflexivity. Qed.

Lemma typed_optional_reference_payload : forall cenv Gamma Sigma v bt a,
  type_expr cenv Gamma Sigma (Val v (Ptrtype (Otype (Reftype bt a)))) nil
    (Ptrtype (Otype (Reftype bt a))) ->
  exists payload, v = Voption payload /\ option_reference_payload payload.
Proof.
  intros cenv Gamma Sigma v bt a Htyped. inversion Htyped; subst.
  eexists. split; [reflexivity |].
  destruct o as [payload |]; simpl; [|exact I].
  match goal with Hpayload : forall v, Some payload = Some v -> _ |- _ =>
    pose proof (Hpayload payload eq_refl) as Hinner; inversion Hinner; subst; exact I
  end.
Qed.

Lemma scalar_parameter_store_normalization : forall cenv Gamma Sigma L ty v,
  scalar_parameter_type ty ->
  type_expr cenv Gamma Sigma (Val v ty) nil ty ->
  value_locations L v ty ->
  exists stored,
    decode_memory_value ty
      (Values.Val.load_result (transl_bchunk_cchunk (scalar_parameter_chunk ty))
        (trans_bvalue_cvalue v)) = OK stored /\
    type_expr cenv Gamma Sigma (Val stored ty) nil ty /\
    value_locations L stored ty.
Proof.
  intros cenv Gamma Sigma L ty v [[ [pt Hty] | [[bt [a Hty]] | [bt [a Hty]]]] Hvolatile] Htyped Hlocated;
    subst ty.
  - destruct (primitive_store_normalization pt v (declarative_value_shape _ _ _ _ _ Htyped))
      as [stored [Hdecode Hshape]].
    exists stored. split; [exact Hdecode |]. split.
    + destruct pt, stored; simpl in Hshape; try contradiction; constructor.
    + eapply primitive_value_locations; exact Hshape.
  - inversion Htyped; subst.
    eexists. split; [apply ordinary_reference_store_normalization |]. split; eauto using ty_valloc.
  - destruct (typed_optional_reference_payload _ _ _ _ _ _ Htyped) as [payload [Hv Hpayload]].
    subst v. exists (Voption payload). split; [|split; assumption].
    change (decode_memory_value (Ptrtype (Otype (Reftype bt a)))
      (Values.Val.load_result (transl_bchunk_cchunk option_pointer_chunk)
        (trans_bvalue_cvalue (Voption payload))) = OK (Voption payload)).
    rewrite option_pointer_chunk_translation. apply option_memory_roundtrip; [reflexivity | exact Hpayload].
Qed.

Theorem initialize_scalar_parameter : forall bge cenv Gamma Sigma L m b ofs ty v,
  scalar_parameter_type ty ->
  type_expr cenv Gamma Sigma (Val v ty) nil ty ->
  value_locations L v ty ->
  Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
    b (Ptrofs.unsigned ofs) Freeable ->
  exists m',
    Mem.store (transl_bchunk_cchunk (scalar_parameter_chunk ty)) m b (Ptrofs.unsigned ofs)
      (trans_bvalue_cvalue v) = Some m' /\
    assign_addr bge ty m b ofs Full v m' v /\
    typed_memory_cell cenv Sigma m' b ofs ty (scalar_parameter_chunk ty) /\
    (forall loaded, deref_addr ty m' b ofs Full loaded -> value_locations L loaded ty).
Proof.
  intros bge cenv Gamma Sigma L m b ofs ty v Hscalar Htyped Hlocated Hfree.
  destruct (scalar_parameter_store_normalization _ _ _ _ _ _ Hscalar Htyped Hlocated)
    as [stored [Hdecode [Hstored Hstoredloc]]].
  assert (Hmode := scalar_parameter_chunk_access _ Hscalar).
  destruct Hscalar as [Hkind Hvolatile].
  assert (Hwrite : Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
    b (Ptrofs.unsigned ofs) Writable) by
    (eapply Mem.valid_access_implies; [exact Hfree | constructor]).
  destruct (Mem.valid_access_store m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
    b (Ptrofs.unsigned ofs) (trans_bvalue_cvalue v) Hwrite) as [m' Hstore].
  assert (Hcell : typed_memory_cell cenv Sigma m' b ofs ty (scalar_parameter_chunk ty)).
  { constructor; try assumption.
    - eapply Mem.store_valid_access_1; eauto.
    - eexists; exists stored. split; [eapply Mem.load_store_same; eauto |].
      split; [exact Hdecode |]. eapply value_typing_context_independent; exact Hstored. }
  exists m'. split; [exact Hstore |]. split.
  - destruct Hkind as [[pt Hty] | [[bt [a Hty]] | [bt [a Hty]]]]; subst ty.
    + eapply primitive_assignment_from_store; eauto using declarative_value_shape.
    + inversion Htyped; subst.
      eapply assign_addr_value with
        (chunk := scalar_parameter_chunk (Ptrtype (Reftype bt a)))
        (v := trans_bvalue_cvalue (Vloc l ofs0)).
      * exact Hmode.
      * exact Hvolatile.
      * exact Hstore.
      * reflexivity.
    + destruct (typed_optional_reference_payload _ _ _ _ _ _ Htyped) as [payload [Hv Hpayload]].
      subst v. eapply assign_addr_option; [reflexivity | reflexivity | exact Hvolatile | exact Hpayload |].
      change (Mem.store (transl_bchunk_cchunk option_pointer_chunk) m b (Ptrofs.unsigned ofs)
        (trans_bvalue_cvalue (Voption payload)) = Some m') in Hstore.
      rewrite option_pointer_chunk_translation in Hstore. exact Hstore.
  - split; [exact Hcell |]. intros loaded Hread.
    assert (Hreadstored : deref_addr ty m' b ofs Full stored).
    { eapply deref_addr_value; eauto. simpl. eapply Mem.load_store_same; eauto. }
    assert (loaded = stored) by (eapply deref_full_deterministic; eauto).
    subst loaded. exact Hstoredloc.
Qed.

Print Assumptions scalar_parameter_store_normalization.
Print Assumptions initialize_scalar_parameter.
