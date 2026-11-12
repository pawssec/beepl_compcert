(* Nullable-reference representation regressions and actual store/load laws.
   Unit storage remains a separate, explicitly recorded language obligation. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL.
Import ListNotations.

Lemma none_encoding_is_null :
  trans_bvalue_cvalue (Voption None) = Values.Vnullptr.
Proof. reflexivity. Qed.

Lemma none_some_encoding_distinct : forall b ofs,
  trans_bvalue_cvalue (Voption None) <>
    trans_bvalue_cvalue (Voption (Some (Vloc b ofs))).
Proof. intros. simpl. unfold Values.Vnullptr. destruct Archi.ptr64; discriminate. Qed.

Lemma optional_pointer_roundtrip : forall payload,
  option_reference_payload payload ->
  decode_optional_pointer (trans_bvalue_cvalue (Voption payload)) = OK (Voption payload).
Proof.
  intros [v|] Hshape.
  - destruct v; simpl in Hshape; try contradiction. reflexivity.
  - unfold trans_bvalue_cvalue, Values.Vnullptr, decode_optional_pointer.
    destruct Archi.ptr64; simpl; rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity.
Qed.

Lemma optional_pointer_load_result : forall payload,
  option_reference_payload payload ->
  Values.Val.load_result Mptr (trans_bvalue_cvalue (Voption payload)) =
    trans_bvalue_cvalue (Voption payload).
Proof.
  intros [v|] Hshape.
  - destruct v; simpl in Hshape; try contradiction.
    simpl. unfold Mptr, Values.Val.load_result. destruct Archi.ptr64; reflexivity.
  - simpl. unfold Mptr, Values.Vnullptr. destruct Archi.ptr64; reflexivity.
Qed.

Theorem option_memory_roundtrip : forall pt payload,
  is_option_ptr_type pt = false -> option_reference_payload payload ->
  decode_memory_value (Ptrtype (Otype pt))
    (Values.Val.load_result Mptr (trans_bvalue_cvalue (Voption payload))) =
    OK (Voption payload).
Proof.
  intros pt payload Hnested Hshape. unfold decode_memory_value. rewrite Hnested.
  rewrite optional_pointer_load_result by exact Hshape.
  apply optional_pointer_roundtrip. exact Hshape.
Qed.

Definition option_pointer_chunk : bmemory_chunk :=
  if Archi.ptr64 then BMint64 else BMint32.

Lemma option_pointer_chunk_translation : transl_bchunk_cchunk option_pointer_chunk = Mptr.
Proof. unfold option_pointer_chunk, Mptr. destruct Archi.ptr64; reflexivity. Qed.

Theorem option_reference_store_load : forall bge pt payload m b ofs,
  is_option_ptr_type pt = false ->
  option_reference_payload payload ->
  type_is_volatile (transBeePL_type (Ptrtype (Otype pt))) = false ->
  Mem.valid_access m Mptr b (Ptrofs.unsigned ofs) Writable ->
  exists m',
    assign_addr bge (Ptrtype (Otype pt)) m b ofs Full (Voption payload) m' (Voption payload) /\
    deref_addr (Ptrtype (Otype pt)) m' b ofs Full (Voption payload).
Proof.
  intros bge pt payload m b ofs Hnested Hshape Hvolatile Haccess.
  destruct (Mem.valid_access_store m Mptr b (Ptrofs.unsigned ofs)
    (trans_bvalue_cvalue (Voption payload)) Haccess) as [m' Hstore].
  exists m'. split.
  - eapply assign_addr_option; eauto.
  - eapply deref_addr_value with (chunk := option_pointer_chunk)
      (v := Values.Val.load_result Mptr (trans_bvalue_cvalue (Voption payload))).
    + simpl. rewrite option_pointer_chunk_translation. reflexivity.
    + exact Hvolatile.
    + simpl. rewrite option_pointer_chunk_translation. eapply Mem.load_store_same; eauto.
    + apply option_memory_roundtrip; assumption.
Qed.

Theorem unit_full_assignment_impossible : forall bge m b ofs m' result,
  ~ assign_addr bge Utype m b ofs Full Vunit m' result.
Proof.
  intros bge m b ofs m' result Hassign. inversion Hassign; subst; discriminate.
Qed.

Theorem unit_parameter_binding_no_store : forall bge vm m id b,
  PTree.get id vm = Some (b, Utype) ->
  bind_variables bge vm m [(id, Utype)] [Vunit] m.
Proof.
  intros. eapply bind_variables_unit; [eassumption | constructor].
Qed.

Theorem unit_parameter_binding_preserves_memory : forall bge vm m id m',
  bind_variables bge vm m [(id, Utype)] [Vunit] m' -> m' = m.
Proof.
  intros bge vm m id m' Hbind. inversion Hbind; subst.
  - exfalso. eapply unit_full_assignment_impossible; eauto.
  - match goal with H : bind_variables _ _ _ [] [] _ |- _ =>
      inversion H; reflexivity end.
Qed.

Print Assumptions option_memory_roundtrip.
Print Assumptions none_some_encoding_distinct.
Print Assumptions option_reference_store_load.
Print Assumptions unit_parameter_binding_no_store.
Print Assumptions unit_parameter_binding_preserves_memory.
