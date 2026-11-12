(* Source Mbool rejects noncanonical bytes with Vundef; it does NOT map every
   nonzero byte to true. A successful source read already establishes 0/1. *)
Require Import List ZArith Coqlib Integers AST Maps Memory Memdata Ctypes Csyntax.
Require Import Csem Cstrategy Cop Events Values Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_compiler_dereference_evaluation.
Local Open Scope Z_scope.

Lemma decoded_normal_bool_exact : forall raw value,
  decode_memory_value (Vtype Tbool) (Val.norm_bool raw) = OK value ->
  raw = trans_bvalue_cvalue value.
Proof.
  intros raw value Hdecode.
  pose proof (Val.norm_bool_is_lessdef raw) as Hless.
  destruct (Val.norm_bool_cases raw) as [E|[E|E]];
    rewrite E in Hdecode,Hless; simpl in Hdecode; try discriminate;
    inversion Hdecode; subst; inversion Hless; reflexivity.
Qed.

Lemma source_boolean_read_is_canonical_byte : forall source b ofs value,
  deref_addr (Vtype Tbool) source b ofs Full value ->
  Mem.loadv Mint8unsigned source (Values.Vptr b ofs) =
    Some (trans_bvalue_cvalue value).
Proof.
  intros source b ofs value Hread; inversion Hread; subst; try discriminate.
  match goal with Hmode : access_mode_type (Vtype Tbool) = By_value (transl_bchunk_cchunk ?chunk) |- _ =>
    assert (Echunk : transl_bchunk_cchunk chunk = Mbool) by
      (simpl in Hmode; inversion Hmode; reflexivity)
  end.
  match goal with Hload : Mem.loadv _ source _ = Some ?cv |- _ =>
    rewrite Echunk in Hload; simpl in Hload;
    rewrite Mem.load_bool_int8_unsigned in Hload;
    destruct (Mem.load Mint8unsigned source b (Ptrofs.unsigned ofs)) as [raw|] eqn:Eload;
    simpl in Hload; try discriminate; inversion Hload; subst
  end.
  simpl. rewrite Eload. f_equal. eapply decoded_normal_bool_exact; eauto.
Qed.

Theorem injected_boolean_dereference : forall target_ge env injection source target
    source_block source_offset target_block target_offset value pointerty,
  Mem.inject injection source target ->
  Values.Val.inject injection (Values.Vptr source_block source_offset)
    (Values.Vptr target_block target_offset) ->
  deref_addr (Vtype Tbool) source source_block source_offset Full value ->
  exists target_value,
    Values.Val.inject injection (trans_bvalue_cvalue value) target_value /\
    eval_expression target_ge env target
      (Evalof (Ederef (Eval (Values.Vptr target_block target_offset) pointerty)
         (transBeePL_type (Vtype Tbool))) (transBeePL_type (Vtype Tbool)))
      E0 target target_value.
Proof.
  intros tge env injection source target sb so tb tofs value pointerty Hinject Hpointer Hread.
  pose proof(source_boolean_read_is_canonical_byte _ _ _ _ Hread) as Hload.
  destruct(Mem.loadv_inject _ _ _ _ _ _ _ Hinject Hload Hpointer)
    as [loaded [Hloaded Hvalue]].
  exists loaded; split; [exact Hvalue|].
  eapply scalar_target_literal_dereference; [reflexivity|reflexivity|exact Hloaded].
Qed.

Example raw_two_is_not_a_source_boolean :
  decode_memory_value (Vtype Tbool) (Val.norm_bool (Values.Vint (Int.repr 2))) =
    Error (MSG "Invalid boolean memory representation" :: nil).
Proof. reflexivity. Qed.
Print Assumptions source_boolean_read_is_canonical_byte.
Print Assumptions injected_boolean_dereference.

Theorem stored_raw_two_boolean_boundary : forall before after block offset,
  Mem.store Mint8unsigned before block offset (Values.Vint (Int.repr 2)) = Some after ->
  Mem.load Mint8unsigned after block offset = Some (Values.Vint (Int.repr 2)) /\
  Mem.load Mbool after block offset = Some Values.Vundef /\
  decode_memory_value (Vtype Tbool) Values.Vundef =
    Error (MSG "Invalid boolean memory representation" :: nil).
Proof.
  intros before after block offset Hstore.
  pose proof(Mem.load_store_same _ _ _ _ _ _ Hstore) as Hbyte.
  change (Mem.load Mint8unsigned after block offset = Some(Values.Vint(Int.repr 2))) in Hbyte.
  split; [exact Hbyte|]. split; [|reflexivity].
  rewrite Mem.load_bool_int8_unsigned,Hbyte. reflexivity.
Qed.

Theorem stored_raw_two_has_no_source_boolean_read : forall before after block offset,
  Mem.store Mint8unsigned before block (Ptrofs.unsigned offset)
    (Values.Vint (Int.repr 2)) = Some after ->
  forall value, ~deref_addr (Vtype Tbool) after block offset Full value.
Proof.
  intros before after block offset Hstore value Hread.
  destruct(stored_raw_two_boolean_boundary _ _ _ _ Hstore) as [Hbyte [Hbool _]].
  inversion Hread; subst; try discriminate.
  match goal with Hmode : access_mode_type (Vtype Tbool)=By_value(transl_bchunk_cchunk ?chunk) |- _ =>
    assert(Echunk:transl_bchunk_cchunk chunk=Mbool) by
      (simpl in Hmode; inversion Hmode; reflexivity)
  end.
  match goal with Hload:Mem.loadv _ after _=Some _ |- _ =>
    rewrite Echunk in Hload; simpl in Hload; rewrite Hbool in Hload;
    inversion Hload; subst
  end. discriminate.
Qed.
Print Assumptions stored_raw_two_boolean_boundary.
Print Assumptions stored_raw_two_has_no_source_boolean_read.

Definition surface_primitive_read (pt : primitive_type) : Prop :=
  match pt with Tint IBool _ _ => False | _ => True end.

Theorem injected_surface_primitive_dereference :
  forall target_ge env injection source target pt source_block source_offset
    target_block target_offset value pointerty,
  surface_primitive_read pt -> typeof_value value (Vtype pt) ->
  Mem.inject injection source target ->
  Values.Val.inject injection (Values.Vptr source_block source_offset)
    (Values.Vptr target_block target_offset) ->
  deref_addr (Vtype pt) source source_block source_offset Full value ->
  exists target_value,
    Values.Val.inject injection (trans_bvalue_cvalue value) target_value /\
    eval_expression target_ge env target
      (Evalof (Ederef (Eval (Values.Vptr target_block target_offset) pointerty)
         (transBeePL_type (Vtype pt))) (transBeePL_type (Vtype pt)))
      E0 target target_value.
Proof.
  intros ge env injection source target pt sb so tb tofs value pointerty
    Hsurface Hshape Hinject Hpointer Hread.
  destruct pt as [|sz sg attr|sg attr].
  - eapply injected_boolean_dereference; eauto.
  - eapply injected_nonbool_primitive_dereference; eauto.
  - eapply injected_nonbool_primitive_dereference; eauto.
Qed.
Print Assumptions injected_surface_primitive_dereference.

(* Raw Coq Tint IBool is distinct from surface Tbool. Its source access mode
   currently is Mint8unsigned, while C IBool uses Mbool. Do not generalize the
   surface theorem to this raw constructor without repairing that mismatch. *)
Theorem raw_ibool_read_boundary : forall before after block offset,
  Mem.store Mint8unsigned before block (Ptrofs.unsigned offset)
    (Values.Vint (Int.repr 2)) = Some after ->
  deref_addr (Vtype (Tint IBool Unsigned noattr)) after block offset Full
    (BeePL_values.Vint (Int.repr 2)) /\
  Mem.load Mbool after block (Ptrofs.unsigned offset) = Some Values.Vundef.
Proof.
  intros before after block offset Hstore.
  destruct(stored_raw_two_boolean_boundary _ _ _ _ Hstore) as [Hbyte [Hbool _]].
  split; [|exact Hbool].
  eapply deref_addr_value with (chunk:=BMint8unsigned)
    (v:=Values.Vint(Int.repr 2)); [reflexivity|reflexivity|exact Hbyte|reflexivity].
Qed.
Print Assumptions raw_ibool_read_boundary.
