(* Emission/validation regressions, not a semantic refinement theorem for the
   unverified Asmexpand pseudo-instruction expansion. *)
Require Import Coqlib Errors AST Integers Memdata Locations Mach Asm Asmgen.
Require Import List.
Import ListNotations.

Lemma memcpy_scratch_excludes_bases : forall dst src,
  memcpy_scratch dst src <> dst /\ memcpy_scratch dst src <> src.
Proof. intros dst src; destruct dst; destruct src; vm_compute; intuition discriminate. Qed.

Definition copy_word (offset: Z) : code :=
  [Pload DBWord R3 R2 (Ptrofs.repr offset);
   Pstore DBWord R1 (inl R3) (Ptrofs.repr offset)].
Example memcpy_aligned_16 :
  transl_memcpy 0 16 8 [BA I1;BA I2] BR_none [] = OK (copy_word 0 ++ copy_word 8).
Proof. vm_compute; reflexivity. Qed.
Example memcpy_aligned_24 :
  transl_memcpy 0 24 8 [BA I1;BA I2] BR_none [] = OK (copy_word 0 ++ copy_word 8 ++ copy_word 16).
Proof. vm_compute; reflexivity. Qed.
Example memcpy_same_base :
  transl_memcpy 0 8 8 [BA I1;BA I1] BR_none [] =
  OK [Pload DBWord R2 R1 Ptrofs.zero; Pstore DBWord R1 (inl R2) Ptrofs.zero].
Proof. vm_compute; reflexivity. Qed.
Example memcpy_swapped_bases :
  transl_memcpy 0 8 8 [BA I2;BA I1] BR_none [] =
  OK [Pload DBWord R3 R1 Ptrofs.zero; Pstore DBWord R2 (inl R3) Ptrofs.zero].
Proof. vm_compute; reflexivity. Qed.
Example memcpy_mixed_width_tail :
  transl_memcpy 0 15 8 [BA I1;BA I2] BR_none [] = OK
  (copy_word 0 ++ [Pload Word R3 R2 (Ptrofs.repr 8);Pstore Word R1 (inl R3) (Ptrofs.repr 8);
    Pload HalfWord R3 R2 (Ptrofs.repr 12);Pstore HalfWord R1 (inl R3) (Ptrofs.repr 12);
    Pload Byte R3 R2 (Ptrofs.repr 14);Pstore Byte R1 (inl R3) (Ptrofs.repr 14)]).
Proof. vm_compute; reflexivity. Qed.
Example memcpy_invalid_offset :
  memcpy_offset_range (Ptrofs.repr 32760) 16 = false.
Proof. vm_compute; reflexivity. Qed.
Example memcpy_negative_offset_valid :
  memcpy_offset_range (Ptrofs.repr (-512)) 512 = true.
Proof. vm_compute; reflexivity. Qed.
Example memcpy_bad_shape :
  exists message, transl_memcpy 0 8 8 [BA_int Int.zero;BA I2] BR_none [] = Error message.
Proof. vm_compute; eexists; reflexivity. Qed.
Example memcpy_negative_size :
  exists message, transl_memcpy 0 (-1) 8 [BA I1;BA I2] BR_none [] = Error message.
Proof. vm_compute; eexists; reflexivity. Qed.
Print Assumptions memcpy_scratch_excludes_bases.
Example memcpy_bad_stack_span_rejected :
  exists message, transl_memcpy 16 16 8
    [BA_addrstack (Ptrofs.repr 32760); BA I2] BR_none [] = Error message.
Proof. vm_compute; eexists; reflexivity. Qed.
Example memcpy_stack_frame_translation :
  transl_memcpy 32 8 8 [BA_addrstack Ptrofs.zero; BA I2] BR_none [] =
  OK [Pload DBWord R1 R2 Ptrofs.zero;
      Pstore DBWord R10 (inl R1) (Ptrofs.repr (-16))].
Proof.
  replace (Ptrofs.repr (-16)) with
    (Ptrofs.add (transl_stack_offset 32 Ptrofs.zero) Ptrofs.zero).
  - vm_compute; reflexivity.
  - apply Ptrofs.same_if_eq; vm_compute; reflexivity.
Qed.

(* These general round trips use Memdata's common encoding/decoding byte order;
   they do not rely on a little-endian-only byte reversal in the planner. *)
Lemma memcpy_integer_word_roundtrip : forall n,
  decode_val Mint64 (encode_val Mint64 (Values.Vlong n)) = Values.Vlong n.
Proof. intros; exact (decode_encode_val_general (Values.Vlong n) Mint64 Mint64). Qed.
Lemma memcpy_pointer_word_roundtrip : forall b offset,
  Archi.ptr64 = true ->
  decode_val Mint64 (encode_val Mint64 (Values.Vptr b offset)) = Values.Vptr b offset.
Proof. intros b offset H64.
  pose proof (decode_encode_val_general (Values.Vptr b offset) Mint64 Mint64) as H.
  change (decode_val Mint64 (encode_val Mint64 (Values.Vptr b offset)) =
    if Archi.ptr64 then Values.Vptr b offset else Values.Vundef) in H.
  rewrite H64 in H; exact H.
Qed.
Lemma memcpy_integer_halfword_roundtrip : forall n,
  decode_val Mint16unsigned (encode_val Mint16unsigned (Values.Vint n)) =
    Values.Vint (Int.zero_ext 16 n).
Proof. intros; exact (decode_encode_val_general (Values.Vint n) Mint16unsigned Mint16unsigned). Qed.
Lemma memcpy_integer_byte_roundtrip : forall n,
  decode_val Mint8unsigned (encode_val Mint8unsigned (Values.Vint n)) =
    Values.Vint (Int.zero_ext 8 n).
Proof. intros; exact (decode_encode_val_general (Values.Vint n) Mint8unsigned Mint8unsigned). Qed.
Example memcpy_anyword_does_not_decode_integer_bytes :
  decode_val Many64 (encode_val Mint64 (Values.Vlong Int64.one)) = Values.Vundef.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions memcpy_pointer_word_roundtrip.
Print Assumptions memcpy_integer_word_roundtrip.
