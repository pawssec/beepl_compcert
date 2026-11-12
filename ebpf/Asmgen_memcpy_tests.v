(* Emission/validation regressions, not a semantic refinement theorem for the
   unverified Asmexpand pseudo-instruction expansion. *)
Require Import Coqlib Errors AST Integers Memdata Locations Mach Asm Asmgen.
Require Import List.
Import ListNotations.

Lemma memcpy_scratch_excludes_bases : forall dst src,
  memcpy_scratch dst src <> dst /\ memcpy_scratch dst src <> src.
Proof. intros dst src; destruct dst; destruct src; vm_compute; intuition discriminate. Qed.

Definition copy_word (offset: Z) : code :=
  [Pload DBWordAny R3 R2 (Ptrofs.repr offset);
   Pstore DBWordAny R1 (inl R3) (Ptrofs.repr offset)].
Example memcpy_aligned_16 :
  transl_memcpy 0 16 8 [BA I1;BA I2] BR_none [] = OK (copy_word 0 ++ copy_word 8).
Proof. vm_compute; reflexivity. Qed.
Example memcpy_aligned_24 :
  transl_memcpy 0 24 8 [BA I1;BA I2] BR_none [] = OK (copy_word 0 ++ copy_word 8 ++ copy_word 16).
Proof. vm_compute; reflexivity. Qed.
Example memcpy_same_base :
  transl_memcpy 0 8 8 [BA I1;BA I1] BR_none [] =
  OK [Pload DBWordAny R2 R1 Ptrofs.zero; Pstore DBWordAny R1 (inl R2) Ptrofs.zero].
Proof. vm_compute; reflexivity. Qed.
Example memcpy_swapped_bases :
  transl_memcpy 0 8 8 [BA I2;BA I1] BR_none [] =
  OK [Pload DBWordAny R3 R1 Ptrofs.zero; Pstore DBWordAny R2 (inl R3) Ptrofs.zero].
Proof. vm_compute; reflexivity. Qed.
Example memcpy_mixed_width_tail :
  transl_memcpy 0 15 8 [BA I1;BA I2] BR_none [] = OK
  (copy_word 0 ++ [Pload WordAny R3 R2 (Ptrofs.repr 8);Pstore WordAny R1 (inl R3) (Ptrofs.repr 8);
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
