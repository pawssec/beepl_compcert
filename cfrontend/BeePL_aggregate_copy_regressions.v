(* A real Massgn step copies both initialized elements of an allocated array. *)
Require Import List ZArith Lia AST Integers Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_copy BeePL_copy_bytes.
Import ListNotations.
Local Open Scope Z_scope.
Definition copy_regression_array : type := Atype (Vtype (Tint I32 Signed noattr)) 2 noattr.
Definition copy_regression_reference : type :=
  Ptrtype (Reftype (Barray (Tint I32 Signed noattr) 2 noattr) noattr).

Theorem two_element_array_assignment : forall ge p vm,
  exists initial allocated first written copied src dst,
    Mem.alloc Mem.empty 0 8 = (initial, src) /\
    Mem.alloc initial 0 8 = (allocated, dst) /\
    Mem.store Mint32 allocated src 0 (Values.Vint (Int.repr 41)) = Some first /\
    Mem.store Mint32 first src 4 (Values.Vint (Int.repr 73)) = Some written /\
    aggregate_copy_ready ge written copy_regression_array src Ptrofs.zero dst Ptrofs.zero /\
    ssem_expr ge p vm written
      (Prim Massgn [Val (Vloc dst Ptrofs.zero) copy_regression_reference;
        Val (Vloc src Ptrofs.zero) copy_regression_array] Utype)
      copied vm (Val Vunit Utype) /\
    Mem.load Mint32 copied dst 0 = Some (Values.Vint (Int.repr 41)) /\
    Mem.load Mint32 copied dst 4 = Some (Values.Vint (Int.repr 73)).
Proof.
  intros ge p vm.
  destruct (Mem.alloc Mem.empty 0 8) as [initial src] eqn:Hs.
  destruct (Mem.alloc initial 0 8) as [allocated dst] eqn:Hd.
  assert (Haccess : forall ofs, ofs = 0 \/ ofs = 4 ->
      Mem.valid_access allocated Mint32 src ofs Freeable).
  { intros ofs [-> | ->]; eapply Mem.valid_access_alloc_other; [exact Hd | | exact Hd |];
      eapply Mem.valid_access_alloc_same; try exact Hs; simpl; try lia.
    - exists 0; lia.
    - exists 1; lia. }
  assert (Hw0 : Mem.valid_access allocated Mint32 src 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [apply Haccess; auto | constructor]. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vint (Int.repr 41)) Hw0) as [first Hstore0].
  assert (Hw4 : Mem.valid_access first Mint32 src 4 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.store_valid_access_1; [exact Hstore0 | apply Haccess; auto]. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vint (Int.repr 73)) Hw4) as [written Hstore4].
  assert (Hload0 : Mem.load Mint32 written src 0 = Some (Values.Vint (Int.repr 41))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore4); [|right; left; simpl; lia].
    exact (Mem.load_store_same _ _ _ _ _ _ Hstore0). }
  assert (Hload4 : Mem.load Mint32 written src 4 = Some (Values.Vint (Int.repr 73))).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hstore4). }
  assert (Hready : aggregate_copy_ready ge written copy_regression_array src Ptrofs.zero dst Ptrofs.zero).
  { constructor; try reflexivity; rewrite ?Ptrofs.unsigned_zero;
      change (aggregate_copy_size ge copy_regression_array) with 8 in *.
    - lia.
    - eapply Mem.store_valid_block_1; [exact Hstore4 |].
      eapply Mem.store_valid_block_1; [exact Hstore0 |].
      eapply Mem.valid_block_alloc; [exact Hd |]. eapply Mem.valid_new_block; exact Hs.
    - eapply Mem.store_valid_block_1; [exact Hstore4 |].
      eapply Mem.store_valid_block_1; [exact Hstore0 |]. eapply Mem.valid_new_block; exact Hd.
    - vm_compute; congruence.
    - vm_compute; congruence.
    - exists 0; lia.
    - exists 0; lia.
    - right; left; reflexivity.
    - intros ofs Hin. eapply Mem.perm_store_1; [exact Hstore4 |].
      eapply Mem.perm_store_1; [exact Hstore0 |]. eapply Mem.perm_alloc_1; [exact Hd |].
      eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact Hs | exact Hin] | constructor].
    - intros ofs Hin. eapply Mem.perm_store_1; [exact Hstore4 |].
      eapply Mem.perm_store_1; [exact Hstore0 |]. eapply Mem.perm_alloc_2; [exact Hd | exact Hin]. }
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hready) as [copied Hassign].
  destruct (aggregate_assignment_bytes ge written copy_regression_array src Ptrofs.zero dst Ptrofs.zero copied eq_refl Hassign) as [bytes [Hbytes Hcopy]].
  rewrite Ptrofs.unsigned_zero in Hbytes, Hcopy.
  change (Mem.loadbytes written src 0 8 = Some bytes) in Hbytes.
  exists initial, allocated, first, written, copied, src, dst.
  split; [reflexivity |]. split; [exact Hd |]. split; [exact Hstore0 |].
  split; [exact Hstore4 |]. split; [exact Hready |]. split.
  - apply ssem_massgn3. exact Hassign.
  - split.
    + change (Mem.load Mint32 copied dst (0 + 0) = Some (Values.Vint (Int.repr 41))).
      eapply copied_bytes_scalar_load with (sourceStart := 0) (delta := 0); eauto; simpl; try lia.
      exists 0; lia.
    + change (Mem.load Mint32 copied dst (0 + 4) = Some (Values.Vint (Int.repr 73))).
      eapply copied_bytes_scalar_load with (sourceStart := 0) (delta := 4); eauto; simpl; try lia.
      exists 1; lia.
Qed.
Print Assumptions two_element_array_assignment.
