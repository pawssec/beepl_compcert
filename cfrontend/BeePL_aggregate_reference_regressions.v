(* Ref of an initialized aggregate allocates and copies a distinct object.
   The source is constructed by the checked two-element assignment regression. *)
Require Import List ZArith Lia AST Integers Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_copy BeePL_fresh_aggregate_memory BeePL_copy_bytes.
Require Import BeePL_aggregate_copy_regressions.
Import ListNotations.
Local Open Scope Z_scope.

Theorem initialized_array_reference_copies : forall ge p vm,
  exists source_memory allocated final source fresh,
    Mem.load Mint32 source_memory source 0 = Some (Values.Vint (Int.repr 41)) /\
    Mem.load Mint32 source_memory source 4 = Some (Values.Vint (Int.repr 73)) /\
    Mem.alloc source_memory 0 8 = (allocated, fresh) /\
    fresh <> source /\
    ssem_expr ge p vm source_memory
      (Prim Ref [Val (Vloc source Ptrofs.zero) copy_regression_array] copy_regression_reference)
      final vm (Val (Vloc fresh Ptrofs.zero) copy_regression_reference) /\
    Mem.load Mint32 final fresh 0 = Some (Values.Vint (Int.repr 41)) /\
    Mem.load Mint32 final fresh 4 = Some (Values.Vint (Int.repr 73)).
Proof.
  intros ge p vm.
  destruct (two_element_array_assignment ge p vm)
    as [initial [both [first [written [source_memory [oldsrc [source
      [Halloc1 [Halloc2 [Hstore0 [Hstore4 [Hready [Hstep [Hload0 Hload4]]]]]]]]]]]]]].
  assert (Haccess0 := Mem.load_valid_access _ _ _ _ _ Hload0).
  assert (Haccess4 := Mem.load_valid_access _ _ _ _ _ Hload4).
  assert (Hvalid : Mem.valid_block source_memory source).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
      [exact Haccess0 | constructor]. }
  assert (Hreadable : aggregate_readable ge.(genv_cenv) source_memory source
      Ptrofs.zero copy_regression_array).
  { unfold aggregate_readable. rewrite Ptrofs.unsigned_zero.
    change (true = true /\ 0 <= 8 /\ 0 + 8 <= Ptrofs.modulus /\
      Mem.valid_block source_memory source /\ Mem.range_perm source_memory source 0 (0+8) Cur Readable).
    split; [reflexivity |]. split; [lia |]. split; [vm_compute; congruence |].
    split; [exact Hvalid |]. intros ofs Hin.
    destruct Haccess0 as [Hperm0 _]. destruct Haccess4 as [Hperm4 _].
    destruct (Z_lt_dec ofs 4).
    - apply Hperm0. simpl; lia.
    - apply Hperm4. simpl; lia. }
  destruct (Mem.alloc source_memory 0 8) as [allocated fresh] eqn:Halloc.
  assert (Hfresh : fresh <> source).
  { intro Heq. subst fresh. eapply Mem.fresh_block_alloc; eauto. }
  assert (Hcopyready : aggregate_copy_ready ge allocated copy_regression_array
      source Ptrofs.zero fresh Ptrofs.zero).
  { eapply fresh_aggregate_copy_ready; [exact Halloc | exact Hreadable |].
    rewrite Ptrofs.unsigned_zero. exists 0; lia. }
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hcopyready) as [final Hassign].
  destruct (aggregate_assignment_bytes ge allocated copy_regression_array source Ptrofs.zero
    fresh Ptrofs.zero final eq_refl Hassign) as [bytes [Hbytes Hcopy]].
  rewrite Ptrofs.unsigned_zero in Hbytes, Hcopy.
  change (Mem.loadbytes allocated source 0 8 = Some bytes) in Hbytes.
  assert (Hload0' : Mem.load Mint32 allocated source 0 = Some (Values.Vint (Int.repr 41))).
  { eapply Mem.load_alloc_other; eauto. }
  assert (Hload4' : Mem.load Mint32 allocated source 4 = Some (Values.Vint (Int.repr 73))).
  { eapply Mem.load_alloc_other; eauto. }
  exists source_memory, allocated, final, source, fresh.
  split; [exact Hload0 |]. split; [exact Hload4 |]. split; [exact Halloc |].
  split; [exact Hfresh |]. split.
  - unfold copy_regression_reference, copy_regression_array.
    eapply ssem_ref_aggregate with (basic := Barray (Tint I32 Signed noattr) 2 noattr);
      [reflexivity | exact Halloc | exact Hassign].
  - split.
    + change (Mem.load Mint32 final fresh (0+0) = Some (Values.Vint (Int.repr 41))).
      eapply copied_bytes_scalar_load with (sourceStart := 0) (delta := 0); eauto; simpl; try lia.
      exists 0; lia.
    + change (Mem.load Mint32 final fresh (0+4) = Some (Values.Vint (Int.repr 73))).
      eapply copied_bytes_scalar_load with (sourceStart := 0) (delta := 4); eauto; simpl; try lia.
      exists 1; lia.
Qed.
Print Assumptions initialized_array_reference_copies.
