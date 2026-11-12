(* Nested indexing executes in two small steps, selecting an embedded aggregate
   before loading its scalar element. Only the selected inner array is initialized. *)
Require Import List ZArith Lia AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_interior_array_regressions.
Import ListNotations.
Local Open Scope Z_scope.

Theorem nested_array_index_execution : forall ge p vm,
  exists allocated first final block,
    Mem.alloc Mem.empty 0 16 = (allocated, block) /\
    Mem.store Mint32 allocated block 8 (Values.Vint (Int.repr 41)) = Some first /\
    Mem.store Mint32 first block 12 (Values.Vint (Int.repr 73)) = Some final /\
    ssem_expr ge p vm final
      (Prim (ArrayRead 1)
        [Prim (ArrayRead 1) [Val (Vloc block Ptrofs.zero) interior_array_outer] interior_array_inner]
        interior_array_element)
      final vm
      (Prim (ArrayRead 1) [Val (Vloc block (Ptrofs.repr 8)) interior_array_inner] interior_array_element) /\
    ssem_expr ge p vm final
      (Prim (ArrayRead 1) [Val (Vloc block (Ptrofs.repr 8)) interior_array_inner] interior_array_element)
      final vm (Val (Vint (Int.repr 73)) interior_array_element).
Proof.
  intros ge p vm.
  destruct (interior_array_index_preserves_base ge p vm)
    as [allocated [first [final [block [Sigma [Halloc [Hstore8 [Hstore12 [Hobject [Htype Hscalar]]]]]]]]]].
  assert (Hreadable : aggregate_readable ge.(genv_cenv) final block (Ptrofs.repr 8) interior_array_inner).
  { unfold aggregate_readable.
    change (true = true /\ 0 <= 8 /\ 8 + 8 <= Ptrofs.modulus /\
      Mem.valid_block final block /\ Mem.range_perm final block 8 (8+8) Cur Readable).
    split; [reflexivity |]. split; [lia |]. split; [vm_compute; congruence |]. split.
    - eapply Mem.store_valid_block_1; [exact Hstore12 |].
      eapply Mem.store_valid_block_1; [exact Hstore8 |]. eapply Mem.valid_new_block; exact Halloc.
    - intros ofs Hin. eapply Mem.perm_store_1; [exact Hstore12 |].
      eapply Mem.perm_store_1; [exact Hstore8 |].
      eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact Halloc | lia] | constructor]. }
  exists allocated, first, final, block.
  split; [exact Halloc |]. split; [exact Hstore8 |]. split; [exact Hstore12 |].
  split; [|exact Hscalar]. apply ssem_array_read_context.
  change (ssem_expr ge p vm final
    (Prim (ArrayRead 1)
      [Val (Vloc block Ptrofs.zero) (Atype interior_array_inner 2 noattr)] interior_array_inner)
    final vm (Val (Vloc block
      (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat 1 * sizeof_type ge.(genv_cenv) interior_array_inner))))
      interior_array_inner)).
  eapply ssem_array_read_aggregate.
  - change (1 < 2)%nat. lia.
  - change (8 <= Ptrofs.max_unsigned). vm_compute; congruence.
  - change (aggregate_readable ge.(genv_cenv) final block (Ptrofs.repr 8) interior_array_inner).
    exact Hreadable.
Qed.
Print Assumptions nested_array_index_execution.
