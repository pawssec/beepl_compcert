(* An inner array starts eight bytes into an actual allocation. Indexing it
   must retain that base rather than accidentally reading the outer array. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Import ListNotations.

Definition interior_array_element : type := Vtype (Tint I32 Signed noattr).
Definition interior_array_inner : type := Atype interior_array_element 2 noattr.
Definition interior_array_outer : type := Atype interior_array_inner 2 noattr.

Theorem interior_array_index_preserves_base : forall bge p vm,
  exists allocated first final block Sigma,
    Mem.alloc Mem.empty 0 16 = (allocated, block) /\
    Mem.store Mint32 allocated block 8 (Values.Vint (Int.repr 41)) = Some first /\
    Mem.store Mint32 first block 12 (Values.Vint (Int.repr 73)) = Some final /\
    object_type_at bge.(genv_cenv) Sigma block 8 interior_array_inner /\
    type_expr bge.(genv_cenv) empty_context Sigma
      (Val (Vloc block (Ptrofs.repr 8)) interior_array_inner) nil interior_array_inner /\
    ssem_expr bge p vm final
      (Prim (ArrayRead 1) [Val (Vloc block (Ptrofs.repr 8)) interior_array_inner]
        interior_array_element)
      final vm (Val (Vint (Int.repr 73)) interior_array_element).
Proof.
  intros bge p vm.
  destruct (Mem.alloc Mem.empty 0 16) as [allocated block] eqn:Halloc.
  assert (Haccess8 : Mem.valid_access allocated Mint32 block 8 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc|lia|simpl; lia|].
    exists 2%Z. reflexivity. }
  destruct (Mem.valid_access_store allocated Mint32 block 8 (Values.Vint (Int.repr 41)) Haccess8)
    as [first Hstore8].
  assert (Haccess12 : Mem.valid_access first Mint32 block 12 Writable).
  { eapply Mem.store_valid_access_1; [exact Hstore8|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc|lia|simpl; lia|].
    exists 3%Z. reflexivity. }
  destruct (Mem.valid_access_store first Mint32 block 12 (Values.Vint (Int.repr 73)) Haccess12)
    as [final Hstore12].
  set (Sigma := PTree.set block interior_array_outer empty_stcontext).
  assert (Hroot : object_type_at bge.(genv_cenv) Sigma block 0 interior_array_outer).
  { eapply object_type_root with (stored := interior_array_outer).
    - unfold Sigma; apply PTree.gss.
    - change (0 <= 16)%Z. lia. }
  assert (Hinner : object_type_at bge.(genv_cenv) Sigma block 8 interior_array_inner).
  { change (object_type_at bge.(genv_cenv) Sigma block
      (0 + 1 * sizeof_type bge.(genv_cenv) interior_array_inner) interior_array_inner).
    eapply object_type_array_element; [exact Hroot|change (0 <= 1 < 2)%Z; lia|].
    change (0 <= 8)%Z. lia. }
  assert (Hbase : Ptrofs.unsigned (Ptrofs.repr 8) = 8%Z) by (vm_compute; reflexivity).
  assert (Hoffset : Ptrofs.unsigned
    (Ptrofs.add (Ptrofs.repr 8)
      (Ptrofs.repr (Z.of_nat 1 * sizeof_type bge.(genv_cenv) interior_array_element))) = 12%Z)
    by (vm_compute; reflexivity).
  exists allocated, first, final, block, Sigma.
  split; [reflexivity|]. split; [exact Hstore8|]. split; [exact Hstore12|].
  split; [exact Hinner|]. split.
  - apply ty_valarray. rewrite Hbase; exact Hinner.
  - eapply ssem_array_read_value.
    + change (1 < 2)%nat. lia.
    + eapply deref_addr_value with (chunk := BMint32)
        (v := Values.Val.load_result Mint32 (Values.Vint (Int.repr 73))).
      * reflexivity.
      * reflexivity.
      * change (Mem.load Mint32 final block 12 =
          Some (Values.Val.load_result Mint32 (Values.Vint (Int.repr 73)))).
        eapply Mem.load_store_same; exact Hstore12.
      * reflexivity.
Qed.

Print Assumptions interior_array_index_preserves_base.
