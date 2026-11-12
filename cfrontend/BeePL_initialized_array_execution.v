Require Import BeePL_heap_extents BeePL_block_extents.
(* An actual Bool array initializer allocates and writes two distinct bytes.
   Its certified initialized coverage accompanies observable true/false reads. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_allocation_proofs.
Require Import BeePL_array_proofs BeePL_initialized_arrays.
Import ListNotations.
Local Open Scope Z_scope.

Definition initialized_array_empty_objects : aggregate_object_context := fun _ _ _ => False.
Definition initialized_array_empty_cells : scalar_layout := fun _ _ _ _ => False.
Definition boolean_pair_type := Atype (Vtype Tbool) 2 noattr.
Definition boolean_pair_values := [Val (Vbool true) (Vtype Tbool); Val (Vbool false) (Vtype Tbool)].

Lemma initialized_array_empty_memory : forall ge,
  initialized_object_memory ge empty_stcontext Mem.empty
    initialized_array_empty_objects initialized_array_empty_cells.
Proof.
  intros ge. constructor.
  - constructor; intros b ofs ty H; contradiction.
  - intros b ofs ty H; contradiction.
  - intros b ofs ty chunk H; contradiction.
  - intros b ofs ty chunk H; contradiction.
  - intros b ofs ty H; contradiction.
Qed.

Theorem initialized_boolean_array_execution : forall ge p vm arr,
  exists allocated first final block Sigma,
    initialized_object_memory ge empty_stcontext Mem.empty
      initialized_array_empty_objects initialized_array_empty_cells /\
    Mem.alloc Mem.empty 0 2 = (allocated, block) /\
    Mem.store Mbool allocated block 0 (Values.Vint Int.one) = Some first /\
    Mem.store Mbool first block 1 (Values.Vint Int.zero) = Some final /\
    ssem_expr ge p vm Mem.empty (Ainit arr boolean_pair_type boolean_pair_values boolean_pair_type)
      final vm (Val (Vloc block Ptrofs.zero) boolean_pair_type) /\
    initialized_object_memory ge Sigma final
      (add_aggregate_descriptor initialized_array_empty_objects block Ptrofs.zero boolean_pair_type)
      (extend_array_layout initialized_array_empty_cells block Tbool 2) /\
    ssem_expr ge p vm final
      (Prim (ArrayRead 0) [Val (Vloc block Ptrofs.zero) boolean_pair_type] (Vtype Tbool))
      final vm (Val (Vbool true) (Vtype Tbool)) /\
    ssem_expr ge p vm final
      (Prim (ArrayRead 1) [Val (Vloc block Ptrofs.zero) boolean_pair_type] (Vtype Tbool))
      final vm (Val (Vbool false) (Vtype Tbool)).
Proof.
  intros ge p vm arr.
  destruct (alloc_variables_single ge empty_stcontext vm Mem.empty arr boolean_pair_type)
    as [allocated [block [Halloc Hvars]]].
  change (Mem.alloc Mem.empty 0 2 = (allocated, block)) in Halloc.
  assert (Haccess0 : Mem.valid_access allocated Mbool block 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc | lia | simpl; lia |]. exists 0; reflexivity. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vint Int.one) Haccess0) as [first Hstore0].
  assert (Haccess1 : Mem.valid_access first Mbool block 1 Writable).
  { eapply Mem.store_valid_access_1; [exact Hstore0 |].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc | lia | simpl; lia |]. exists 1; reflexivity. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vint Int.zero) Haccess1) as [final Hstore1].
  assert (Hinit : sem_array_init ge empty_stcontext arr boolean_pair_type [Vbool true; Vbool false]
    vm Mem.empty (PTree.set arr (block, boolean_pair_type) vm) final
    (PTree.set block boolean_pair_type empty_stcontext)).
  { eapply sem_allocate_array; [exact Hvars | apply PTree.gss | reflexivity | reflexivity |].
    eapply sem_allocate_array_elm.
    - apply assign_addr_boolean; [reflexivity | exact Hstore0].
    - eapply sem_allocate_array_elm.
      + apply assign_addr_boolean; [reflexivity | exact Hstore1].
      + constructor. }
  assert (Hblocks : store_blocks_valid empty_stcontext Mem.empty).
  { intros b ty Hget. rewrite PTree.gempty in Hget. discriminate. }
  destruct (primitive_array_initialized_objects ge empty_context empty_stcontext
    initialized_array_empty_objects initialized_array_empty_cells arr Tbool 2 noattr
    [Vbool true; Vbool false] vm Mem.empty _ final _ Hinit
    (initialized_array_empty_memory ge) Hblocks
    ltac:(repeat constructor) eq_refl ltac:(vm_compute; congruence))
    as [fresh [Hlookup [Hext [Hvalid [Hmemory Htyped]]]]].
  rewrite PTree.gss in Hlookup. inversion Hlookup; subst fresh.
  assert (Hread0 : Mem.load Mbool final block 0 = Some (Values.Vint Int.one)).
  { erewrite Mem.load_store_other; [|exact Hstore1 | right; left; simpl; lia].
    pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore0) as Hload. exact Hload. }
  assert (Hread1 : Mem.load Mbool final block 1 = Some (Values.Vint Int.zero)).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hstore1). }
  exists allocated, first, final, block, (PTree.set block boolean_pair_type empty_stcontext).
  split; [apply initialized_array_empty_memory |]. split; [exact Halloc |].
  split; [exact Hstore0 |]. split; [exact Hstore1 |]. split.
  - eapply ssem_array_init3.
    + constructor; [do 2 eexists; reflexivity |].
      constructor; [do 2 eexists; reflexivity | constructor].
    + exact Hinit.
    + apply PTree.gss.
  - split; [exact Hmemory |]. split; eapply ssem_array_read_value.
    + change (0 < 2)%nat. lia.
    + eapply deref_addr_value with (chunk := BMbool) (v := Values.Vint Int.one);
        [reflexivity | reflexivity | exact Hread0 | reflexivity].
    + change (1 < 2)%nat. lia.
    + eapply deref_addr_value with (chunk := BMbool) (v := Values.Vint Int.zero);
        [reflexivity | reflexivity | exact Hread1 | reflexivity].
Qed.

Print Assumptions initialized_array_empty_memory.
Print Assumptions initialized_boolean_array_execution.
