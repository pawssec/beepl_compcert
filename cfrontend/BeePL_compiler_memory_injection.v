(* Source expression-time allocation into a target local block allocated
   earlier at function entry. This is a memory foundation, not a complete
   expression/compiler simulation theorem. *)
Require Import List ZArith Lia Coqlib AST Maps Integers Values Memory Ctypes Csem.
Require Import BeePL_compiler_local_allocation.
Import ListNotations.
Local Open Scope Z_scope.

Definition unused_target_slot (f:meminj) (slot:block) : Prop :=
  forall b delta, f b <> Some(slot,delta).

Theorem source_allocation_into_local_slot : forall f source target size after fresh slot,
  Mem.inject f source target ->
  Mem.alloc source 0 size=(after,fresh) ->
  Mem.valid_block target slot ->
  (forall ofs, 0<=ofs<size -> Mem.perm target slot ofs Cur Freeable) ->
  unused_target_slot f slot ->
  exists f', Mem.inject f' after target /\ inject_incr f f' /\
    f' fresh=Some(slot,0) /\ (forall b, b<>fresh -> f' b=f b).
Proof.
  intros f source target size after fresh slot Hinj Halloc Hvalid Hperm Hunused.
  eapply Mem.alloc_left_mapped_inject;
    [exact Hinj|exact Halloc|exact Hvalid| | | | |].
  - pose proof (Ptrofs.unsigned_range_2 Ptrofs.zero); lia.
  - intros; left; reflexivity.
  - intros ofs k p Hrange. rewrite Z.add_0_r.
    eapply Mem.perm_implies; [eapply Mem.perm_cur; apply Hperm; exact Hrange|].
    destruct p; constructor.
  - intros chunk Hsize. apply Z.divide_0_r.
  - intros b delta ofs k p Hmap Haccess Hrange. exact (Hunused b delta Hmap).
Qed.

Theorem source_allocation_and_scalar_store : forall f source target size allocated fresh slot
    chunk ofs value targetvalue initialized,
  Mem.inject f source target ->
  Mem.alloc source 0 size=(allocated,fresh) ->
  Mem.valid_block target slot ->
  (forall offset, 0<=offset<size -> Mem.perm target slot offset Cur Freeable) ->
  unused_target_slot f slot ->
  Val.inject f value targetvalue ->
  Mem.store chunk allocated fresh ofs value=Some initialized ->
  exists f' targetinitialized,
    inject_incr f f' /\ f' fresh=Some(slot,0) /\
    (forall b, b<>fresh -> f' b=f b) /\
    Mem.store chunk target slot ofs targetvalue=Some targetinitialized /\
    Mem.inject f' initialized targetinitialized.
Proof.
  intros f source target size allocated fresh slot chunk ofs value targetvalue initialized
    Hinj Halloc Hvalid Hperm Hunused Hvalue Hstore.
  destruct (source_allocation_into_local_slot _ _ _ _ _ _ _ Hinj Halloc Hvalid Hperm Hunused)
    as [f' [Hinj' [Hincr [Hfresh Hframe]]]].
  assert (Hvalue' : Val.inject f' value targetvalue).
  { eapply val_inject_incr; eauto. }
  destruct (Mem.store_mapped_inject _ _ _ _ _ _ _ _ _ _ _ Hinj' Hstore Hfresh Hvalue')
    as [targetinitialized [Htarget Hfinal]].
  rewrite Z.add_0_r in Htarget. exists f',targetinitialized; auto.
Qed.

Theorem allocated_c_local_can_receive_source_allocation :
  forall ge env before vars env' target f source size after fresh id ty,
  Csem.alloc_variables ge env before vars env' target ->
  NoDup(map fst vars) -> In(id,ty)vars ->
  Mem.inject f source target ->
  Mem.alloc source 0 size=(after,fresh) ->
  size<=Ctypes.sizeof ge ty ->
  (forall slot, env'!id=Some(slot,ty) -> unused_target_slot f slot) ->
  exists slot f', env'!id=Some(slot,ty) /\ Mem.inject f' after target /\
    inject_incr f f' /\ f' fresh=Some(slot,0) /\
    (forall b, b<>fresh -> f' b=f b).
Proof.
  intros ge env before vars env' target f source size after fresh id ty
    Hlocals Hnames Hin Hinj Halloc Hsize Hunused.
  destruct (c_local_allocation_declared _ _ _ _ _ _ Hlocals Hnames _ _ Hin)
    as [slot [Hget [Hvalid Hperm]]].
  destruct (source_allocation_into_local_slot f source target size after fresh slot)
    as [f' Hresult]; auto.
  - intros; apply Hperm; lia.
  - exists slot,f'; auto.
Qed.

Definition no_blocks_mapped : meminj := fun _ => None.

Lemma empty_source_injection : forall target,
  Mem.inject no_blocks_mapped Mem.empty target.
Proof.
  intros target. constructor.
  - constructor; intros; discriminate.
  - intros; reflexivity.
  - intros; discriminate.
  - unfold Mem.meminj_no_overlap; intros; discriminate.
  - intros; discriminate.
  - intros; discriminate.
Qed.

Print Assumptions source_allocation_into_local_slot.
Print Assumptions source_allocation_and_scalar_store.
Print Assumptions allocated_c_local_can_receive_source_allocation.

(* The target already owns its C local while the source heap is still empty.
   A later source allocation and initialization are simulated by reusing that
   local, without any second target allocation. *)
Example preallocated_int32_local_witness : forall ge id,
  exists target slot sourceallocated sourceblock f sourceinitialized targetinitialized,
    Csem.alloc_variables ge (PTree.empty _) Mem.empty
      [(id,Ctypes.Tint Ctypes.I32 Ctypes.Signed noattr)]
      (PTree.set id (slot,Ctypes.Tint Ctypes.I32 Ctypes.Signed noattr) (PTree.empty _)) target /\
    Mem.alloc Mem.empty 0 4=(sourceallocated,sourceblock) /\
    Mem.inject no_blocks_mapped Mem.empty target /\
    f sourceblock=Some(slot,0) /\
    Mem.store Mint32 sourceallocated sourceblock 0 (Vint(Int.repr 41))=Some sourceinitialized /\
    Mem.store Mint32 target slot 0 (Vint(Int.repr 41))=Some targetinitialized /\
    Mem.inject f sourceinitialized targetinitialized /\
    Mem.load Mint32 sourceinitialized sourceblock 0=Some(Vint(Int.repr 41)) /\
    Mem.load Mint32 targetinitialized slot 0=Some(Vint(Int.repr 41)).
Proof.
  intros ge id.
  destruct (Mem.alloc Mem.empty 0 4) as [allocated block] eqn:Halloc.
  assert (Haccess : Mem.valid_access allocated Mint32 block 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc|lia|simpl; lia|].
    apply Z.divide_0_r. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint(Int.repr 41)) Haccess)
    as [initialized Hstore].
  assert (Hvalid : Mem.valid_block allocated block).
  { eapply Mem.valid_new_block; exact Halloc. }
  assert (Hperm : forall ofs, 0<=ofs<4 -> Mem.perm allocated block ofs Cur Freeable).
  { intros. eapply Mem.perm_alloc_2; eauto. }
  destruct (source_allocation_and_scalar_store no_blocks_mapped Mem.empty allocated 4
    allocated block block Mint32 0 (Vint(Int.repr 41)) (Vint(Int.repr 41)) initialized)
    as [f [targetinitialized [Hincr [Hmap [Hframe [Htarget Hinj]]]]]];
    try exact Halloc; try exact Hvalid; try exact Hperm; try exact Hstore.
  - apply empty_source_injection.
  - intros b delta; discriminate.
  - constructor.
  - exists allocated,block,allocated,block,f,initialized,targetinitialized.
    split.
    + econstructor; [exact Halloc|constructor].
    + refine (conj eq_refl (conj (empty_source_injection _)
        (conj Hmap (conj Hstore (conj Htarget (conj Hinj _)))))).
      split.
      * exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
      * exact (Mem.load_store_same _ _ _ _ _ _ Htarget).
Qed.

Print Assumptions preallocated_int32_local_witness.
