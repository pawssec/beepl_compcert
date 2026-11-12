(* A source-live reference cannot keep its representation in a freed target
   stack slot. This audits the lifetime obligation; it does not implement an
   escape checker or claim a complete program counterexample theorem. *)
Require Import ZArith Lia Coqlib Maps AST Memory Values.
Local Open Scope Z_scope.

Theorem live_source_cannot_map_to_freed_slot :
 forall source target released f source_block target_block offset delta lo hi,
 Mem.free target target_block lo hi = Some released ->
 f source_block = Some (target_block,delta) ->
 Mem.perm source source_block offset Cur Readable ->
 lo <= offset + delta < hi ->
 ~ Mem.inject f source released.
Proof.
 intros * Hfree Hmap Hread Hrange Hinject.
 pose proof (Mem.perm_inject _ _ _ _ _ _ _ _ _ Hmap Hinject Hread) as Htarget.
 exact (Mem.perm_free_2 _ _ _ _ _ Hfree _ _ _ Hrange Htarget).
Qed.

Example live_source_freed_target_witness : exists allocated released block,
 Mem.alloc Mem.empty 0 4 = (allocated,block) /\
 Mem.free allocated block 0 4 = Some released /\
 Mem.perm allocated block 0 Cur Readable /\
 forall f, f block = Some(block,0) -> ~Mem.inject f allocated released.
Proof.
 destruct (Mem.alloc Mem.empty 0 4) as [allocated block] eqn:Halloc.
 assert (Hrange : Mem.range_perm allocated block 0 4 Cur Freeable).
 { intros offset Hbounds. eapply Mem.perm_alloc_2; eauto. }
 destruct (Mem.range_perm_free _ _ _ _ Hrange) as [released Hfree].
 exists allocated,released,block; split; [reflexivity|].
 split; [exact Hfree|].
 assert (Hread : Mem.perm allocated block 0 Cur Readable).
 { apply Mem.perm_implies with Freeable; [apply Hrange; lia|constructor]. }
 split; [exact Hread|]. intros f Hmap.
 eapply live_source_cannot_map_to_freed_slot; eauto; lia.
Qed.
Print Assumptions live_source_cannot_map_to_freed_slot.
Print Assumptions live_source_freed_target_witness.
