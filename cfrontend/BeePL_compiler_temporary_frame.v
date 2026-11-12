(* A target-only capture slot is outside the source memory injection's range.
   Source-corresponding stores therefore cannot modify it.  This derives the
   concrete mutation frame needed by binary_capture_prefix; it is not yet a
   frame theorem for arbitrary expression evaluation or external calls. *)
Require Import List ZArith Coqlib AST Integers Values Memory.
Require Import BeePL_compiler_memory_injection.
Import ListNotations.
Local Open Scope Z_scope.

Lemma allocated_capture_slot_unused : forall f source target lo hi allocated slot,
 Mem.inject f source target -> Mem.alloc target lo hi = (allocated,slot) ->
 unused_target_slot f slot /\ Mem.inject f source allocated.
Proof.
 intros * Hinj Halloc; split.
 - intros b delta Hmap.
   pose proof (Mem.valid_block_inject_2 _ _ _ _ _ _ Hmap Hinj) as Hvalid.
   exact (Mem.fresh_block_alloc _ _ _ _ _ Halloc Hvalid).
 - eapply Mem.alloc_right_inject; eauto.
Qed.

Lemma mapped_store_frames_capture : forall f slot source_block target_block delta
 chunk target offset value after,
 unused_target_slot f slot -> f source_block = Some(target_block,delta) ->
 Mem.store chunk target target_block offset value = Some after ->
 Mem.unchanged_on (fun block _ => block = slot) target after.
Proof.
 intros * Hunused Hmap Hstore.
 eapply Mem.store_unchanged_on; [exact Hstore|].
 intros i Hrange Hequal; subst target_block. exact (Hunused source_block delta Hmap).
Qed.

Lemma mapped_storebytes_frames_capture : forall f slot source_block target_block delta
 target offset bytes after,
 unused_target_slot f slot -> f source_block = Some(target_block,delta) ->
 Mem.storebytes target target_block offset bytes = Some after ->
 Mem.unchanged_on (fun block _ => block = slot) target after.
Proof.
 intros * Hunused Hmap Hstore.
 eapply Mem.storebytes_unchanged_on; [exact Hstore|].
 intros i Hrange Hequal; subst target_block. exact (Hunused source_block delta Hmap).
Qed.

Theorem injected_scalar_store_preserves_capture : forall f slot chunk source source_block
 offset source_value source_after target target_block delta target_value,
 Mem.inject f source target -> unused_target_slot f slot ->
 Mem.store chunk source source_block offset source_value = Some source_after ->
 f source_block = Some(target_block,delta) -> Val.inject f source_value target_value ->
 exists target_after,
 Mem.store chunk target target_block (offset+delta) target_value = Some target_after /\
 Mem.inject f source_after target_after /\
 Mem.unchanged_on (fun block _ => block = slot) target target_after.
Proof.
 intros * Hinj Hunused Hstore Hmap Hvalue.
 destruct (Mem.store_mapped_inject _ _ _ _ _ _ _ _ _ _ _ Hinj Hstore Hmap Hvalue)
   as [target_after [Htarget Hafter]].
 exists target_after; split; [exact Htarget|]. split; [exact Hafter|].
 eapply mapped_store_frames_capture; eauto.
Qed.

(* Source allocation may extend the injection into another reserved C local.
   Merely inject_incr is insufficient: it might map into this capture slot.
   These actual-allocation update equations make the needed exclusion explicit. *)
Lemma unused_slot_after_other_mapping : forall f f' slot fresh other delta,
 unused_target_slot f slot -> other <> slot ->
 f' fresh = Some(other,delta) -> (forall b, b<>fresh -> f' b=f b) ->
 unused_target_slot f' slot.
Proof.
 intros * Hunused Hdistinct Hnew Hother b shift Hmap.
 destruct (peq b fresh) as [Heq|Hneq].
 - subst b. rewrite Hnew in Hmap. inversion Hmap; contradiction.
 - rewrite Hother in Hmap by exact Hneq. eapply Hunused; exact Hmap.
Qed.

Record scalar_write := {
 write_chunk : memory_chunk;
 write_source_block : block;
 write_offset : Z;
 write_source_value : val;
 write_target_value : val
}.

Inductive source_mapped_writes (f : meminj) : list scalar_write -> mem -> mem -> Prop :=
| source_writes_nil : forall m, source_mapped_writes f [] m m
| source_writes_cons : forall w ws before middle final target_block delta,
 f (write_source_block w) = Some(target_block,delta) ->
 Val.inject f (write_source_value w) (write_target_value w) ->
 Mem.store (write_chunk w) before (write_source_block w) (write_offset w)
   (write_source_value w) = Some middle ->
 source_mapped_writes f ws middle final ->
 source_mapped_writes f (w::ws) before final.

Inductive target_mapped_writes (f : meminj) : list scalar_write -> mem -> mem -> Prop :=
| target_writes_nil : forall m, target_mapped_writes f [] m m
| target_writes_cons : forall w ws before middle final target_block delta,
 f (write_source_block w) = Some(target_block,delta) ->
 Mem.store (write_chunk w) before target_block (write_offset w + delta)
   (write_target_value w) = Some middle ->
 target_mapped_writes f ws middle final ->
 target_mapped_writes f (w::ws) before final.

Theorem injected_scalar_writes_preserve_capture : forall f writes source source_after,
 source_mapped_writes f writes source source_after ->
 forall target slot, Mem.inject f source target -> unused_target_slot f slot ->
 exists target_after,
 target_mapped_writes f writes target target_after /\
 Mem.inject f source_after target_after /\
 Mem.unchanged_on (fun block _ => block = slot) target target_after.
Proof.
 intros f writes source source_after Hwrites; induction Hwrites;
 intros target slot Hinj Hunused.
 - exists target; split; [constructor|]. split; [exact Hinj|apply Mem.unchanged_on_refl].
 - destruct (injected_scalar_store_preserves_capture _ _ _ _ _ _ _ _ _ _ _ _
     Hinj Hunused H1 H H0) as [target_middle [Hstore [Hmiddle Hframe1]]].
   destruct (IHHwrites target_middle slot Hmiddle Hunused)
     as [target_after [Htail [Hfinal Hframe2]]].
   exists target_after; split.
   + econstructor; eauto.
   + split; [exact Hfinal|]. eapply Mem.unchanged_on_trans; eauto.
Qed.

Corollary injected_scalar_writes_keep_captured_value : forall f writes source source_after
 target slot chunk offset value,
 source_mapped_writes f writes source source_after ->
 Mem.inject f source target -> unused_target_slot f slot ->
 Mem.load chunk target slot offset = Some value ->
 exists target_after,
 target_mapped_writes f writes target target_after /\
 Mem.inject f source_after target_after /\
 Mem.load chunk target_after slot offset = Some value.
Proof.
 intros * Hwrites Hinj Hunused Hload.
 destruct (injected_scalar_writes_preserve_capture _ _ _ _ Hwrites target slot Hinj Hunused)
   as [target_after [Htarget [Hafter Hframe]]].
 exists target_after; split; [exact Htarget|]. split; [exact Hafter|].
 eapply Mem.load_unchanged_on; [exact Hframe| |exact Hload]. intros; reflexivity.
Qed.

Print Assumptions allocated_capture_slot_unused.
Print Assumptions injected_scalar_store_preserves_capture.
Print Assumptions injected_scalar_writes_preserve_capture.
Print Assumptions injected_scalar_writes_keep_captured_value.

Lemma capture_store_preserves_injection : forall f source target slot chunk offset value saved,
 Mem.inject f source target -> unused_target_slot f slot ->
 Mem.store chunk target slot offset value = Some saved ->
 Mem.inject f source saved.
Proof.
 intros * Hinj Hunused Hstore.
 eapply Mem.store_outside_inject; [exact Hinj| |exact Hstore].
 intros b delta ofs Hmap Hperm Hrange. exact (Hunused b delta Hmap).
Qed.

Theorem capture_then_injected_scalar_writes : forall f source target slot chunk offset value,
 Mem.inject f source target -> unused_target_slot f slot ->
 Mem.valid_access target chunk slot offset Writable ->
 Val.load_result chunk value = value ->
 exists saved,
 Mem.store chunk target slot offset value = Some saved /\
 Mem.inject f source saved /\
 forall writes source_after,
 source_mapped_writes f writes source source_after ->
 exists target_after,
 target_mapped_writes f writes saved target_after /\
 Mem.inject f source_after target_after /\
 Mem.unchanged_on (fun block _ => block = slot) saved target_after /\
 Mem.load chunk target_after slot offset = Some value.
Proof.
 intros * Hinj Hunused Haccess Hnormalize.
 destruct (Mem.valid_access_store _ _ _ _ value Haccess) as [saved Hstore].
 assert (Hsaved : Mem.inject f source saved).
 { eapply capture_store_preserves_injection; eauto. }
 exists saved; split; [exact Hstore|]. split; [exact Hsaved|].
 intros writes source_after Hwrites.
 destruct (injected_scalar_writes_preserve_capture _ _ _ _ Hwrites saved slot Hsaved Hunused)
   as [target_after [Htarget [Hafter Hframe]]].
 exists target_after; split; [exact Htarget|]. split; [exact Hafter|]. split; [exact Hframe|].
 eapply Mem.load_unchanged_on; [exact Hframe| |].
 - intros; reflexivity.
 - rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore), Hnormalize. reflexivity.
Qed.

Theorem source_allocation_store_frames_other_capture : forall f source target size allocated fresh
 destination capture chunk offset value target_value initialized,
 Mem.inject f source target ->
 Mem.alloc source 0 size = (allocated,fresh) ->
 Mem.valid_block target destination ->
 (forall ofs, 0<=ofs<size -> Mem.perm target destination ofs Cur Freeable) ->
 unused_target_slot f destination -> unused_target_slot f capture -> destination<>capture ->
 Val.inject f value target_value ->
 Mem.store chunk allocated fresh offset value = Some initialized ->
 exists f' target_after,
 inject_incr f f' /\ f' fresh=Some(destination,0) /\
 unused_target_slot f' capture /\
 Mem.store chunk target destination offset target_value = Some target_after /\
 Mem.inject f' initialized target_after /\
 Mem.unchanged_on (fun block _ => block=capture) target target_after.
Proof.
 intros * Hinj Halloc Hvalid Hperm Hdest Hcapture Hdistinct Hvalue Hstore.
 destruct (source_allocation_and_scalar_store _ _ _ _ _ _ _ _ _ _ _ _
   Hinj Halloc Hvalid Hperm Hdest Hvalue Hstore)
   as [f' [target_after [Hincr [Hfresh [Hother [Htarget Hafter]]]]]].
 assert (Hunused : unused_target_slot f' capture).
 { eapply unused_slot_after_other_mapping; eauto. }
 exists f',target_after; split; [exact Hincr|]. split; [exact Hfresh|].
 split; [exact Hunused|]. split; [exact Htarget|]. split; [exact Hafter|].
 eapply mapped_store_frames_capture; eauto.
Qed.

Print Assumptions capture_store_preserves_injection.
Print Assumptions capture_then_injected_scalar_writes.
Print Assumptions source_allocation_store_frames_other_capture.
