(* Target call return frees C locals while source CallFrame return retains its
   allocations. Retire mappings for inaccessible source objects, rather than
   requiring impossible equality of the two memories. The retained-memory
   closure premise is explicit: the escape gate still needs a semantic proof
   establishing it across complete checked calls, including aggregate copies
   and external helpers. *)
Require Import List Bool ZArith Lia Coqlib Maps Integers AST Values Memdata Memory.
Import ListNotations.
Local Open Scope Z_scope.

Definition retain_injection (keep : block -> bool) (f : meminj) : meminj :=
  fun b => match f b with
           | Some (target, delta) => if keep target then Some (target, delta) else None
           | None => None
           end.

Definition retained_value (keep : block -> bool) (f : meminj) (v : val) : Prop :=
  match v with
  | Vptr b _ => forall target delta, f b = Some (target, delta) -> keep target = true
  | _ => True
  end.

Definition retained_memval (keep : block -> bool) (f : meminj) (v : memval) : Prop :=
  match v with Fragment v _ _ => retained_value keep f v | _ => True end.

Definition retained_memory (keep : block -> bool) (f : meminj) (m : Mem.mem) : Prop :=
  forall b target delta ofs,
  f b = Some (target, delta) -> keep target = true ->
  Mem.perm m b ofs Cur Readable ->
  retained_memval keep f (ZMap.get ofs (PMap.get b (Mem.mem_contents m))).

Lemma retain_injection_lookup : forall keep f b target delta,
  retain_injection keep f b = Some (target, delta) <->
  f b = Some (target, delta) /\ keep target = true.
Proof.
  intros. unfold retain_injection.
  destruct (f b) as [[tb d]|] eqn:E; [destruct (keep tb) eqn:K|];
    split; intros H; try discriminate; try (destruct H; discriminate).
  - inversion H; subst; auto.
  - destruct H as [H _]. inversion H; subst; reflexivity.
  - destruct H as [H Hkeep]. inversion H; subst. congruence.
Qed.

Lemma retained_value_inject : forall keep f source target,
  Val.inject f source target -> retained_value keep f source ->
  Val.inject (retain_injection keep f) source target.
Proof.
  intros keep f source target H Hkeep. inversion H; subst; try constructor.
  eapply Val.inject_ptr. apply retain_injection_lookup; split; [exact H0|].
  exact (Hkeep _ _ H0).
  reflexivity.
Qed.

Lemma retained_memval_inject : forall keep f source target,
  memval_inject f source target -> retained_memval keep f source ->
  memval_inject (retain_injection keep f) source target.
Proof.
  intros keep f source target H Hkeep. inversion H; subst; constructor.
  apply retained_value_inject; assumption.
Qed.

(* A callee can grow the mapping privately and then forget those new mappings.
   The caller's entry mapping is nevertheless preserved, so its already-live
   values remain related after return. *)
Theorem caller_injection_survives_private_return : forall keep entry final,
  inject_incr entry final ->
  (forall b target delta, entry b = Some (target, delta) -> keep target = true) ->
  inject_incr entry (retain_injection keep final).
Proof.
  intros keep entry final Hincr Hkept b target delta Hmap.
  apply retain_injection_lookup; split; eauto.
Qed.

Corollary caller_entry_value_survives_private_return : forall keep entry final sv tv,
  inject_incr entry final ->
  (forall b target delta, entry b = Some (target, delta) -> keep target = true) ->
  Val.inject entry sv tv -> Val.inject (retain_injection keep final) sv tv.
Proof.
  intros. eapply val_inject_incr; [|eassumption].
  eapply caller_injection_survives_private_return; eauto.
Qed.

Theorem retain_memory_injection : forall keep f source target,
  Mem.inject f source target -> retained_memory keep f source ->
  Mem.inject (retain_injection keep f) source target.
Proof.
  intros keep f source target H Hclosed. constructor.
  - constructor.
    + intros b tb delta ofs k p Hmap Hperm.
      apply retain_injection_lookup in Hmap as [Hmap _].
      eapply Mem.perm_inject; eauto.
    + intros b tb delta chunk ofs p Hmap Hperm.
      apply retain_injection_lookup in Hmap as [Hmap _].
      eapply Mem.mi_align; [exact (Mem.mi_inj _ _ _ H)|eassumption|eassumption].
    + intros b ofs tb delta Hmap Hperm.
      apply retain_injection_lookup in Hmap as [Hmap Hkeep].
      apply retained_memval_inject.
      * eapply Mem.mi_memval; [exact (Mem.mi_inj _ _ _ H)|eassumption|eassumption].
      * eapply Hclosed; eauto.
  - intros b Hinvalid. unfold retain_injection.
    rewrite (Mem.mi_freeblocks _ _ _ H b Hinvalid). reflexivity.
  - intros b tb delta Hmap. apply retain_injection_lookup in Hmap as [Hmap _].
    eapply Mem.mi_mappedblocks; eauto.
  - unfold Mem.meminj_no_overlap. intros b1 tb1 d1 b2 tb2 d2 ofs1 ofs2 Hneq H1 H2 P1 P2.
    apply retain_injection_lookup in H1 as [H1 _].
    apply retain_injection_lookup in H2 as [H2 _].
    eapply Mem.mi_no_overlap; eauto.
  - intros b tb delta ofs Hmap Hperm.
    apply retain_injection_lookup in Hmap as [Hmap _].
    eapply Mem.mi_representable; eauto.
  - intros b ofs tb delta k p Hmap Hperm.
    apply retain_injection_lookup in Hmap as [Hmap _].
    eapply Mem.mi_perm_inv; eauto.
Qed.

Theorem free_retired_target_blocks : forall ranges keep f source target released,
  Mem.inject (retain_injection keep f) source target ->
  Mem.free_list target ranges = Some released ->
  (forall b lo hi, In (b, lo, hi) ranges -> keep b = false) ->
  Mem.inject (retain_injection keep f) source released.
Proof.
  induction ranges as [|[[b lo] hi] rest IH]; intros keep f source target released H Hfree Hretired.
  - simpl in Hfree. inversion Hfree; subst; assumption.
  - simpl in Hfree. destruct (Mem.free target b lo hi) as [next|] eqn:E; try discriminate.
    eapply IH; [|exact Hfree|].
    + eapply Mem.free_right_inject; [exact H|exact E|].
      intros sb delta ofs k p Hmap Hperm Hrange.
      apply retain_injection_lookup in Hmap as [_ Hkeep].
      specialize (Hretired b lo hi (or_introl eq_refl)). congruence.
    + intros. eapply Hretired. right; eassumption.
Qed.

Theorem caller_memory_after_frame_release : forall keep f source target ranges released,
  Mem.inject f source target -> retained_memory keep f source ->
  Mem.free_list target ranges = Some released ->
  (forall b lo hi, In (b, lo, hi) ranges -> keep b = false) ->
  Mem.inject (retain_injection keep f) source released.
Proof.
  intros. eapply free_retired_target_blocks; eauto using retain_memory_injection.
Qed.

Corollary caller_value_after_frame_release : forall keep f source target ranges released sv tv,
  Mem.inject f source target -> retained_memory keep f source ->
  Mem.free_list target ranges = Some released ->
  (forall b lo hi, In (b, lo, hi) ranges -> keep b = false) ->
  Val.inject f sv tv -> retained_value keep f sv ->
  Mem.inject (retain_injection keep f) source released /\
  Val.inject (retain_injection keep f) sv tv.
Proof.
  intros; split; eauto using caller_memory_after_frame_release, retained_value_inject.
Qed.

Lemma retained_fragment_injection_extension : forall keep f f' source target,
  inject_incr f f' -> memval_inject f source target ->
  retained_memval keep f source -> retained_memval keep f' source.
Proof.
  intros keep f f' source target Hincr Hmv Hkeep.
  inversion Hmv; subst; simpl in *; auto.
  match goal with H : Val.inject _ _ _ |- _ => inversion H; subst end;
    simpl in *; auto.
  intros tb d Hnew.
  pose proof (Hincr _ _ _ H0) as Hold.
  assert (E : tb = b2) by congruence. subst tb.
  eapply Hkeep; exact H0.
Qed.

Theorem private_source_allocation_retains_memory :
  forall keep f f' source target lo hi allocated fresh slot delta,
  Mem.inject f source target -> retained_memory keep f source ->
  Mem.alloc source lo hi = (allocated, fresh) ->
  inject_incr f f' -> (forall b, b <> fresh -> f' b = f b) ->
  f' fresh = Some (slot, delta) -> keep slot = false ->
  retained_memory keep f' allocated.
Proof.
  intros keep f f' source target lo hi allocated fresh slot delta
    Hinj Hclosed Halloc Hincr Hframe Hfresh Hretired b tb d ofs Hmap Hkeep Hperm.
  assert (Hdifferent : b <> fresh).
  { intro E; subst b. rewrite Hfresh in Hmap. inversion Hmap; subst. congruence. }
  rewrite Hframe in Hmap by exact Hdifferent.
  assert (Hbefore : Mem.perm source b ofs Cur Readable).
  { eapply Mem.perm_alloc_4; eauto. }
  assert (Hcontents : ZMap.get ofs (PMap.get b (Mem.mem_contents allocated)) =
    ZMap.get ofs (PMap.get b (Mem.mem_contents source))).
  { eapply Mem.unchanged_on_contents with (P := fun _ _ => True);
      [eapply Mem.alloc_unchanged_on; exact Halloc|exact I|exact Hbefore]. }
  rewrite Hcontents.
  eapply retained_fragment_injection_extension; [exact Hincr| |].
  - eapply Mem.mi_memval; [exact (Mem.mi_inj _ _ _ Hinj)|exact Hmap|exact Hbefore].
  - eapply Hclosed; eauto.
Qed.

Theorem private_slot_initialization_retains_memory :
  forall keep f before after chunk fresh ofs value slot delta,
  retained_memory keep f before ->
  Mem.store chunk before fresh ofs value = Some after ->
  f fresh = Some (slot, delta) -> keep slot = false ->
  retained_memory keep f after.
Proof.
  intros keep f before after chunk fresh ofs value slot delta
    Hclosed Hstore Hfresh Hretired b tb d pos Hmap Hkeep Hperm.
  assert (Hdifferent : b <> fresh).
  { intro E; subst b. rewrite Hfresh in Hmap. inversion Hmap; subst. congruence. }
  assert (Hbefore : Mem.perm before b pos Cur Readable).
  { eapply Mem.perm_store_2; eauto. }
  erewrite Mem.unchanged_on_contents with
    (P := fun block _ => block <> fresh) (m_before := before).
  - eapply Hclosed; eauto.
  - eapply Mem.store_unchanged_on; [exact Hstore|]. intros i Hrange Hneq; apply Hneq; reflexivity.
  - exact Hdifferent.
  - exact Hbefore.
Qed.

Print Assumptions caller_memory_after_frame_release.
Print Assumptions caller_value_after_frame_release.
Print Assumptions private_source_allocation_retains_memory.
Print Assumptions private_slot_initialization_retains_memory.

(* A concrete caller block survives while a second, source-live frame block
   loses its target mapping. Neither memory equality nor an everywhere-empty
   injection can establish this witness. *)
Local Transparent Mem.alloc.
Definition release_witness_caller := fst (Mem.alloc Mem.empty 0 4).
Definition release_witness_memory := fst (Mem.alloc release_witness_caller 0 4).
Definition release_witness_keep (b : block) := negb (Pos.eqb b 2%positive).

Example live_source_frame_can_be_retired : exists released,
  Mem.free_list release_witness_memory [(2%positive, 0, 4)] = Some released /\
  Mem.perm release_witness_memory 2%positive 0 Cur Readable /\
  Mem.inject (retain_injection release_witness_keep
    (Mem.flat_inj (Mem.nextblock release_witness_memory))) release_witness_memory released /\
  retain_injection release_witness_keep
    (Mem.flat_inj (Mem.nextblock release_witness_memory)) 2%positive = None /\
  retain_injection release_witness_keep
    (Mem.flat_inj (Mem.nextblock release_witness_memory)) 1%positive = Some (1%positive, 0) /\
  Mem.perm released 1%positive 0 Cur Readable.
Proof.
  assert (A1 : Mem.alloc Mem.empty 0 4 = (release_witness_caller, 1%positive)) by reflexivity.
  assert (A2 : Mem.alloc release_witness_caller 0 4 = (release_witness_memory, 2%positive)) by reflexivity.
  assert (Hneutral : Mem.inject_neutral (Mem.nextblock release_witness_memory) release_witness_memory).
  { eapply Mem.alloc_inject_neutral; [exact A2| |reflexivity].
    eapply Mem.alloc_inject_neutral; [exact A1|apply Mem.empty_inject_neutral|reflexivity]. }
  assert (Hclosed : retained_memory release_witness_keep
    (Mem.flat_inj (Mem.nextblock release_witness_memory)) release_witness_memory).
  { intros b target delta ofs Hmap Hkeep Hperm.
    unfold release_witness_memory, release_witness_caller, Mem.alloc.
    cbn [fst Mem.mem_contents].
    repeat rewrite PMap.gsspec. repeat destruct (peq _ _);
      try rewrite PMap.gi; try rewrite ZMap.gi; cbn [retained_memval]; try exact I.
  }
  assert (Hrange : Mem.range_perm release_witness_memory 2%positive 0 4 Cur Freeable).
  { intros ofs Hbounds. eapply Mem.perm_alloc_2; eauto. }
  destruct (Mem.range_perm_free _ _ _ _ Hrange) as [released Hfree].
  assert (Hfree_list : Mem.free_list release_witness_memory [(2%positive,0,4)] = Some released).
  { simpl. rewrite Hfree; reflexivity. }
  assert (Hinject : Mem.inject
    (retain_injection release_witness_keep (Mem.flat_inj (Mem.nextblock release_witness_memory)))
    release_witness_memory released).
  { eapply caller_memory_after_frame_release; [apply Mem.neutral_inject; exact Hneutral|exact Hclosed|exact Hfree_list|].
    intros b lo hi [Heq|Hnil]; [inversion Heq; reflexivity|contradiction]. }
  exists released. split; [exact Hfree_list|]. split.
  - eapply Mem.perm_implies; [apply Hrange; lia|constructor].
  - split; [exact Hinject|]. split; [reflexivity|]. split; [reflexivity|].
    replace 0 with (0+0) by lia.
    eapply Mem.perm_inject with (b1 := 1%positive)
      (f := retain_injection release_witness_keep (Mem.flat_inj (Mem.nextblock release_witness_memory)));
      [reflexivity|exact Hinject|].
    eapply Mem.perm_alloc_1; [exact A2|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact A1|lia]|constructor].
Qed.
Print Assumptions live_source_frame_can_be_retired.
