(* Byte-level confinement includes aggregate padding. Source typing of fields
   alone does not constrain padding, so padding provenance is explicit below.
   None of these premises assumes closure of the final memory. *)
Require Import List ZArith Lia Coqlib Maps Integers AST Values Memdata Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_aggregate_copy.
Require Import BeePL_escape_store BeePL_compiler_frame_release.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Mem.loadbytes.

Definition retained_byte_region keep f (m : mem) b start size : Prop :=
  forall pos, start <= pos < start + size ->
  retained_memval keep f (ZMap.get pos (PMap.get b (Mem.mem_contents m))).

(* Each copied byte originates in a retained scalar encoding or in padding
   known not to contain a pointer fragment. This allows overlapping encodings
   only when the actual byte has the stated provenance. *)
Definition aggregate_byte_provenance keep f (m : mem) b start size : Prop :=
  forall pos, start <= pos < start + size ->
  let byte := ZMap.get pos (PMap.get b (Mem.mem_contents m)) in
  (~ pointer_fragment byte) \/
  exists chunk value, retained_value keep f value /\ In byte (encode_val chunk value).

Lemma retained_encoding : forall keep f chunk value,
  retained_value keep f value -> Forall (retained_memval keep f) (encode_val chunk value).
Proof.
  intros keep f chunk value Hvalue.
  assert (Hbytes : forall bytes, Forall (retained_memval keep f) (inj_bytes bytes)).
  { induction bytes; simpl; constructor; simpl; auto. }
  assert (Hundef : forall n, Forall (retained_memval keep f) (repeat Undef n)).
  { induction n; simpl; constructor; simpl; auto. }
  assert (Hfrags : forall n q, Forall (retained_memval keep f) (inj_value_rec n value q)).
  { induction n; intros; simpl; constructor; simpl; auto. }
  destruct value; destruct chunk; cbn [encode_val];
    try apply Hbytes; try apply Hundef; unfold inj_value; apply Hfrags.
Qed.

Lemma aggregate_provenance_retained : forall keep f m b start size,
  aggregate_byte_provenance keep f m b start size ->
  retained_byte_region keep f m b start size.
Proof.
  intros keep f m b start size H pos Hrange.
  destruct (H pos Hrange) as [Hpadding|[chunk [value [Hv Hin]]]].
  - unfold retained_memval. destruct (ZMap.get pos (PMap.get b (Mem.mem_contents m)))
      as [|byte|v q n] eqn:E; simpl; auto.
    destruct v; simpl; auto. exfalso; apply Hpadding.
    exists b0, i, q, n; reflexivity.
  - eapply Forall_forall; [eapply retained_encoding; exact Hv|exact Hin].
Qed.

Lemma retained_region_loadbytes : forall keep f m b start size bytes,
  retained_byte_region keep f m b start size ->
  Mem.loadbytes m b start size = Some bytes ->
  Forall (retained_memval keep f) bytes.
Proof.
  intros keep f m b start size bytes Hregion Hload.
  unfold Mem.loadbytes in Hload.
  destruct (Mem.range_perm_dec m b start (start + size) Cur Readable); try discriminate.
  inversion Hload; subst bytes.
  destruct (zle 0 size) as [Hsize|Hsize].
  - assert (Hrange : forall pos, start <= pos < start + Z.of_nat (Z.to_nat size) ->
        retained_memval keep f (ZMap.get pos (PMap.get b (Mem.mem_contents m)))).
    { rewrite Z2Nat.id by lia; exact Hregion. }
    clear Hregion Hload r Hsize. generalize dependent start.
    induction (Z.to_nat size); intros; simpl; constructor.
    + apply Hrange. rewrite Nat2Z.inj_succ; lia.
    + apply IHn. intros; apply Hrange. rewrite Nat2Z.inj_succ; lia.
  - rewrite Z_to_nat_neg by lia. constructor.
Qed.

Lemma retained_memory_source_region : forall keep f m b target delta start size bytes,
  retained_memory keep f m -> f b = Some (target, delta) -> keep target = true ->
  Mem.loadbytes m b start size = Some bytes -> retained_byte_region keep f m b start size.
Proof.
  intros keep f m b target delta start size bytes Hclosed Hmap Hkeep Hload pos Hrange.
  eapply Hclosed; eauto. eapply Mem.loadbytes_range_perm; eauto.
Qed.

Theorem closed_storebytes_retains_memory : forall keep f m dst offset bytes final,
  retained_memory keep f m -> Forall (retained_memval keep f) bytes ->
  Mem.storebytes m dst offset bytes = Some final -> retained_memory keep f final.
Proof.
  intros keep f m dst offset bytes final Hclosed Hbytes Hstore
    b target delta pos Hmap Hkeep Hread.
  pose proof (Mem.perm_storebytes_2 _ _ _ _ _ Hstore _ _ _ _ Hread) as Hold.
  erewrite Mem.storebytes_mem_contents by exact Hstore.
  destruct (peq b dst) as [E|E].
  - subst b. rewrite PMap.gss.
    destruct (zle offset pos); destruct (zlt pos (offset + Z.of_nat (length bytes))).
    + eapply Forall_forall; [exact Hbytes|]. apply Mem.setN_in; lia.
    + rewrite Mem.setN_outside by lia. eapply Hclosed; eauto.
    + rewrite Mem.setN_outside by lia. eapply Hclosed; eauto.
    + rewrite Mem.setN_outside by lia. eapply Hclosed; eauto.
  - rewrite PMap.gso by congruence. eapply Hclosed; eauto.
Qed.

Theorem aggregate_copy_retains_memory : forall keep f m src start size dst offset bytes final,
  retained_memory keep f m -> retained_byte_region keep f m src start size ->
  Mem.loadbytes m src start size = Some bytes ->
  Mem.storebytes m dst offset bytes = Some final -> retained_memory keep f final.
Proof.
  intros keep f m src start size dst offset bytes final Hclosed Hregion Hload Hstore.
  eapply closed_storebytes_retains_memory; [exact Hclosed| |exact Hstore].
  eapply retained_region_loadbytes; [exact Hregion|exact Hload].
Qed.

Corollary retained_source_copy_retains_memory :
  forall keep f m src target delta start size dst offset bytes final,
  retained_memory keep f m -> f src = Some (target, delta) -> keep target = true ->
  Mem.loadbytes m src start size = Some bytes ->
  Mem.storebytes m dst offset bytes = Some final -> retained_memory keep f final.
Proof.
  intros. eapply aggregate_copy_retains_memory; eauto using retained_memory_source_region.
Qed.

Theorem aggregate_assignment_retains_memory :
  forall ge keep f m ty src start dst offset final,
  retained_memory keep f m -> is_aggregate_type ty = true ->
  retained_byte_region keep f m src (Ptrofs.unsigned start) (aggregate_copy_size ge ty) ->
  assign_addr ge ty m dst offset Full (Vloc src start) final (Vloc src start) ->
  retained_memory keep f final.
Proof.
  intros ge keep f m ty src start dst offset final Hclosed Hkind Hregion Hassign.
  destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign)
    as [bytes [Hload Hstore]]. eapply aggregate_copy_retains_memory; eauto.
Qed.

Corollary retained_source_aggregate_assignment :
  forall ge keep f m ty src target delta start dst offset final,
  retained_memory keep f m -> is_aggregate_type ty = true ->
  f src = Some (target, delta) -> keep target = true ->
  assign_addr ge ty m dst offset Full (Vloc src start) final (Vloc src start) ->
  retained_memory keep f final.
Proof.
  intros ge keep f m ty src target delta start dst offset final
    Hclosed Hkind Hmap Hkeep Hassign.
  destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign)
    as [bytes [Hload Hstore]]. eapply retained_source_copy_retains_memory; eauto.
Qed.

(* Private temporary objects need this byte provenance (or a stronger typed
   layout invariant implying it). Merely checking their declared fields cannot
   justify pointer-containing padding. *)
Corollary provenance_aggregate_assignment_retains_memory :
  forall ge keep f m ty src start dst offset final,
  retained_memory keep f m -> is_aggregate_type ty = true ->
  aggregate_byte_provenance keep f m src (Ptrofs.unsigned start) (aggregate_copy_size ge ty) ->
  assign_addr ge ty m dst offset Full (Vloc src start) final (Vloc src start) ->
  retained_memory keep f final.
Proof.
  intros. eapply aggregate_assignment_retains_memory; eauto using aggregate_provenance_retained.
Qed.

Print Assumptions aggregate_assignment_retains_memory.
Print Assumptions retained_source_aggregate_assignment.
Print Assumptions aggregate_provenance_retained.
