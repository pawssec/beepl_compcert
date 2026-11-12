(* Profiles of the actual fresh header allocation and boolean-normalization
   writes performed by a Bytes match. No permissions are inferred from types. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_packet BeePL_packet_proofs.
Require Import BeePL_block_extents BeePL_heap_extents.
Local Open Scope Z_scope.

Lemma normalize_packet_booleans_extent_frame : forall offsets m b final tracked limit,
  normalize_packet_booleans m b offsets = OK final ->
  source_block_extent m tracked limit -> source_block_extent final tracked limit.
Proof.
  induction offsets as [|offset offsets IH]; intros m b final tracked limit Hnormalize Hextent.
  - inversion Hnormalize; subst; exact Hextent.
  - cbn [normalize_packet_booleans] in Hnormalize.
    destruct (normalize_packet_boolean m b offset) as [[next flag]|error] eqn:Hnext; try discriminate.
    eapply IH; [exact Hnormalize|]. eapply source_block_extent_store; [|exact Hextent].
    eapply normalize_packet_boolean_store; exact Hnext.
Qed.

Theorem prepared_packet_header_extent : forall env members m bytes final fresh,
  prepare_packet_header env members m bytes = OK(final,fresh) ->
  Z.of_nat (List.length bytes) <= Ptrofs.max_unsigned ->
  source_block_extent final fresh (Z.of_nat (List.length bytes)).
Proof.
  intros * Hprepare Hbound.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  eapply normalize_packet_booleans_extent_frame; [exact Hnormalize|].
  eapply source_block_extent_storebytes; [exact Hstore|].
  eapply allocated_source_block_extent; [exact Halloc|lia].
Qed.

Theorem prepared_packet_old_extent : forall env members m bytes final fresh b limit,
  prepare_packet_header env members m bytes = OK(final,fresh) ->
  source_block_extent m b limit -> source_block_extent final b limit.
Proof.
  intros * Hprepare Hextent.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  eapply normalize_packet_booleans_extent_frame; [exact Hnormalize|].
  eapply source_block_extent_storebytes; [exact Hstore|].
  eapply source_block_extent_alloc_frame; eauto.
Qed.

Theorem prepared_packet_heap_extents : forall env members Sigma Sigma' objects cells packets
  objects' cells' packets' m bytes final fresh,
  heap_block_extents Sigma m objects cells packets ->
  prepare_packet_header env members m bytes = OK(final,fresh) ->
  Z.of_nat (List.length bytes) <= Ptrofs.max_unsigned ->
  (forall b, tracked_data_block Sigma' objects' cells' packets' b ->
    tracked_data_block Sigma objects cells packets b \/ b=fresh) ->
  heap_block_extents Sigma' final objects' cells' packets'.
Proof.
  intros * [limits [Hvalid Hcover]] Hprepare Hbound Horigin.
  exists (PTree.set fresh (Z.of_nat (List.length bytes)) limits). split.
  - intros b limit Hget. rewrite PTree.gsspec in Hget.
    destruct (Coqlib.peq b fresh).
    + subst b. inversion Hget; subst limit. eapply prepared_packet_header_extent; eauto.
    + eapply prepared_packet_old_extent; [exact Hprepare|apply Hvalid; exact Hget].
  - intros b Htracked. destruct (Horigin _ Htracked) as [Hold | Heq].
    + destruct (Coqlib.peq b fresh) as [Heq | Hneq].
      * subst b. exists (Z.of_nat(List.length bytes)); apply PTree.gss.
      * destruct (Hcover _ Hold) as [limit Hget]. exists limit. rewrite PTree.gso; assumption.
    + subst b. exists (Z.of_nat(List.length bytes)); apply PTree.gss.
Qed.

Print Assumptions prepared_packet_heap_extents.
