(* Object-level packet separation is hereditary: registering a previously
   known subobject cannot introduce a new alias assumption. The invariant
   describes memory locations before any copy, independently of an operation. *)
Require Import List ZArith Lia Integers AST Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_packet.
Require Import BeePL_packet_descriptor_copy BeePL_packet_state BeePL_packet_mutation.
Require Export BeePL_packet_object_layout.
Require Import BeePL_packet_heap BeePL_packet_coverage BeePL_packet_replacement BeePL_bytes_execution.
Import ListNotations.
Local Open Scope Z_scope.

Theorem coherent_object_packet_replacement_plan :
  forall cenv Sigma m objects packets source source_base destination target root,
  aggregate_objects_valid cenv Sigma m objects ->
  objects source source_base root -> objects destination target root ->
  packet_state_valid m packets -> packet_object_coverage cenv objects packets ->
  packet_object_coherence cenv m objects packets ->
  packet_copy_replacement_plan m packets source (Ptrofs.unsigned source_base)
    destination (Ptrofs.unsigned target) (sizeof_type cenv root).
Proof.
  intros cenv Sigma m objects packets source source_base destination target root
    Hobjects Hsource Htarget Hvalid Hcoverage Hcoherent.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Htarget)
    as [_ [Hsize Hrest]].
  pose proof (packet_object_coherence_root _ _ _ _ _ _ _ Hcoherent Htarget Hsize) as Hregion.
  split.
  - intros descriptor offset Hin. destruct (proj1 (Hregion _ _ Hin)) as [Hapart|[delta [Hpath [Hd Ho]]]].
    + left; exact Hapart.
    + right. exists delta, (Ptrofs.repr (Ptrofs.unsigned source_base + delta)).
      destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hsource Hpath)
        as [Hdelta [Hoffset Hbound]].
      destruct (object_path_bounds _ _ _ _ Hpath) as [Hnonnegative [Hbytes Hinside]].
      split; [exact Hd|]. split; [exact Ho|]. split; [eapply Hcoverage; eauto|].
      split; [exact Hoffset|]. split; [exact Hnonnegative|]. split; [exact Hinside|].
      destruct (Hvalid _ _ Hin) as [_ [view [contents [Hdescriptor Hcontents]]]].
      rewrite <- Ho. eapply packet_descriptor_alignment; exact Hdescriptor.
  - intros descriptor offset Hin view Hview. exact (proj2 (Hregion _ _ Hin) _ Hview).
Qed.

Theorem packet_object_coherence_replacement :
  forall cenv m final objects packets source source_start destination target count bytes,
  0 <= count -> packet_state_valid m packets -> packet_object_coherence cenv m objects packets ->
  packet_copy_replacement_plan m packets source source_start destination target count ->
  Mem.loadbytes m source source_start count = Some bytes ->
  Mem.storebytes m destination target bytes = Some final ->
  packet_object_coherence cenv final objects packets.
Proof.
  intros cenv m final objects packets source source_start destination target count bytes Hcount Hv Hcoherent Hplan Hr Hw.
  destruct (packet_copy_replacement_state _ _ _ _ _ _ _ _ _ Hcount Hv Hplan Hr Hw) as [_ Horigin].
  eapply packet_object_coherence_view_origins; eauto.
Qed.

Print Assumptions coherent_object_packet_replacement_plan.
Print Assumptions packet_object_coherence_subobject_extension.
Print Assumptions packet_object_coherence_replacement.
Print Assumptions packet_object_coherence_scalar_store.

Require Export BeePL_packet_copy.

