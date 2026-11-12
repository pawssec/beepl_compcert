(* Allocation provenance excludes independent cells in a structure's padding.
   This invariant constrains the layout, not the post-copy memory contents. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_initialization_proofs.
Require Import BeePL_array_proofs BeePL_structure_copy_layout BeePL_copy_cells.
Require Import BeePL_aggregate_copy BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_initialized_aggregate_mutation.
Require Import BeePL_packet_replacement.
Import ListNotations.
Local Open Scope Z_scope.

Definition field_block_footprint (cells : scalar_layout) block (fs : list primitive_field_plan) : Prop :=
  forall ofs ty chunk, cells block ofs ty chunk ->
  exists f, In f fs /\ ofs = planned_address Ptrofs.zero f /\
    ty = Vtype (planned_type f) /\ chunk = planned_chunk f.

Theorem allocated_field_block_footprint : forall cenv Sigma cells m allocated fresh size fs,
  typed_memory_layout cenv Sigma cells m -> Mem.alloc m 0 size = (allocated, fresh) ->
  field_block_footprint (extend_field_layout cells fresh Ptrofs.zero fs) fresh fs.
Proof.
  intros cenv Sigma cells m allocated fresh size fs Hmemory Halloc ofs ty chunk Hcell.
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hcell)
    as [Hold|[f [Hin [Hb [Hofs [Hty Hchunk]]]]]].
  - exfalso. eapply Mem.fresh_block_alloc; [exact Halloc|].
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. apply Hmemory; exact Hold.
  - exists f. repeat split; assumption.
Qed.

Lemma field_block_footprint_field_extension : forall cells block fs added base newfields,
  field_block_footprint cells block fs -> block <> added ->
  field_block_footprint (extend_field_layout cells added base newfields) block fs.
Proof.
  intros cells block fs added base newfields Hfoot Hneq ofs ty chunk Hcell.
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hcell)
    as [Hold|[f [Hin [Hb Hrest]]]]; [apply Hfoot; exact Hold|contradiction].
Qed.

Lemma field_block_footprint_array_extension : forall cells block fs added pt count,
  field_block_footprint cells block fs -> block <> added ->
  field_block_footprint (extend_array_layout cells added pt count) block fs.
Proof.
  intros cells block fs added pt count Hfoot Hneq ofs ty chunk [Hold|[i [Hi [Hb Hrest]]]];
    [apply Hfoot; exact Hold|contradiction].
Qed.

Lemma field_block_footprint_block_extension : forall cells cells' block fs,
  field_block_footprint cells block fs ->
  (forall ofs ty chunk, cells' block ofs ty chunk -> cells block ofs ty chunk) ->
  field_block_footprint cells' block fs.
Proof. intros cells cells' block fs Hfoot Hinc ofs ty chunk Hcell. apply Hfoot; auto. Qed.

Theorem existing_field_block_copy_plan : forall cells src dst count fs,
  field_block_footprint cells dst fs ->
  (forall f, In f fs -> cells src (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f)) ->
  (forall f, In f fs -> 0 <= planned_start Ptrofs.zero f /\
    planned_end Ptrofs.zero f <= count /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f)) ->
  scalar_copy_plan cells cells src 0 dst 0 count.
Proof.
  intros cells src dst count fs Hfoot Hsource Hbounds b ofs ty chunk Hcell.
  destruct (peq b dst) as [Hb|Hneq]; [subst b|left; split; [exact Hcell|left; exact Hneq]].
  destruct (Hfoot _ _ _ Hcell) as [f [Hin [Hofs [Hty Hchunk]]]]. subst ofs ty chunk.
  right. split; [reflexivity|]. exists (planned_start Ptrofs.zero f), (planned_address Ptrofs.zero f).
  destruct (Hbounds f Hin) as [Hlo [Hhi Halign]].
  split; [apply Hsource; exact Hin|]. split; [exact Hlo|]. split; [exact Hhi|].
  split; [unfold planned_start; lia|]. split; [unfold planned_start; lia|exact Halign].
Qed.

Theorem allocated_structure_existing_copy_plan :
  forall cenv Sigma before m allocated src dst count fs,
  typed_memory_layout cenv Sigma before m -> Mem.alloc m 0 count = (allocated, dst) ->
  (forall f, In f fs -> before src (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f)) ->
  (forall f, In f fs -> 0 <= planned_start Ptrofs.zero f /\
    planned_end Ptrofs.zero f <= count /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f)) ->
  scalar_copy_plan (extend_field_layout before dst Ptrofs.zero fs)
    (extend_field_layout before dst Ptrofs.zero fs) src 0 dst 0 count.
Proof.
  intros cenv Sigma before m allocated src dst count fs Hmemory Halloc Hsource Hbounds.
  eapply existing_field_block_copy_plan; [eapply allocated_field_block_footprint; eauto| |exact Hbounds].
  intros f Hin. apply extend_field_layout_old. apply Hsource; exact Hin.
Qed.

Theorem completed_structure_field_footprint :
  forall ge cenv Sigma cells p vm m sid ids es result final vm' fresh fs,
  typed_memory_layout cenv Sigma cells m ->
  ssem_expr ge p vm m (Sinit sid ids es result) final vm' (Val (Vloc fresh Ptrofs.zero) result) ->
  field_block_footprint (extend_field_layout cells fresh Ptrofs.zero fs) fresh fs.
Proof.
  intros ge cenv Sigma cells p vm m sid ids es result final vm' fresh fs Hmemory Hstep.
  inversion Hstep; subst. eapply allocated_field_block_footprint; eauto.
Qed.

Theorem coherent_structure_assignment_with_footprint :
  forall ge Gamma Sigma vm m objects cells packets p sid attr pa src dst ef final vm' e' fs,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid attr) pa));
      Val (Vloc src Ptrofs.zero) (Stype sid attr)] Utype) ef Utype ->
  aggregate_copy_ready ge m (Stype sid attr) src Ptrofs.zero dst Ptrofs.zero ->
  field_block_footprint cells dst fs ->
  (forall f, In f fs -> cells src (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f)) ->
  (forall f, In f fs -> 0 <= planned_start Ptrofs.zero f /\
    planned_end Ptrofs.zero f <= aggregate_copy_size ge (Stype sid attr) /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f)) ->
  ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc dst Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid attr) pa));
      Val (Vloc src Ptrofs.zero) (Stype sid attr)] Utype) final vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil Utype /\
  sub_effect nil ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p sid attr pa src dst ef final vm' e' fs
    Hconfig Hready Hfoot Hsource Hbounds Hstep.
  eapply coherent_aggregate_assignment_preservation; [exact Hconfig|exact Hready|exact Hstep].
Qed.

Print Assumptions allocated_field_block_footprint.
Print Assumptions existing_field_block_copy_plan.
Print Assumptions completed_structure_field_footprint.
Print Assumptions coherent_structure_assignment_with_footprint.
