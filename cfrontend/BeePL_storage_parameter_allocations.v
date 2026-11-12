(* Exact allocation capacity for every admitted data parameter. Code aliases
   are handled by the existing partition and never enter this data list. *)
Require Import List ZArith Lia Coqlib AST Maps Memory.
Require Import BeeTypes BeePL BeePL_allocation_proofs BeePL_block_extents.
Require Import BeePL_heap_extents BeePL_storage_types BeePL_parameter_storage_check.
Import ListNotations.
Local Open Scope Z_scope.

Lemma storage_parameter_allocation_extent_frame : forall ge Sigma vm m params callee allocated Sigma',
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  forall b limit, source_block_extent m b limit -> source_block_extent allocated b limit.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' Ha. induction Ha; intros b limit Hextent; auto.
  apply IHHa. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [next fresh] eqn:Halloc.
  inversion H; subst. eapply source_block_extent_alloc_frame; eauto.
Qed.

Theorem storage_parameter_allocation_slots : forall ge Sigma vm m params callee allocated Sigma',
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => storage_type_check ge.(genv_cenv) (snd param)=true) params ->
  forall id ty block, In (id,ty) params -> callee ! id=Some(block,ty) ->
  source_block_extent allocated block (sizeof_type ge.(genv_cenv) ty).
Proof.
  intros ge Sigma vm m params callee allocated Sigma' Ha.
  induction Ha as [Sigma vm m|Sigma vm m id ty params next fresh final callee Sigma1 Sigma' Halloc Htail IH];
    intros Hnames Htypes name t block Hin Hget; [contradiction|].
  inversion Hnames as [|? ? Hfresh Hnames']; subst.
  inversion Htypes as [|? ? Htype Htypes']; subst.
  destruct Hin as [Heq|Hin]; [inversion Heq; subst name t|eapply IH; eauto].
  rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Htail id Hfresh) in Hget.
  rewrite PTree.gss in Hget. inversion Hget; subst block.
  eapply storage_parameter_allocation_extent_frame; [exact Htail|].
  unfold balloc in Halloc.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [allocated newblock] eqn:Hactual.
  inversion Halloc; subst. eapply allocated_source_block_extent; [exact Hactual|].
  apply storage_type_size_bounds; exact Htype.
Qed.

Theorem storage_parameter_allocation_heap_extents : forall ge Sigma vm m params callee allocated Sigma' objects cells packets,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  Forall (fun param => storage_type_check ge.(genv_cenv) (snd param)=true) params ->
  heap_block_extents Sigma m objects cells packets ->
  heap_block_extents Sigma' allocated objects cells packets.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' objects cells packets Ha.
  induction Ha; intros Htypes Hheap; auto.
  inversion Htypes; subst. apply IHHa; auto. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [next fresh] eqn:Halloc.
  inversion H; subst.
  eapply heap_extents_allocation; [exact Hheap|exact Halloc| |].
  - apply storage_type_size_bounds; assumption.
  - eapply tracked_data_block_same_block_extension; try (intros; left; assumption).
    intros block t Hget. rewrite PTree.gsspec in Hget.
    match type of Hget with context [if ?test then _ else _] => destruct test; auto end.
Qed.

Corollary checked_data_parameter_allocation_slots : forall ge Sigma vm m allparams params callee allocated Sigma',
  parameters_storage_check ge.(genv_cenv) allparams=true -> incl params allparams ->
  Forall (fun param => is_funtype(snd param)=false) params ->
  alloc_variables ge Sigma vm m params callee allocated Sigma' -> NoDup(map fst params) ->
  forall id ty block, In(id,ty)params -> callee ! id=Some(block,ty) ->
  source_block_extent allocated block (sizeof_type ge.(genv_cenv) ty).
Proof.
  intros. eapply storage_parameter_allocation_slots; eauto using parameters_storage_data_list.
Qed.

Print Assumptions storage_parameter_allocation_slots.
Print Assumptions storage_parameter_allocation_heap_extents.

(* Allocation itself is total; admission bounds ensure the resulting slots
   satisfy the source profile, not that Mem.alloc can be called. *)
Lemma data_parameter_allocation_total : forall ge Sigma vm m params,
  exists callee allocated Sigma', alloc_variables ge Sigma vm m params callee allocated Sigma'.
Proof.
  intros ge Sigma vm m params. revert Sigma vm m. induction params as [|[id ty] rest IH]; intros.
  - exists vm,m,Sigma; constructor.
  - destruct (balloc ge Sigma m ty 0 (sizeof_type ge.(genv_cenv) ty))
      as [[next fresh] Sigma1] eqn:Halloc.
    destruct (IH Sigma1 (PTree.set id (fresh,ty) vm) next) as [callee [allocated [Sigma' Htail]]].
    exists callee,allocated,Sigma'. econstructor; eauto.
Qed.

Theorem checked_data_parameters_allocate : forall ge Sigma vm m allparams params objects cells packets,
  parameters_storage_check ge.(genv_cenv) allparams=true -> incl params allparams ->
  Forall (fun param => is_funtype(snd param)=false) params -> NoDup(map fst params) ->
  heap_block_extents Sigma m objects cells packets ->
  exists callee allocated Sigma',
    alloc_variables ge Sigma vm m params callee allocated Sigma' /\
    heap_block_extents Sigma' allocated objects cells packets /\
    forall id ty block, In(id,ty)params -> callee ! id=Some(block,ty) ->
      source_block_extent allocated block (sizeof_type ge.(genv_cenv) ty).
Proof.
  intros ge Sigma vm m allparams params objects cells packets Hcheck Hsub Hdata Hnames Hheap.
  assert(Hstorage: Forall (fun param => storage_type_check ge.(genv_cenv)(snd param)=true) params)
    by (eapply parameters_storage_data_list; eauto).
  destruct(data_parameter_allocation_total ge Sigma vm m params) as [callee [allocated [Sigma' Ha]]].
  exists callee,allocated,Sigma'. split; [exact Ha|]. split.
  - eapply storage_parameter_allocation_heap_extents; eauto.
  - eapply storage_parameter_allocation_slots; eauto.
Qed.

Print Assumptions checked_data_parameters_allocate.
