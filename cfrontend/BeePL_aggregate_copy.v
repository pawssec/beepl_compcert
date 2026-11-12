(* Aggregate assignment copies the source object extent used by allocation,
   array strides, and readable descriptors. Alignment and nonoverlap remain
   explicit. This does not assert that every source extent equals its C ABI. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_copy_cells BeePL_aggregate_memory.
Import ListNotations.
Local Open Scope Z_scope.

Definition aggregate_copy_size (ge : genv) (ty : type) : Z :=
  sizeof_type ge.(genv_cenv) ty.

Record aggregate_copy_ready (ge : genv) (m : Mem.mem) (ty : type)
    (src : Values.block) (source : ptrofs) (dst : Values.block) (target : ptrofs) : Prop := {
  copy_kind : is_aggregate_type ty = true;
  copy_size_nonnegative : 0 <= aggregate_copy_size ge ty;
  copy_source_block : Mem.valid_block m src;
  copy_target_block : Mem.valid_block m dst;
  copy_source_bound : Ptrofs.unsigned source + aggregate_copy_size ge ty <= Ptrofs.modulus;
  copy_target_bound : Ptrofs.unsigned target + aggregate_copy_size ge ty <= Ptrofs.modulus;
  copy_source_alignment :
    (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type ty)
      | Ptrofs.unsigned source);
  copy_target_alignment :
    (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type ty)
      | Ptrofs.unsigned target);
  copy_nonoverlap : src <> dst \/ Ptrofs.unsigned source = Ptrofs.unsigned target \/
    Ptrofs.unsigned source + aggregate_copy_size ge ty <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + aggregate_copy_size ge ty <= Ptrofs.unsigned source;
  copy_source_permission : Mem.range_perm m src (Ptrofs.unsigned source)
    (Ptrofs.unsigned source + aggregate_copy_size ge ty) Cur Readable;
  copy_target_permission : Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + aggregate_copy_size ge ty) Cur Freeable
}.

Lemma aggregate_copy_ready_from_descriptors :
  forall ge Sigma objects m ty src source dst target,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects src source ty -> objects dst target ty ->
  (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type ty)
    | Ptrofs.unsigned source) ->
  (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type ty)
    | Ptrofs.unsigned target) ->
  (src <> dst \/ Ptrofs.unsigned source = Ptrofs.unsigned target \/
    Ptrofs.unsigned source + aggregate_copy_size ge ty <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + aggregate_copy_size ge ty <= Ptrofs.unsigned source) ->
  Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + aggregate_copy_size ge ty) Cur Freeable ->
  aggregate_copy_ready ge m ty src source dst target.
Proof.
  intros ge Sigma objects m ty src source dst target Hobjects Hsrc Hdst
    HsrcAlign HdstAlign Hapart Hwrite.
  assert (Hsize : aggregate_copy_size ge ty = sizeof_type ge.(genv_cenv) ty) by reflexivity.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsrc)
    as [Hkind [Hnonnegative [HsrcBound [HsrcBlock Hread]]]].
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hdst)
    as [_ [_ [HdstBound [HdstBlock _]]]].
  constructor; try assumption; rewrite Hsize; assumption.
Qed.

Theorem aggregate_assignment_progress : forall ge m ty src source dst target,
  aggregate_copy_ready ge m ty src source dst target ->
  exists m', assign_addr ge ty m dst target Full (Vloc src source) m' (Vloc src source).
Proof.
  intros ge m ty src source dst target Hready.
  destruct Hready as [Hkind Hsize Hsrc Hdst HsrcBound HdstBound
    HsrcAlign HdstAlign Hapart Hread Hwrite].
  destruct (Mem.range_perm_loadbytes m src (Ptrofs.unsigned source)
    (aggregate_copy_size ge ty) Hread) as [bytes Hbytes].
  assert (Hlength : Z.of_nat (length bytes) = aggregate_copy_size ge ty).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hbytes). apply Z2Nat.id; assumption. }
  assert (HstorePerm : Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlength. intros offset Hin.
    eapply Mem.perm_implies; [apply Hwrite; exact Hin | constructor]. }
  destruct (Mem.range_perm_storebytes m dst (Ptrofs.unsigned target) bytes HstorePerm)
    as [m' Hstore].
  exists m'. eapply assign_addr_copy; eauto.
Qed.

Lemma aggregate_assignment_bytes : forall ge m ty src source dst target m',
  is_aggregate_type ty = true ->
  assign_addr ge ty m dst target Full (Vloc src source) m' (Vloc src source) ->
  exists bytes,
    Mem.loadbytes m src (Ptrofs.unsigned source) (aggregate_copy_size ge ty) = Some bytes /\
    Mem.storebytes m dst (Ptrofs.unsigned target) bytes = Some m'.
Proof.
  intros ge m ty src source dst target m' Hkind Hassign.
  inversion Hassign; subst; try solve [simpl in Hkind; discriminate].
  - destruct ty; simpl in Hkind; try discriminate;
      match goal with H : access_mode_type _ = By_value _ |- _ => discriminate H end.
  - eexists; split; eassumption.
Qed.

Theorem aggregate_assignment_preserves_layout :
  forall ge Sigma L before after objects m m' ty src source dst target,
  aggregate_copy_ready ge m ty src source dst target ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations L before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  scalar_copy_plan before after src (Ptrofs.unsigned source) dst
    (Ptrofs.unsigned target) (aggregate_copy_size ge ty) ->
  assign_addr ge ty m dst target Full (Vloc src source) m' (Vloc src source) ->
  typed_memory_layout ge.(genv_cenv) Sigma after m' /\
  memory_locations L after m' /\ aggregate_objects_valid ge.(genv_cenv) Sigma m' objects.
Proof.
  intros ge Sigma L before after objects m m' ty src source dst target
    Hready Htyped Hlocated Hobjects Hplan Hassign.
  destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _
    (copy_kind _ _ _ _ _ _ _ Hready) Hassign) as [bytes [Hbytes Hstore]].
  destruct (typed_located_layout_copy ge.(genv_cenv) Sigma L before after m m'
    src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target)
    (aggregate_copy_size ge ty) bytes
    (copy_size_nonnegative _ _ _ _ _ _ _ Hready) Hbytes Hstore
    (copy_target_permission _ _ _ _ _ _ _ Hready) Htyped Hlocated Hplan)
    as [Htyped' Hlocated'].
  split; [exact Htyped' |]. split; [exact Hlocated' |].
  eapply aggregate_objects_valid_storebytes; eauto.
Qed.

Theorem aggregate_massgn_progress : forall ge p vm m basic attr src source dst target,
  aggregate_copy_ready ge m (construct_type_btype basic) src source dst target ->
  exists m', ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype)
    m' vm (Val Vunit Utype).
Proof.
  intros ge p vm m basic attr src source dst target Hready.
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hready) as [m' Hassign].
  exists m'. apply ssem_massgn3. exact Hassign.
Qed.

Print Assumptions aggregate_assignment_progress.
Print Assumptions aggregate_assignment_preserves_layout.
Print Assumptions aggregate_massgn_progress.

Theorem aggregate_massgn_preservation :
  forall ge p vm Sigma Gamma L before after objects m m' vm' e'
    basic attr src source dst target,
  aggregate_copy_ready ge m (construct_type_btype basic) src source dst target ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations L before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  scalar_copy_plan before after src (Ptrofs.unsigned source) dst
    (Ptrofs.unsigned target) (aggregate_copy_size ge (construct_type_btype basic)) ->
  ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) m' vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  type_expr ge.(genv_cenv) Gamma Sigma e' nil Utype /\
  typed_memory_layout ge.(genv_cenv) Sigma after m' /\
  memory_locations L after m' /\ aggregate_objects_valid ge.(genv_cenv) Sigma m' objects.
Proof.
  intros ge p vm Sigma Gamma L before after objects m m' vm' e'
    basic attr src source dst target Hready Htyped Hlocated Hobjects Hplan Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - exfalso. eapply value_has_no_small_step; eauto.
  - split; [reflexivity |]. split; [reflexivity |]. split; [constructor |].
    eapply aggregate_assignment_preserves_layout; eauto.
Qed.

Print Assumptions aggregate_massgn_preservation.
