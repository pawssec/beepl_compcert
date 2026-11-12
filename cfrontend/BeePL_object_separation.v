(* Paths through ordinary structs and arrays form disjoint subobjects or
   ancestor/descendant pairs. This derives copy nonoverlap from provenance. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_object_paths BeePL_object_edges.
Require Import BeePL_layout_proofs BeePL_bytes_layout BeePL_aggregate_memory.
Local Open Scope Z_scope.

Lemma object_source_size_nonnegative : forall env ty, 0 <= sizeof_type env ty.
Proof.
  intros env ty. induction ty; simpl.
  - lia.
  - destruct p; try destruct i; simpl; lia.
  - destruct Archi.ptr64; lia.
  - destruct (PTree.get i env) as [co|]; [pose proof (co_sizeof_pos co)|]; lia.
  - apply Z.mul_nonneg_nonneg; [assumption|lia].
  - lia.
  - unfold Mptr; destruct Archi.ptr64; simpl; lia.
Qed.

Lemma object_pointer_c_size : forall env pt,
  Ctypes.sizeof env (transBeePL_ptr_type pt) = if Archi.ptr64 then 8 else 4.
Proof.
  intros env pt; induction pt as [bt a|pt IH|args effects result variadic]; simpl; auto.
  destruct bt as [pt|sid a'|pt len a']; try destruct pt; reflexivity.
Qed.

Lemma program_object_source_c_size_bound : forall p ty,
  sizeof_type p.(prog_comp_env) ty <=
  Ctypes.sizeof (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type ty).
Proof.
  intros p ty; induction ty; simpl.
  - lia.
  - destruct p0; try destruct i; simpl; lia.
  - rewrite object_pointer_c_size. lia.
  - rewrite translated_composite_lookup. destruct (PTree.get i (prog_comp_env p)); reflexivity.
  - apply Z.mul_le_mono_nonneg_r; [lia|assumption].
  - lia.
  - change (2 * size_chunk Mptr <= Ctypes.sizeof (bcomposite_composite_env (prog_comp_env p)) (transBeePL_type Bytes)).
    rewrite program_bytes_c_size; lia.
Qed.

Inductive object_descent (env : bcomposite_env) : Z -> type -> Z -> type -> Prop :=
| descent_root : forall base ty, object_descent env base ty base ty
| descent_step : forall base root offset child result leaf,
    object_edge env (base,root) (offset,child) ->
    object_descent env offset child result leaf ->
    object_descent env base root result leaf.

Lemma object_descent_trans : forall env start root middle child final leaf,
  object_descent env start root middle child ->
  object_descent env middle child final leaf -> object_descent env start root final leaf.
Proof.
  intros env start root middle child final leaf Hfirst Hsecond.
  induction Hfirst; [exact Hsecond|eapply descent_step; eauto].
Qed.

Lemma object_path_descent : forall env root offset leaf,
  object_path env root offset leaf -> object_descent env 0 root offset leaf.
Proof.
  intros env root offset leaf Hpath. induction Hpath.
  - constructor.
  - eapply object_descent_trans; [exact IHHpath|].
    eapply descent_step; [eapply object_edge_field; eauto|constructor].
  - eapply object_descent_trans; [exact IHHpath|].
    eapply descent_step; [eapply object_edge_array; eauto|constructor].
Qed.

Lemma object_edge_bounds : forall env base root offset child,
  object_edge env (base,root) (offset,child) ->
  base <= offset /\ offset + sizeof_type env child <= base + sizeof_type env root.
Proof.
  intros env base root offset child Hedge. inversion Hedge; subst.
  - split; lia.
  - simpl. rewrite Z.max_r by lia. split; nia.
Qed.

Lemma object_descent_bounds : forall env base root offset child,
  object_descent env base root offset child ->
  base <= offset /\ offset + sizeof_type env child <= base + sizeof_type env root.
Proof.
  intros env base root offset child Hpath. induction Hpath; [split; lia|].
  pose proof (object_edge_bounds _ _ _ _ _ H). lia.
Qed.

Lemma program_object_siblings : forall p base root first first_type second second_type,
  object_edge p.(prog_comp_env) (base,root) (first,first_type) ->
  object_edge p.(prog_comp_env) (base,root) (second,second_type) ->
  (first = second /\ first_type = second_type) \/
  first + sizeof_type p.(prog_comp_env) first_type <= second \/
  second + sizeof_type p.(prog_comp_env) second_type <= first.
Proof.
  intros p base root first first_type second second_type Hfirst Hsecond.
  inversion Hfirst; subst; inversion Hsecond; subst.
  - assert (co0 = co) by congruence. subst co0.
    destruct (ident_eq field field0) as [Heq|Hneq].
    + subst field0. assert (second_type = first_type) by congruence. subst second_type.
      assert (delta0 = delta) by congruence. subst delta0. left; auto.
    + pose proof (source_member_type_translation _ _ _ H5) as Htype1.
      pose proof (source_member_type_translation _ _ _ H13) as Htype2.
      pose proof (program_object_source_c_size_bound p first_type).
      pose proof (program_object_source_c_size_bound p second_type).
      pose proof (Ctypes.field_offset_no_overlap _ _ _ _ _ _ _ _ _ _
        H6 Htype1 H14 Htype2 Hneq) as Hseparation.
      unfold layout_start, layout_width, bitsizeof in Hseparation. right; lia.
  - destruct (Z.lt_trichotomy index index0) as [Hlt|[Heq|Hgt]].
    + right; left. nia.
    + subst index0. left; auto.
    + right; right. nia.
Qed.

Theorem program_object_descents_separate_or_nested :
  forall p base root first first_type second second_type,
  object_descent p.(prog_comp_env) base root first first_type ->
  object_descent p.(prog_comp_env) base root second second_type ->
  first + sizeof_type p.(prog_comp_env) first_type <= second \/
  second + sizeof_type p.(prog_comp_env) second_type <= first \/
  object_descent p.(prog_comp_env) first first_type second second_type \/
  object_descent p.(prog_comp_env) second second_type first first_type.
Proof.
  intros p base root first first_type second second_type Hfirst.
  revert second second_type. induction Hfirst; intros second second_type Hsecond.
  - right; right; left; exact Hsecond.
  - inversion Hsecond; subst.
    + right; right; right. eapply descent_step; eauto.
    + destruct (program_object_siblings _ _ _ _ _ _ _ H H0)
        as [[Hoffset Hchild]|[Hbefore|Hafter]].
      * subst. apply IHHfirst; assumption.
      * pose proof (object_descent_bounds _ _ _ _ _ Hfirst).
        match goal with Htail : object_descent _ _ _ second second_type |- _ =>
          pose proof (object_descent_bounds _ _ _ _ _ Htail) end.
        left; lia.
      * pose proof (object_descent_bounds _ _ _ _ _ Hfirst).
        match goal with Htail : object_descent _ _ _ second second_type |- _ =>
          pose proof (object_descent_bounds _ _ _ _ _ Htail) end.
        right; left; lia.
Qed.

Lemma typed_object_descent : forall env Sigma block offset ty,
  object_type_at env Sigma block offset ty ->
  exists stored, PTree.get block Sigma = Some stored /\
    object_descent env 0 (stored_object_type stored) offset ty.
Proof.
  intros env Sigma block offset ty Hobject. induction Hobject.
  - exists stored; split; [assumption|constructor].
  - destruct IHHobject as [stored [Hget Hpath]]. exists stored; split; [exact Hget|].
    eapply object_descent_trans; [exact Hpath|].
    eapply descent_step; [eapply object_edge_field; eauto|constructor].
  - destruct IHHobject as [stored [Hget Hpath]]. exists stored; split; [exact Hget|].
    eapply object_descent_trans; [exact Hpath|].
    eapply descent_step; [eapply object_edge_array; eauto|constructor].
Qed.

Theorem program_same_typed_objects_nonoverlap : forall p Sigma block first second ty,
  object_type_at p.(prog_comp_env) Sigma block first ty ->
  object_type_at p.(prog_comp_env) Sigma block second ty ->
  first = second \/ first + sizeof_type p.(prog_comp_env) ty <= second \/
    second + sizeof_type p.(prog_comp_env) ty <= first.
Proof.
  intros p Sigma block first second ty Hfirst Hsecond.
  destruct (typed_object_descent _ _ _ _ _ Hfirst) as [stored [Hget Hpath]].
  destruct (typed_object_descent _ _ _ _ _ Hsecond) as [other [Hget' Hpath']].
  assert (other = stored) by congruence. subst other.
  destruct (program_object_descents_separate_or_nested _ _ _ _ _ _ _ Hpath Hpath')
    as [Hbefore|[Hafter|[Hdown|Hup]]]; auto;
    pose proof (object_descent_bounds _ _ _ _ _ ltac:(eassumption)); left; lia.
Qed.

Theorem program_aggregate_objects_nonoverlap :
  forall p Sigma m objects ty source source_base destination target,
  aggregate_objects_valid p.(prog_comp_env) Sigma m objects ->
  objects source source_base ty -> objects destination target ty ->
  source <> destination \/ Ptrofs.unsigned source_base = Ptrofs.unsigned target \/
    Ptrofs.unsigned source_base + sizeof_type p.(prog_comp_env) ty <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + sizeof_type p.(prog_comp_env) ty <= Ptrofs.unsigned source_base.
Proof.
  intros p Sigma m objects ty source source_base destination target Hobjects Hsource Htarget.
  destruct (Pos.eq_dec source destination) as [Heq|Hneq]; [subst destination|auto].
  right. eapply program_same_typed_objects_nonoverlap;
    eapply aggregate_object_typing; eauto.
Qed.

Print Assumptions program_object_descents_separate_or_nested.
Print Assumptions program_same_typed_objects_nonoverlap.
Print Assumptions program_aggregate_objects_nonoverlap.

Lemma object_edge_as_path : forall env base root offset child,
  object_edge env (base,root) (offset,child) ->
  object_path env root (offset-base) child.
Proof.
  intros env base root offset child Hedge. inversion Hedge; subst.
  - replace (base+delta-base) with (0+delta) by lia.
    eapply path_field; [constructor; apply object_source_size_nonnegative|eassumption|eassumption|
      eassumption|eassumption|eassumption|eassumption|eassumption].
  - replace (base+index*sizeof_type env child-base) with (0+index*sizeof_type env child) by lia.
    eapply path_array_element; [constructor; apply object_source_size_nonnegative|eassumption|eassumption].
Qed.

Lemma object_descent_as_path : forall env base root offset child,
  object_descent env base root offset child -> object_path env root (offset-base) child.
Proof.
  intros env base root offset child Hpath. induction Hpath.
  - replace (base-base) with 0 by lia. constructor; apply object_source_size_nonnegative.
  - replace (result-base) with ((offset-base)+(result-offset)) by lia.
    eapply object_path_compose; [eapply object_edge_as_path; exact H|exact IHHpath].
Qed.

Lemma scalar_object_descent_identity : forall env base ty offset child chunk,
  access_mode_type ty = By_value chunk -> object_descent env base ty offset child ->
  offset=base /\ child=ty.
Proof.
  intros env base ty offset child chunk Hmode Hpath. inversion Hpath; subst; [auto|].
  match goal with Hedge : object_edge _ _ _ |- _ => inversion Hedge; subst; discriminate Hmode end.
Qed.

Theorem program_scalar_leaf_subobject : forall p root cell_offset ty chunk child_offset child,
  scalar_object_leaf p.(prog_comp_env) root cell_offset ty chunk ->
  object_path p.(prog_comp_env) root child_offset child ->
  (cell_offset + size_chunk (transl_bchunk_cchunk chunk) <= child_offset \/
    child_offset + sizeof_type p.(prog_comp_env) child <= cell_offset) \/
  exists relative, scalar_object_leaf p.(prog_comp_env) child relative ty chunk /\
    cell_offset = child_offset + relative.
Proof.
  intros p root cell_offset ty chunk child_offset child [Hcell Hmode] Hchild.
  pose proof (scalar_type_chunk_size p.(prog_comp_env) _ _ Hmode) as Hsize.
  destruct (program_object_descents_separate_or_nested _ _ _ _ _ _ _
    (object_path_descent _ _ _ _ Hcell) (object_path_descent _ _ _ _ Hchild))
    as [Hbefore|[Hafter|[Hdown|Hup]]].
  - left; left; lia.
  - left; right; exact Hafter.
  - destruct (scalar_object_descent_identity _ _ _ _ _ _ Hmode Hdown) as [Hoffset Htype].
    subst child_offset child. right; exists 0. split; [split|]; auto; [|lia].
    constructor; apply object_source_size_nonnegative.
  - right; exists (cell_offset-child_offset). split; [split|]; auto; [|lia].
    eapply object_descent_as_path; exact Hup.
Qed.

Print Assumptions program_scalar_leaf_subobject.

Lemma aggregate_value_object_provenance : forall env Gamma Sigma block offset ty ef,
  is_aggregate_type ty = true ->
  BeePL_typesystem.type_expr env Gamma Sigma (Val (Vloc block offset) ty) ef ty ->
  object_type_at env Sigma block (Ptrofs.unsigned offset) ty.
Proof.
  intros env Gamma Sigma block offset ty ef Hkind Htyped.
  inversion Htyped; subst; try discriminate Hkind; assumption.
Qed.

Theorem program_aggregate_value_reference_nonoverlap :
  forall p Gamma Sigma m objects ty source source_base destination target ef,
  aggregate_objects_valid p.(prog_comp_env) Sigma m objects ->
  is_aggregate_type ty = true ->
  BeePL_typesystem.type_expr p.(prog_comp_env) Gamma Sigma (Val (Vloc source source_base) ty) ef ty ->
  objects destination target ty ->
  source <> destination \/ Ptrofs.unsigned source_base = Ptrofs.unsigned target \/
    Ptrofs.unsigned source_base + sizeof_type p.(prog_comp_env) ty <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + sizeof_type p.(prog_comp_env) ty <= Ptrofs.unsigned source_base.
Proof.
  intros p Gamma Sigma m objects ty source source_base destination target ef Hobjects Hkind Hsource Htarget.
  destruct (Pos.eq_dec source destination) as [Heq|Hneq]; [subst destination|auto].
  right. eapply program_same_typed_objects_nonoverlap.
  - eapply aggregate_value_object_provenance; eauto.
  - eapply aggregate_object_typing; eauto.
Qed.
Print Assumptions program_aggregate_value_reference_nonoverlap.

Require Import BeePL_packet_alignment BeePL_aggregate_copy.

Lemma pointer_blockcopy_alignment : forall env pt,
  alignof_blockcopy env (transBeePL_ptr_type pt) = if Archi.ptr64 then 8 else 4.
Proof.
  intros env pt. induction pt as [bt attr|pt IH|args effects result variadic]; simpl; auto.
  destruct bt as [pt|sid attr'|pt len attr']; try destruct pt; reflexivity.
Qed.

Lemma program_blockcopy_natural_alignment : forall p ty,
  alignof_blockcopy (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type ty) =
    Z.min 8 (natural_object_alignment p.(prog_comp_env) ty).
Proof.
  intros p ty. induction ty.
  - reflexivity.
  - destruct p0 as [|size sign attr|sign attr]; try destruct size; reflexivity.
  - simpl. rewrite pointer_blockcopy_alignment. destruct Archi.ptr64; reflexivity.
  - simpl. rewrite translated_composite_lookup. destruct (PTree.get i p.(prog_comp_env)); reflexivity.
  - simpl. exact IHty.
  - reflexivity.
  - destruct (built_bytes_layout _ _ (prog_comp_env_eq p))
      as [co [Hget [Hmembers [Hshape [Hsize Halign]]]]].
    simpl. rewrite translated_composite_lookup, Hget. simpl. rewrite Halign. reflexivity.
Qed.

Lemma minimum_blockcopy_alignment_divides : forall env ty,
  (Z.min 8 (natural_object_alignment env ty) | natural_object_alignment env ty).
Proof.
  intros env ty. destruct (Z_le_dec (natural_object_alignment env ty) 8).
  - rewrite Z.min_r by assumption. apply Z.divide_refl.
  - rewrite Z.min_l by lia. apply power_alignment_le_divides.
    + exists 3%nat; reflexivity.
    + apply natural_object_alignment_power.
    + lia.
Qed.

Theorem program_typed_object_copy_alignment : forall p Sigma block offset ty,
  object_type_at p.(prog_comp_env) Sigma block offset ty ->
  (alignof_blockcopy (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type ty) | offset).
Proof.
  intros p Sigma block offset ty Hobject.
  destruct (typed_object_descent _ _ _ _ _ Hobject) as [stored [Hget Hdescent]].
  pose proof (object_descent_as_path _ _ _ _ _ Hdescent) as Hpath.
  rewrite Z.sub_0_r in Hpath.
  rewrite program_blockcopy_natural_alignment.
  eapply Z.divide_trans; [apply minimum_blockcopy_alignment_divides|].
  exact (proj1 (program_object_path_alignment _ _ _ _ Hpath _
    (natural_object_alignment_power _ _) (Z.le_refl _))).
Qed.

Theorem program_aggregate_copy_ready :
  forall p Sigma m objects ty source source_base destination target,
  aggregate_objects_valid p.(prog_comp_env) Sigma m objects ->
  objects source source_base ty -> objects destination target ty ->
  Mem.range_perm m destination (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + sizeof_type p.(prog_comp_env) ty) Cur Freeable ->
  aggregate_copy_ready (globalenv p) m ty source source_base destination target.
Proof.
  intros p Sigma m objects ty source source_base destination target Hobjects Hsource Htarget Hwrite.
  eapply aggregate_copy_ready_from_descriptors; [exact Hobjects|exact Hsource|exact Htarget| | | |exact Hwrite].
  - eapply program_typed_object_copy_alignment. eapply aggregate_object_typing; eauto.
  - eapply program_typed_object_copy_alignment. eapply aggregate_object_typing; eauto.
  - eapply program_aggregate_objects_nonoverlap; eauto.
Qed.

Print Assumptions program_typed_object_copy_alignment.
Print Assumptions program_aggregate_copy_ready.
