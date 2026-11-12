(* Primitive structure copy plans follow from actual allocation freshness and
   validated source field layouts, not assumptions on copied memory. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_copy_cells.
Require Import BeePL_initialization_proofs BeePL_layout_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma extend_field_layout_origin : forall fs layout block base b ofs ty chunk,
  extend_field_layout layout block base fs b ofs ty chunk ->
  layout b ofs ty chunk \/ exists f, In f fs /\ b = block /\
    ofs = planned_address base f /\ ty = Vtype (planned_type f) /\ chunk = planned_chunk f.
Proof.
  induction fs as [|head fs IH]; intros layout block base b ofs ty chunk H; simpl in H.
  - left; exact H.
  - destruct (IH _ _ _ _ _ _ _ H) as [[Hold | Hhead] | [f [Hin Hfield]]].
    + left; exact Hold.
    + right. exists head. split; [left; reflexivity | exact Hhead].
    + right. exists f. split; [right; exact Hin | exact Hfield].
Qed.

Theorem fresh_field_copy_plan : forall cenv Sigma before m allocated src dst count fs,
  Mem.alloc m 0 count = (allocated, dst) ->
  typed_memory_layout cenv Sigma before m ->
  (forall f, In f fs -> before src (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f)) ->
  (forall f, In f fs -> 0 <= planned_start Ptrofs.zero f /\
    planned_end Ptrofs.zero f <= count /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f)) ->
  scalar_copy_plan before (extend_field_layout before dst Ptrofs.zero fs)
    src 0 dst 0 count.
Proof.
  intros cenv Sigma before m allocated src dst count fs Halloc Htyped Hsource Hbounds
    b ofs ty chunk Hentry.
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hentry)
    as [Hold | [f [Hin [Hb [Hofs [Hty Hchunk]]]]]].
  - left. split; [exact Hold |]. left. intro Heq. subst b.
    eapply (Mem.fresh_block_alloc _ _ _ _ _ Halloc).
    eapply initialized_scalar_valid_block.
    eapply typed_memory_cell_erasure. apply Htyped; exact Hold.
  - subst b ofs ty chunk. right. split; [reflexivity |].
    exists (planned_start Ptrofs.zero f), (planned_address Ptrofs.zero f).
    destruct (Hbounds f Hin) as [Hlo [Hhi Halign]].
    split; [apply Hsource; exact Hin |]. split; [exact Hlo |].
    split; [exact Hhi |]. split; [unfold planned_start; lia |].
    split; [unfold planned_start; lia | exact Halign].
Qed.

Theorem primitive_structure_fresh_copy_plan :
  forall ge Sigma before m allocated src dst sid co fs,
  PTree.get sid ge.(genv_cenv) = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env ge.(genv_cenv)) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_plan_valid ge sid f) ->
  (forall f, In f fs -> field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
    OK (transBeePL_type (Vtype (planned_type f)))) ->
  (forall f, In f fs -> (align_chunk (transl_bchunk_cchunk (planned_chunk f)) |
    Ctypes.alignof (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type (Vtype (planned_type f))))) ->
  NoDup (map planned_field fs) ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Stype sid noattr)) = (allocated, dst) ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  (forall f, In f fs -> before src (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f)) ->
  scalar_copy_plan before (extend_field_layout before dst Ptrofs.zero fs)
    src 0 dst 0 (sizeof_type ge.(genv_cenv) (Stype sid noattr)) /\
  field_plans_separated Ptrofs.zero fs.
Proof.
  intros ge Sigma before m allocated src dst sid co fs Hco Hconsistent Hstruct
    Hsize Hvalid Htypes Halign Hdistinct Halloc Htyped Hsource.
  split.
  - eapply fresh_field_copy_plan; eauto.
    eapply primitive_field_plan_bounds; eauto.
  - eapply primitive_field_plan_separation; eauto.
Qed.

Print Assumptions primitive_structure_fresh_copy_plan.
