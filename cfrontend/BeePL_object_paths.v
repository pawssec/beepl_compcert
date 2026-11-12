(* Object paths stay within the allocated aggregate. A pointer is a scalar
   leaf; this relation never follows it into its pointed-to object. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL.
Local Open Scope Z_scope.

Inductive object_path (cenv : bcomposite_env) (root : type) : Z -> type -> Prop :=
| path_root :
    0 <= sizeof_type cenv root -> object_path cenv root 0 root
| path_field : forall base sid attr co field cty ty delta,
    object_path cenv root base (Stype sid attr) ->
    PTree.get sid cenv = Some co ->
    Ctyping.type_of_member attr field (bmembers_cmembers co.(co_members)) = OK cty ->
    source_member_type field co.(co_members) = OK ty ->
    field_offset (bcomposite_composite_env cenv) field
      (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
    0 <= delta -> 0 <= sizeof_type cenv ty ->
    delta + sizeof_type cenv ty <= sizeof_type cenv (Stype sid attr) ->
    object_path cenv root (base + delta) ty
| path_array_element : forall base ty len attr index,
    object_path cenv root base (Atype ty len attr) ->
    0 <= index < len -> 0 <= sizeof_type cenv ty ->
    object_path cenv root (base + index * sizeof_type cenv ty) ty.

Theorem object_path_bounds : forall cenv root offset ty,
  object_path cenv root offset ty ->
  0 <= offset /\ 0 <= sizeof_type cenv ty /\
    offset + sizeof_type cenv ty <= sizeof_type cenv root.
Proof.
  intros cenv root offset ty Hpath. induction Hpath.
  - repeat split; lia.
  - destruct IHHpath as [Hbase [Hparent Hbound]]. repeat split; lia.
  - destruct IHHpath as [Hbase [Hparent Hbound]].
    simpl in Hparent, Hbound. rewrite Z.max_r in Hparent, Hbound by lia.
    repeat split; nia.
Qed.

Theorem object_path_compose : forall cenv root middle delta leaf offset,
  object_path cenv root delta middle ->
  object_path cenv middle offset leaf ->
  object_path cenv root (delta + offset) leaf.
Proof.
  intros cenv root middle delta leaf offset Hfirst Hsecond.
  induction Hsecond.
  - rewrite Z.add_0_r. exact Hfirst.
  - replace (delta + (base + delta0)) with ((delta + base) + delta0) by lia.
    eapply path_field; eauto.
  - replace (delta + (base + index * sizeof_type cenv ty))
      with ((delta + base) + index * sizeof_type cenv ty) by lia.
    eapply path_array_element; eauto.
Qed.

Theorem object_path_typing : forall cenv root offset ty,
  object_path cenv root offset ty ->
  forall Sigma block base,
  object_type_at cenv Sigma block base root ->
  object_type_at cenv Sigma block (base + offset) ty.
Proof.
  intros cenv root offset ty Hpath. induction Hpath; intros Sigma block start Hobject.
  - rewrite Z.add_0_r. exact Hobject.
  - replace (start + (base + delta)) with ((start + base) + delta) by lia.
    eapply object_type_field; eauto.
  - replace (start + (base + index * sizeof_type cenv ty))
      with ((start + base) + index * sizeof_type cenv ty) by lia.
    eapply object_type_array_element; eauto.
Qed.

Lemma scalar_type_chunk_size : forall cenv ty cc,
  access_mode_type ty = By_value cc -> size_chunk cc = sizeof_type cenv ty.
Proof.
  intros cenv ty cc Hmode.
  destruct ty as [|pt|ptr|sid attr|elem len attr|args effects result variadic|];
    simpl in Hmode; try discriminate.
  - destruct pt as [|sz sign attr|sign attr]; try destruct sz; try destruct sign;
      simpl in Hmode; inversion Hmode; reflexivity.
  - unfold Mptr in Hmode. destruct Archi.ptr64 eqn:Harch; inversion Hmode;
      simpl; rewrite Harch; reflexivity.
Qed.

Definition scalar_object_leaf (cenv : bcomposite_env) (root : type)
    (delta : Z) (ty : type) (chunk : bmemory_chunk) : Prop :=
  object_path cenv root delta ty /\
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk).

Theorem scalar_object_leaf_bounds : forall cenv root delta ty chunk,
  scalar_object_leaf cenv root delta ty chunk ->
  0 <= delta /\ 0 <= sizeof_type cenv ty /\
    delta + size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type cenv root.
Proof.
  intros cenv root delta ty chunk [Hpath Hmode].
  rewrite (scalar_type_chunk_size cenv ty _ Hmode).
  eapply object_path_bounds; eauto.
Qed.

Print Assumptions object_path_bounds.
Print Assumptions object_path_compose.
Print Assumptions object_path_typing.
Print Assumptions scalar_type_chunk_size.
Print Assumptions scalar_object_leaf_bounds.
