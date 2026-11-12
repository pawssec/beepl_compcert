(* Finite nested-array coverage. Arrays have no padding: the rejected offset 2
   is inside an element, not a padding byte. Pointer paths never dereference. *)
Require Import List ZArith Lia AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_aggregate_memory BeePL_soundness_memory.
Local Open Scope Z_scope.
Definition coverage_int : type := Vtype (Tint I32 Signed noattr).
Definition coverage_inner : type := Atype coverage_int 2 noattr.
Definition coverage_outer : type := Atype coverage_inner 2 noattr.

Lemma nested_array_paths : forall env delta ty,
  object_path env coverage_outer delta ty ->
  (ty = coverage_outer /\ delta = 0) \/
  (ty = coverage_inner /\ (delta = 0 \/ delta = 8)) \/
  (ty = coverage_int /\ (delta = 0 \/ delta = 4 \/ delta = 8 \/ delta = 12)).
Proof.
  intros env delta ty H. induction H.
  - left; auto.
  - destruct IHobject_path as [[Hty Hoff] | [[Hty Hoff] | [Hty Hoff]]]; discriminate Hty.
  - destruct IHobject_path as [[Hty Hoff] | [[Hty Hoff] | [Hty Hoff]]].
    + unfold coverage_outer in Hty. inversion Hty; subst.
      right; left. split; [reflexivity |]. change (0 + index * 8 = 0 \/ 0 + index * 8 = 8). lia.
    + unfold coverage_inner in Hty. inversion Hty; subst.
      right; right. split; [reflexivity |].
      change (base + index * 4 = 0 \/ base + index * 4 = 4 \/ base + index * 4 = 8 \/ base + index * 4 = 12). lia.
    + discriminate Hty.
Qed.

Definition four_array_cells (block : Values.block) : scalar_layout :=
  fun b ofs ty chunk => b = block /\ ty = coverage_int /\ chunk = BMint32 /\
    (ofs = Ptrofs.repr 0 \/ ofs = Ptrofs.repr 4 \/ ofs = Ptrofs.repr 8 \/ ofs = Ptrofs.repr 12).
Definition outer_array_object (block : Values.block) : aggregate_object_context :=
  fun b base ty => b = block /\ base = Ptrofs.zero /\ ty = coverage_outer.

Theorem four_cells_cover_nested_array : forall env block,
  initialized_object_coverage env (outer_array_object block) (four_array_cells block).
Proof.
  intros env block b base root [Hb [Hbase Hroot]] delta ty chunk [Hpath Hmode].
  subst b base root. destruct (nested_array_paths _ _ _ Hpath)
    as [[Hty Hoff] | [[Hty Hoff] | [Hty Hoff]]]; subst ty;
    try discriminate Hmode.
  exists BMint32. split.
  - unfold four_array_cells. rewrite Ptrofs.unsigned_zero.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    destruct Hoff as [-> | [-> | [-> | ->]]]; simpl; auto.
  - simpl in Hmode. inversion Hmode. reflexivity.
Qed.

Lemma second_inner_array_path : forall env, object_path env coverage_outer 8 coverage_inner.
Proof.
  intros. change 8 with (0 + 1 * sizeof_type env coverage_inner).
  eapply path_array_element with (len := 2) (attr := noattr).
  - constructor. change (0 <= 16). lia.
  - lia.
  - change (0 <= 8). lia.
Qed.

Theorem inner_array_at_eight_covered : forall env block,
  initialized_object_coverage env
    (add_aggregate_descriptor (outer_array_object block) block (Ptrofs.repr 8) coverage_inner)
    (four_array_cells block).
Proof.
  intros. eapply object_coverage_subobject_extension with
    (base := Ptrofs.zero) (root := coverage_outer) (delta := 8).
  - apply four_cells_cover_nested_array.
  - repeat split; reflexivity.
  - apply second_inner_array_path.
  - rewrite Ptrofs.unsigned_zero, Ptrofs.unsigned_repr; [reflexivity | vm_compute; split; congruence].
Qed.

Theorem nested_array_has_no_leaf_at_two_or_sixteen : forall env ty chunk delta,
  delta = 2 \/ delta = 16 -> ~ scalar_object_leaf env coverage_outer delta ty chunk.
Proof.
  intros env ty chunk delta Hbad [Hpath Hmode].
  destruct (nested_array_paths _ _ _ Hpath) as [[Hty Hoff] | [[Hty Hoff] | [Hty Hoff]]];
    subst ty; try discriminate Hmode; lia.
Qed.

Theorem pointer_paths_stop : forall env ptr delta ty,
  object_path env (Ptrtype ptr) delta ty -> delta = 0 /\ ty = Ptrtype ptr.
Proof.
  intros env ptr delta ty H. remember (Ptrtype ptr) as root eqn:Hroot.
  induction H; subst.
  - auto.
  - destruct IHobject_path as [_ Heq]. discriminate Heq.
  - destruct IHobject_path as [_ Heq]. discriminate Heq.
Qed.

Corollary nominal_pointer_does_not_expose_struct : forall env sid attr pointer_attr delta,
  ~ object_path env (Ptrtype (Reftype (Bstruct sid attr) pointer_attr)) delta (Stype sid attr).
Proof. intros env sid attr pointer_attr delta H. apply pointer_paths_stop in H. destruct H; discriminate. Qed.

Print Assumptions four_cells_cover_nested_array.
Print Assumptions inner_array_at_eight_covered.
Print Assumptions nominal_pointer_does_not_expose_struct.

Definition boolean_array_object (block : Values.block) : aggregate_object_context :=
  fun b base ty => b = block /\ base = Ptrofs.zero /\
    ty = Atype (Vtype Tbool) 1 noattr.
Definition canonical_boolean_cell (block : Values.block) : scalar_layout :=
  fun b ofs ty chunk => b = block /\ ofs = Ptrofs.zero /\
    ty = Vtype Tbool /\ chunk = BMbool.

Lemma boolean_array_paths : forall env delta ty,
  object_path env (Atype (Vtype Tbool) 1 noattr) delta ty ->
  delta = 0 /\ (ty = Atype (Vtype Tbool) 1 noattr \/ ty = Vtype Tbool).
Proof.
  intros env delta ty H. induction H.
  - auto.
  - destruct IHobject_path as [_ [Hty | Hty]]; discriminate Hty.
  - destruct IHobject_path as [Hbase [Hty | Hty]]; [|discriminate Hty].
    inversion Hty; subst. split; [change (0 + index * 1 = 0); lia | auto].
Qed.

Theorem canonical_bool_covers_chunk_aliases : forall env block,
  initialized_object_coverage env (boolean_array_object block) (canonical_boolean_cell block).
Proof.
  intros env block b base root [Hb [Hbase Hroot]] delta ty chunk [Hpath Hmode].
  subst b base root. destruct (boolean_array_paths _ _ _ Hpath) as [Hdelta [Hty | Hty]];
    subst delta ty; [discriminate Hmode |].
  exists BMbool. split.
  - unfold canonical_boolean_cell. rewrite Ptrofs.unsigned_zero.
    repeat split; reflexivity.
  - simpl in Hmode. inversion Hmode. reflexivity.
Qed.

Print Assumptions canonical_bool_covers_chunk_aliases.
