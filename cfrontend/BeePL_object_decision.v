(* Exact decidable object ancestry, using the proved finite graph domain.
   This checks typing evidence, not live-memory permissions or contents. *)
Require Import List Bool ZArith Lia AST Maps Ctypes Errors.
Require Import BeeTypes BeePL BeePL_type_equality BeePL_object_paths BeePL_object_finiteness BeePL_object_edges BeePL_finite_reachability BeePL_worklist_reachability.
Import ListNotations.
Local Open Scope Z_scope.

Lemma object_eq_primitive_refl : forall pt, eq_primitive_type pt pt = true.
Proof.
  destruct pt; simpl;
    repeat match goal with
    | |- context [Ctyping.intsize_eq ?x ?x] => destruct (Ctyping.intsize_eq x x); [|contradiction]
    | |- context [Ctyping.signedness_eq ?x ?x] => destruct (Ctyping.signedness_eq x x); [|contradiction]
    | |- context [attr_eq ?x ?x] => destruct (attr_eq x x); [|contradiction]
    end; reflexivity.
Qed.
Lemma object_eq_basic_refl : forall bt, eq_basic_type bt bt = true.
Proof.
  destruct bt; simpl; try rewrite object_eq_primitive_refl; try rewrite Pos.eqb_refl;
    try rewrite Z.eqb_refl; try (destruct (attr_eq a a); [|contradiction]); reflexivity.
Qed.
Lemma object_eq_effect_refl : forall ef, eq_effect ef ef = true.
Proof. induction ef as [|label rest IH]; simpl; [reflexivity|]; rewrite IH; destruct label; reflexivity. Qed.

Fixpoint object_eq_type_refl (ty : type) : eq_type ty ty = true
with object_eq_ptr_refl (pt : ptr_type) : eq_ptr_type pt pt = true.
Proof.
  - destruct ty; simpl; try reflexivity.
    + apply object_eq_primitive_refl.
    + apply object_eq_ptr_refl.
    + rewrite Pos.eqb_refl. destruct (attr_eq a a); [reflexivity|contradiction].
    + rewrite object_eq_type_refl, Z.eqb_refl. destruct (attr_eq a a); [reflexivity|contradiction].
    + assert (Hargs : eq_types eq_type l l = true).
      { induction l; simpl; [reflexivity|]. rewrite object_eq_type_refl, IHl; reflexivity. }
      rewrite Hargs, object_eq_effect_refl, object_eq_type_refl. destruct b; reflexivity.
  - destruct pt; simpl.
    + rewrite object_eq_basic_refl. destruct (attr_eq a a); [reflexivity|contradiction].
    + apply object_eq_ptr_refl.
    + assert (Hargs : eq_types eq_type l l = true).
      { induction l; simpl; [reflexivity|]. rewrite object_eq_type_refl, IHl; reflexivity. }
      rewrite Hargs, object_eq_effect_refl, object_eq_type_refl. destruct b; reflexivity.
Defined.

Definition object_type_eq_dec (x y : type) : {x = y} + {x <> y}.
Proof.
  destruct (eq_type x y) eqn:H.
  - left. apply eq_type_sound; exact H.
  - right. intro Heq; subst. rewrite object_eq_type_refl in H; discriminate.
Defined.
Definition object_vertex_eq_dec (x y : Z * type) : {x = y} + {x <> y}.
Proof. decide equality; [apply object_type_eq_dec|apply Z.eq_dec]. Defined.

(* This membership check avoids constructing every byte-offset/type pair. *)
Definition object_vertex_member (env : bcomposite_env) (root : type) (state : Z * type) : bool :=
  let '(offset, ty) := state in
  (0 <=? offset) && Nat.ltb (Z.to_nat offset) (S (Z.to_nat (sizeof_type env root))) &&
  existsb (eq_type ty) (object_type_universe env root).

Lemma object_vertex_membership : forall env root offset ty,
  In (offset, ty) (object_path_vertices env root) <->
  0 <= offset /\ (Z.to_nat offset < S (Z.to_nat (sizeof_type env root)))%nat /\
  In ty (object_type_universe env root).
Proof.
  intros env root offset ty. unfold object_path_vertices. split.
  - intro H. apply in_flat_map in H as [index [Hindex Hmapped]].
    apply in_map_iff in Hmapped as [element [Heq Htype]].
    inversion Heq; subst. apply in_seq in Hindex.
    rewrite Nat2Z.id. repeat split; try lia; assumption.
  - intros [Hoffset [Hindex Htype]]. apply in_flat_map. exists (Z.to_nat offset). split.
    + apply in_seq; lia.
    + apply in_map_iff. exists ty. rewrite Z2Nat.id by assumption. auto.
Qed.

Lemma object_vertex_member_spec : forall env root state,
  object_vertex_member env root state = true <-> In state (object_path_vertices env root).
Proof.
  intros env root [offset ty]. unfold object_vertex_member.
  rewrite !andb_true_iff, Z.leb_le, Nat.ltb_lt, object_vertex_membership.
  split.
  - intros [[Hoffset Hindex] Htype]. apply existsb_exists in Htype as [other [Hin Heq]].
    apply eq_type_sound in Heq; subst; auto.
  - intros [Hoffset [Hindex Htype]]. split; [auto|]. apply existsb_exists.
    exists ty; split; [exact Htype|apply object_eq_type_refl].
Qed.

Definition bounded_object_successors (env : bcomposite_env) (root : type) (state : Z * type) :=
  filter (object_vertex_member env root) (object_successors env state).

Lemma bounded_object_successors_spec : forall env root from to,
  In to (bounded_object_successors env root from) <->
  In to (object_path_vertices env root) /\ object_edge env from to.
Proof.
  intros env root from to. unfold bounded_object_successors. rewrite filter_In.
  rewrite object_vertex_member_spec. split.
  - intros [Hedge Hin]; split; [exact Hin|apply object_successors_sound; exact Hedge].
  - intros [Hin Hedge]; split; [apply object_successors_complete; exact Hedge|exact Hin].
Qed.

Definition object_vertex_bound (env : bcomposite_env) (root : type) : nat :=
  S (Z.to_nat (sizeof_type env root)) * length (object_type_universe env root).

Lemma object_vertex_bound_exact : forall env root,
  length (object_path_vertices env root) = object_vertex_bound env root.
Proof.
  intros env root. unfold object_path_vertices, object_vertex_bound.
  assert (Hlength : forall indices,
    length (flat_map (fun index => map (fun ty => (Z.of_nat index, ty)) (object_type_universe env root)) indices) =
    (length indices * length (object_type_universe env root))%nat).
  { induction indices; simpl; [reflexivity|]. rewrite app_length, map_length, IHindices; lia. }
  rewrite Hlength, seq_length; reflexivity.
Qed.

Definition bounded_object_edge (env : bcomposite_env) (root : type) :=
  successor_edge object_vertex_eq_dec (bounded_object_successors env root).

Lemma bounded_object_edge_spec : forall env root from to,
  bounded_object_edge env root from to = true <->
  In to (object_path_vertices env root) /\ object_edge env from to.
Proof.
  intros. unfold bounded_object_edge. rewrite successor_edge_spec.
  apply bounded_object_successors_spec.
Qed.

Lemma bounded_object_walk_path : forall env root from to,
  finite_walk (bounded_object_edge env root) from to ->
  object_path env root (fst from) (snd from) -> object_path env root (fst to) (snd to).
Proof.
  intros env root from to Hwalk; induction Hwalk; intro Hpath; [exact Hpath|].
  apply IHHwalk. apply bounded_object_edge_spec in H as [_ Hedge].
  eapply object_edge_extends_path; eauto.
Qed.

Lemma object_path_bounded_walk : forall env root offset ty,
  object_path env root offset ty ->
  finite_walk (bounded_object_edge env root) (0, root) (offset, ty).
Proof.
  intros env root offset ty Hpath; induction Hpath.
  - constructor.
  - eapply finite_walk_trans; [exact IHHpath|]. eapply finite_walk_cons; [|constructor].
    apply bounded_object_edge_spec. split.
    + eapply object_path_vertex_finite. eapply path_field; eauto.
    + eapply object_edge_field; eauto.
  - eapply finite_walk_trans; [exact IHHpath|]. eapply finite_walk_cons; [|constructor].
    apply bounded_object_edge_spec. split.
    + eapply object_path_vertex_finite. eapply path_array_element; eauto.
    + apply object_edge_array; assumption.
Qed.

Definition object_path_check (env : bcomposite_env) (root : type) (offset : Z) (ty : type) : bool :=
  (0 <=? sizeof_type env root) &&
  worklist_reach object_vertex_eq_dec (bounded_object_successors env root)
    (object_vertex_bound env root) (0, root) (offset, ty).

Theorem object_path_check_spec : forall env root offset ty,
  object_path_check env root offset ty = true <-> object_path env root offset ty.
Proof.
  intros env root offset ty. unfold object_path_check. rewrite andb_true_iff. split.
  - intros [Hsize Hreach]. apply Z.leb_le in Hsize.
    apply worklist_reach_correct with (universe := object_path_vertices env root) in Hreach.
    + eapply bounded_object_walk_path with (from := (0, root)) (to := (offset, ty)); [exact Hreach|simpl; constructor; exact Hsize].
    + intros x y Hx Hedge. apply bounded_object_successors_spec in Hedge; tauto.
    + apply object_path_vertex_finite. constructor; exact Hsize.
    + rewrite object_vertex_bound_exact; lia.
  - intro Hpath. pose proof (object_path_bounds _ _ _ _ Hpath) as [Hoffset [Hsize Hbound]].
    assert (Hroot : 0 <= sizeof_type env root) by lia.
    split; [apply Z.leb_le; exact Hroot|].
    apply worklist_reach_correct with (universe := object_path_vertices env root).
    + intros x y Hx Hedge. apply bounded_object_successors_spec in Hedge; tauto.
    + apply object_path_vertex_finite. constructor; exact Hroot.
    + rewrite object_vertex_bound_exact; lia.
    + apply object_path_bounded_walk; exact Hpath.
Qed.

Definition object_type_at_check (env : bcomposite_env) (Sigma : store_context)
    (block : Values.block) (offset : Z) (ty : type) : bool :=
  match Sigma ! block with
  | Some stored => object_path_check env (stored_object_type stored) offset ty
  | None => false
  end.

Theorem object_type_at_check_spec : forall env Sigma block offset ty,
  object_type_at_check env Sigma block offset ty = true <-> object_type_at env Sigma block offset ty.
Proof.
  intros env Sigma block offset ty. unfold object_type_at_check.
  destruct (Sigma ! block) as [stored|] eqn:Hstored.
  - rewrite object_path_check_spec. symmetry. apply object_type_at_root_path_iff; exact Hstored.
  - split; [discriminate|]. intro Hobject.
    destruct (object_type_at_has_root_path _ _ _ _ _ Hobject) as [stored [Hlookup _]].
    rewrite Hstored in Hlookup; discriminate.
Qed.

Definition object_type_at_decidable env Sigma block offset ty :
  {object_type_at env Sigma block offset ty} + {~ object_type_at env Sigma block offset ty}.
Proof.
  destruct (object_type_at_check env Sigma block offset ty) eqn:Hcheck.
  - left. apply object_type_at_check_spec; exact Hcheck.
  - right. intro Hobject. apply object_type_at_check_spec in Hobject. congruence.
Defined.
Print Assumptions object_path_check_spec.
Print Assumptions object_type_at_check_spec.
Print Assumptions object_type_at_decidable.

Definition object_decision_test_int := Vtype (Tint I32 Signed noattr).
Definition object_decision_test_inner := Atype object_decision_test_int 2 noattr.
Definition object_decision_test_outer := Atype object_decision_test_inner 2 noattr.
Example object_decision_nested_array_base_eight :
  object_path_check (PTree.empty _) object_decision_test_outer 8 object_decision_test_inner = true.
Proof. vm_compute; reflexivity. Qed.
Example object_decision_nested_scalar_offset_twelve :
  object_path_check (PTree.empty _) object_decision_test_outer 12 object_decision_test_int = true.
Proof. vm_compute; reflexivity. Qed.
Example object_decision_rejects_interior_gap :
  object_path_check (PTree.empty _) object_decision_test_outer 2 object_decision_test_int = false.
Proof. vm_compute; reflexivity. Qed.
Example object_decision_rejects_out_of_bounds :
  object_path_check (PTree.empty _) object_decision_test_outer 16 object_decision_test_int = false.
Proof. vm_compute; reflexivity. Qed.
(* The billion logical elements share one zero-sized object state. Execution
   visits only the root and unit element; it does not enumerate the indices. *)
Example object_decision_large_unit_array :
  object_path_check (PTree.empty _) (Atype Utype 1000000000 noattr) 0 Utype = true.
Proof. vm_compute; reflexivity. Qed.
Example object_decision_does_not_follow_pointer :
  object_path_check (PTree.empty _) (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))
    0 object_decision_test_int = false.
Proof. vm_compute; reflexivity. Qed.
