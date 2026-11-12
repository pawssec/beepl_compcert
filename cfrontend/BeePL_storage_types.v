(* Necessary inline-storage conditions, checked over a finite visited graph.
   Pointers are leaves. Nominal cycles terminate through visited membership;
   layout consistency and actual aggregate initialization remain separate. *)
Require Import List Bool ZArith Lia Coqlib Integers AST Maps Ctypes Memdata.
Require Import BeeTypes BeePL BeePL_object_finiteness BeePL_object_decision.
Require Import BeePL_finite_reachability BeePL_worklist_reachability.
Import ListNotations.
Local Open Scope Z_scope.

Definition storage_successors (env : bcomposite_env) (ty : type) : list type :=
  match ty with
  | Atype elem _ _ => [elem]
  | Stype name _ => match PTree.get name env with
      | Some co => map type_bmember (co_members co) | None => [] end
  | _ => []
  end.

Lemma storage_successors_in_universe : forall env root parent child,
  In parent (object_type_universe env root) ->
  In child (storage_successors env parent) ->
  In child (object_type_universe env root).
Proof.
  intros env root parent child Hparent Hchild. destruct parent; simpl in Hchild;
    try contradiction.
  - destruct (PTree.get i env) as [co|] eqn:Hco; [|contradiction].
    unfold object_type_universe. apply in_flat_map. exists child. split.
    + right. unfold object_environment_types. apply in_flat_map.
      exists (i,co). split; [apply PTree.elements_correct; exact Hco|exact Hchild].
    + apply object_array_types_root.
  - destruct Hchild as [Heq|Hfalse]; [subst|contradiction].
    eapply object_universe_array_element; exact Hparent.
Qed.

Definition storage_reachable_types env root : list type :=
  fst (worklist_search object_type_eq_dec (storage_successors env)
    (length (object_type_universe env root)) [] [root]).

Lemma storage_reachable_types_spec : forall env root ty,
  In ty (storage_reachable_types env root) <->
  finite_walk (successor_edge object_type_eq_dec (storage_successors env)) root ty.
Proof.
  intros env root ty.
  pose proof (worklist_reach_correct object_type_eq_dec (storage_successors env)
    (object_type_universe env root) (length (object_type_universe env root)) root ty
    (storage_successors_in_universe env root) (object_universe_root env root)
    (Nat.le_refl _)) as H.
  unfold worklist_reach in H. fold (storage_reachable_types env root) in H.
  destruct (in_dec object_type_eq_dec ty (storage_reachable_types env root)); intuition discriminate.
Qed.

Definition storage_slot_bounds (env : bcomposite_env) (ty : type) : bool :=
  negb (type_is_volatile (transBeePL_type ty)) &&
  (0 <=? sizeof_type env ty) && (sizeof_type env ty <=? Ptrofs.max_unsigned).

Definition storage_slot_check (env : bcomposite_env) (ty : type) : bool :=
  storage_slot_bounds env ty &&
  match ty with
  | Ftype _ _ _ _ => false
  | Atype _ count _ => 0 <=? count
  | Stype name _ => match PTree.get name env with Some _ => true | None => false end
  | _ => true
  end.

Definition storage_type_check (env : bcomposite_env) (ty : type) : bool :=
  forallb (storage_slot_check env) (storage_reachable_types env ty).

Theorem storage_type_check_spec : forall env root,
  storage_type_check env root = true <->
  forall ty, finite_walk (successor_edge object_type_eq_dec (storage_successors env)) root ty ->
    storage_slot_check env ty = true.
Proof.
  intros. unfold storage_type_check. rewrite forallb_forall.
  split; intros H ty Hty; apply H; apply storage_reachable_types_spec; exact Hty.
Qed.

Lemma storage_type_root_checked : forall env ty,
  storage_type_check env ty = true -> storage_slot_check env ty = true.
Proof. intros env ty H. apply (proj1 (storage_type_check_spec env ty) H). constructor. Qed.

Lemma storage_type_nonvolatile : forall env ty,
  storage_type_check env ty = true -> type_is_volatile (transBeePL_type ty) = false.
Proof.
  intros env ty H. apply storage_type_root_checked in H.
  unfold storage_slot_check, storage_slot_bounds in H.
  repeat rewrite Bool.andb_true_iff in H. apply Bool.negb_true_iff. tauto.
Qed.

Lemma storage_type_size_bounds : forall env ty,
  storage_type_check env ty = true -> 0 <= sizeof_type env ty <= Ptrofs.max_unsigned.
Proof.
  intros env ty H. apply storage_type_root_checked in H.
  unfold storage_slot_check, storage_slot_bounds in H.
  repeat rewrite Bool.andb_true_iff in H. destruct H as [[[Hvol Hlo] Hhi] Hshape].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. auto.
Qed.

Lemma storage_type_successor : forall env parent child,
  storage_type_check env parent = true -> In child (storage_successors env parent) ->
  storage_type_check env child = true.
Proof.
  intros env parent child Hparent Hchild.
  apply (proj2 (storage_type_check_spec env child)). intros ty Hwalk.
  apply (proj1 (storage_type_check_spec env parent) Hparent).
  eapply finite_walk_cons; [apply successor_edge_spec; exact Hchild|exact Hwalk].
Qed.

Lemma array_storage_element_admissible : forall env elem count attr,
  storage_type_check env (Atype elem count attr) = true -> storage_type_check env elem = true.
Proof. intros. eapply storage_type_successor; [exact H|simpl; auto]. Qed.

Lemma array_storage_element_nonvolatile : forall env elem count attr,
  storage_type_check env (Atype elem count attr) = true ->
  type_is_volatile (transBeePL_type elem) = false.
Proof. intros. eapply storage_type_nonvolatile with (env := env). eapply array_storage_element_admissible; exact H. Qed.

Lemma storage_type_function_rejected : forall env args effects result variadic,
  storage_type_check env (Ftype args effects result variadic) = false.
Proof.
  intros. destruct (storage_type_check env (Ftype args effects result variadic)) eqn:H; [|reflexivity].
  apply storage_type_root_checked in H. unfold storage_slot_check in H.
  rewrite Bool.andb_false_r in H. discriminate.
Qed.

Lemma storage_type_function_array_rejected : forall env args effects result variadic count attr,
  storage_type_check env (Atype (Ftype args effects result variadic) count attr) = false.
Proof.
  intros. destruct (storage_type_check env (Atype (Ftype args effects result variadic) count attr)) eqn:H; [|reflexivity].
  apply array_storage_element_admissible in H. rewrite storage_type_function_rejected in H. discriminate.
Qed.

Lemma storage_type_complete_struct : forall env name attr,
  storage_type_check env (Stype name attr) = true -> exists co, PTree.get name env = Some co.
Proof.
  intros env name attr H. apply storage_type_root_checked in H.
  unfold storage_slot_check in H. destruct (PTree.get name env) eqn:Hco; eauto.
  rewrite Bool.andb_false_r in H. discriminate.
Qed.

Print Assumptions storage_type_check_spec.
Print Assumptions storage_type_nonvolatile.
Print Assumptions storage_type_size_bounds.
Print Assumptions array_storage_element_nonvolatile.

Example storage_unit_admitted : storage_type_check (PTree.empty bcomposite) Utype = true.
Proof. vm_compute. reflexivity. Qed.
Example storage_bytes_admitted : storage_type_check (PTree.empty bcomposite) Bytes = true.
Proof. vm_compute. reflexivity. Qed.
Example storage_reference_does_not_unfold_nominal :
  storage_type_check (PTree.empty bcomposite)
    (Ptrtype (Reftype (Bstruct 1%positive noattr) noattr)) = true.
Proof. vm_compute. reflexivity. Qed.
Example storage_nested_array_admitted :
  storage_type_check (PTree.empty bcomposite)
    (Atype (Atype (Vtype (Tint I32 Signed noattr)) 3 noattr) 2 noattr) = true.
Proof. vm_compute. reflexivity. Qed.
Example storage_array_of_bytes_admitted :
  storage_type_check (PTree.empty bcomposite) (Atype Bytes 2 noattr) = true.
Proof. vm_compute. reflexivity. Qed.
Example storage_incomplete_nominal_rejected :
  storage_type_check (PTree.empty bcomposite) (Stype 1%positive noattr) = false.
Proof. vm_compute. reflexivity. Qed.
Example storage_oversized_extent_rejected :
  storage_type_check (PTree.empty bcomposite)
    (Atype (Vtype (Tint I32 Signed noattr)) (Ptrofs.modulus + 1) noattr) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma storage_type_from_successors : forall env root,
  storage_slot_check env root = true ->
  (forall child, In child (storage_successors env root) -> storage_type_check env child = true) ->
  storage_type_check env root = true.
Proof.
  intros env root Hroot Hchildren. apply (proj2 (storage_type_check_spec env root)).
  intros ty Hwalk. inversion Hwalk; subst; [exact Hroot|].
  match goal with Hedge : successor_edge _ _ root ?child = true,
    Htail : finite_walk _ ?child ty |- _ =>
      apply successor_edge_spec in Hedge;
      exact (proj1 (storage_type_check_spec env child) (Hchildren child Hedge) ty Htail)
  end.
Qed.

Lemma storage_type_leaf_admissible : forall env ty,
  storage_successors env ty = [] -> storage_slot_check env ty = true ->
  storage_type_check env ty = true.
Proof.
  intros. apply storage_type_from_successors; [assumption|].
  intros child Hin. rewrite H in Hin. contradiction.
Qed.

Lemma storage_array_admissible : forall env elem count attr,
  storage_slot_bounds env (Atype elem count attr) = true ->
  0 <= count -> storage_type_check env elem = true ->
  storage_type_check env (Atype elem count attr) = true.
Proof.
  intros env elem count attr Hbounds Hcount Helem.
  apply storage_type_from_successors.
  - unfold storage_slot_check. rewrite Hbounds. simpl. apply Z.leb_le. exact Hcount.
  - intros child [Heq|Hfalse]; [subst; exact Helem|contradiction].
Qed.

Lemma storage_unit_admissible : forall env, storage_type_check env Utype = true.
Proof. intros. apply storage_type_leaf_admissible; [reflexivity|]. vm_compute; reflexivity. Qed.

Lemma storage_type_member_admissible : forall env name attr co field ty,
  storage_type_check env (Stype name attr) = true ->
  PTree.get name env = Some co ->
  source_member_type field (co_members co) = Errors.OK ty ->
  storage_type_check env ty = true.
Proof.
  intros env name attr co field ty Hroot Hco Hmember.
  eapply storage_type_successor; [exact Hroot|].
  simpl. rewrite Hco. eapply source_member_type_in_types; exact Hmember.
Qed.

Lemma storage_type_member_nonvolatile : forall env name attr co field ty,
  storage_type_check env (Stype name attr) = true ->
  PTree.get name env = Some co ->
  source_member_type field (co_members co) = Errors.OK ty ->
  type_is_volatile (transBeePL_type ty) = false.
Proof.
  intros. eapply storage_type_nonvolatile with (env := env).
  eapply storage_type_member_admissible; eauto.
Qed.

Print Assumptions storage_type_member_admissible.
Print Assumptions storage_type_member_nonvolatile.

Definition storage_align8 : attr := {| attr_volatile := false; attr_alignas := Some 3%N |}.

Example storage_accepts_nested_unpadded_annotation :
  storage_type_check (PTree.empty bcomposite)
    (Atype (Atype (Vtype (Tint I8 Unsigned noattr)) 1 storage_align8) 8 noattr) = true.
Proof. vm_compute; reflexivity. Qed.

Example annotated_byte_array_copy_alignment : forall env,
  Ctypes.alignof_blockcopy (bcomposite_composite_env env)
    (transBeePL_type (Atype (Vtype (Tint I8 Unsigned noattr)) 1 storage_align8)) = 1.
Proof. reflexivity. Qed.

Example storage_retains_erased_unit_array_alignment :
  storage_type_check (PTree.empty bcomposite)
    (Atype (Atype Utype 3 storage_align8) 2 storage_align8) = true.
Proof. vm_compute; reflexivity. Qed.

(* Operational alignment ignores use-site over-alignment annotations. It is
   intrinsic for Bytes and composes through arrays even in an empty env. *)
Fixpoint storage_copy_alignment (env : bcomposite_env) (ty : type) : Z :=
  match ty with
  | Utype => 1
  | Vtype pt => align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt))
  | Ptrtype _ | Bytes => align_chunk Mptr
  | Stype id _ => match PTree.get id env with
      | Some co => Z.min 8 co.(co_alignof) | None => 1 end
  | Atype elem _ _ => storage_copy_alignment env elem
  | Ftype _ _ _ _ => 1
  end.

Lemma source_composite_copy_stride : forall co : bcomposite,
  (Z.min 8 co.(co_alignof) | co.(co_sizeof)).
Proof.
  intros co. eapply Z.divide_trans; [|apply co_sizeof_alignof].
  destruct (co_alignof_two_p co) as [n Heq]. rewrite Heq.
  destruct n; [apply Z.divide_refl|].
  destruct n; [apply Z.divide_refl|].
  destruct n; [apply Z.divide_refl|].
  apply Z.min_case; [|apply Z.divide_refl].
  exists (two_p (Z.of_nat n)). change 8 with (two_p 3).
  rewrite <- two_p_is_exp by lia. rewrite two_power_nat_two_p.
  rewrite !Nat2Z.inj_succ. f_equal; lia.
Qed.

Theorem source_storage_copy_stride : forall env ty,
  (storage_copy_alignment env ty | sizeof_type env ty).
Proof.
  intros env ty. induction ty; simpl.
  - apply Z.divide_0_r.
  - destruct p as [|sz sg attr|sg attr]; try destruct sz; try destruct sg;
      first [apply Z.divide_refl|exists 1; reflexivity].
  - unfold Mptr; destruct Archi.ptr64; apply Z.divide_refl.
  - destruct (PTree.get i env) as [co|]; [apply source_composite_copy_stride|apply Z.divide_0_r].
  - destruct IHty as [factor Hfactor]. exists (factor * Z.max 0 z). nia.
  - apply Z.divide_refl.
  - unfold Mptr; destruct Archi.ptr64; exists 2; reflexivity.
Qed.

Print Assumptions source_storage_copy_stride.
