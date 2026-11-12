(* A finite universe for exact aggregate-path search. Nominal struct cycles
   and zero-sized array elements are allowed; no guessed recursion fuel or
   composite-rank assumption is used. Pointer pointees are not traversed. *)
Require Import List ZArith Lia AST Maps Ctypes Errors.
Require Import BeeTypes BeePL BeePL_object_paths.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint object_array_types (root : type) : list type :=
  root :: match root with Atype elem _ _ => object_array_types elem | _ => [] end.

Definition object_environment_types (env : bcomposite_env) : list type :=
  flat_map (fun entry => map type_bmember (co_members (snd entry))) (PTree.elements env).

Definition object_type_universe (env : bcomposite_env) (root : type) : list type :=
  flat_map object_array_types (root :: object_environment_types env).

Lemma object_array_types_root : forall root, In root (object_array_types root).
Proof. intro root; destruct root; simpl; auto. Qed.

Lemma object_array_types_element : forall root elem len attr,
  In (Atype elem len attr) (object_array_types root) ->
  In elem (object_array_types root).
Proof.
  induction root; intros elem len attr H; simpl in *;
    destruct H as [Heq | Hrest]; try discriminate; try contradiction.
  - inversion Heq; subst. right. apply object_array_types_root.
  - right. eapply IHroot; eauto.
Qed.

Lemma source_member_type_in_types : forall members field ty,
  source_member_type field members = OK ty -> In ty (map type_bmember members).
Proof.
  induction members as [|member rest IH]; intros field ty Hlookup; simpl in Hlookup; try discriminate.
  destruct member as [name memberTy|name sz sign attrs width pad]; simpl in *;
    (destruct (ident_eq field name); [inversion Hlookup; subst; auto | right; eapply IH; exact Hlookup]).
Qed.

Lemma object_environment_contains_field : forall env sid co field ty,
  env ! sid = Some co -> source_member_type field (co_members co) = OK ty ->
  In ty (object_environment_types env).
Proof.
  intros env sid co field ty Hco Hfield. unfold object_environment_types.
  apply in_flat_map. exists (sid, co). split.
  - apply PTree.elements_correct; exact Hco.
  - simpl. eapply source_member_type_in_types; eauto.
Qed.

Lemma object_universe_root : forall env root, In root (object_type_universe env root).
Proof.
  intros env root. unfold object_type_universe. apply in_flat_map.
  exists root; split; [simpl; auto|apply object_array_types_root].
Qed.

Lemma object_universe_member : forall env root sid co field ty,
  env ! sid = Some co -> source_member_type field (co_members co) = OK ty ->
  In ty (object_type_universe env root).
Proof.
  intros env root sid co field ty Hco Hfield. unfold object_type_universe.
  apply in_flat_map. exists ty; split.
  - right. eapply object_environment_contains_field; eauto.
  - apply object_array_types_root.
Qed.

Lemma object_universe_array_element : forall env root elem len attr,
  In (Atype elem len attr) (object_type_universe env root) ->
  In elem (object_type_universe env root).
Proof.
  intros env root elem len attr H. unfold object_type_universe in *.
  apply in_flat_map in H as [parent [Hin Harray]].
  apply in_flat_map. exists parent; split; [exact Hin|].
  eapply object_array_types_element; eauto.
Qed.

Theorem object_path_type_finite : forall env root offset ty,
  object_path env root offset ty -> In ty (object_type_universe env root).
Proof.
  intros env root offset ty Hpath. induction Hpath.
  - apply object_universe_root.
  - eapply object_universe_member; eauto.
  - eapply object_universe_array_element; eauto.
Qed.

Definition object_path_vertices (env : bcomposite_env) (root : type) : list (Z * type) :=
  flat_map (fun n => map (fun ty => (Z.of_nat n, ty)) (object_type_universe env root))
    (seq 0 (S (Z.to_nat (sizeof_type env root)))).

Theorem object_path_vertex_finite : forall env root offset ty,
  object_path env root offset ty -> In (offset, ty) (object_path_vertices env root).
Proof.
  intros env root offset ty Hpath.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hoffset [Hsize Hbound]].
  unfold object_path_vertices. apply in_flat_map. exists (Z.to_nat offset). split.
  - apply in_seq. split; [lia|].
    assert ((Z.to_nat offset <= Z.to_nat (sizeof_type env root))%nat).
    { apply Z2Nat.inj_le; lia. }
    lia.
  - apply in_map_iff. exists ty. split.
    + rewrite Z2Nat.id by exact Hoffset; reflexivity.
    + eapply object_path_type_finite; eauto.
Qed.

Theorem object_type_at_has_root_path : forall env Sigma block offset ty,
  object_type_at env Sigma block offset ty ->
  exists stored, Sigma ! block = Some stored /\
    object_path env (stored_object_type stored) offset ty.
Proof.
  intros env Sigma block offset ty Hobject. induction Hobject.
  - exists stored; split; [assumption|constructor; assumption].
  - destruct IHHobject as [stored [Hstored Hpath]]. exists stored; split; [exact Hstored|].
    eapply path_field; eauto.
  - destruct IHHobject as [stored [Hstored Hpath]]. exists stored; split; [exact Hstored|].
    eapply path_array_element; eauto.
Qed.

Theorem object_type_at_root_path_iff : forall env Sigma block stored offset ty,
  Sigma ! block = Some stored ->
  (object_type_at env Sigma block offset ty <->
   object_path env (stored_object_type stored) offset ty).
Proof.
  intros env Sigma block stored offset ty Hstored. split.
  - intro Hobject. destruct (object_type_at_has_root_path _ _ _ _ _ Hobject) as [other [Hother Hpath]].
    rewrite Hstored in Hother; inversion Hother; subst; exact Hpath.
  - intro Hpath. replace offset with (0 + offset) by lia.
    eapply object_path_typing; [exact Hpath|]. apply object_type_root with (stored := stored); [exact Hstored|].
    pose proof (object_path_bounds _ _ _ _ Hpath) as [Hoffset [Hsize Hbound]]; lia.
Qed.
Print Assumptions object_path_vertex_finite.
Print Assumptions object_type_at_root_path_iff.
