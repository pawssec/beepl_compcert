(* Exact finite successors for object paths. Field lookup keeps all existing
   Full/size checks; zero-sized arrays produce one successor rather than
   enumerating arbitrarily many identical zero-offset elements. *)
Require Import List Bool ZArith Lia AST Maps Ctypes Errors.
Require Import BeeTypes BeePL BeePL_object_paths BeePL_object_finiteness.
Import ListNotations.
Local Open Scope Z_scope.

Definition object_member_name (member : bmember) : ident :=
  match member with Member_plain name _ | Member_bitfield name _ _ _ _ _ => name end.

Definition object_field_successors (env : bcomposite_env) (base : Z)
    (sid : ident) (attr : attr) (co : bcomposite) (field : ident) : list (Z * type) :=
  match Ctyping.type_of_member attr field (bmembers_cmembers (co_members co)),
        source_member_type field (co_members co),
        field_offset (bcomposite_composite_env env) field (bmembers_cmembers (co_members co)) with
  | OK _, OK ty, OK (delta, Full) =>
      if (0 <=? delta) && (0 <=? sizeof_type env ty) &&
         (delta + sizeof_type env ty <=? sizeof_type env (Stype sid attr))
      then [(base + delta, ty)] else []
  | _, _, _ => []
  end.

Definition object_successors (env : bcomposite_env) (state : Z * type) : list (Z * type) :=
  let '(base, ty) := state in
  match ty with
  | Stype sid attr =>
      match env ! sid with
      | Some co => flat_map (fun member => object_field_successors env base sid attr co (object_member_name member)) (co_members co)
      | None => []
      end
  | Atype elem len attr =>
      if (0 <=? sizeof_type env elem) then
        if (sizeof_type env elem =? 0) then
          if (0 <? len) then [(base, elem)] else []
        else map (fun index => (base + Z.of_nat index * sizeof_type env elem, elem))
          (seq 0 (Z.to_nat len))
      else []
  | _ => []
  end.

Inductive object_edge (env : bcomposite_env) : (Z * type) -> (Z * type) -> Prop :=
| object_edge_field : forall base sid attr co field cty ty delta,
    env ! sid = Some co ->
    Ctyping.type_of_member attr field (bmembers_cmembers (co_members co)) = OK cty ->
    source_member_type field (co_members co) = OK ty ->
    field_offset (bcomposite_composite_env env) field (bmembers_cmembers (co_members co)) = OK (delta, Full) ->
    0 <= delta -> 0 <= sizeof_type env ty ->
    delta + sizeof_type env ty <= sizeof_type env (Stype sid attr) ->
    object_edge env (base, Stype sid attr) (base + delta, ty)
| object_edge_array : forall base elem len attr index,
    0 <= index < len -> 0 <= sizeof_type env elem ->
    object_edge env (base, Atype elem len attr) (base + index * sizeof_type env elem, elem).

Lemma source_member_type_has_name : forall members field ty,
  source_member_type field members = OK ty ->
  exists member, In member members /\ object_member_name member = field.
Proof.
  induction members as [|member rest IH]; intros field ty H; simpl in H; try discriminate.
  destruct member as [name memberTy|name sz sign attrs width pad]; simpl in *;
    (destruct (ident_eq field name) as [Heq|Hneq];
     [ subst field; eexists; split; [left; reflexivity|reflexivity]
     | destruct (IH _ _ H) as [member [Hin Hname]]; exists member; split; [right; exact Hin|exact Hname] ]).
Qed.

Lemma object_field_successors_sound : forall env base sid attr co field state,
  env ! sid = Some co ->
  In state (object_field_successors env base sid attr co field) ->
  object_edge env (base, Stype sid attr) state.
Proof.
  intros env base sid attr co field state Hco Hin. unfold object_field_successors in Hin.
  destruct (Ctyping.type_of_member attr field (bmembers_cmembers (co_members co))) as [cty|err] eqn:Hct; try contradiction.
  destruct (source_member_type field (co_members co)) as [ty|err] eqn:Hty; try contradiction.
  destruct (field_offset (bcomposite_composite_env env) field (bmembers_cmembers (co_members co))) as [[delta bits]|err] eqn:Hoffset; try contradiction.
  destruct bits; try contradiction.
  destruct ((0 <=? delta) && (0 <=? sizeof_type env ty) &&
    (delta + sizeof_type env ty <=? sizeof_type env (Stype sid attr))) eqn:Hguard; try contradiction.
  simpl in Hin. destruct Hin as [Heq|Hfalse]; [subst state|contradiction].
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
  eapply object_edge_field; eauto.
Qed.

Lemma object_field_successors_complete : forall env base sid attr co field cty ty delta,
  Ctyping.type_of_member attr field (bmembers_cmembers (co_members co)) = OK cty ->
  source_member_type field (co_members co) = OK ty ->
  field_offset (bcomposite_composite_env env) field (bmembers_cmembers (co_members co)) = OK (delta, Full) ->
  0 <= delta -> 0 <= sizeof_type env ty ->
  delta + sizeof_type env ty <= sizeof_type env (Stype sid attr) ->
  In (base + delta, ty) (object_field_successors env base sid attr co field).
Proof.
  intros env base sid attr co field cty ty delta Hct Hty Hoffset Hd Hsize Hbound.
  unfold object_field_successors. rewrite Hct, Hty, Hoffset.
  assert (Hguard : (0 <=? delta) && (0 <=? sizeof_type env ty) &&
    (delta + sizeof_type env ty <=? sizeof_type env (Stype sid attr)) = true).
  { apply andb_true_iff; split; [apply andb_true_iff; split|]; apply Z.leb_le; assumption. }
  rewrite Hguard; simpl; auto.
Qed.

Lemma nat_index_range : forall index len,
  In index (seq 0 (Z.to_nat len)) -> 0 <= Z.of_nat index < len.
Proof.
  intros index len Hin. apply in_seq in Hin.
  destruct (Z_le_gt_dec 0 len) as [Hlen|Hnegative].
  - assert (Hconvert := Z2Nat.id len Hlen).
    split; [lia|]. destruct Hin as [Hlo Hhi]. apply Nat2Z.inj_lt in Hhi. lia.
  - assert (Hnat : Z.to_nat len = 0%nat) by (destruct len; simpl in *; lia).
    rewrite Hnat in Hin; lia.
Qed.

Lemma object_successors_sound : forall env from to,
  In to (object_successors env from) -> object_edge env from to.
Proof.
  intros env [base ty] to Hin. destruct ty as [|prim|pt|sid attr|elem len attr|params eff rt va|]; simpl in Hin; try contradiction.
  - destruct (env ! sid) as [co|] eqn:Hco; try contradiction.
    apply in_flat_map in Hin as [member [Hmember Hedge]].
    eapply object_field_successors_sound; eauto.
  - destruct (0 <=? sizeof_type env elem) eqn:Hsize; try contradiction.
    apply Z.leb_le in Hsize.
    destruct (sizeof_type env elem =? 0) eqn:Hzero.
    + destruct (0 <? len) eqn:Hlen; try contradiction.
      apply Z.ltb_lt in Hlen. apply Z.eqb_eq in Hzero.
      destruct Hin as [Heq|Hfalse]; [subst to|contradiction].
      replace base with (base + 0 * sizeof_type env elem) at 2 by lia.
      apply object_edge_array; lia.
    + apply in_map_iff in Hin as [index [Heq Hindex]]. subst to.
      apply object_edge_array; [apply nat_index_range; exact Hindex|exact Hsize].
Qed.

Lemma object_successors_complete : forall env from to,
  object_edge env from to -> In to (object_successors env from).
Proof.
  intros env from to Hedge. inversion Hedge; subst; simpl.
  - rewrite H. apply in_flat_map.
    destruct (source_member_type_has_name _ _ _ H1) as [member [Hmember Hname]].
    exists member; split; [exact Hmember|]. rewrite Hname.
    eapply object_field_successors_complete; eauto.
  - assert (Hsize : (0 <=? sizeof_type env elem) = true) by (apply Z.leb_le; assumption).
    rewrite Hsize. destruct (sizeof_type env elem =? 0) eqn:Hzero.
    + apply Z.eqb_eq in Hzero. assert (Hlen : (0 <? len) = true) by (apply Z.ltb_lt; lia).
      rewrite Hlen, Hzero. simpl; left; f_equal; lia.
    + apply in_map_iff. exists (Z.to_nat index). split.
      * rewrite Z2Nat.id by lia; reflexivity.
      * apply in_seq. split; [lia|]. apply Z2Nat.inj_lt; lia.
Qed.

Lemma object_edge_extends_path : forall env root from to,
  object_path env root (fst from) (snd from) -> object_edge env from to ->
  object_path env root (fst to) (snd to).
Proof. intros env root from to Hpath Hedge; inversion Hedge; subst; simpl in *; eauto using path_field, path_array_element. Qed.

Print Assumptions object_successors_sound.
Print Assumptions object_successors_complete.
