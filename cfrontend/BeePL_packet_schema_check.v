(* Executable packet schema validation, independent of declarative typing.
   Storage checks apply to the complete header, including unbound fields. *)
Require Import List Bool ZArith AST Maps Ctypes BeeTypes BeePL BeePL_packet.
Require Import BeePL_storage_types BeePL_type_equality.
Import ListNotations.

Definition packet_plain_primitive_check (member : bmember) : bool :=
  match member with Member_plain _ (Vtype _) => true | _ => false end.

Definition packet_binding_check (members : list bmember) (field : ident * type) : bool :=
  match snd field, packet_member_type (fst field) members with
  | Vtype expected, Some (Vtype actual) => eq_primitive_type expected actual
  | _, _ => false
  end.

Definition packet_schema_check (env : bcomposite_env) (sid : ident)
    (fields : list (ident * type)) : bool :=
  match PTree.get sid env with
  | Some co =>
      match co_su co with
      | Struct => forallb packet_plain_primitive_check (co_members co) &&
          forallb (packet_binding_check (co_members co)) fields &&
          storage_type_check env (Stype sid noattr)
      | Union => false
      end
  | None => false
  end.

Definition storage_safe_packet_schema (env : bcomposite_env) (sid : ident)
    (fields : list (ident * type)) : Prop :=
  exists co, PTree.get sid env = Some co /\ co_su co = Struct /\
    Forall (fun member => exists name pt, member = Member_plain name (Vtype pt)) (co_members co) /\
    Forall (fun field => exists pt, snd field = Vtype pt /\
      packet_member_type (fst field) (co_members co) = Some (Vtype pt)) fields /\
    storage_type_check env (Stype sid noattr) = true.

Lemma packet_primitive_eq_refl : forall pt, eq_primitive_type pt pt = true.
Proof.
  destruct pt; simpl; repeat match goal with
    | |- context [Ctyping.intsize_eq ?x ?x] => destruct (Ctyping.intsize_eq x x); [|contradiction]
    | |- context [Ctyping.signedness_eq ?x ?x] => destruct (Ctyping.signedness_eq x x); [|contradiction]
    | |- context [attr_eq ?x ?x] => destruct (attr_eq x x); [|contradiction]
    end; reflexivity.
Qed.

Lemma packet_plain_primitive_check_spec : forall member,
  packet_plain_primitive_check member = true <->
  exists name pt, member = Member_plain name (Vtype pt).
Proof.
  intros member. split.
  - destruct member as [name ty|]; [destruct ty|]; simpl; try discriminate.
    intros; eauto.
  - intros [name [pt ->]]; reflexivity.
Qed.

Lemma packet_binding_check_spec : forall members field,
  packet_binding_check members field = true <->
  exists pt, snd field = Vtype pt /\ packet_member_type (fst field) members = Some(Vtype pt).
Proof.
  intros members [name ty]. unfold packet_binding_check; simpl.
  split.
  - destruct ty; try discriminate.
    destruct (packet_member_type name members) as [actual|] eqn:Hactual; try discriminate.
    destruct actual; try discriminate. intros Heq.
    apply eq_primitive_type_sound in Heq; subst. eauto.
  - intros [pt [-> Hlookup]]. rewrite Hlookup. apply packet_primitive_eq_refl.
Qed.

Lemma packet_forallb_spec : forall A (check : A -> bool) (P : A -> Prop),
  (forall x, check x = true <-> P x) ->
  forall xs, forallb check xs = true <-> Forall P xs.
Proof.
  intros A check P Hspec xs. induction xs; simpl.
  - split; intros; constructor.
  - rewrite Bool.andb_true_iff, Hspec, IHxs. split; intros H;
      [destruct H; constructor; assumption|inversion H; auto].
Qed.

Theorem packet_schema_check_spec : forall env sid fields,
  packet_schema_check env sid fields = true <-> storage_safe_packet_schema env sid fields.
Proof.
  intros env sid fields. unfold packet_schema_check, storage_safe_packet_schema.
  destruct (PTree.get sid env) as [co|] eqn:Hlookup.
  - destruct (co_su co) eqn:Hkind.
    + rewrite !Bool.andb_true_iff.
      rewrite (packet_forallb_spec _ _ _ packet_plain_primitive_check_spec).
      rewrite (packet_forallb_spec _ _ _ (packet_binding_check_spec (co_members co))).
      split.
      * intros [[Hmembers Hfields] Hstorage]. exists co; auto.
      * intros [other [Heq [Hstruct [Hmembers [Hfields Hstorage]]]]].
        inversion Heq; subst other. auto.
    + split; [discriminate|]. intros [other [Heq [Hstruct _]]].
      inversion Heq; subst other. congruence.
  - split; [discriminate|]. intros [co [Hfalse _]]; discriminate.
Qed.

Print Assumptions packet_schema_check_spec.
