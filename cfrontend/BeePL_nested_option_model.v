(* Pure representation specification, not yet a memory layout or compiler ABI.
   The tag counts present wrappers before the first absent wrapper. At depth
   zero the value is an unmodified pointer. No tag bits are stored in pointers.
   Location validity and the terminal pointer type's provenance are separate
   obligations of the eventual language integration. *)
Require Import ZArith Arith Lia Integers BeeTypes BeePL_values.
Local Open Scope nat_scope.

Fixpoint optional_pointer_type (depth : nat) (terminal : ptr_type) : ptr_type :=
  match depth with
  | O => terminal
  | S n => Otype (optional_pointer_type n terminal)
  end.

Inductive nested_pointer_value : nat -> value -> Prop :=
| nested_pointer_leaf : forall b ofs, nested_pointer_value O (Vloc b ofs)
| nested_pointer_none : forall n, nested_pointer_value (S n) (Voption None)
| nested_pointer_some : forall n v, nested_pointer_value n v ->
    nested_pointer_value (S n) (Voption (Some v)).

Definition tagged_pointer := (nat * option (positive * ptrofs))%type.

Definition tagged_pointer_valid (depth : nat) (r : tagged_pointer) : Prop :=
  match snd r with
  | None => fst r < depth
  | Some _ => fst r = depth
  end.

Fixpoint encode_nested_pointer (depth : nat) (v : value) : option tagged_pointer :=
  match depth, v with
  | O, Vloc b ofs => Some (O, Some (b, ofs))
  | S n, Voption None => Some (O, None)
  | S n, Voption (Some child) =>
      match encode_nested_pointer n child with
      | Some (tag, payload) => Some (S tag, payload)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint decode_nested_pointer (depth : nat) (r : tagged_pointer) : option value :=
  match depth, fst r, snd r with
  | O, O, Some (b, ofs) => Some (Vloc b ofs)
  | S n, O, None => Some (Voption None)
  | S n, S tag, payload =>
      match decode_nested_pointer n (tag, payload) with
      | Some child => Some (Voption (Some child))
      | None => None
      end
  | _, _, _ => None
  end.

Theorem nested_pointer_encode_roundtrip : forall depth v,
  nested_pointer_value depth v -> exists r,
    encode_nested_pointer depth v = Some r /\
    tagged_pointer_valid depth r /\ decode_nested_pointer depth r = Some v.
Proof.
  intros depth v H; induction H as [b ofs|n|n v H IH].
  - exists (O, Some (b, ofs)); repeat split; reflexivity.
  - exists (O, None); unfold tagged_pointer_valid; simpl; repeat split; auto with arith.
  - destruct IH as [[tag payload] [He [Hv Hd]]].
    exists (S tag, payload). simpl. rewrite He, Hd. split; [reflexivity|].
    split; [|reflexivity]. unfold tagged_pointer_valid in *; simpl in *.
    destruct payload; lia.
Qed.

Theorem nested_pointer_decode_roundtrip : forall depth r,
  tagged_pointer_valid depth r -> exists v,
    decode_nested_pointer depth r = Some v /\
    nested_pointer_value depth v /\ encode_nested_pointer depth v = Some r.
Proof.
  induction depth as [|n IH]; intros [tag payload] H;
    unfold tagged_pointer_valid in H; simpl in H.
  - destruct payload as [[b ofs]|]; [subst tag|lia].
    exists (Vloc b ofs); repeat split; try reflexivity; constructor.
  - destruct tag as [|tag].
    + destruct payload; [lia|]. exists (Voption None).
      repeat split; try reflexivity; constructor.
    + assert (Hv : tagged_pointer_valid n (tag,payload)).
      { unfold tagged_pointer_valid; simpl. destruct payload; lia. }
      destruct (IH (tag,payload) Hv) as [v [Hd [Ht He]]].
      exists (Voption (Some v)). simpl. rewrite Hd, He.
      repeat split; try reflexivity. constructor; exact Ht.
Qed.

Theorem nested_pointer_encoding_injective : forall depth left right r,
  nested_pointer_value depth left -> nested_pointer_value depth right ->
  encode_nested_pointer depth left = Some r ->
  encode_nested_pointer depth right = Some r -> left = right.
Proof.
  intros depth left right r Hl Hr El Er.
  destruct (nested_pointer_encode_roundtrip _ _ Hl) as [rl [El' [_ Dl]]].
  destruct (nested_pointer_encode_roundtrip _ _ Hr) as [rr [Er' [_ Dr]]].
  rewrite El in El'; inversion El'; subst rl.
  rewrite Er in Er'; inversion Er'; subst rr.
  congruence.
Qed.

Lemma tagged_pointer_tag_bound : forall depth r,
  tagged_pointer_valid depth r -> fst r <= depth.
Proof.
  intros depth [tag payload] H; unfold tagged_pointer_valid in H; simpl in *.
  destruct payload; lia.
Qed.

Lemma nested_pointer_decode_sound : forall depth r v,
  decode_nested_pointer depth r = Some v ->
  tagged_pointer_valid depth r /\ nested_pointer_value depth v.
Proof.
  induction depth as [|n IH]; intros [tag payload] v H;
    destruct tag as [|tag]; destruct payload as [[b ofs]|]; simpl in H;
    try discriminate.
  - inversion H; subst. split; [reflexivity|constructor].
  - inversion H; subst. split; [unfold tagged_pointer_valid; simpl; lia|constructor].
  - destruct (decode_nested_pointer n (tag, Some (b, ofs))) as [child|] eqn:Hd;
      try discriminate. inversion H; subst.
    destruct (IH _ _ Hd) as [Hv Ht]. split.
    + unfold tagged_pointer_valid in *; simpl in *; lia.
    + constructor; assumption.
  - destruct (decode_nested_pointer n (tag, None)) as [child|] eqn:Hd;
      try discriminate. inversion H; subst.
    destruct (IH _ _ Hd) as [Hv Ht]. split.
    + unfold tagged_pointer_valid in *; simpl in *; lia.
    + constructor; assumption.
Qed.

Example nested_none_tag : encode_nested_pointer 2 (Voption None) = Some (0,None).
Proof. reflexivity. Qed.
Example nested_some_none_tag :
  encode_nested_pointer 2 (Voption (Some (Voption None))) = Some (1,None).
Proof. reflexivity. Qed.
Example nested_some_some_pointer_tag : forall b ofs,
  encode_nested_pointer 2 (Voption (Some (Voption (Some (Vloc b ofs))))) =
  Some (2,Some (b,ofs)).
Proof. reflexivity. Qed.

Print Assumptions nested_pointer_encode_roundtrip.
Print Assumptions nested_pointer_decode_roundtrip.
Print Assumptions nested_pointer_encoding_injective.
