(* Compositional pure ABI model. Depth one uses an ordinary nullable pointer.
   Each additional optional layer contributes one separate boolean tag (to be
   lowered to a pointer-width word), not bits in the pointer. Inactive records
   are canonically initialized to false tags and a null payload. This file
   proves representation facts only, not memory or elaboration correctness. *)
Require Import List Bool ZArith Arith Lia Integers BeeTypes BeePL_values.
Require Import BeePL_nested_option_model.
Import ListNotations.
Local Open Scope nat_scope.

Definition layered_pointer := (list bool * option (positive * ptrofs))%type.
Definition inactive_pointer (extra : nat) : layered_pointer :=
  (repeat false extra, None).
Definition layered_pointer_eq_dec : forall x y : layered_pointer, {x=y}+{x<>y}.
Proof. repeat decide equality; apply Ptrofs.eq_dec. Defined.

Fixpoint encode_layered_pointer (depth : nat) (v : value) : option layered_pointer :=
 match depth with
 | O => match v with Vloc b ofs => Some ([],Some(b,ofs)) | _ => None end
 | S O => match v with
   | Voption None => Some ([],None)
   | Voption(Some(Vloc b ofs)) => Some([],Some(b,ofs))
   | _ => None end
 | S (S n) => match v with
   | Voption None => Some(inactive_pointer (S n))
   | Voption(Some child) => match encode_layered_pointer (S n) child with
     | Some(tags,payload) => Some(true::tags,payload) | None => None end
   | _ => None end
 end.

Fixpoint decode_layered_pointer (depth : nat) (r : layered_pointer) {struct depth} : option value :=
 match depth with
 | O => match r with ([],Some(b,ofs)) => Some(Vloc b ofs) | _ => None end
 | S inner => match inner with
   | O => match r with
     | ([],None) => Some(Voption None)
     | ([],Some(b,ofs)) => Some(Voption(Some(Vloc b ofs)))
     | _ => None end
   | S n => match r with
     | (false::tags,payload) =>
       if layered_pointer_eq_dec (tags,payload) (inactive_pointer n)
       then Some(Voption None) else None
     | (true::tags,payload) =>
       match decode_layered_pointer inner (tags,payload) with
       | Some child => Some(Voption(Some child)) | None => None end
     | _ => None end
   end
 end.

Lemma decode_inactive_pointer : forall n,
 decode_layered_pointer (S n) (inactive_pointer n) = Some(Voption None).
Proof.
 intros [|n]; [reflexivity|]. change ((if layered_pointer_eq_dec
 (repeat false n,None) (inactive_pointer n) then Some(Voption None) else None) = Some(Voption None)). destruct(layered_pointer_eq_dec
 (repeat false n,None) (inactive_pointer n)); [reflexivity|].
 exfalso; apply n0; reflexivity.
Qed.

Theorem layered_pointer_roundtrip : forall depth v,
 nested_pointer_value depth v -> exists r,
 encode_layered_pointer depth v = Some r /\
 length(fst r)=Nat.pred depth /\ decode_layered_pointer depth r=Some v.
Proof.
 intros depth v H; induction H as [b ofs|n|n v H IH].
 - exists([],Some(b,ofs)); repeat split; reflexivity.
 - exists(inactive_pointer n). split.
   + destruct n; reflexivity.
   + split; [unfold inactive_pointer; simpl; apply repeat_length|apply decode_inactive_pointer].
 - destruct n as [|n].
   + inversion H; subst. exists([],Some(b,ofs)); repeat split; reflexivity.
   + destruct IH as [[tags payload] [He [Hl Hd]]].
     exists(true::tags,payload). split; [simpl; rewrite He; reflexivity|].
     split; [simpl in *; lia|]. change
       (match decode_layered_pointer (S n) (tags,payload) with
        |Some child=>Some(Voption(Some child))|None=>None end = Some(Voption(Some v))).
     rewrite Hd; reflexivity.
Qed.

Definition canonical_layered_pointer depth r := exists v,
 nested_pointer_value depth v /\ encode_layered_pointer depth v=Some r.

Theorem layered_pointer_decode_encode : forall depth r,
 canonical_layered_pointer depth r -> exists v,
 decode_layered_pointer depth r=Some v /\ encode_layered_pointer depth v=Some r.
Proof.
 intros depth r [v [Ht He]]. destruct(layered_pointer_roundtrip _ _ Ht)
 as [r' [He' [_ Hd]]]. rewrite He in He'; inversion He'; subst r'. eauto.
Qed.

Theorem layered_pointer_injective : forall depth v w r,
 nested_pointer_value depth v -> nested_pointer_value depth w ->
 encode_layered_pointer depth v=Some r -> encode_layered_pointer depth w=Some r -> v=w.
Proof.
 intros depth v w r Hv Hw Ev Ew.
 destruct(layered_pointer_roundtrip _ _ Hv) as [rv [Ev' [_ Dv]]].
 destruct(layered_pointer_roundtrip _ _ Hw) as [rw [Ew' [_ Dw]]].
 rewrite Ev in Ev'; inversion Ev'; subst rv.
 rewrite Ew in Ew'; inversion Ew'; subst rw. congruence.
Qed.

Lemma layered_outer_none : forall n,
 encode_layered_pointer (S(S n)) (Voption None)=Some(false::repeat false n,None).
Proof. reflexivity. Qed.
Lemma layered_outer_some : forall n child tags payload,
 encode_layered_pointer (S n) child=Some(tags,payload) ->
 encode_layered_pointer (S(S n)) (Voption(Some child))=Some(true::tags,payload).
Proof. intros; simpl; rewrite H; reflexivity. Qed.
Lemma layered_unwrap_some : forall n tags payload child,
 decode_layered_pointer (S n) (tags,payload)=Some child ->
 decode_layered_pointer (S(S n)) (true::tags,payload)=Some(Voption(Some child)).
Proof. intros; change (match decode_layered_pointer (S n) (tags,payload) with
 |Some v=>Some(Voption(Some v))|None=>None end = Some(Voption(Some child))); rewrite H; reflexivity. Qed.

Example depth_two_absence : encode_layered_pointer 2 (Voption None)=Some([false],None).
Proof. reflexivity. Qed.
Example depth_two_inner_absence : encode_layered_pointer 2 (Voption(Some(Voption None)))=Some([true],None).
Proof. reflexivity. Qed.
Example depth_three_outer_absence : encode_layered_pointer 3 (Voption None)=Some([false;false],None).
Proof. reflexivity. Qed.
Example depth_three_middle_absence : encode_layered_pointer 3 (Voption(Some(Voption None)))=Some([true;false],None).
Proof. reflexivity. Qed.
Example depth_three_inner_absence : encode_layered_pointer 3 (Voption(Some(Voption(Some(Voption None)))))=Some([true;true],None).
Proof. reflexivity. Qed.
Example depth_three_pointer : forall b ofs,
 encode_layered_pointer 3 (Voption(Some(Voption(Some(Voption(Some(Vloc b ofs)))))))=
 Some([true;true],Some(b,ofs)).
Proof. reflexivity. Qed.
Print Assumptions layered_pointer_roundtrip.
Print Assumptions layered_pointer_decode_encode.
Print Assumptions layered_pointer_injective.
