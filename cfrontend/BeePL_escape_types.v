(* Conservative reference-escape boundary classifier. This is a type-shape
   check, not a lifetime analysis. Unknown/cyclic/depth-exhausted metadata fails
   closed. Bytes and function values are unsafe alongside every pointer type.
   Fuel is derived from the finite inline-type universe; it is not machine-word
   dependent. The visited list is path-local, so repeated sibling structs work. *)
Require Import List Bool ZArith Lia Coqlib AST Maps Ctypes.
Require Import BeeTypes BeePL BeePL_object_finiteness.
Import ListNotations.

Fixpoint reference_free_type_fuel (fuel : nat) (seen : list ident)
    (env : bcomposite_env) (ty : type) : bool :=
 match fuel with
 | O => false
 | S rest => match ty with
   | Utype | Vtype _ => true
   | Ptrtype _ | Bytes | Ftype _ _ _ _ => false
   | Atype elem count _ => Z.leb 0 count && reference_free_type_fuel rest seen env elem
   | Stype name _ =>
     if in_dec ident_eq name seen then false else
     match PTree.get name env with
     | None => false
     | Some co => forallb (fun member =>
         reference_free_type_fuel rest (name::seen) env (type_bmember member)) (co_members co)
     end
   end
 end.

Definition reference_free_type_check (env : bcomposite_env) (ty : type) : bool :=
 reference_free_type_fuel (S(length(object_type_universe env ty))) [] env ty.

Inductive reference_free_type_spec (env : bcomposite_env) : type -> Prop :=
| reference_free_unit : reference_free_type_spec env Utype
| reference_free_scalar : forall primitive, reference_free_type_spec env (Vtype primitive)
| reference_free_array : forall elem count attr,
 (0<=count)%Z -> reference_free_type_spec env elem ->
 reference_free_type_spec env (Atype elem count attr)
| reference_free_structure : forall name attr co,
 PTree.get name env=Some co ->
 Forall (fun member => reference_free_type_spec env(type_bmember member)) (co_members co) ->
 reference_free_type_spec env (Stype name attr).

Theorem reference_free_type_fuel_sound : forall fuel seen env ty,
 reference_free_type_fuel fuel seen env ty=true -> reference_free_type_spec env ty.
Proof.
 induction fuel as [|fuel IH]; intros seen env ty H; [discriminate|].
 destruct ty; cbn [reference_free_type_fuel] in H; try discriminate; try constructor.
 - destruct(in_dec ident_eq i seen); [discriminate|].
   destruct(PTree.get i env) as [co|] eqn:E; [|discriminate].
   econstructor; [exact E|]. apply Forall_forall; intros member Hin.
   apply forallb_forall with (x:=member) in H; [|exact Hin]. eapply IH; exact H.
 - apply andb_true_iff in H as [Hcount Hinner].
   + apply Z.leb_le; exact Hcount.
 - apply andb_true_iff in H as [Hcount Hinner]. eapply IH; exact Hinner.
Qed.
Theorem reference_free_type_check_sound : forall env ty,
 reference_free_type_check env ty=true -> reference_free_type_spec env ty.
Proof. intros env ty; apply reference_free_type_fuel_sound. Qed.

Lemma reference_free_pointer_rejected : forall env pointer,
 reference_free_type_check env(Ptrtype pointer)=false.
Proof. reflexivity. Qed.
Lemma reference_free_bytes_rejected : forall env,
 reference_free_type_check env Bytes=false.
Proof. reflexivity. Qed.
Lemma reference_free_function_rejected : forall env args effects result variadic,
 reference_free_type_check env(Ftype args effects result variadic)=false.
Proof. reflexivity. Qed.
Lemma reference_free_missing_structure_rejected : forall env name attr,
 PTree.get name env=None -> reference_free_type_check env(Stype name attr)=false.
Proof. intros; unfold reference_free_type_check; cbn [reference_free_type_fuel]. rewrite H; reflexivity. Qed.
Lemma reference_free_seen_structure_rejected : forall fuel seen env name attr,
 In name seen -> reference_free_type_fuel fuel seen env(Stype name attr)=false.
Proof.
 intros [|fuel] seen env name attr Hin; [reflexivity|].
 cbn [reference_free_type_fuel]. destruct(in_dec ident_eq name seen); [reflexivity|contradiction].
Qed.
Lemma reference_free_no_pointer_spec : forall env pointer,
 ~reference_free_type_spec env(Ptrtype pointer).
Proof. intros env pointer H; inversion H. Qed.
Lemma reference_free_no_bytes_spec : forall env,
 ~reference_free_type_spec env Bytes.
Proof. intros env H; inversion H. Qed.

Example scalar_array_safe : reference_free_type_check (PTree.empty _)
 (Atype (Vtype Tbool) 3 noattr)=true.
Proof. reflexivity. Qed.
Example pointer_array_unsafe : reference_free_type_check (PTree.empty _)
 (Atype (Ptrtype(Reftype(Bprim Tbool) noattr)) 3 noattr)=false.
Proof. reflexivity. Qed.
Example zero_length_pointer_array_unsafe : reference_free_type_check (PTree.empty _)
 (Atype (Ptrtype(Reftype(Bprim Tbool) noattr)) 0 noattr)=false.
Proof. reflexivity. Qed.
Example nested_option_array_unsafe : reference_free_type_check (PTree.empty _)
 (Atype (Ptrtype(Otype(Otype(Reftype(Bprim Tbool) noattr)))) 2 noattr)=false.
Proof. reflexivity. Qed.
Example byte_array_unsafe : reference_free_type_check (PTree.empty _)
 (Atype Bytes 2 noattr)=false.
Proof. reflexivity. Qed.
Print Assumptions reference_free_type_check_sound.

Lemma reference_free_array_element_sound : forall env elem count attr,
 reference_free_type_check env(Atype elem count attr)=true ->
 reference_free_type_spec env elem.
Proof. intros; apply reference_free_type_check_sound in H; inversion H; assumption. Qed.

Lemma reference_free_structure_member_sound : forall env name attr co member,
 reference_free_type_check env(Stype name attr)=true ->
 PTree.get name env=Some co -> In member(co_members co) ->
 reference_free_type_spec env(type_bmember member).
Proof.
 intros env name attr co member Hcheck Hco Hin.
 apply reference_free_type_check_sound in Hcheck.
 inversion Hcheck; subst. assert(co0=co) by congruence; subst co0.
 rewrite Forall_forall in H2; eauto.
Qed.

Lemma reference_free_direct_cycle_rejected : forall fuel seen env name attr co member childattr,
 PTree.get name env=Some co -> In member(co_members co) ->
 type_bmember member=Stype name childattr ->
 reference_free_type_fuel fuel seen env(Stype name attr)=false.
Proof.
 intros [|fuel] seen env name attr co member childattr Hco Hin Htype; [reflexivity|].
 cbn [reference_free_type_fuel]. destruct(in_dec ident_eq name seen); [reflexivity|].
 rewrite Hco. apply Bool.not_true_is_false; intro Hcheck.
 apply forallb_forall with(x:=member) in Hcheck; [|exact Hin].
 rewrite Htype in Hcheck.
 rewrite reference_free_seen_structure_rejected in Hcheck; [discriminate|simpl; auto].
Qed.
Print Assumptions reference_free_direct_cycle_rejected.
