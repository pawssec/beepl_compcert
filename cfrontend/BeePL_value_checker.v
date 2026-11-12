(* Exact declarative checking of runtime values. Heap permissions and authentic
   function addresses remain separate runtime invariants; this checker matches
   the source typing rules, including their ordinary-reference offset policy. *)
Require Import List Bool Integers AST Maps Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_type_equality.
Require Import BeePL_object_decision.

Fixpoint value_type_check (env : bcomposite_env) (Sigma : store_context)
    (v : value) (ty : type) {struct v} : bool :=
  match v with
  | Vunit => match ty with Utype => true | _ => false end
  | Vbool _ => match ty with Vtype Tbool => true | _ => false end
  | Vint _ => match ty with Vtype (Tint _ _ _) => true | _ => false end
  | Vint64 _ => match ty with Vtype (Tlong _ _) => true | _ => false end
  | Vloc block offset =>
      match ty with
      | Ptrtype (Reftype _ _) =>
          match PTree.get block Sigma with Some stored => eq_type stored ty | None => false end
      | Stype _ _ | Atype _ _ _ | Bytes =>
          object_type_at_check env Sigma block (Ptrofs.unsigned offset) ty
      | Ftype _ _ _ _ => Ptrofs.eq offset Ptrofs.zero
      | _ => false
      end
  | Voption payload =>
      match ty with
      | Ptrtype (Otype inner) =>
          negb (is_option_ptr_type inner) &&
          match payload with
          | None => true
          | Some contents => value_type_check env Sigma contents (Ptrtype inner)
          end
      | _ => false
      end
  end.

Theorem value_type_check_sound : forall env Gamma Sigma v ty,
  value_type_check env Sigma v ty = true ->
  type_expr env Gamma Sigma (Val v ty) nil ty.
Proof.
  fix IH 4. intros env Gamma Sigma v ty Hcheck.
  destruct v as [|b|i|i|block offset|payload];
    destruct ty as [|pt|ptr|sid attr|elem len attr|args effects result variadic|];
    simpl in Hcheck; try discriminate; try solve [constructor].
  - destruct pt; try discriminate; constructor.
  - destruct pt; try discriminate; constructor.
  - destruct pt; try discriminate; constructor.
  - destruct ptr; try discriminate.
    destruct (PTree.get block Sigma) as [stored|] eqn:Hstored; try discriminate.
    apply eq_type_sound in Hcheck. subst stored. constructor; exact Hstored.
  - apply ty_valstruct. apply object_type_at_check_spec; exact Hcheck.
  - apply ty_valarray. apply object_type_at_check_spec; exact Hcheck.
  - apply Ptrofs.same_if_eq in Hcheck. subst. constructor.
  - apply ty_valbytes. apply object_type_at_check_spec; exact Hcheck.
  - destruct ptr; try discriminate.
    apply Bool.andb_true_iff in Hcheck as [Hnested Hpayload].
    apply Bool.negb_true_iff in Hnested.
    destruct payload as [contents|].
    + pose proof (IH env Gamma Sigma contents (Ptrtype ptr) Hpayload) as Hcontents.
      apply ty_valo; [exact Hnested|]. intros other Heq. inversion Heq; subst. exact Hcontents.
    + apply ty_valo; [exact Hnested|]. intros other Heq. discriminate.
Qed.

Theorem value_type_check_complete : forall env Gamma Sigma v ty,
  type_expr env Gamma Sigma (Val v ty) nil ty ->
  value_type_check env Sigma v ty = true.
Proof.
  fix IH 4. intros env Gamma Sigma v ty Htyped.
  destruct v; inversion Htyped; subst; simpl; try reflexivity.
  - match goal with H : PTree.get _ Sigma = Some _ |- _ => rewrite H end.
    apply object_eq_type_refl.
  - apply object_type_at_check_spec; assumption.
  - apply object_type_at_check_spec; assumption.
  - apply object_type_at_check_spec; assumption.
  - match goal with H : is_option_ptr_type _ = false |- _ => rewrite H end.
    simpl. destruct o as [contents|]; [eapply IH; eauto|reflexivity].
Qed.

Theorem value_type_check_spec : forall env Gamma Sigma v ty,
  value_type_check env Sigma v ty = true <->
  type_expr env Gamma Sigma (Val v ty) nil ty.
Proof. split; [apply value_type_check_sound|apply value_type_check_complete]. Qed.

Print Assumptions value_type_check_sound.
Print Assumptions value_type_check_complete.
Print Assumptions value_type_check_spec.

(* Shape and boundary regressions: None does not require a payload witness,
   whereas Some must recursively satisfy exactly the payload typing rule. *)
Example value_check_rejects_bool_as_integer : forall env Sigma,
  value_type_check env Sigma (Vbool true) (Vtype (Tint I32 Signed noattr)) = false.
Proof. reflexivity. Qed.

Example value_check_none_function_pointer : forall env Sigma,
  value_type_check env Sigma (Voption None)
    (Ptrtype (Otype (Fptype nil nil Utype false))) = true.
Proof. reflexivity. Qed.

Example value_check_rejects_some_function_pointer : forall env Sigma b ofs,
  value_type_check env Sigma (Voption (Some (Vloc b ofs)))
    (Ptrtype (Otype (Fptype nil nil Utype false))) = false.
Proof. reflexivity. Qed.

Example value_check_rejects_nested_none : forall env Sigma inner,
  value_type_check env Sigma (Voption None) (Ptrtype (Otype (Otype inner))) = false.
Proof. reflexivity. Qed.

Example value_check_reference_arbitrary_offset : forall env Sigma b ofs basic attr,
  PTree.get b Sigma = Some (Ptrtype (Reftype basic attr)) ->
  value_type_check env Sigma (Vloc b ofs) (Ptrtype (Reftype basic attr)) = true.
Proof. intros; simpl; rewrite H; apply object_eq_type_refl. Qed.

Example value_check_function_nonzero_rejected : forall env Sigma b ofs args effects result variadic,
  ofs <> Ptrofs.zero ->
  value_type_check env Sigma (Vloc b ofs) (Ftype args effects result variadic) = false.
Proof.
  intros. simpl. destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:Heq; [|reflexivity].
  apply Ptrofs.same_if_eq in Heq. contradiction.
Qed.
