(* Successful lowering enforces the conservative escape gate. These theorems
   certify gate enforcement and its structural return-type property, not a
   lifetime theorem for arbitrary ill-typed ASTs or unknown external code. *)
Require Import List Bool String ZArith AST Errors BeeTypes BeePL BeePL_Csyntax.
Require Import BeePL_Check_Reserved_Struct BeePL_escape_types BeePL_escape_check.
Require Import BeePL_escape_policy.
Require Import BeePL_representation_check.
Import ListNotations.

Theorem successful_compiler_escape_check : forall p cp names sections,
  BeePL_compcert p=OK(cp,names,sections) -> escape_program_check p=true.
Proof.
  intros p cp names sections H. unfold BeePL_compcert in H.
  destruct(check_struct_from_program p) eqn:Ereserved; simpl in H; try discriminate.
  destruct(check_compiler_representation p) eqn:Erepresentation; simpl in H; try discriminate.
  destruct(check_reference_escapes p) eqn:Eescape; simpl in H; try discriminate.
  eapply check_reference_escapes_success; exact Eescape.
Qed.

Theorem successful_compiler_internal_function_escape_check :
  forall p cp names sections id fn section,
  BeePL_compcert p=OK(cp,names,sections) ->
  In(id,Gfun(Internal fn),section)(prog_defs p) ->
  reference_free_type_check (prog_comp_env p)(fn_return fn)=true /\
  escape_expression_check p fn (map fst(fn_args fn))(fn_body fn)=true.
Proof.
  intros p cp names sections id fn section Hcompile Hin.
  pose proof (checked_program_internal_function _ _ _ _
    (successful_compiler_escape_check _ _ _ _ Hcompile) Hin) as Hcheck.
  apply andb_true_iff in Hcheck. exact Hcheck.
Qed.

Corollary successful_compiler_internal_return_reference_free :
  forall p cp names sections id fn section,
  BeePL_compcert p=OK(cp,names,sections) ->
  In(id,Gfun(Internal fn),section)(prog_defs p) ->
  reference_free_type_spec (prog_comp_env p)(fn_return fn).
Proof.
  intros. apply reference_free_type_check_sound.
  eapply successful_compiler_internal_function_escape_check; eauto.
Qed.

Lemma escape_identifier_in_member : forall id ids,
  In id ids -> escape_identifier_in id ids=true.
Proof.
  intros id ids Hin. unfold escape_identifier_in.
  apply existsb_exists. exists id; split; auto. apply Pos.eqb_refl.
Qed.

Lemma shadowed_direct_call_rejected : forall p locals shadow id annotation args result,
  In id (locals++shadow) ->
  escape_call_check p locals shadow (Var id annotation) args result=false.
Proof.
  intros. unfold escape_call_check.
  rewrite escape_identifier_in_member by assumption. reflexivity.
Qed.

Example indirect_expression_call_rejected : forall p locals shadow op operands annotation args result,
  escape_call_check p locals shadow (Prim op operands annotation) args result=false.
Proof. reflexivity. Qed.

Lemma parameter_array_destination_rejected : forall p fn shadow id element length attr result,
  In id (map fst(fn_args fn)) ->
  escape_local_array p fn shadow id (Atype element length attr) result=false.
Proof.
  intros. unfold escape_local_array.
  rewrite escape_identifier_in_member.
  - reflexivity.
  - apply in_or_app; right. apply in_or_app; left; assumption.
Qed.

Lemma global_array_destination_rejected : forall p fn shadow id element length attr result,
  In id (map (fun '(name,_,_) => name)(prog_defs p)) ->
  escape_local_array p fn shadow id (Atype element length attr) result=false.
Proof.
  intros. unfold escape_local_array.
  rewrite escape_identifier_in_member.
  - reflexivity.
  - apply in_or_app; right. apply in_or_app; right; assumption.
Qed.

Example pointer_cast_escape_rejected : forall env pointer value,
  escape_primitive_check env (Cast(Ptrtype pointer)) [value]=false.
Proof.
  intros. unfold escape_primitive_check.
  rewrite reference_free_pointer_rejected. reflexivity.
Qed.

Print Assumptions successful_compiler_escape_check.
Print Assumptions successful_compiler_internal_return_reference_free.
Print Assumptions shadowed_direct_call_rejected.

Corollary successful_compiler_all_stores_reference_free :
  forall p cp names sections id fn section target payload ty,
  BeePL_compcert p = OK (cp, names, sections) ->
  In (id, Gfun (Internal fn), section) (prog_defs p) ->
  escape_subexpression (fn_body fn) (Prim Massgn [target; payload] ty) ->
  reference_free_type_spec (prog_comp_env p) (typeof_expr payload).
Proof.
  intros. apply reference_free_type_check_sound.
  eapply checked_program_all_stores_reference_free; [|eassumption|eassumption].
  eapply successful_compiler_escape_check; eassumption.
Qed.
