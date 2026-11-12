(* Successful executable lowering enforces the representation boundary. *)
Require Import List AST Errors BeeTypes BeePL BeePL_Csyntax.
Require Import BeePL_Check_Reserved_Struct BeePL_representation_check.
Import ListNotations.

Theorem successful_compiler_representation_check : forall p cp names sections,
  BeePL_compcert p=OK(cp,names,sections) -> representation_program_check p=true.
Proof.
  intros p cp names sections H. unfold BeePL_compcert in H.
  destruct(check_struct_from_program p) eqn:Estruct; simpl in H; try discriminate.
  destruct(check_compiler_representation p) eqn:Erepresentation; simpl in H; try discriminate.
  unfold check_compiler_representation in Erepresentation.
  destruct(representation_program_check p); [reflexivity|discriminate].
Qed.

Theorem successful_compiler_no_raw_ibool : forall p cp names sections signed attr,
  BeePL_compcert p=OK(cp,names,sections) ->
  ~In (Tint Ctypes.IBool signed attr)(program_primitive_occurrences p).
Proof.
  intros p cp names sections signed attr H Hin.
  pose proof(successful_compiler_representation_check _ _ _ _ H) as Hsafe.
  apply representation_program_check_spec in Hsafe.
  rewrite Forall_forall in Hsafe. specialize(Hsafe _ Hin). eapply Hsafe; reflexivity.
Qed.

Theorem successful_compiler_function_representation : forall p cp names sections id fn section,
  BeePL_compcert p=OK(cp,names,sections) ->
  In(id,Gfun(Internal fn),section)(prog_defs p) ->
  representation_type_check(fn_return fn)=true /\
  representation_expression_check(fn_body fn)=true /\
  Forall primitive_representation_safe(function_primitive_occurrences fn).
Proof.
  intros p cp names sections id fn section Hcompile Hin.
  pose proof(checked_program_internal_function_representation _ _ _ _
    (successful_compiler_representation_check _ _ _ _ Hcompile) Hin) as Hsafe.
  split; [apply checked_function_return_representation; exact Hsafe|].
  split; [apply checked_function_body_representation; exact Hsafe|exact Hsafe].
Qed.
Print Assumptions successful_compiler_representation_check.
Print Assumptions successful_compiler_no_raw_ibool.
Print Assumptions successful_compiler_function_representation.
