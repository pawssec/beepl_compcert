(* Operation correspondence uses actual successful expression translation and
   successful scalar decoding. This does not prove expression evaluation or
   correctness of untyped input programs. *)
Require Import Coqlib Errors Integers Maps AST Memory Ctypes Csyntax Cop SimplExpr.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_compiler_expression_types.

Lemma decoded_value_roundtrip : forall raw value,
 trans_cvalue_bvalue raw = OK value -> trans_bvalue_cvalue value = raw.
Proof.
 intros raw value H. destruct raw; simpl in H; try discriminate;
 inversion H; reflexivity.
Qed.

Lemma translated_unary_operation_preserved : forall uop v e m v' v'' fctx bctx ce fctx' bctx' g g' i',
Cop.sem_unary_operation uop (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) m = Some v' ->
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
trans_cvalue_bvalue v' = OK v'' ->
Cop.sem_unary_operation uop (trans_bvalue_cvalue v) (Csyntax.typeof ce) m = Some (trans_bvalue_cvalue v'').
Proof.
 intros * Hoperation Htranslate Hdecode.
 pose proof (compilation_preserve_type_checked _ _ _ _ _ _ _ _ _ Htranslate) as Htype.
 pose proof (decoded_value_roundtrip _ _ Hdecode) as Hvalue.
 rewrite <- Htype, Hvalue. exact Hoperation.
Qed.

(***** Semantic equivalence of casting operator between BeePL and C *****)
Lemma translated_cast_operation_preserved: forall v e t m v' fctx bctx g ce fctx' bctx' g' i' v'',
Cop.sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) t m = Some v' ->
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
trans_cvalue_bvalue v' = OK v'' ->
Cop.sem_cast (trans_bvalue_cvalue v) (Csyntax.typeof ce) t m = Some (trans_bvalue_cvalue v'').
Proof.
 intros * Hoperation Htranslate Hdecode.
 pose proof (compilation_preserve_type_checked _ _ _ _ _ _ _ _ _ Htranslate) as Htype.
 pose proof (decoded_value_roundtrip _ _ Hdecode) as Hvalue.
 rewrite <- Htype, Hvalue. exact Hoperation.
Qed.

Print Assumptions translated_unary_operation_preserved.
Print Assumptions translated_cast_operation_preserved.
