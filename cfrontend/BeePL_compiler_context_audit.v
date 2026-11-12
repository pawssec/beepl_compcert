(* Audit of the legacy universal fresh-context hypothesis, reproduced here
   without importing the admitted compiler simulation module. A bounded final
   context can constrain one compilation run; it cannot contain the unchanged
   input context of every possible compilation run. *)
Require Import List String ZArith Lia Coqlib Integers AST Maps Csyntax SimplExpr.
Require Import BeeTypes BeePL_values BeePL BeePL_compiler_bindings BeePL_Csyntax.
Import ListNotations.
Definition audit_context_subset (small large : list (ident * BeeTypes.type * string)) :=
 forall id ty tag, In (id,ty,tag) small -> In (id,ty,tag) large.
Definition legacy_universal_final_context (ff : list (ident * BeeTypes.type * string)) :=
 forall e fctx bctx g ce fctx' bctx' g' i',
 transBeePL_expr_expr e fctx bctx g=Res(ce,fctx',bctx') g' i' ->
 audit_context_subset fctx fctx' /\ audit_context_subset fctx' ff.
Definition context_identifier_bound (ff : list (ident * BeeTypes.type * string)) :=
 fold_right Nat.max 0%nat (map(fun entry=>Pos.to_nat(fst(fst entry))) ff).
Lemma context_identifier_bounded : forall ff id ty tag,
 In(id,ty,tag) ff -> (Pos.to_nat id <= context_identifier_bound ff)%nat.
Proof.
 intros ff; induction ff as [|[[head t] name] rest IH]; intros id ty tag Hin;
 simpl in Hin; [contradiction|]. unfold context_identifier_bound; simpl.
 destruct Hin as [E|Hin].
 - inversion E; subst; apply Nat.le_max_l.
 - eapply Nat.le_trans; [eapply IH; exact Hin|apply Nat.le_max_r].
Qed.
Theorem legacy_universal_final_context_impossible : forall ff,
 ~legacy_universal_final_context ff.
Proof.
 intros ff Hall.
 set (id:=Pos.of_nat(S(context_identifier_bound ff))).
 set (ctx:= {| arg_ctx:=[]; benv:=PTree.empty _; reserved_identifiers:=[]; lexical_bindings:=empty_compiler_bindings |}).
 set (g:=mkgenerator 1%positive []).
 assert (Hrun: transBeePL_expr_expr (BeePL.Val Vunit Utype)
  [(id,Utype,EmptyString)] ctx g =
  Res(Csyntax.Eval (trans_bvalue_cvalue Vunit) (transBeePL_type Utype),[(id,Utype,EmptyString)],ctx) g (Ple_refl(gen_next g))).
 { reflexivity. }
 destruct(Hall _ _ _ _ _ _ _ _ _ Hrun) as [_ Hsubset].
 pose proof(Hsubset id Utype EmptyString (or_introl eq_refl)) as Hin.
 pose proof(context_identifier_bounded _ _ _ _ Hin) as Hbound.
 unfold id in Hbound. rewrite Nat2Pos.id in Hbound by lia. lia.
Qed.
Print Assumptions legacy_universal_final_context_impossible.
