(* Whole-syntax consequences of the escape gate. These are syntactic policy
   facts, not a semantic lifetime/no-escape theorem or helper-correctness proof. *)
Require Import List Bool AST Maps BeeTypes BeePL.
Require Import BeePL_escape_types BeePL_escape_check.
Import ListNotations.

Definition escape_children (e : expr) : list expr :=
 match e with
 | App callee args _ => callee::args
 | Prim _ args _ | Sinit _ _ args _ | Ebytes args _ | Ainit _ _ args _ => args
 | Bind _ _ first body _ => [first;body]
 | Cond condition yes no _ => [condition;yes;no]
 | For lower upper _ body _ => [lower;upper;body]
 | Sfield value _ _ | Esome value _ | CallFrame _ value _ => [value]
 | Match value _ branches _ => value::branches
 | LoopFrame _ template active => [template;active]
 | _ => []
 end.

Inductive escape_subexpression : expr -> expr -> Prop :=
| escape_subexpression_self : forall e, escape_subexpression e e
| escape_subexpression_child : forall e child descendant,
 In child(escape_children e) -> escape_subexpression child descendant ->
 escape_subexpression e descendant.

Lemma checked_callee_is_direct : forall p locals shadow callee args result,
 escape_call_check p locals shadow callee args result=true ->
 exists id annotation, callee=Var id annotation.
Proof. intros p locals shadow callee args result H; destruct callee; simpl in H; try discriminate; eauto. Qed.

Lemma checked_expression_child : forall p fd shadow e child,
 escape_expression_check p fd shadow e=true -> In child(escape_children e) ->
 exists child_shadow, escape_expression_check p fd child_shadow child=true.
Proof.
 intros p fd shadow e; destruct e; intros child Hcheck Hin;
 cbn [escape_expression_check] in Hcheck; cbn [escape_children] in Hin;
 try contradiction; try discriminate;
 repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H end;
 repeat match goal with H : forallb _ _ = true |- _ => rewrite forallb_forall in H end;
 repeat match goal with H : In _ (_::_) |- _ => destruct H as [E|H]; [subst|] end;
 try contradiction; try solve[eauto].
 - match goal with H : escape_call_check _ _ _ _ _ _=true |- _ =>
   destruct(checked_callee_is_direct _ _ _ _ _ _ H) as [id [annotation E]]; subst end.
   exists shadow; reflexivity.
Qed.

Theorem checked_subexpression : forall root descendant,
 escape_subexpression root descendant -> forall p fd shadow,
 escape_expression_check p fd shadow root=true ->
 exists descendant_shadow, escape_expression_check p fd descendant_shadow descendant=true.
Proof.
 intros root descendant H; induction H; intros p fd shadow Hcheck; [eauto|].
 destruct(checked_expression_child _ _ _ _ _ Hcheck H) as [child_shadow Hchild].
 eapply IHescape_subexpression; exact Hchild.
Qed.

Theorem every_checked_store_reference_free : forall p fd shadow e target payload ty,
 escape_expression_check p fd shadow e=true ->
 escape_subexpression e(Prim Massgn [target;payload] ty) ->
 reference_free_type_check (prog_comp_env p)(typeof_expr payload)=true.
Proof.
 intros p fd shadow e target payload ty Hcheck Hsub.
 destruct(checked_subexpression _ _ Hsub _ _ _ Hcheck) as [scope Hstore].
 eapply checked_store_reference_free; exact Hstore.
Qed.

Theorem every_checked_call_has_scoped_contract : forall p fd shadow e callee args result,
 escape_expression_check p fd shadow e=true ->
 escape_subexpression e(App callee args result) ->
 exists scope, escape_call_check p (map fst(fn_vars fd)) scope callee args result=true.
Proof.
 intros p fd shadow e callee args result Hcheck Hsub.
 destruct(checked_subexpression _ _ Hsub _ _ _ Hcheck) as [scope Hcall].
 exists scope. apply andb_true_iff in Hcall; exact(proj1 Hcall).
Qed.

Corollary every_checked_call_direct : forall p fd shadow e callee args result,
 escape_expression_check p fd shadow e=true ->
 escape_subexpression e(App callee args result) -> exists id annotation,callee=Var id annotation.
Proof.
 intros. destruct(every_checked_call_has_scoped_contract _ _ _ _ _ _ _ H H0) as [scope Hcall].
 eapply checked_callee_is_direct; exact Hcall.
Qed.

Corollary checked_function_all_stores_reference_free : forall p fd target payload ty,
 escape_function_check p fd=true ->
 escape_subexpression (fn_body fd)(Prim Massgn [target;payload] ty) ->
 reference_free_type_check (prog_comp_env p)(typeof_expr payload)=true.
Proof.
 intros p fd target payload ty Hcheck Hsub. apply andb_true_iff in Hcheck.
 eapply every_checked_store_reference_free; [exact(proj2 Hcheck)|exact Hsub].
Qed.

Corollary checked_program_all_stores_reference_free : forall p id fd section target payload ty,
 escape_program_check p=true -> In(id,Gfun(Internal fd),section)(prog_defs p) ->
 escape_subexpression (fn_body fd)(Prim Massgn [target;payload] ty) ->
 reference_free_type_check (prog_comp_env p)(typeof_expr payload)=true.
Proof.
 intros. eapply checked_function_all_stores_reference_free; [|eassumption].
 eapply checked_program_internal_function; eauto.
Qed.
Print Assumptions every_checked_store_reference_free.
Print Assumptions every_checked_call_has_scoped_contract.
Print Assumptions checked_program_all_stores_reference_free.
