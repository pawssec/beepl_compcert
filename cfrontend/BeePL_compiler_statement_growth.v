Require Import List String ZArith Lia Coqlib Integers AST Maps SimplExpr.
Require Import BeeTypes BeePL BeePL_Csyntax BeePL_compiler_context_growth.
Import ListNotations.
Definition statement_context_growth (e : BeePL.expr) :=
 forall env ctx bctx g cs ctx' bctx' g' proof,
 transBeePL_expr_st env e ctx bctx g=Res(cs,ctx',bctx')g' proof -> context_growth ctx ctx'.
Ltac statement_grow_collect :=
 repeat match goal with
 | E:fresh_compiler_binding ?source ?ty ?ctx ?bc ?g=Res(?binding,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gbinding" in let R:=fresh "Rbinding" in
   destruct(fresh_compiler_binding_growth _ _ _ _ _ _ _ _ _ _ E) as [G R]; clear E
 | E:compiler_destination ?selected ?ty ?ctx ?bc ?g=Res(?id,?ctx')?g' ?ip |- _ =>
   let G:=fresh "Gdestination" in pose proof(compiler_destination_growth _ _ _ _ _ _ _ _ _ E) as G; clear E
 | E:fresh_compiler_fields ?fields ?ctx ?bc ?g=Res(?bindings,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gfields" in let R:=fresh "Rfields" in
   destruct(fresh_compiler_fields_growth _ _ _ _ _ _ _ _ _ E) as [G R]; clear E

 | E : guarded_binop ?op ?es ?ces ?ty ?ctx ?bc ?g=Res(?ce,?ctx',?bc')?g' ?ip |- _ =>
     let G := fresh "Gguard" in let EQ := fresh "EQguard" in
     destruct(guarded_binop_context_growth _ _ _ _ _ _ _ _ _ _ _ _ E) as [EQ G]; clear E; subst
 | IH : statement_context_growth ?e,
   E : transBeePL_expr_st ?env ?e ?ctx ?bc ?g=Res(?cs,?ctx',?bc') ?g' ?ip |- _ =>
     let K := fresh "Gchild" in pose proof(IH _ _ _ _ _ _ _ _ _ E) as K; clear IH
 | E : transBeePL_expr_expr ?e ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
     let K := fresh "Gexpr" in pose proof(expression_translation_context_growth e _ _ _ _ _ _ _ _ E) as K; clear E
 | E : transBeePL_expr_exprs transBeePL_expr_expr ?es ?ctx ?bc ?g=Res(?ces,?ctx',?bc') ?g' ?ip |- _ =>
     let K := fresh "Glist" in pose proof(expression_list_translation_context_growth _ _ _ _ _ _ _ _ _ E) as K; clear E
 end.
Ltac new_context_slot := apply context_growth_fresh; let Hpresent := fresh "Hpresent" in intro Hpresent;
 match goal with Hn : ~_ |- _ => apply Hn;
   first [exact Hpresent | right; apply in_or_app; left; exact Hpresent] end.
Ltac growth_chain :=
 first [assumption | apply context_growth_refl |
   match goal with
   | G : context_growth ?middle ?last |- context_growth ?first ?last =>
     eapply context_growth_trans with (b:=middle); [clear G; growth_chain|exact G]
   end |
   match goal with
   | |- context_growth ?first ((?id,?ty,?tag)::?tail) =>
     eapply context_growth_trans with (b:=tail); [growth_chain|new_context_slot]
   end].
Ltac statement_grow_solve := statement_grow_collect; cbn beta iota zeta in *;
 try solve [growth_chain].
Theorem statement_translation_context_growth : forall e, statement_context_growth e.
Proof.
 intros e; induction e using expr_ind_rec;
 unfold statement_context_growth at 1; intros env ctx bc g ce ctx' bc' g' ip Hrun;
 cbn [transBeePL_expr_st] in Hrun;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret,SimplExpr.error in Hrun;
 cbn beta iota zeta in Hrun;
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
     let rec descend t := lazymatch t with
       | context[match ?inner with _ => _ end] => descend inner
       | _ => let E := fresh "Epart" in destruct t eqn:E
       end in descend scr;
     repeat match goal with p : (_ * _)%type |- _ => destruct p end;
     cbn beta iota zeta in *; try discriminate
 end;
 try (inversion Hrun; subst; clear Hrun; statement_grow_solve).
all: repeat match goal with
 | E : fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof |- _ =>
 let Hfresh := fresh "Hfresh" in
 pose proof(reserved_exclusion_left used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) as Hfresh; clear E
 end.
all: try solve [eapply context_growth_trans; [eassumption|]; apply context_growth_fresh; assumption].
all: try solve [growth_chain].
all: repeat match goal with
 | IH : forall child, In child ?es -> statement_context_growth child,
   E : transBeePL_expr_st ?env ?child ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
     let Hin := fresh "Hin" in assert (Hin : In child es) by (simpl; tauto);
     let K := fresh "Gbranch" in
     pose proof (IH child Hin _ _ _ _ _ _ _ _ _ E) as K; clear E
 end.
all: try solve [growth_chain].
all: simpl in *.
all: try solve [growth_chain].
Qed.

Print Assumptions statement_translation_context_growth.

Lemma initial_compiler_context_identifiers : forall vars names g ctx g' proof,
 create_fn_ctx vars names g=Res ctx g' proof ->
 map unzip_ident ctx=map fst vars.
Proof.
 intros vars; induction vars as [|[id ty] rest IH]; intros names g ctx g' proof H;
 cbn [create_fn_ctx] in H;
 unfold SimplExpr.bind,SimplExpr.ret,SimplExpr.error in H.
 - inversion H; reflexivity.
 - destruct(create_fn_ctx rest names g) as [msg|tail gm ip] eqn:E; try discriminate.
   destruct(lookup_string id names) eqn:F; cbn in H; try discriminate.
   inversion H; subst. simpl. f_equal. eapply IH; exact E.
Qed.

Require Import BeePL_compiler_structure BeePL_compiler_local_allocation.
Theorem translated_function_locals_distinct : forall env bf names bc cf names' bc',
 transBeePL_function_function env bf names bc=Errors.OK(cf,names',bc') ->
 NoDup(map fst (Csyntax.fn_vars cf)).
Proof.
 intros env bf names bc cf names' bc' Hcompile.
 destruct(function_translation_body_context _ _ _ _ _ _ _ Hcompile)
 as [initial [g0 [i0 [ctx [g1 [i1 [Hinitial [Hbody Hlocals]]]]]]]].
 pose proof(initial_compiler_context_identifiers _ _ _ _ _ _ Hinitial) as Hids.
 pose proof(statement_translation_context_growth _ _ _ _ _ _ _ _ _ _ Hbody) as [_ Hgrow].
 assert(Hfinal:NoDup(map unzip_ident ctx)). { apply Hgrow. rewrite Hids; constructor. }
 rewrite Hlocals. change(NoDup(map fst(compiled_context_locals ctx))).
 rewrite compiled_context_locals_map,map_map. exact Hfinal.
Qed.
Print Assumptions translated_function_locals_distinct.
