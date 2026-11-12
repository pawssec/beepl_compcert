(* Context invariants for actual expression translation runs. *)
Require Import List String ZArith Lia Coqlib Integers AST Maps SimplExpr.
Require Import BeeTypes BeePL BeePL_Csyntax.
Import ListNotations.
Definition compilation_context := list (ident * BeeTypes.type * string).
Definition context_growth (before after : compilation_context) : Prop :=
 incl before after /\ (NoDup(map unzip_ident before) -> NoDup(map unzip_ident after)).
Lemma context_growth_refl : forall ctx, context_growth ctx ctx.
Proof. unfold context_growth,incl; firstorder. Qed.
Lemma context_growth_trans : forall a b c,
 context_growth a b -> context_growth b c -> context_growth a c.
Proof. unfold context_growth,incl; firstorder. Qed.
Lemma context_growth_fresh : forall ctx id ty tag,
 ~In id(map unzip_ident ctx) -> context_growth ctx ((id,ty,tag)::ctx).
Proof. intros; split; [unfold incl; simpl; auto|]. simpl; intros; constructor; auto. Qed.
Lemma identifier_test_false : forall used id,
 in_idents id used=false -> ~In id used.
Proof.
 induction used as [|head rest IH]; intros id H; simpl in *; [tauto|].
 destruct(Pos.eq_dec id head); [discriminate|]. intros [E|Hin]; [congruence|exact (IH id H Hin)].
Qed.
Lemma actual_fresh_identifier : forall fuel used id tag g g' proof,
 fresh_ident used fuel g=Res(id,tag)g' proof -> ~In id used.
Proof.
 induction fuel as [|fuel IH]; intros used id tag g g' proof H;
 cbn [fresh_ident] in H;
 match type of H with context[if ?test then _ else _] => destruct test eqn:E end;
 cbn [error ret] in H; try discriminate.
 - inversion H; subst; eapply identifier_test_false; exact E.
 - eapply IH; exact H.
 - inversion H; subst; eapply identifier_test_false; exact E.
Qed.
Lemma reserved_exclusion_left : forall (used reserved : list ident) id,
 ~In id(used ++ reserved) -> ~In id used.
Proof. intros used reserved id H Hin; apply H,in_or_app; auto. Qed.
Lemma guarded_binop_context_growth : forall op es ces ty ctx bc g ce ctx' bc' g' ip,
 guarded_binop op es ces ty ctx bc g=Res(ce,ctx',bc')g' ip ->
 bc'=bc /\ context_growth ctx ctx'.
Proof.
 intros op es ces ty ctx bc g ce ctx' bc' g' ip Hrun.
 unfold guarded_binop, SimplExpr.bind2, SimplExpr.bind, SimplExpr.ret, SimplExpr.error in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
     let rec descend t := lazymatch t with
       | context[match ?inner with _ => _ end] => descend inner
       | _ => let E := fresh "Epart" in destruct t eqn:E
       end in descend scr;
     repeat match goal with p : (_ * _)%type |- _ => destruct p end;
     cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; split; try reflexivity.
 all: repeat match goal with
 | E : fresh_ident (seq.cat ?used ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof |- _ =>
 let HF := fresh "HF" in
 pose proof(reserved_exclusion_left used reserved id(actual_fresh_identifier _ _ _ _ _ _ _ E)) as HF; clear E
 end.
 all: match goal with |- context_growth _ (_ :: ?tail) => eapply context_growth_trans with (b:=tail) end; apply context_growth_fresh; assumption.
Qed.

Lemma fresh_compiler_binding_growth : forall source ty ctx bc g binding ctx' bc' g' ip,
 fresh_compiler_binding source ty ctx bc g=Res(binding,ctx',bc')g' ip ->
 context_growth ctx ctx' /\ reserved_identifiers bc'=reserved_identifiers bc.
Proof.
 intros * Hrun.
 unfold fresh_compiler_binding,SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E:=fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair:(_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; split; try reflexivity; try apply context_growth_refl.
 all: apply context_growth_fresh;
 match goal with E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?gf ?pi |- _ =>
 exact (reserved_exclusion_left used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) end.
Qed.

Lemma compiler_destination_growth : forall selected ty ctx bc g id ctx' g' ip,
 compiler_destination selected ty ctx bc g=Res(id,ctx')g' ip -> context_growth ctx ctx'.
Proof.
 intros * Hrun. unfold compiler_destination,SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E:=fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair:(_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; try apply context_growth_refl.
 all: apply context_growth_fresh;
 match goal with E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?gf ?pi |- _ =>
 exact (reserved_exclusion_left used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) end.
Qed.

Lemma fresh_compiler_fields_growth : forall fields ctx bc g bindings ctx' bc' g' ip,
 fresh_compiler_fields fields ctx bc g=Res(bindings,ctx',bc')g' ip ->
 context_growth ctx ctx' /\ reserved_identifiers bc'=reserved_identifiers bc.
Proof.
 induction fields as [|[field ty] fields IH]; intros * Hrun;
 cbn [fresh_compiler_fields] in Hrun;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 - inversion Hrun; split; [apply context_growth_refl|reflexivity].
 - destruct (fresh_compiler_binding field ty ctx bc g) as [msg|[[binding mid] scope] gm pm] eqn:Hbinding;
   cbn [fst snd] in Hrun; try discriminate.
   destruct (fresh_compiler_fields fields mid scope gm) as [msg|[[rest final] finalscope] gf pf] eqn:Hfields;
   cbn [fst snd] in Hrun; try discriminate.
   destruct binding; inversion Hrun; subst;
   destruct (fresh_compiler_binding_growth _ _ _ _ _ _ _ _ _ _ Hbinding) as [Gbinding Rbinding];
   destruct (IH _ _ _ _ _ _ _ _ Hfields) as [Gfields Rfields]; split.
   all: first [eapply context_growth_trans; eassumption | congruence].
Qed.

Definition expression_context_growth (e : BeePL.expr) :=
 forall ctx bctx g ce ctx' bctx' g' proof,
 transBeePL_expr_expr e ctx bctx g=Res(ce,ctx',bctx')g' proof -> context_growth ctx ctx'.
Lemma list_context_growth : forall es,
 (forall e, In e es -> expression_context_growth e) ->
 forall ctx bctx g ces ctx' bctx' g' proof,
 transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx g=
 Res(ces,ctx',bctx')g' proof -> context_growth ctx ctx'.
Proof.
 intros es; induction es as [|e rest IH]; intros Hall ctx bctx g ces ctx' bctx' g' proof H;
 cbn [transBeePL_expr_exprs] in H;
 unfold SimplExpr.bind2, SimplExpr.bind, SimplExpr.ret in H; cbn in H.
 - inversion H; subst; apply context_growth_refl.
 - destruct(transBeePL_expr_expr e ctx bctx g) as [msg|[[ce mid] bc] gm im] eqn:E;
   cbn in H; try discriminate.
   destruct(transBeePL_expr_exprs transBeePL_expr_expr rest mid bc gm)
   as [msg|[[cs final] bc'] gf ip] eqn:F; cbn in H; try discriminate.
   inversion H; subst. eapply context_growth_trans.
   + exact (Hall e (or_introl eq_refl) _ _ _ _ _ _ _ _ E).
   + eapply IH; [intros; apply Hall; simpl; auto|exact F].
Qed.

Ltac grow_collect :=
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

 | IH : expression_context_growth ?e,
   E : transBeePL_expr_expr ?e ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
     let K := fresh "Gchild" in
     pose proof (IH _ _ _ _ _ _ _ _ E) as K; clear IH
 | IH : forall child, In child ?es -> expression_context_growth child,
   E : transBeePL_expr_exprs transBeePL_expr_expr ?es ?ctx ?bc ?g=Res(?ces,?ctx',?bc') ?g' ?ip |- _ =>
     let K := fresh "Glist" in
     pose proof (list_context_growth es IH _ _ _ _ _ _ _ _ E) as K; clear IH
 end.
Ltac grow_solve :=
 grow_collect; cbn beta iota zeta in *;
 try solve [eauto 4 using context_growth_refl,context_growth_trans].

Theorem expression_translation_context_growth : forall e, expression_context_growth e.
Proof.
 intros e; induction e using expr_ind_rec;
 unfold expression_context_growth at 1; intros ctx bc g ce ctx' bc' g' ip Hrun;
 cbn [transBeePL_expr_expr] in Hrun;
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
 try (inversion Hrun; subst; clear Hrun; grow_solve).
all: repeat match goal with
 | E : fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof |- _ =>
 let Hfresh := fresh "Hfresh" in
 pose proof(reserved_exclusion_left used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) as Hfresh; clear E
 end.
all: try solve [eapply context_growth_trans; [eassumption|]; apply context_growth_fresh; assumption].
all: try solve [eauto 6 using context_growth_trans,context_growth_refl].
all: repeat match goal with
 | IH : forall child, In child ?es -> expression_context_growth child,
   E : transBeePL_expr_expr ?child ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
     let Hin := fresh "Hin" in assert (Hin : In child es) by (simpl; tauto);
     let K := fresh "Gbranch" in
     pose proof (IH child Hin _ _ _ _ _ _ _ _ E) as K; clear E
 end.
all: try solve [eauto 6 using context_growth_trans,context_growth_refl].
all: simpl in *.
all: lazymatch goal with
 | G : context_growth ((?id,?ty,?tag)::?locals) ?out |- _ =>
   assert (Hadded : context_growth locals ((id,ty,tag)::locals)) by
    (apply context_growth_fresh; intro Hpresent;
     match goal with Hn : ~_ |- _ => apply Hn end;
     right; apply in_or_app; left; exact Hpresent)
 end.
all: eauto 6 using context_growth_trans.
Qed.

Theorem expression_list_translation_context_growth : forall es ctx bc g ces ctx' bc' g' proof,
 transBeePL_expr_exprs transBeePL_expr_expr es ctx bc g=Res(ces,ctx',bc')g' proof ->
 context_growth ctx ctx'.
Proof. intros; eapply list_context_growth; [intros; apply expression_translation_context_growth|eassumption]. Qed.
Print Assumptions expression_translation_context_growth.
Print Assumptions expression_list_translation_context_growth.
