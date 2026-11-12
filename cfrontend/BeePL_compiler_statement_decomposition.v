(* Exact inversion for selected actual statement translations. Other cases
   retain the legacy specification's explicitly unclaimed True branch. *)
Require Import String ZArith Integers AST Maps Coqlib Errors Ctypes Csyntax
  Csyntaxdefs SimplExpr BeeTypes BeePL BeePL_Csyntax BeePL_values.
From mathcomp Require Import all_ssreflect.

Theorem statement_translation_decomposition: forall bcmp e fctx bctx (ct:Csyntax.statement) f b g g' i',
transBeePL_expr_st bcmp e fctx bctx g = Res (ct, f, b) g' i' ->
match e with
| Val v t => ct = Csyntax.Sreturn (Some (Eval (trans_bvalue_cvalue v) (transBeePL_type t)))
             /\ f = fctx /\ b = bctx
| Var x t => ct = Csyntax.Sreturn (Some (trans_bound_variable bctx x t))
             /\ f = fctx /\ b = bctx
| Const (ConsInt i) t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint i) (transBeePL_type t)))
                         /\ f = fctx /\ b = bctx
| Const (ConsLong i) t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vlong i) (transBeePL_type t)))
                         /\ f = fctx /\ b = bctx
| Const ConsUnit t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)))
                      /\ f = fctx /\ b = bctx
| Const (ConsBool bo) t => if eqb bo true
                          then ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 1)) (transBeePL_type t)))
                               /\ f = fctx /\ b = bctx
                          else ct =  Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)))
                               /\ f = fctx /\ b = bctx
| Prim Deref es t => exists ces g1 i1,
                     transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                     ct = Csyntax.Sreturn (Some (Evalof (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)) (transBeePL_type t)))
| Prim Massgn es t => exists ces g1 i1 target attr,
                      transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                      Csyntax.typeof (hd default_expr (exprlist_list_expr ces)) = Ctypes.Tpointer target attr /\
                      ct = Csyntax.Sdo
                        (Csyntax.Eassign (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) target)
                          (hd default_expr (tl (exprlist_list_expr ces))) target)
| Prim (Uop o) es t => exists ces g1 i1,
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                       ct = Csyntax.Sreturn (Some (Csyntax.Eunop o
                                     (hd default_expr (exprlist_list_expr ces))
                                     (transBeePL_type t)))
| Prim (Bop o) es t => exists ces fctx1 bctx1 g1 i1,
    transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g =
      Res(ces,fctx1,bctx1)g1 i1 /\
    match o with
    | Cop.Odiv | Cop.Omod | Cop.Oshl | Cop.Oshr =>
        exists guarded i2,
          guarded_binop o es ces t fctx1 bctx1 g1=Res(guarded,f,b)g' i2 /\
          ct=Csyntax.Sreturn(Some guarded)
    | _ => ct=Csyntax.Sreturn(Some(Csyntax.Ebinop o
        (hd default_expr(exprlist_list_expr ces))
        (hd default_expr(tl(exprlist_list_expr ces)))(transBeePL_type t))) /\
        f=fctx1 /\ b=bctx1
    end
| _ => True
end.
Proof.
  move=> bcmp e fctx bctx ct f b g g' i' H.
  destruct e; try exact I.
  - cbn [transBeePL_expr_st ret] in H. inversion H; subst; auto.
  - cbn [transBeePL_expr_st ret] in H. inversion H; subst; auto.
  - destruct c; cbn [transBeePL_expr_st ret] in H;
      try (inversion H; subst; auto).
    destruct b0; inversion H; subst; simpl; auto.
  - match type of H with
    | context [Prim ?op ?operands ?ty] =>
      rename operands into args0; rename ty into ty0; destruct op
    end; try exact I.
    + cbn [transBeePL_expr_st] in H.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr args0 fctx bctx g) H
        => [err | [[ces locals] context] g1 i1] //=.
      move=> [] h1 h2 h3 h4; subst. exists ces,g',i1; auto.
    + cbn [transBeePL_expr_st] in H.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr args0 fctx bctx g) H
        => [err | [[ces locals] context] g1 i1] //=.
      case hptr: (Csyntax.typeof(hd default_expr(exprlist_list_expr ces)))
        => [|sz sg ca|sg ca|sz ca|target ca|elem len ca|args rt cc|id ca|id ca] //=.
      move=> [] h1 h2 h3 h4; subst. exists ces,g',i1,target,ca; auto.
    + cbn [transBeePL_expr_st] in H.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr args0 fctx bctx g) H
        => [err | [[ces locals] context] g1 i1] //=.
      move=> [] h1 h2 h3 h4; subst. exists ces,g',i1; auto.
    + cbn [transBeePL_expr_st] in H.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr args0 fctx bctx g) H
        => [err | [[ces locals] context] g1 i1] //=.
      match goal with | |- context [match ?op with Cop.Oadd => _ | _ => _ end] => destruct op end.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * case hg: (guarded_binop Cop.Odiv args0 ces ty0 locals context g1)
          => [err | [[guarded finalctx] finalbc] g2 i2] //=.
        move=> [] h1 h2 h3 h4; subst.
        exists ces,locals,context,g1,i1; split; [reflexivity|].
        exists guarded,i2; auto.
      * case hg: (guarded_binop Cop.Omod args0 ces ty0 locals context g1)
          => [err | [[guarded finalctx] finalbc] g2 i2] //=.
        move=> [] h1 h2 h3 h4; subst.
        exists ces,locals,context,g1,i1; split; [reflexivity|].
        exists guarded,i2; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * case hg: (guarded_binop Cop.Oshl args0 ces ty0 locals context g1)
          => [err | [[guarded finalctx] finalbc] g2 i2] //=.
        move=> [] h1 h2 h3 h4; subst.
        exists ces,locals,context,g1,i1; split; [reflexivity|].
        exists guarded,i2; auto.
      * case hg: (guarded_binop Cop.Oshr args0 ces ty0 locals context g1)
          => [err | [[guarded finalctx] finalbc] g2 i2] //=.
        move=> [] h1 h2 h3 h4; subst.
        exists ces,locals,context,g1,i1; split; [reflexivity|].
        exists guarded,i2; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
      * move=> [] h1 h2 h3 h4; subst.
        exists ces,f,b,g',i1; auto.
Qed.
Print Assumptions statement_translation_decomposition.
