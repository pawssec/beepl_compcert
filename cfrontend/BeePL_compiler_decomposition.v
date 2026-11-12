(* Checked inversion of successful translation for the constructor cases listed
   below. Cases mapped to True impose no decomposition claim. This lemma is
   structural; semantic preservation is a separate proof obligation. *)
Require Import String ZArith Integers AST Maps Coqlib Errors Ctypes Csyntax
  Csyntaxdefs SimplExpr BeeTypes BeePL BeePL_Csyntax BeePL_values.

From mathcomp Require Import all_ssreflect.
Local Opaque fresh_compiler_binding resolve_compiler_storage.

Lemma expression_translation_decomposition:
(forall e fctx bctx ce f b g g' i',
transBeePL_expr_expr e fctx bctx g = Res (ce, f, b) g' i' ->
match e with
| Val v t => ce = Eval (trans_bvalue_cvalue v) (transBeePL_type t)
             /\ f = fctx /\ b = bctx
| Var x t => ce = trans_bound_variable bctx x t
             /\ f = fctx /\ b = bctx
| Const (ConsInt i) t => ce = Eval (Values.Vint i) (transBeePL_type t)
                         /\ f = fctx /\ b = bctx
| Const (ConsLong i) t => ce = Eval (Values.Vlong i) (transBeePL_type t)
                         /\ f = fctx /\ b = bctx
| Const ConsUnit t => ce = Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
                      /\ f = fctx /\ b = bctx
| Const (ConsBool bo) t => if eqb bo true
                          then ce = Eval (Values.Vint (Int.repr 1)) (transBeePL_type t)
                               /\ f = fctx /\ b = bctx
                          else ce = Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
                               /\ f = fctx /\ b = bctx
| App e es t => exists g1 i1 i2 fce fctx' bctx' ces fctx'' bctx'',
                transBeePL_expr_expr e fctx bctx g = Res (fce, fctx', bctx') g1 i1 /\
                transBeePL_expr_exprs transBeePL_expr_expr es fctx' bctx' g1 = Res (ces, fctx'', bctx'') g' i2 /\
                ce = Ecall fce ces (transBeePL_type t) /\ f = fctx'' /\ b = bctx''
| Prim Ref es t => exists (ces: exprlist) (fctx':seq (ident * type * string)) (bctx': bcompiler_ctx)
                    (i : ident) (pty : type) (str : string) (fctx'': seq (ident * type * string)) (g1: generator)
                    (i1: Ple (gen_next g) (gen_next g1)) (g2: generator) (i2 : Ple (gen_next g1) (gen_next g2))
                    (i3 : Ple (gen_next g2) (gen_next g')) ct,
                   transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, fctx', bctx') g1 i1 /\ Zlength es = 1 /\
                   fresh_ident ((List.map unzip_ident fctx' ++ reserved_identifiers bctx)%list) max_fresh g1 = Res (i, str) g2 i2 /\
                   ref_to_prim t g2 = Res pty g' i3 /\ ct = (transBeePL_type t) /\
                   ce = Ecomma (Eassign (Csyntax.Evar i (transBeePL_type pty)) (hd default_expr (exprlist_list_expr ces)) (transBeePL_type pty))
                                        (Csyntax.Eaddrof (Csyntax.Evar i (transBeePL_type pty)) ct) ct /\
                   f = (i, pty, str) :: fctx' /\ b = bctx'
| Prim Deref es t => exists ces g1 i1,
                     transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                     ce = Evalof (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)) (transBeePL_type t)
| Prim Massgn es t => exists ces g1 i1 target attr,
                      transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                      Csyntax.typeof (hd default_expr (exprlist_list_expr ces)) = Ctypes.Tpointer target attr /\
                      ce = Csyntax.Ecast
                        (Csyntax.Eassign (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) target)
                          (hd default_expr (tl (exprlist_list_expr ces))) target) (transBeePL_type t)
| Prim (Uop o) es t => exists ces g1 i1,
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                       ce = (Csyntax.Eunop o (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t))
| Prim (Bop o) es t => exists ces fctx1 bctx1 g1 i1,
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g =
                         Res (ces, fctx1, bctx1) g1 i1 /\
                       match o with
                       | Cop.Odiv | Cop.Omod | Cop.Oshl | Cop.Oshr =>
                           exists i2, guarded_binop o es ces t fctx1 bctx1 g1 =
                             Res (ce,f,b) g' i2
                       | _ => ce = Csyntax.Ebinop o (hd default_expr (exprlist_list_expr ces))
                                     (hd default_expr (tl (exprlist_list_expr ces)))
                                     (transBeePL_type t) /\ f=fctx1 /\ b=bctx1
                       end
| Prim (Cast t) es t' => exists ces g1 i1,
                         transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                         ce = trans_cast_expression t (hd default_expr (exprlist_list_expr ces))
| Bind x t e1 e2 t' => exists binding scope g0 i0 ce1 fctx1 rhs_ctx g1 i1 ce2 body_ctx g2 i2,
    fresh_compiler_binding x t fctx bctx g = Res (binding,scope) g0 i0 /\
    transBeePL_expr_expr e1 (snd binding) bctx g0 = Res (ce1,fctx1,rhs_ctx) g1 i1 /\
    transBeePL_expr_expr e2 fctx1 scope g1 = Res (ce2,f,body_ctx) g2 i2 /\
    ce = Ecomma (match fst binding with
      | Some target => Eassign (Evar target (transBeePL_type t)) ce1 (transBeePL_type t)
      | None => ce1 end) ce2 (transBeePL_type t') /\ b = bctx
| Cond e1 e2 e3 t => exists ce1 fctx1 bctx1 g1 i1 ce2 fctx2 bctx2 g2 i2 ce3 g3 i3,
                     transBeePL_expr_expr e1 fctx bctx g = Res (ce1, fctx1, bctx1) g1 i1 /\
                     transBeePL_expr_expr e2 fctx1 bctx1 g1 = Res (ce2, fctx2, bctx2) g2 i2 /\
                     transBeePL_expr_expr e3 fctx2 bctx2 g2 = Res (ce3, f, b) g3 i3 /\
                     ce = Econdition ce1 ce2 ce3 (transBeePL_type t)
| Unit t => ce = Eval (trans_bvalue_cvalue Vunit) (transBeePL_type t) /\ f = fctx /\ b = bctx
| Sinit sid fnames es t => match t with
                           | BeeTypes.Stype sid' attrs =>
                             exists ces f1 b1 g1 i1 tmp tag g2 i2,
                             transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f1, b1) g1 i1 /\
                             fresh_ident ((List.map unzip_ident f1 ++ reserved_identifiers bctx)%list) max_fresh g1 = Res (tmp, tag) g2 i2 /\
                             ce = assign_struct_fields_chain (Csyntax.Evar tmp (Ctypes.Tstruct sid' attrs))
                                                             (combine fnames (exprlist_list_expr ces))
                                                             (Evalof (Csyntax.Evar tmp (Ctypes.Tstruct sid' attrs)) (Ctypes.Tstruct sid' attrs))
                                                             (Ctypes.Tstruct sid' attrs) /\
                             f = (tmp, BeeTypes.Stype sid' attrs, tag) :: f1 /\ b = b1
                           | BeeTypes.Ptrtype (BeeTypes.Reftype (BeeTypes.Bstruct sid' attrs) pattrs) =>
                             exists ces f1 b1 g1 i1 tmp tag g2 i2,
                             transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f1, b1) g1 i1 /\
                             fresh_ident ((List.map unzip_ident f1 ++ reserved_identifiers bctx)%list) max_fresh g1 = Res (tmp, tag) g2 i2 /\
                             ce = assign_struct_fields_chain (Csyntax.Evar tmp (Ctypes.Tstruct sid' attrs))
                                                             (combine fnames (exprlist_list_expr ces))
                                                             (Csyntax.Eaddrof (Csyntax.Evar tmp (Ctypes.Tstruct sid' attrs))
                                                                      (Ctypes.Tpointer (Ctypes.Tstruct sid' attrs) pattrs))
                                                             (Ctypes.Tpointer (Ctypes.Tstruct sid' attrs) pattrs) /\
                             f = (tmp, BeeTypes.Stype sid' attrs, tag) :: f1 /\ b = b1
                           | _ => False
                            end
| Addr _ _ _  => False
| _ => True
end) /\
(forall es fctx bctx ces f b g g' i',
 transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g' i' ->
 match es with
 | nil => ces = Enil /\ f = fctx /\ b = bctx
 | e :: es => exists ce f' b' g1 i1 i2 ce' f'' b'',
              transBeePL_expr_expr e fctx bctx g = Res (ce, f', b') g1 i1 /\
              transBeePL_expr_exprs transBeePL_expr_expr es f' b' g1 = Res (ce', f'', b'') g' i2 /\
              ces = Econs ce ce' /\ f = f'' /\ b = b''
end).
Proof.
split.
+ move=> e fctx bctx ce f b g g' i'. elim: e.
  + move=> v t /=. by move=> [] h1 h2 h3 h4; subst.
  + move=> x t /= [] h1 h2 h3 h4; subst;split=> //=.
  + move=> c t /=. case: c=> //=.
    + move=> bo []. case: ifP=> //=.
      + move=> heq [] h1 h2 h3 h4; subst. by case: bo heq=> //=.
      move=> heq [] h1 h2 h3 h4; subst. by case: bo heq=> //=.
    + by move=> i [] h1 h2 h3 h4; subst.
    + by move=> i [] h1 h2 h3 h4; subst.
    by move=> [] h1 h2 h3 h4; subst.
  + move=> e hin es t h. inversion h.
    rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
    case he: (transBeePL_expr_expr e fctx bctx g) H0=> [err |re g1 i1] //=.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es re.1.2 re.2 g1)=> [errs | res g2 i2] //=.
    move=> [] h1 h2 h3 h4; subst. have i3 := Ple_trans (gen_next g) (gen_next g1) (gen_next g') i1 i2.
    exists g1, i1, i2, re.1.1, re.1.2, re.2, res.1.1, res.1.2, res.2. split=> //=.
    + by case: (re) => [[a b] c].
    rewrite hes /=. split=> //=. by case: (res)=> [[a b] c].
  + move=> b'. case: b'.
    (* ref *)
    + move=> es t h. Local Opaque fresh_ident max_fresh unzip_ident. inversion h.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | res g1 i1] //=.
      case hfr: (fresh_ident ((List.map unzip_ident res.1.2 ++ reserved_identifiers bctx)%list) max_fresh g1) => [err | fr g2 i2] //=.
      case es=> //= e es'. case: es'=> //=. case htr : (ref_to_prim t g2) => [err1 | tr g3 i3] //=.
      move=> [] h1 h2 h3 h4; subst. exists res.1.1, res.1.2, res.2, fr.1, tr, fr.2. eexists. auto.
      exists g1, i1, g2, i2, i3, (transBeePL_type t).
      by case: res h hes hfr=> [[a b] c]; subst; case: fr=> [f1 f2];split=> //=.
   (* deref *)
   + move=> es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1. by case: (ces)=> [[a b] c]; split=> //=.
   (* massgn: successful translation certifies the actual pointee type. *)
   + move=> es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     case hptr: (Csyntax.typeof (hd default_expr (exprlist_list_expr ces.1.1)))
       => [|sz sg ca|sg ca|sz ca|target ca|elem len ca|args rt cc|id ca|id ca] //=.
     move=> [] h1 h2 h3 h4; subst.
     exists ces.1.1, g', i1, target, ca. split.
     * by case: (ces) hes hptr => [[a b] c] //=.
     * split=> //=.
   (* uop *)
   + move=> uop es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1. split=> //=.
     by case: (ces)=> [[a b] c] //=.
   (* Guarded operations allocate capture locals; retain their exact helper
      execution instead of equating operand contexts with final contexts. *)
   + move=> bop es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     case: bop h=> //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + case hg: (guarded_binop Cop.Odiv es ces.1.1 t ces.1.2 ces.2 g1)
         => [errg | [[out newctx] newbc] g2 i2] //=.
       move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g1, i1; split.
       * by case: (ces) hes => [[aa bb] cc] //=.
       * exists i2; exact hg.
     + case hg: (guarded_binop Cop.Omod es ces.1.1 t ces.1.2 ces.2 g1)
         => [errg | [[out newctx] newbc] g2 i2] //=.
       move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g1, i1; split.
       * by case: (ces) hes => [[aa bb] cc] //=.
       * exists i2; exact hg.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + case hg: (guarded_binop Cop.Oshl es ces.1.1 t ces.1.2 ces.2 g1)
         => [errg | [[out newctx] newbc] g2 i2] //=.
       move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g1, i1; split.
       * by case: (ces) hes => [[aa bb] cc] //=.
       * exists i2; exact hg.
     + case hg: (guarded_binop Cop.Oshr es ces.1.1 t ces.1.2 ces.2 g1)
         => [errg | [[out newctx] newbc] g2 i2] //=.
       move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g1, i1; split.
       * by case: (ces) hes => [[aa bb] cc] //=.
       * exists i2; exact hg.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
     + move=> h [] h1 h2 h3 h4; subst.
       exists ces.1.1, ces.1.2, ces.2, g', i1.
       by case: (ces) hes => [[aa bb] cc] //=.
  (* cast *)
  move=> t es t' hte. inversion hte; subst.
  rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
  move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1; split=> //=. by case: (ces)=> [[a b] c].
  (* Internal array reads are outside this decomposition specification. *)
  by move=> n es t hte.
(* Bind: retain actual fresh storage and lexical scope, including unit/discard. *)
+ move=> x t e1 hte1 e2 hte2 t' hte.
  cbn [transBeePL_expr_expr] in hte.
  rewrite /SimplExpr.bind2 /SimplExpr.bind in hte.
  case hf: (fresh_compiler_binding x t fctx bctx g) hte
    => [err|[binding scope] g0 i0] //=.
  case he1: (transBeePL_expr_expr e1 (snd binding) bctx g0)
    => [err|[[ce1 fc1] rhs_ctx] g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 fc1 scope g1)
    => [err|[[ce2 fc2] body_ctx] g2 i2] //=.
  move=> [] h1 h2 h3 h4; subst.
  exists binding,scope,g0,i0,ce1,fc1,rhs_ctx,g1,i1,ce2,body_ctx,g',i2.
  repeat split; try reflexivity; assumption.
(* cond *)
+ move=> e1 hte1 e2 hte2 e3 hte3 t hte. inversion hte; subst.
  move: H0. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he1: (transBeePL_expr_expr e1 fctx bctx g) => [err1 | ce1 g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1) => [err2 | ce2 g2 i2] //=.
  case he3: (transBeePL_expr_expr e3 ce2.1.2 ce2.2 g2) => [err3 | ce3 g3 i3] //=.
  move=> [] h1 h2 h3 h4; subst. exists ce1.1.1, ce1.1.2, ce1.2, g1, i1, ce2.1.1, ce2.1.2, ce2.2.
  exists g2, i2, ce3.1.1, g', i3. split=> //=.
  + by case: (ce1)=> [[a b] c].
  split=> //=.
  + by case: (ce2) he2=> [[a b] c].
  split=> //=. by case: (ce3) he3=> [[a b] c].
(* unit *)
+ move=> t hte. by inversion hte; subst.
(* addr *)
+ by auto.
(* sinit *)
+ move=> i ls l' t hte. inversion hte; subst.
  move: H0. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case hes : (transBeePL_expr_exprs transBeePL_expr_expr l' fctx bctx g)=> [errs | [[ces f1] b1] g1 i1] //=.
  case hf : (fresh_ident ((List.map unzip_ident f1 ++ reserved_identifiers bctx)%list) max_fresh g1)=> [errf | [fv f2] g2 i2] //=.
  case: t hte=> //=.
  + move=> p /=; case: p=> //= b' a'; case: b'=> //= h' a''.
    rewrite /SimplExpr.bind2 /SimplExpr.bind. rewrite hes /= hf /=. move=> [] h1 h2 h3 h4 [] h5 h6 h7 h8; subst.
    by exists ces, f1, b, g1, i1, fv, f2, g', i2; split=> //=.
  move=> h' a. rewrite /SimplExpr.bind2 /SimplExpr.bind. rewrite hes /= hf /=.
  move=> [] h1 h2 h3 h4 [] h5 h6 h7 h8; subst.
  by exists ces, f1, b, g1, i1, fv, f2, g', i2; split=> //=.

all: try solve [intros; exact I].
move=> es fctx bctx ces f b g g' i'.
case: es=> [|e es] /=.
- by move=> [] h1 h2 h3 h4; subst.
- rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he: (transBeePL_expr_expr e fctx bctx g)
    => [err | [[ce fc] bc] g1 i1] //=.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fc bc g1)
    => [err | [[tail ft] bt] g2 i2] //=.
  move=> [] h1 h2 h3 h4; subst.
  exists ce, fc, bc, g1, i1, i2, tail, f, b.
  repeat split; assumption.
Qed.
Print Assumptions expression_translation_decomposition.
