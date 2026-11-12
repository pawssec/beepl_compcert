(* Type annotations of successful expression translations. This is a structural
   compiler lemma, not a semantic simulation theorem. *)
Require Import String ZArith List AST Maps Integers BeeTypes BeePL Csyntax
  SimplExpr BeePL_Csyntax BeePL_compiler_bindings BeePL_type_equality.
From mathcomp Require Import all_ssreflect.

Lemma trans_cast_expression_type_checked : forall target operand,
  Csyntax.typeof (trans_cast_expression target operand) = transBeePL_type target.
Proof.
  intros target operand. destruct target; try reflexivity.
  match goal with pt : primitive_type |- _ => destruct pt; reflexivity end.
Qed.

Lemma assign_struct_fields_chain_type : forall base pairs tail ty,
  Csyntax.typeof tail = ty ->
  Csyntax.typeof (assign_struct_fields_chain base pairs tail ty) = ty.
Proof.
  intros base [|[field rhs] rest] tail ty H; simpl; auto.
Qed.

Local Opaque fresh_ident max_fresh unzip_ident fresh_compiler_binding resolve_compiler_storage.

Lemma guarded_binop_type_checked : forall op es ces ty ctx bc g ce ctx' bc' g' proof,
  guarded_binop op es ces ty ctx bc g = Res (ce,ctx',bc') g' proof ->
  Csyntax.typeof ce = transBeePL_type ty.
Proof.
  intros op es ces ty ctx bc g ce ctx' bc' g' proof H.
  unfold guarded_binop, SimplExpr.bind2, SimplExpr.bind, ret, error in H.
  repeat match type of H with
  | context [match ?scr with _ => _ end] =>
    let rec descend term := lazymatch term with
    | context [match ?inner with _ => _ end] => descend inner
    | _ => let E := fresh "Epart" in destruct term eqn:E
    end in descend scr;
    repeat match goal with pair : (_ * _)%type |- _ => destruct pair end;
    cbn beta iota zeta in H; try discriminate
  end;
  inversion H; subst; reflexivity.
Qed.

Lemma compilation_preserve_type_checked : forall e fctx bctx ce fctx' bctx' g g' i',
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
transBeePL_type (typeof_expr e) = Csyntax.typeof ce.
Proof.
move=> e. elim: e=> //=.
(* Val *)
+ move=> v t fctx bctx ce fctx' bctx' g g' i'.
  move=> [] h1 h2 h3 h4 /=; subst. by rewrite /Csyntax.typeof.
(* Var *)
+ move=> v t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  symmetry. apply compiler_bound_value_type. intros; destruct ty; reflexivity.
(* Const *)
+ move=> [].
  (* bool *)
  + move=> b t fctx bctx ce fctx' bctx' g g' i' [] h1 h2; subst.
    move: h1. case: ifP=> //=.
    + by move=> hb [] h; subst.
    by move=> hb [] h; subst.
  (* int *)
  + by move=> i t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  (* long *)
  + by move=> i t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  by move=> t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
(* Call *)
+ move=> e hin es t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he: (transBeePL_expr_expr e fctx bctx g) => [err | [[ce' fe] be] g1 i1] //=.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fe be) => [err' | [[ces' fes] bes] g2 i2] //=.
  by move=> [] h1 h2 h3 h4; subst.
(* builtin *)
+ move=> [].
  (* ref *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'.
    rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [err' | [[ces' fes] bes] g2 i2] //=.
    case hf: (fresh_ident ((List.map unzip_ident fes ++ reserved_identifiers bctx)%list) max_fresh g2)=> [ferr | fi gi ii] //=.
    case: es hes=> [ | e es'] //=. case: es'=> //=. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case he: (transBeePL_expr_expr e fctx bctx g) => [err | [[ce' fe] be] g1 i1] //=.
    move=> [] h1 h2 h3 h4; subst. case h: (ref_to_prim t gi)=> [err | tr gr ir] //=.
    by move=> [] h1 h2 h3 h4 /=; subst.
  (* deref *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'.
    rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    by move=> [] h1 h2 h3 h4; subst.
  (* massgn: the store is pointee-typed; the outer cast retains the source
     annotation, which is Utype for every well-typed assignment. *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'.
    rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    case hptr: (Csyntax.typeof (hd default_expr (exprlist_list_expr ces')))
      => [|sz sg ca|sg ca|sz ca|target ca|elem len ca|args rt cc|id ca|id ca] //=.
    by move=> [] h1 h2 h3 h4;subst.
  (* uop *)
  + move=> u es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    by move=> [] h1 h2 h3 h4; subst.
  (* guarded operators retain the annotation while capturing their operands *)
  + move=> u es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g1 i1] //=.
    destruct u; cbn; intro H;
      try solve [inversion H; subst; reflexivity];
      match type of H with
      | context [guarded_binop ?op ?args ?translated ?ty ?locals ?bc ?gen] =>
        destruct (guarded_binop op args translated ty locals bc gen)
          as [msg|[[guarded locals'] bc'] gf proof] eqn:HG
      end; cbn in H; try discriminate;
      inversion H; subst; symmetry; eapply guarded_binop_type_checked; exact HG.
  (* Cast *)
  move=> t es t' fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g3 i3] //=.
  move=> [] h1 h2 h3 h4; subst. symmetry. apply trans_cast_expression_type_checked.
  (* Array read *)
  move=> n es t fctx bctx ce fctx' bctx' g g' i'.
  case: es=> [|e es] //=. case: es=> [|e2 es] //=.
  rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case hl: (get_array_len (typeof_expr e) g)=> [errlen|len gl il] //=.
  case: ifP=> //= hn.
  case he: (transBeePL_expr_expr e fctx bctx gl)=> [err|[[ce1 fc] bc] g1 i1] //=.
  by move=> [] h1 h2 h3 h4; subst.
(* Bind *)
+ move=> x t e hin e' hin' t' fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case hf: (fresh_compiler_binding x t fctx bctx g)
    => [err|[binding scope] g0 i0] //=.
  case he: (transBeePL_expr_expr e (snd binding) bctx g0)
    => [err|[[ce1 fc1] rhs_ctx] g1 i1] //=.
  case he': (transBeePL_expr_expr e' fc1 scope g1)
    => [err|[[ce2 fc2] body_ctx] g2 i2] //=.
  by move=> [] h1 h2 h3 h4; subst.
(* Cond *)
+ move=> e1 hin1 e2 hin2 e3 hin3 t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he1: (transBeePL_expr_expr e1 fctx bctx g)=> [err1 | ce1 g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1) => [err2 | ce2 g2 i2] //=.
  case he3: (transBeePL_expr_expr e3 ce2.1.2 ce2.2 g2) => [err3 | ce3 g3 i3] //=.
  by move=> [] h1 h2 h3 h4; subst.
(* Unit *)
+ move=> t fctx bctx ce fctx' bctx' g g' i'. by move=> [] h1 h2 h3 h4; subst.
(* Sinit *)
+ move=> sid fields es t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)
    => [err | [[ces fc] bc] g1 i1] //=.
  case hf: (fresh_ident ((List.map unzip_ident fc ++ reserved_identifiers bctx)%list) max_fresh g1)
    => [err | [tmp tag] g2 i2] //=.
  case: t=> //=.
  - move=> [] //= [] //= sid' attrs pattrs [] h1 h2 h3 h4; subst.
    symmetry; apply assign_struct_fields_chain_type; reflexivity.
  - move=> sid' attrs [] h1 h2 h3 h4; subst.
    symmetry; apply assign_struct_fields_chain_type; reflexivity.
(* Sfield *)
+ move=> e hin field t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he: (transBeePL_expr_expr e fctx bctx g)
    => [err | [[ce1 fc] bc] g1 i1] //=.
  case: (typeof_expr e)=> //=.
  - move=> [] //=.
    * move=> [] //= sid attrs pattrs [] h1 h2 h3 h4; subst; reflexivity.
    * move=> [] //= [] //= sid attrs pattrs [] h1 h2 h3 h4; subst; reflexivity.
  - by move=> sid attrs [] h1 h2 h3 h4; subst.
(* None *)
+ move=> t fctx bctx ce fctx' bctx' g g' i'. case: t=> //= p.
  case: ifP=> //= hot. move=> [] h1 h2 h3 h4 /=; subst.
  by rewrite /Csyntax.typeof /=.
(* Some *)
+ move=> e hin t fctx bctx ce fctx' bctx' g g' i'.
  case: t=> //= p. case: p=> //= p.
  case: ifP=> //= ht he.
  have heq := eq_type_sound _ _ ht.
  have htype := hin fctx bctx ce fctx' bctx' g g' i' he.
  by rewrite heq in htype.
(* Match *)
+ move=> e hin ps es t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he: (transBeePL_expr_expr e fctx bctx g)
    => [err | [[ce1 fc] bc] g1 i1] //=.
  case: (typeof_expr e)=> //= p.
  case: ifP=> //= ho.
  case hi: (inner_ptr_of_option p g1)=> [err | inner g2 i2] //=.
  case: ps=> [|pat ps] //=. case: pat=> //=.
  - case: ps=> [|pat ps] //=. case: pat=> //= x.
    case: ps=> [|pat ps] //=. case: es=> [|e1 es] //=.
    case: es=> [|e2 es] //=. case: es=> [|e3 es] //=.
    match goal with
    | |- context [fresh_ident ?ids ?bound g2] =>
      case hf: (fresh_ident ids bound g2)=> [err | [tmp tag] gt it] //=
    end.
    case hn: (transBeePL_expr_expr e1 ((tmp, Ptrtype p, tag) :: fc) bc gt)
      => [err | [[cn fn] bn] g3 i3] //=.
    case hb: (fresh_compiler_binding x (Ptrtype inner) fn bn g3)
      => [err|[binding scope] gb ib] //=.
    case hs: (transBeePL_expr_expr e2 (snd binding) scope gb)
      => [err | [[cs fs] bs] g4 i4] //=.
    by move=> [] h1 h2 h3 h4; subst.
  - move=> x. case: ps=> [|pat ps] //=. case: pat=> //=.
    case: ps=> [|pat ps] //=. case: es=> [|e1 es] //=.
    case: es=> [|e2 es] //=. case: es=> [|e3 es] //=.
    match goal with
    | |- context [fresh_ident ?ids ?bound g2] =>
      case hf: (fresh_ident ids bound g2)=> [err | [tmp tag] gt it] //=
    end.
    case hn: (transBeePL_expr_expr e2 ((tmp, Ptrtype p, tag) :: fc) bc gt)
      => [err | [[cn fn] bn] g3 i3] //=.
    case hb: (fresh_compiler_binding x (Ptrtype inner) fn bn g3)
      => [err|[binding scope] gb ib] //=.
    case hs: (transBeePL_expr_expr e1 (snd binding) scope gb)
      => [err | [[cs fs] bs] g4 i4] //=.
    by move=> [] h1 h2 h3 h4; subst.
(* Bytes *)
+ move=> es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  by case he: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [err | ce' g1 i1] //=.
move=> h t n t' fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind /=.
case hr: (resolve_compiler_storage bctx h g) => [err|target gr ir] //=.
case ha: (get_array_len t gr)=> [err | an g1 i1] //=. case: ifP=> //= hn.
by move=> [] h1 h2 h3 h4; subst.
Qed.

Print Assumptions compilation_preserve_type_checked.
