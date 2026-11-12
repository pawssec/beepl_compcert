Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct. 
Require Import BeePL_Check_Reserved_Struct BeePL_alpha_renaming.
Require Import BeePL_Wrapper_Pass.
Require Import BeePL_escape_check BeePL_representation_check BeePL_compiler_bindings.
From mathcomp Require Import ssreflect seq. 


Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(**** BeePL Compiler *****)

Record bcompiler_ctx := { arg_ctx : list (ident * type);
                          benv : bcomposite_env;
                          reserved_identifiers : list ident;
                          lexical_bindings : compiler_bindings; }.

Definition max_fresh : nat := 1000%nat.

(* BeePL Bool uses a uint8 representation. Preserve its cast-then-truncate
   policy, then canonicalize the resulting byte to the encoded Bool 0 or 1.
   The operand occurs once, including when it has effects. *)
Definition trans_cast_expression (target : BeeTypes.type) (operand : Csyntax.expr) : Csyntax.expr :=
  let ct := transBeePL_type target in
  match target with
  | Vtype Tbool =>
      Ecast (Ebinop Cop.One (Ecast operand ct)
        (Eval (Values.Vint Int.zero) ct)
        (Ctypes.Tint I32 Signed noattr)) ct
  | _ => Ecast operand ct
  end.


(* Source variables denote values. Csyntax separates reading a location from
   naming it; unit has no readable storage and is represented directly. *)
Definition trans_variable_rvalue (id : ident) (ty : BeeTypes.type) : Csyntax.expr :=
  match ty with
  | Utype => Eval (trans_bvalue_cvalue Vunit) (transBeePL_type ty)
  | _ => Evalof (Evar id (transBeePL_type ty)) (transBeePL_type ty)
  end.


Definition with_compiler_bindings (ctx : bcompiler_ctx) (bindings : compiler_bindings)
    : bcompiler_ctx :=
 {| arg_ctx := arg_ctx ctx; benv := benv ctx;
    reserved_identifiers := reserved_identifiers ctx;
    lexical_bindings := bindings |}.

Definition trans_bound_variable (ctx : bcompiler_ctx) (source : ident)
    (ty : BeeTypes.type) : Csyntax.expr :=
  compiler_bound_value trans_variable_rvalue ctx.(lexical_bindings) source ty.

Definition resolve_compiler_storage (ctx : bcompiler_ctx) (source : ident) : mon ident :=
  match compiler_bound_storage ctx.(lexical_bindings) source with
  | Some target => ret target
  | None => error (msg "COMPILER ERROR: Unit binding has no addressable storage")
  end.


(* ------------------------------------------------------------------ *)
(* Renaming environment                                                *)
(* ------------------------------------------------------------------ 

Definition renv := PTree.t ident.

Definition resolve (ρ : renv) (x : ident) : ident :=
  match PTree.get x ρ with Some y => y | None => x end.

Definition extend (ρ : renv) (x cx : ident) : renv :=
  PTree.set x cx ρ.*)

Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> list (ident * BeeTypes.type * string) -> bcompiler_ctx ->
mon (Csyntax.expr * list (ident * BeeTypes.type * string) * bcompiler_ctx).


(* Translates list of BeePL expressions to list of C expressions *)
Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.exprlist * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
match es with 
| nil => ret (Enil, fn_ctx, bctx) 
| e :: es => do (ce, fn_ctx') <- transBeePL_expr_expr e fn_ctx bctx;
             do (ces, fn_ctx'') <- transBeePL_expr_exprs es (snd ce) fn_ctx';
             ret ((Econs (fst ce) (fst ces)), snd ces, fn_ctx'')
end.

End transBeePL_exprs.


Fixpoint exprlist_list_expr (es: Csyntax.exprlist) : list expr :=
match es with 
| Enil => nil 
| Econs e1 es => (e1 :: exprlist_list_expr es)
end.

Definition return_czero (t : Ctypes.type) : mon Values.val :=
match t with 
| Tvoid => error (msg "Tvoid not allowed")
| Ctypes.Tint sz s a => ret (Values.Vint (Int.repr 0))
| Ctypes.Tlong s a => ret (Values.Vlong (Int64.repr 0))
| Tfloat sz a => error (msg "Tfloat not allowed")
| Tpointer t a => error (msg "Tpointer not allowed")
| Tarray t z a => error (msg "Tarray not allowed")
| Tfunction ts t cc => error (msg "Tfunction not allowed")
| Tstruct h a => error (msg "Tstruct not allowed")
| Tunion h a => error (msg "Tunion not allowed")
end.

Definition default_expr := (Eval (Values.Vint (Int.repr 0)) Tvoid).

(* This function exists to handle creating fresh variables for converting Ref to
   CompCert C. 

   Ex) ref(4) => int __fresh; __fresh = 4; &__fresh; 
   
   FIXME: There really shouldn't be a limited number of fresh identifiers *)

Fixpoint in_idents (x : positive) (l : seq positive) : bool :=
  match l with
  | [::] => false
  | y :: ys => if Pos.eq_dec x y then true else in_idents x ys
  end.

Fixpoint fresh_ident (used : list ident) (n : nat) : mon (ident * string) :=
  let candidate_str := "__fresh__" ++ NilZero.string_of_uint (Nat.to_uint n) in
  let candidate := ident_of_string candidate_str in
  if in_idents candidate used then
    match n with
    | O => error (msg "Ran out of fresh identifiers")
    | S n' => fresh_ident used n'
    end
  else
    ret (candidate, candidate_str).

(* These are helpers to deal with fn_ctx in transBeePL_expr_expr and transBeePL_expr_st *)
Definition unzip_ident {A B C} (p : A * B * C) : A :=
  match p with
  | (x, _, _) => x
  end.

Definition unzip_str {A B C} (p : A * B * C) : C :=
match p with
| (_, _, z) => z
end.

Definition unzip_type {A B C} (p : A * B * C) : B :=
match p with
| (_, y, _) => y
end.


(* Allocate storage at a lexical introduction, never from the source-name
   storage catalogue. Unit binders need no C local. The spelling "_" is a
   regular source identifier and may be referenced, so it follows the same
   allocation rule as any other nonunit binding. *)
Definition fresh_compiler_binding (source : ident) (ty : BeeTypes.type)
    (locals : list (ident * BeeTypes.type * string)) (ctx : bcompiler_ctx)
    : mon (option ident * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
  match ty with
  | Utype => ret (None, locals, with_compiler_bindings ctx
      (push_compiler_binding ctx.(lexical_bindings) source Binding_unit))
  | _ =>
      do (target, name) <- fresh_ident
        ((map unzip_ident locals ++ reserved_identifiers ctx)%list) max_fresh;
      ret (Some target, (target, ty, name) :: locals,
        with_compiler_bindings ctx
          (push_compiler_binding ctx.(lexical_bindings) source (Binding_slot target)))
  end.

Definition compiler_destination (selected : option ident) (ty : BeeTypes.type)
    (locals : list (ident * BeeTypes.type * string)) (ctx : bcompiler_ctx)
    : mon (ident * list (ident * BeeTypes.type * string)) :=
  match selected with
  | Some target => ret (target, locals)
  | None =>
      do (target, name) <- fresh_ident
        ((map unzip_ident locals ++ reserved_identifiers ctx)%list) max_fresh;
      ret (target, (target, ty, name) :: locals)
  end.

Fixpoint fresh_compiler_fields (fields : list (ident * BeeTypes.type))
    (locals : list (ident * BeeTypes.type * string)) (ctx : bcompiler_ctx)
    : mon (list (ident * ident * Ctypes.type) * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
  match fields with
  | nil => ret (nil, locals, ctx)
  | (field, ty) :: tail =>
      do (binding, scoped) <- fresh_compiler_binding field ty locals ctx;
      do (rest, scoped') <- fresh_compiler_fields tail (snd binding) scoped;
      match fst binding with
      | Some target => ret ((field, target, transBeePL_type ty) :: fst rest, snd rest, scoped')
      | None => ret (fst rest, snd rest, scoped')
      end
  end.


Fixpoint lookup_string (id : ident) (iss : list (ident * string)) : option string :=
  match iss with
  | nil              => None                       (* should never happen by assumption *)
  | (id', s) :: rest =>
      if ident_eq id id' then Some s else lookup_string id rest
  end.

(* Go through each arg in args and find string in ident to string mapping *)
Fixpoint create_fn_ctx (args : list (ident * BeeTypes.type)) (iss : list (ident * string)) : mon (list (ident * BeeTypes.type * string)) :=
  match args with
  | nil => ret nil
  | (id, ty) :: rest =>
      do triples <- create_fn_ctx rest iss;
      match lookup_string id iss with
      | Some str => ret ((id, ty, str) :: triples)
      | _        => let id_str := NilZero.string_of_uint (Nat.to_uint (Pos.to_nat id)) in
                    let full_msg := "COMPILER ERROR: ident " ++ id_str ++ " is missing from ident to string mapping" in
                    error (msg full_msg)
      end
  end.

Fixpoint merge_ident_string (fn_ctx : list (ident * BeeTypes.type * string)) (iss : list (ident * string)) : list (ident * string) :=
  match fn_ctx with
  | nil => iss
  | (id, _, s) :: rest =>
      match lookup_string id iss with
      | Some _ => merge_ident_string rest iss               (* already present, skip *)
      | None   => merge_ident_string rest ((id, s) :: iss)  (* add new binding *)
      end
  end.

(* It will never be used, but we need for None case *)
Definition get_default_option_val (t : Ctypes.type) : mon Values.val :=
match t with  
| Tvoid =>  ret Values.Vundef
| Ctypes.Tint sz s a => ret (Values.Vint (Int.repr 0)) 
| Ctypes.Tlong s a => ret (Values.Vlong (Int64.repr 0))
| Tfloat sz a => error (msg "No default value for float")
| Tpointer t a => ret (Values.Vlong (Int64.repr 0)) 
| Tarray _ _ _ => error (msg "No default value for array")
| Tfunction _ _ _ => error (msg "No default value for function")
| Tstruct x a => ret (Values.Vlong (Int64.repr 0)) 
| Tunion _ _ => error (msg "No default value for function")
end.

(* Guard conditions have C's canonical int result, independently of the
   integer width of the operands.  Operands passed here are captured locals. *)
Definition check_divmod (op : Cop.binary_operation) (ces : exprlist)
    (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
  let lhs := hd default_expr (exprlist_list_expr ces) in
  let rhs := hd default_expr (tl (exprlist_list_expr ces)) in
  let finish zero overflow :=
    Econdition (Ebinop Cop.Oor (Ebinop Cop.Oeq rhs (Eval zero t) tint)
      overflow tint) (Eval v t) (Ebinop op lhs rhs t) t in
  let signed_overflow minimum minusone :=
    Ebinop Cop.Oand (Ebinop Cop.Oeq lhs (Eval minimum t) tint)
      (Ebinop Cop.Oeq rhs (Eval minusone t) tint) tint in
  match t with
  | Ctypes.Tint I32 Signed _ => ret (finish (Values.Vint Int.zero)
      (signed_overflow (Values.Vint (Int.repr Int.min_signed)) (Values.Vint Int.mone)))
  | Ctypes.Tint I32 Unsigned _ => ret (finish (Values.Vint Int.zero)
      (Eval (Values.Vint Int.zero) tint))
  | Ctypes.Tlong Signed _ => ret (finish (Values.Vlong Int64.zero)
      (signed_overflow (Values.Vlong (Int64.repr Int64.min_signed)) (Values.Vlong Int64.mone)))
  | Ctypes.Tlong Unsigned _ => ret (finish (Values.Vlong Int64.zero)
      (Eval (Values.Vint Int.zero) tint))
  | _ => error (msg "The type of argument of div/mod should be int or long")
  end.

Definition check_div := check_divmod Cop.Odiv.
Definition check_mod := check_divmod Cop.Omod.

(* Unsigned comparison implements the source Int.ltu/Int64.ltu test:
   negative counts, as well as counts at or above the width, return zero. *)
Definition check_shift (op : Cop.binary_operation) (ces : exprlist)
    (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
  let lhs := hd default_expr (exprlist_list_expr ces) in
  let rhs := hd default_expr (tl (exprlist_list_expr ces)) in
  match t with
  | Ctypes.Tint _ _ _ =>
      let unsigned := Ctypes.Tint I32 Unsigned noattr in
      ret (Econdition (Ebinop Cop.Olt (Ecast rhs unsigned)
        (Eval (Values.Vint Int.iwordsize) unsigned) tint)
        (Ebinop op lhs rhs t) (Eval v t) t)
  | Ctypes.Tlong _ _ =>
      let unsigned := Ctypes.Tlong Unsigned noattr in
      ret (Econdition (Ebinop Cop.Olt (Ecast rhs unsigned)
        (Eval (Values.Vlong Int64.iwordsize) unsigned) tint)
        (Ebinop op lhs rhs t) (Eval v t) t)
  | _ => error (msg "COMPILER ERROR: The type of argument of shift should be int or long")
  end.

Definition check_shl := check_shift Cop.Oshl.
Definition check_shr := check_shift Cop.Oshr.

(* Evaluate both source operands once, left to right, before testing a guard.
   Generated names exclude every existing local and reserved source name. *)
Definition guarded_binop (op : Cop.binary_operation) (es : list BeePL.expr)
    (ces : Csyntax.exprlist) (ty : BeeTypes.type)
    (ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx)
    : mon (Csyntax.expr * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
  match es, ces with
  | lhs_source :: rhs_source :: nil, Econs cleft (Econs cright Enil) =>
    let lt := typeof_expr lhs_source in
    let rt := typeof_expr rhs_source in
    let clt := transBeePL_type lt in
    let crt := transBeePL_type rt in
    let ct := transBeePL_type ty in
    do (li, ln) <- fresh_ident (List.map unzip_ident ctx ++ reserved_identifiers bctx) max_fresh;
    let ctx1 := (li, lt, ln) :: ctx in
    do (ri, rn) <- fresh_ident (List.map unzip_ident ctx1 ++ reserved_identifiers bctx) max_fresh;
    let captured := Econs (Evalof (Evar li clt) clt)
                         (Econs (Evalof (Evar ri crt) crt) Enil) in
    do zero <- return_czero ct;
    do guarded <- match op with
      | Cop.Odiv => check_div captured zero ct
      | Cop.Omod => check_mod captured zero ct
      | Cop.Oshl => check_shl captured zero ct
      | Cop.Oshr => check_shr captured zero ct
      | _ => error (msg "COMPILER ERROR: Expected guarded binary operator")
      end;
    ret (Ecomma (Eassign (Evar li clt) cleft clt)
          (Ecomma (Eassign (Evar ri crt) cright crt) guarded ct) ct,
         (ri, rt, rn) :: ctx1, bctx)
  | _, _ => error (msg "COMPILER ERROR: Binary operator requires two operands")
  end.

Fixpoint init_struct_fields
  (tmp   : ident)
  (tstr  : Ctypes.type)
  (pairs : list (ident * Csyntax.expr))
  (ret   : Csyntax.expr)
  (ret_ty: Ctypes.type)
  : Csyntax.expr :=
  match pairs with
  | nil => ret
  | (f, e) :: rest =>
      let tf  := typeof e in
      let lhs := Efield (Evalof (Evar tmp tstr) tstr) f tf in
      let asg := Eassign lhs e tf in
      Ecomma asg (init_struct_fields tmp tstr rest ret ret_ty) ret_ty
  end.


Fixpoint use_comma_rec (ces : list Csyntax.expr) : expr :=
match ces with 
| nil => default_expr
| ce :: ces => let ces' := (use_comma_rec ces) in
               (Ecomma ce ces' (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr))
end.

Fixpoint assign_struct_fields_chain
  (base    : Csyntax.expr)                       (* e.g. Evar tmp (Tstruct ...) *)
  (pairs   : list (ident * Csyntax.expr))        (* (field, rhs) list *)
  (tail    : Csyntax.expr)                       (* expression after inits *)
  (tail_ty : Ctypes.type)
  : Csyntax.expr :=
  match pairs with
  | nil => tail
  | (f,e) :: rest =>
      let tf  := typeof e in
      let lhs := Efield (Evalof base (typeof base)) f tf in             (* base.f *)
      let asg := Eassign lhs e tf in             (* base.f = e *)
      Ecomma asg (assign_struct_fields_chain base rest tail tail_ty) tail_ty
  end.

(*let x = 3 in (x + x) ==> temp = 3; [x <= temp](x+x)
temp = 3; [x <= temp](x+x)*)

(*fresh var  = temp
map (temp, x)
[x] => [temp] 

main () {
int x = 2;
{ int x = 3;
  x := x  + 1;
}
return x;*)

Fixpoint transBeePL_expr_expr (e : BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.expr * (list (ident * BeeTypes.type * string)) * bcompiler_ctx) := 
match e with 
| Val v t => ret (Eval (trans_bvalue_cvalue v) (transBeePL_type t), fn_ctx, bctx) 
| Var x t => ret (trans_bound_variable bctx x t, fn_ctx, bctx)
| Const c t => match c with 
               | ConsInt i => ret (Eval (Values.Vint i) (transBeePL_type t), fn_ctx, bctx)
               | ConsLong i => ret (Eval (Values.Vlong i) (transBeePL_type t), fn_ctx, bctx)
               | ConsUnit => ret (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx, bctx) 
               | ConsBool b => ret (if eqb b true 
                                    then (Eval (Values.Vint (Int.repr 1)) (transBeePL_type t), fn_ctx, bctx) 
                                    else (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx, bctx))
               end
| App e es t => do (ce, bctx') <- (transBeePL_expr_expr e fn_ctx bctx); 
                do (ces, bctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es (snd ce) bctx');
                ret (Ecall (fst ce) (fst ces) (transBeePL_type t), snd ces, bctx'')
| Prim b es t => match b with 
                 | Ref => (* es: function arguments. If a function argument is Ref a fresh variable needs to be inserted prior to bind 
                         
                             let x = 3 in
                             let y = add(x, ref(4))

                             should become

                             int x = 3;
                             int __fresh; <- can be acomplished by adding a fresh variable to fn_ctx
                             int y = add(x, (__fresh = 4, &_fresh));
                           *)
                          do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (((List.map unzip_ident (snd ces))) ++ reserved_identifiers bctx)%list max_fresh);

                          match es with
                          | e :: nil => 
                                        do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in
                                        let fn_ctx'' := (i, pty, str) :: (snd ces) in
                                        ret ((Ecomma (Eassign (Evar i cpty) 
                                                              (hd default_expr (exprlist_list_expr (fst ces))) 
                                                              (cpty)) 
                                                     (Eaddrof (Evar i cpty) 
                                                              (ct))
                                                     (ct)), fn_ctx'', bctx')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret ((Evalof (Ederef (hd default_expr (exprlist_list_expr (fst ces))) ct) ct), snd ces, bctx')
                 | Massgn => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                     let pointer := hd default_expr (exprlist_list_expr (fst ces)) in
                     let value := hd default_expr (tl (exprlist_list_expr (fst ces))) in
                     match typeof pointer with
                     | Tpointer target _ =>
                         (* Store the pointee width, not the pointer width.
                            The source assignment has unit result. *)
                         ret (Ecast (Eassign (Ederef pointer target) value target) (transBeePL_type t),
                              snd ces, bctx')
                     | _ => error (msg "COMPILER ERROR: Assignment requires a reference")
                     end
                 | Uop o => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret ((Eunop o
                                (hd default_expr (exprlist_list_expr (fst ces))) 
                                ct), snd ces, bctx')
                 | Bop o => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            match o with 
                            | Cop.Odiv | Cop.Omod | Cop.Oshl | Cop.Oshr =>
                                guarded_binop o es (fst ces) t (snd ces) bctx'
                            | _ => ret (Ebinop o
                                        (hd default_expr (exprlist_list_expr (fst ces))) 
                                        (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                        (transBeePL_type t), snd ces, bctx')

                           end
               | ArrayRead n => match es with
                   | e :: nil =>
                     do len <- get_array_len (typeof_expr e);
                     if (n <? Z.to_nat len)%nat then
                       do (ce, bctx') <- transBeePL_expr_expr e fn_ctx bctx;
                       ret (Evalof (Ederef (Ebinop Cop.Oadd (fst ce)
                         (Eval (Values.Vint (Int.repr (Z.of_nat n))) tint)
                         (tptr (transBeePL_type t))) (transBeePL_type t))
                         (transBeePL_type t), snd ce, bctx')
                     else error (msg "Array read index out of bounds")
                   | _ => error (msg "Array read expects one argument")
                   end
               | Cast t' => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                           ret (trans_cast_expression t' (hd default_expr (exprlist_list_expr (fst ces))), snd ces, bctx')
end
| Bind x t e1 e2 t' =>
    do (binding, scope) <- fresh_compiler_binding x t fn_ctx bctx;
    do (ce1, rhs_ctx) <- transBeePL_expr_expr e1 (snd binding) bctx;
    do (ce2, body_ctx) <- transBeePL_expr_expr e2 (snd ce1) scope;
    let first := match fst binding with
      | Some target => Eassign (Evar target (transBeePL_type t)) (fst ce1) (transBeePL_type t)
      | None => fst ce1
      end in
    ret (Ecomma first (fst ce2) (transBeePL_type t'), snd ce2, bctx)
| Cond e e' e'' t => do (ce, bctx') <- (transBeePL_expr_expr e fn_ctx bctx);
                     do (ce', bctx'') <- (transBeePL_expr_expr e' (snd ce) bctx');
                     do (ce'', bctx''') <- (transBeePL_expr_expr e'' (snd ce') bctx'');
                     let ct := (transBeePL_type t) in
                     ret (Econdition (fst ce) (fst ce') (fst ce'') ct, snd ce'', bctx''')  
| Unit t=> let ct := (transBeePL_type t) in
           ret (Eval (trans_bvalue_cvalue Vunit) ct, fn_ctx, bctx) (* Fix me *)
| Addr l ofs t =>  (*let ct := transBeePL_type t in
                   let lval := Eloc l.(lname) ofs l.(lbitfield) ct in
                   (*let pty  := Ctypes.Tpointer ct Ctypes.noattr in*)
                   ret (Eaddrof lval ct, fn_ctx, bctx)*) 
                   error (msg "Programmers are never allowed to use raw address")
(*| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := map Ctypes.typeconv (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es venv fn_ctx bctx);
                     ret (Ebuiltin cef cts (fst ces) ct, snd ces, bctx')*)
| Sinit sid fnames es t => (* translate constructor arguments *)
                           do (ces, bctx') <- transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx;
                           do (tmp, tag)   <- fresh_ident (((List.map unzip_ident (snd ces))) ++ reserved_identifiers bctx)%list max_fresh;

                           let args := exprlist_list_expr (fst ces) in
                           let pairs := combine fnames args in
                           match t with
                           | BeeTypes.Stype sid' attrs =>
                               let tstruct := Ctypes.Tstruct sid' attrs in
                               let base := Evar tmp tstruct in
                               let chain := assign_struct_fields_chain base pairs (Evalof base tstruct) tstruct in
                               let fn_ctx' := (tmp, BeeTypes.Stype sid' attrs, tag) :: (snd ces) in
                               ret (chain, fn_ctx', bctx')
                           | BeeTypes.Ptrtype (BeeTypes.Reftype (BeeTypes.Bstruct sid' attrs) pattrs) =>
                               let tstruct := Ctypes.Tstruct sid' attrs in
                               let base := Evar tmp tstruct in
                               let tptr := Ctypes.Tpointer tstruct pattrs in
                               let addr := Eaddrof base tptr in
                               let chain := assign_struct_fields_chain base pairs addr tptr in
                               let fn_ctx' := (tmp, BeeTypes.Stype sid' attrs, tag) :: (snd ces) in
                               ret (chain, fn_ctx', bctx')
                           | _ => error (msg "Sinit expects struct or pointer-to-struct type")
                           end
| Sfield e x t =>
    (* Translate the base expression *)
    do (ce, bctx') <- transBeePL_expr_expr e fn_ctx bctx;
    let te := typeof_expr e in
    let ct := transBeePL_type t in
    match te with
    (* ----- struct value: e has type Stype s ----- *)
    | Stype s _ =>
        let lval := Efield (fst ce) x ct in
        ret (Evalof lval ct, snd ce, bctx')

    (* ----- pointer to struct: e : &struct s ----- *)
    | Ptrtype (Reftype (Bstruct s _) _) =>
        let struct_ty := Tstruct s noattr in
        let lval      := Efield (Evalof (Ederef (fst ce) struct_ty) struct_ty) x ct in
        ret (Evalof lval ct, snd ce, bctx')

    (* ----- option pointer to struct: e : ostruct s* ----- *)
    | Ptrtype (Otype (Reftype (Bstruct s _) _)) =>
        (* In the some-branch, we assume e is non-null *)
        let struct_ty := Tstruct s noattr in
        let lval      := Efield (Evalof (Ederef (fst ce) struct_ty) struct_ty) x ct in
        ret (Evalof lval ct, snd ce, bctx')

    | _ =>
        error (msg "Sfield: expected struct or pointer-to-struct base")
    end
| For e1 e2 d e t => error (msg "COMPILER ERROR: For loop cannot be translated to another C expr")
| Enone t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                             then ret ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (transBeePL_ptr_type t')), fn_ctx, bctx)
                             else error (msg "COMPILER ERROR: Expression none should be a pointer option type")
             | _ => error (msg "COMPILER ERROR: Expression none should be a pointer type")
             end
| Esome e t => match t with 
             | Ptrtype (Otype t') => if is_option_ptr_type (Otype t') && eq_type (typeof_expr e) (Ptrtype t')
                                     then transBeePL_expr_expr e fn_ctx bctx
                                     else error (msg "COMPILER ERROR: Expression some should be a pointer option type")
             | _ => error (msg "COMPILER ERROR: Expression some should be a pointer type")
             end
| Match e ps es t =>
    (* First, translate the scrutinee expression. *)
    do (ce, bctx') <- transBeePL_expr_expr e fn_ctx bctx;
    let te := typeof_expr e in
    match te with 

    (* ---------- OPTION POINTER: match some / none ---------- *)
    | Ptrtype opt_t =>
        if is_option_ptr_type opt_t then
          (* opt_t must be Otype inner_pt *)
          do inner_pt <- inner_ptr_of_option opt_t;

          (* We only support exactly two branches: some / none in any order *)
          match ps, es with
          | (Pnone :: Psome x :: nil), (e_none :: e_some :: nil)
          | (Psome x :: Pnone :: nil), (e_some :: e_none :: nil) =>

              (* Capture once before branching.  Reserve source names as well
                 as generated locals and parameters, so the capture cannot
                 shadow a source operand or the Some binder. *)
              do (tmp, tmp_name) <- fresh_ident (((x :: (List.map unzip_ident (snd ce) ++ unzip1 bctx'.(arg_ctx) ++
                  free_variables e ++ free_variables e_none ++ free_variables e_some))) ++ reserved_identifiers bctx)%list max_fresh;
              let captured_ctx := (tmp, te, tmp_name) :: snd ce in
              let ct := transBeePL_type te in
              let captured := Evalof (Evar tmp ct) ct in
              let capture := Eassign (Evar tmp ct) (fst ce) ct in
              do (c_none, b1) <- transBeePL_expr_expr e_none captured_ctx bctx';

              do (binding, some_scope) <- fresh_compiler_binding x (Ptrtype inner_pt) (snd c_none) b1;
              do (c_some, b2) <- transBeePL_expr_expr e_some (snd binding) some_scope;

              (* condition: is scrutinee None? (ptr == 0) *)
              let is_none : Csyntax.expr :=
                Ebinop Cop.Oeq
                  captured
                  (Ecast (Eval (Values.Vint (Int.repr 0)) tint)
                         (transBeePL_type te))
                  (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr) in

              (* bind x in SOME branch before evaluating its body:
                 cx = (inner* scrutinee; *)
              let bind_x : Csyntax.expr :=
                match fst binding with
                | Some target => Eassign (Evar target (transBeePL_type (Ptrtype inner_pt)))
                    (Ecast captured (transBeePL_type (Ptrtype inner_pt)))
                    (transBeePL_type (Ptrtype inner_pt))
                | None => Eval (Values.Vint Int.zero) Ctypes.Tvoid
                end in

              (* if (u == 0) ? none-body : (x = u, some-body) *)
              ret ( Ecomma capture (Econdition is_none
                     (fst c_none)
                     (Ecomma bind_x (fst c_some) (transBeePL_type t))
                     (transBeePL_type t)) (transBeePL_type t),
                   (* keep extended ctx so cx is declared local *)
                   snd c_some, bctx)

          | _, _ =>
              error (msg "COMPILER ERROR: Match supports exactly two branches: some/none")
          end
        else
          error (msg "COMPILER ERROR: Match expression must be an option pointer")

    (* ---------- BYTES: not supported at expression level ---------- *)
    | Bytes =>
        error (msg "COMPILER ERROR: Match on bytes is only supported in statement position")

    (* ---------- Anything else is not supported ---------- *)
    | _ =>
        error (msg "COMPILER ERROR: Match can be only performed on option pointer or bytes type")
    end
| Ebytes es t => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx); 
                 error (msg "COMPILER ERROR: Bitstring translation is not supported yet")
| Ainit a t es t' => error (msg "COMPILER ERROR: Array initialization cannot be treated as expression in C")
| CallFrame _ _ _ | LoopFrame _ _ _ => error (msg "COMPILER ERROR: Internal runtime frames are not source expressions")
| Aaccess source t n t' => do a <- resolve_compiler_storage bctx source;
                      do al <- get_array_len t;
                      if (n <? Z.to_nat al)%nat 
                      then ret (Evalof (Ederef (Ebinop Cop.Oadd (Evalof (Evar a (transBeePL_type t)) (transBeePL_type t))
                                                           (Eval (Values.Vint (Int.repr (Z.of_nat n))) tint) (tptr (transBeePL_type t')))
                                          (transBeePL_type t')) (transBeePL_type t'), fn_ctx, bctx)
                      else error (msg "The accessed index should be within array length")
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.

Fixpoint assign_array_cast (a : ident) (sz : Z) (ts : list Ctypes.type) (ces : list Csyntax.expr) : mon Csyntax.statement :=
match ces, ts with 
| nil, nil => ret Sskip
| ce1 :: ce2 :: ces1, t1 :: t2 :: ts1 => 
  do rs <- assign_array_cast a sz ts1 ces1;
  ret (Ssequence (Sdo (Eassign (Ederef (Ecast (Evalof (Evar a (tarray tschar sz)) (tarray tschar sz)) (tptr t1)) t1)
                                                        ce1 t1))
                 (Ssequence (Sdo (Eassign (Ederef (Ecast (Ebinop Cop.Oadd (Evalof (Evar a (tarray tschar sz)) (tarray tschar sz))
                                                                          (Esizeof t1 t2) t2) (tptr t2)) t2)
                                     ce2 t2)) rs))
| _, _ => error (msg "COMPILER ERROR: The length of type list and expression list should be same in bitstring")
end.  

(* struct xdp_md_wrapper xdp_md_wrapper;
    xdp_md_wrapper.data.start = (\* char)ctx->data;
    xdp_md_wrapper.data.end = (\* char)ctx->data_end; *)
(* Definition set_ebpf_struct_bee_struct (beei : ident) (t : Ctypes.type) (fdata : ident) (t' : Ctypes.type) :=
           (Ssequence (Sdo (Eassign (Efield (Evalof (Efield (Evalof (Evar beei t) t)
                                                            _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) (* bees.data *)
                                             bytes_start (tptr tuchar)) (* bees.data.start *)
                                    (Ecast (Evalof (Efield (Evalof (Ederef (Evalof (Evar fdata t') t') t') t') _data tulong) tulong) (tptr tuchar)) (tptr tuchar))) (* (star char)ctx->data *) 
                      (Sdo (Eassign (Efield (Evalof (Efield (Evalof (Evar beei t) t)
                                                            _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) (* bees.data *)
                                             bytes_end (tptr tuchar)) (* bees.data.end *)
                                    (Ecast (Evalof (Efield (Evalof (Ederef (Evalof (Evar fdata t') t') t') t') _data_end tulong) tulong) (tptr tuchar)) (tptr tuchar)))). (* (star char)ctx->data_end *) *)

(* p.bytes_start = (unsigned char  ctx->data; 
   p.bytes_end   = (unsigned char ctx->data_end; *)
Definition set_bytes_from_ctx
           (p    : ident)           (* local "p" : struct bytes_t *)
           (ctx  : ident)           (* function parameter "ctx" *)
           (tctx : Ctypes.type)     (* type of [ctx], e.g. Tpointer (Tstruct _xdp_md noattr) noattr *)
  : Csyntax.statement :=
  let t_xdp   := Tstruct _xdp_md noattr in
  let t_u32   := Ctypes.Tint I32 Unsigned noattr in
  let t_pchar := tptr tuchar in
  Ssequence
    (* p.bytes_start = (unsigned char  ctx->data; *)
    (Sdo
       (Eassign
          (Efield
             (Evalof (Evar p (Tstruct bytes_t noattr))
                     (Tstruct bytes_t noattr))
             bytes_start t_pchar)
          (Ecast
             (Evalof
                (Efield
                   (Evalof (Ederef (Evalof (Evar ctx tctx) tctx) t_xdp) t_xdp)
                   _data t_u32)
                t_u32)
             t_pchar)
          t_pchar))
    (* p.bytes_end = (unsigned char  ctx->data_end; *)
    (Sdo
       (Eassign
          (Efield
             (Evalof (Evar p (Tstruct bytes_t noattr))
                     (Tstruct bytes_t noattr))
             bytes_end t_pchar)
          (Ecast
             (Evalof
                (Efield
                   (Evalof (Ederef (Evalof (Evar ctx tctx) tctx) t_xdp) t_xdp)
                   _data_end t_u32)
                t_u32)
             t_pchar)
          t_pchar)).


(* if (xdp_md_wrapper.data.start + sizeof(struct ethhdr) > xdp_md_wrapper.data.end) then ee else se *)
(*Definition bound_check (input : ident) (t : Ctypes.type) (t' : Ctypes.type) (ee se : Csyntax.statement) := 
(Sifthenelse (Ebinop Cop.Ogt
                     (Ebinop Cop.Oadd
                       (Efield (Evalof (Efield (Evalof (Evar input t) t)
                                               _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr))
                               bytes_start (tptr tuchar)) 
                       (Esizeof t' tulong) (tptr tuchar)) (* xdp_md_bee.data.start + sizeof(struct ethhdr) *)
                     (Efield (Evalof (Efield (Evalof (Evar input t) t) 
                                             _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) 
                               bytes_end (tptr tuchar)) tint) (* xdp_md_bee.data.end *)
             ee 
             se).*)

(* if (p.bytes_start + sizeof(hdr_ty) > p.bytes_end) ... *)
Definition bound_check_bytes
           (p      : ident)
           (hdr_ty : Ctypes.type)
           (ee se  : Csyntax.statement)
  : Csyntax.statement :=
  let t_pchar := tptr tuchar in
  Sifthenelse
    (Ebinop Cop.Ogt
       (Ebinop Cop.Oadd
          (Evalof (Efield (Evalof (Evar p (Tstruct bytes_t noattr))
                          (Tstruct bytes_t noattr))
                  bytes_start t_pchar) t_pchar)
          (Esizeof hdr_ty tulong)
          t_pchar)
       (Evalof (Efield (Evalof (Evar p (Tstruct bytes_t noattr))
                       (Tstruct bytes_t noattr))
               bytes_end t_pchar) t_pchar)
       tint)
    ee se.


(*Definition set_temp_for_copy (temp : ident) (t : Ctypes.type) (from: ident) (t' : Ctypes.type) : Csyntax.statement :=
(Sdo (Eassign (Evar temp t) (Ecast (Evalof (Efield (Evalof (Efield (Evalof (Evar from t') t') _data_bee
                                           (Tstruct bytes_t noattr)) 
                                            (Tstruct bytes_t noattr)) bytes_start
                                                      (tptr tuchar)) (tptr tuchar)) t) t)).*)

(* tmp = (struct hdr p.bytes_start; *)
Definition set_temp_for_copy
           (tmp   : ident)
           (t_tmp : Ctypes.type)    (* usually tptr (Tstruct s noattr) *)
           (p     : ident)
  : Csyntax.statement :=
  let t_pchar := tptr tuchar in
  Sdo
    (Eassign
       (Evar tmp t_tmp)
       (Ecast
          (Evalof
             (Efield (Evalof (Evar p (Tstruct bytes_t noattr))
                             (Tstruct bytes_t noattr))
                     bytes_start t_pchar)
             t_pchar)
          t_tmp)
       t_tmp).

(* Pbytes introduces both a header value and named field bindings. *)
Fixpoint bind_buffer_fields (header schema : ident)
         (fields : list (ident * Ctypes.type)) : Csyntax.statement :=
  match fields with
  | nil => Sskip
  | (field, ty) :: rest =>
      Ssequence
        (Sdo (Eassign (Evar field ty)
          (Evalof (Efield
            (Evalof (Evar header (Tstruct schema noattr)) (Tstruct schema noattr))
            field ty) ty) ty))
        (bind_buffer_fields header schema rest)
  end.

(* Keep schema selectors separate from lexical target slots. *)
Fixpoint bind_scoped_buffer_fields (header schema : ident)
    (fields : list (ident * ident * Ctypes.type)) : Csyntax.statement :=
  match fields with
  | nil => Sskip
  | (field, target, ty) :: rest =>
      Ssequence
        (Sdo (Eassign (Evar target ty)
          (Evalof (Efield
            (Evalof (Evar header (Tstruct schema noattr)) (Tstruct schema noattr))
            field ty) ty) ty))
        (bind_scoped_buffer_fields header schema rest)
  end.

Fixpoint copy_buffer
         (to   : ident)
         (sto  : ident)
         (tsto : Ctypes.type) (* usually tptr (Tstruct sto noattr) or similar *)
         (xts  : list (ident * Ctypes.type))
         (from : ident)
  : Csyntax.statement :=
  match xts with 
  | nil => Sskip
  | x :: xs =>
      let bs := copy_buffer to sto tsto xs from in
      let f  := fst x in
      let tf := snd x in
      Ssequence
        (Sdo
           (Eassign
              (Efield
                 (Evalof (Evar to (Tstruct sto noattr))
                         (Tstruct sto noattr))
                 f tf)
              (Evalof
                 (Efield
                    (Evalof
                       (Ederef (Evalof (Evar from (tptr (Tstruct sto noattr)))
                                       (tptr (Tstruct sto noattr)))
                               (Tstruct sto noattr))
                       (Tstruct sto noattr))
                    f tf)
                 tf)
              tf))
        bs
  end.


(*Definition incr_data_ptr (wv : ident) (s : ident) (bv : ident) : Csyntax.statement :=
(Sdo (Eassign (Efield (Evalof (Efield (Evalof
                             (Evar wv (Tstruct s noattr))
                             (Tstruct s noattr)) _data_bee
                           (Tstruct bytes_t noattr))
                         (Tstruct bytes_t noattr)) bytes_start (tptr tuchar))
                     (Ebinop Cop.Oadd (Evalof (Efield (Evalof (Efield (Evalof
                                 (Evar wv (Tstruct s noattr))
                                 (Tstruct s noattr)) _data_bee
                               (Tstruct bytes_t noattr))
                             (Tstruct bytes_t noattr)) bytes_start (tptr tuchar))
                         (tptr tuchar))
                       (Esizeof (Tstruct bv noattr) tulong)
                       (tptr tuchar)) (tptr tuchar))).*)

(* p.bytes_start += sizeof(struct hdr); *)
Definition incr_bytes_ptr
           (p   : ident)
           (hdr : ident)            (* struct name, e.g. ethhdr *)
  : Csyntax.statement :=
  let t_pchar := tptr tuchar in
  Sdo
    (Eassign
       (Efield (Evalof (Evar p (Tstruct bytes_t noattr))
                       (Tstruct bytes_t noattr))
               bytes_start t_pchar)
       (Ebinop Cop.Oadd
          (Evalof (Efield (Evalof (Evar p (Tstruct bytes_t noattr))
                          (Tstruct bytes_t noattr))
                  bytes_start t_pchar) t_pchar)
          (Esizeof (Tstruct hdr noattr) tulong)
          t_pchar)
       t_pchar).

Definition get_carray_elm_ty (t : Ctypes.type) : mon Ctypes.type :=
match t with 
| Tarray t n a => ret t 
| _ => error (msg "Not an array type")
end.

(* write [es] starting at index [i] *) 
Fixpoint array_init_from (a : ident) (t : Ctypes.type) (i : Z) (es : list Csyntax.expr) : mon Csyntax.statement :=
match es with
| nil => ret Sskip
| e :: es' => do aty <- get_carray_elm_ty t;
              do r <- array_init_from a t (i + 1) es';
              ret (Ssequence (Sdo (Eassign (Ederef (Ebinop Cop.Oadd
                                                      (Evalof (Evar a t) t)
                                                      (Eval (Values.Vint (Int.repr i)) tint)
                                                      (tptr aty)) aty)
                                           e
                                  (typeof e))) 
                             r)
end.

(* Public: write [ai] at 0, then [ais] at 1.. *)
Definition array_init (a : ident) (t : Ctypes.type) (es : list Csyntax.expr) : mon Csyntax.statement :=
match es with
| nil => error (msg "COMPILER ERROR: Array should be always initialized")
| ai :: ais => do aty <- get_carray_elm_ty t;
               do r <- array_init_from a t 1 ais;
               ret (Ssequence (Sdo (Eassign (Ederef  (Ebinop Cop.Oadd
                                                        (Evalof (Evar a t) t)
                                                        (Eval (Values.Vint (Int.repr 0)) tint)
                                                        (tptr aty)) aty)
                                            ai
                                   (typeof ai)))
                               r)
end.

Fixpoint init_struct_fields_stmt
  (x    : ident)                    (* target C local (already declared) *)
  (tstr : Ctypes.type)              (* C struct type of [x] *)
  (ps   : list (ident * Csyntax.expr))  (* (field, rhs) list *)
  : Csyntax.statement :=
  match ps with
  | nil => Sskip
  | (f, rhs) :: rest =>
      let tf  := typeof rhs in
      let lhs := Efield (Evalof (Evar x tstr) tstr) f tf in    (* x.f *)
      Ssequence
        (Sdo (Eassign lhs rhs tf))               (* x.f = rhs; *)
        (init_struct_fields_stmt x tstr rest)
  end.

Fixpoint transBeePL_expr_st (cenv : bcomposite_env) (e : BeePL.expr ) (ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.statement * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
match e with 
| Val v t => let vt := (transBeePL_type t) in
             ret (Sreturn (Some (Eval (trans_bvalue_cvalue v) vt)), ctx, bctx) 
| Var x t => ret (Sreturn (Some (trans_bound_variable bctx x t)), ctx, bctx)
| Const c t => let ct := (transBeePL_type t) in
               ret (Sreturn (Some (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      | ConsBool b => if eqb b true 
                                                      then Eval (Values.Vint (Int.repr 1)) ct
                                                      else Eval (Values.Vint (Int.repr 0)) ct
                                      end)), ctx, bctx)
| App e es t => do (ce, ctx') <- (transBeePL_expr_expr e ctx bctx);
                do (ces, ctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es (snd ce) ctx');
                let ct := (transBeePL_type t) in
                let call := Ecall (fst ce) (fst ces) ct in
                ret ((match t with Utype => Sdo call | _ => Sreturn (Some call) end),
                     snd ces, ctx'')
| Prim b es t => match b with 
                 | Ref => (* TODO: figure out how to recude duplicate code between here and transBeePL_expr_st *)
                          do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (((List.map unzip_ident (snd ces))) ++ reserved_identifiers bctx)%list max_fresh);
                          match es with
                          | e :: nil => do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in        
                                        let ctx'' := (i, pty, str) :: (snd ces) in
                                        ret (Ssequence (Sdo (Eassign (Evar i cpty)
                                                                     (hd default_expr (exprlist_list_expr (fst ces)))
                                                                     (cpty)))
                                                       (Sdo (Eaddrof (Evar i cpty) 
                                                                     (ct))), ctx'', ctx')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret (Sreturn (Some (Evalof (Ederef (hd default_expr (exprlist_list_expr (fst ces))) ct) ct)), snd ces, ctx')
                 | Massgn => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                     let pointer := hd default_expr (exprlist_list_expr (fst ces)) in
                     let value := hd default_expr (tl (exprlist_list_expr (fst ces))) in
                     match typeof pointer with
                     | Tpointer target _ =>
                         ret (Sdo (Eassign (Ederef pointer target) value target), snd ces, fn_ctx')
                     | _ => error (msg "COMPILER ERROR: Assignment requires a reference")
                     end
                 | Uop o => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            let ct := (transBeePL_type t) in 
                            ret (Sreturn (Some (Eunop o 
                                     (hd default_expr (exprlist_list_expr (fst ces))) 
                                     ct)), snd ces, ctx') 
                 | Bop o => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            match o with 
                            | Cop.Odiv | Cop.Omod | Cop.Oshl | Cop.Oshr =>
                                do (guarded, final_bctx) <- guarded_binop o es (fst ces) t (snd ces) fn_ctx';
                                ret (Sreturn (Some (fst guarded)), snd guarded, final_bctx)
                            | _ => ret (Sreturn (Some (Ebinop o
                                        (hd default_expr (exprlist_list_expr (fst ces))) 
                                        (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                        (transBeePL_type t))), snd ces, fn_ctx')

                           end
                 | ArrayRead n =>
                     do (ce, bctx') <- transBeePL_expr_expr (Prim (ArrayRead n) es t) ctx bctx;
                     ret (Sreturn (Some (fst ce)), snd ce, bctx')
                 | Cast t' => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                              ret (Sreturn (Some (trans_cast_expression t' (hd default_expr (exprlist_list_expr (fst ces))))),
                                snd ces, fn_ctx')
                 end  
| Bind x t e e' t' =>
    do (binding, scope) <- fresh_compiler_binding x t ctx bctx;
    match e with
    | Prim Massgn _ _ | For _ _ _ _ _ =>
        do (rhs, ignored) <- transBeePL_expr_st cenv e (snd binding) bctx;
        do (body, ignored') <- transBeePL_expr_st cenv e' (snd rhs) scope;
        ret (Ssequence (fst rhs) (fst body), snd body, bctx)
    | Ainit _ array_ty elements _ =>
        do (destination, storage) <- compiler_destination (fst binding) array_ty (snd binding) bctx;
        do (values, ignored) <- transBeePL_expr_exprs transBeePL_expr_expr elements storage bctx;
        do initialize <- array_init destination (transBeePL_type array_ty) (exprlist_list_expr (fst values));
        do (body, ignored') <- transBeePL_expr_st cenv e' (snd values) scope;
        ret (Ssequence initialize (fst body), snd body, bctx)
    | Sinit _ ids elements init_ty =>
        do (destination, storage) <- compiler_destination (fst binding) t (snd binding) bctx;
        do (values, ignored) <- transBeePL_expr_exprs transBeePL_expr_expr elements storage bctx;
        let pairs := combine ids (exprlist_list_expr (fst values)) in
        match transBeePL_type init_ty with
        | Ctypes.Tstruct sid attrs as struct_ty =>
            do (body, ignored') <- transBeePL_expr_st cenv e' (snd values) scope;
            ret (Ssequence (init_struct_fields_stmt destination struct_ty pairs) (fst body), snd body, bctx)
        | Ctypes.Tpointer (Ctypes.Tstruct sid attrs as struct_ty) ptrattrs =>
            do (temporary, storage') <- compiler_destination None (BeeTypes.Stype sid attrs) (snd values) bctx;
            do (body, ignored') <- transBeePL_expr_st cenv e' storage' scope;
            let ptr_ty := Ctypes.Tpointer struct_ty ptrattrs in
            let assign := Sdo (Eassign (Evar destination ptr_ty) (Eaddrof (Evar temporary struct_ty) ptr_ty) ptr_ty) in
            ret (Ssequence (init_struct_fields_stmt temporary struct_ty pairs)
                  (Ssequence assign (fst body)), snd body, bctx)
        | _ => error (msg "Sinit let-binding must have struct or pointer-to-struct type")
        end
    | _ =>
        do (rhs, ignored) <- transBeePL_expr_expr e (snd binding) bctx;
        do (body, ignored') <- transBeePL_expr_st cenv e' (snd rhs) scope;
        let first := match fst binding with
          | Some target => Sdo (Eassign (Evar target (transBeePL_type t)) (fst rhs) (transBeePL_type t))
          | None => Sdo (fst rhs)
          end in
        ret (Ssequence first (fst body), snd body, bctx)
    end
| Cond e e' e'' t' => do (ce, ctx') <- (transBeePL_expr_expr e ctx bctx);
                      do (ce', ctx'') <- (transBeePL_expr_st cenv e' (snd ce) ctx');
                      do (ce'', ctx''') <- (transBeePL_expr_st cenv e'' (snd ce') ctx'');
                      let ct' := (transBeePL_type t') in
                      ret (Sifthenelse (fst ce) (fst ce') (fst ce''), snd ce'', ctx''')
| Unit t=> ret (Sskip, ctx, bctx) (*Sreturn (Some (Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)))*) (* In case of unit, we return 0 *)
| Addr l ofs t =>  (*let ct := transBeePL_type t in
                   let lval := Eloc l.(lname) ofs l.(lbitfield) ct in
                   let pty  := Ctypes.Tpointer ct Ctypes.noattr in
                   ret ((Sdo (Eaddrof lval pty)), ctx, bctx) *)
                   error (msg "Programmers are never allowed to use raw address")
(*| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := map Ctypes.typeconv (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es venv ctx bctx);
                     ret (Sdo (Ebuiltin cef cts (fst ces) ct), snd ces, ctx')*)
| Sinit sx ids es t => error (msg "COMPILER ERROR: Struct creation should be done inside a let-binding") 
| Sfield e x t =>
    do (ce, ctx') <- transBeePL_expr_expr e ctx bctx;
    let te := typeof_expr e in
    let ct := transBeePL_type t in
    match te with
    (* ----- struct value ----- *)
    | Stype s _ =>
        let lval := Efield (fst ce) x ct in
        ret (Sreturn (Some (Evalof lval ct)), snd ce, ctx')

    (* ----- pointer to struct ----- *)
    | Ptrtype (Reftype (Bstruct s _) _) =>
        let struct_ty := Tstruct s noattr in
        let lval      := Efield (Evalof (Ederef (fst ce) struct_ty) struct_ty) x ct in
        ret (Sreturn (Some (Evalof lval ct)), snd ce, ctx')

    (* ----- option pointer to struct ----- *)
    | Ptrtype (Otype (Reftype (Bstruct s _) _)) =>
        let struct_ty := Tstruct s noattr in
        let lval      := Efield (Evalof (Ederef (fst ce) struct_ty) struct_ty) x ct in
        ret (Sreturn (Some (Evalof lval ct)), snd ce, ctx')

    | _ =>
        error (msg "Sfield (statement): expected struct or pointer-to-struct base")
    end
| For e1 e2 d e t => do (ce1, bctx1) <- transBeePL_expr_expr e1 ctx bctx;
                     do (low, strl) <- (fresh_ident (((List.map unzip_ident (snd ce1))) ++ reserved_identifiers bctx)%list max_fresh);
                     let ctx2 := (low, typeof_expr e1, strl) :: snd ce1 in
                     do (ce2, bctx2) <- transBeePL_expr_expr e2 ctx2 bctx1;
                     do (high, strh) <- (fresh_ident (((List.map unzip_ident (snd ce2))) ++ reserved_identifiers bctx)%list max_fresh);
                     let ctx4 := (high, typeof_expr e2, strh) :: snd ce2 in
                     do (ce3, bctx3) <- transBeePL_expr_st cenv e ctx4 bctx2;
                     do (i, stri) <- (fresh_ident (((List.map unzip_ident (snd ce3))) ++ reserved_identifiers bctx)%list max_fresh);
                     let ctx6 := (i, typeof_expr e1, stri) :: snd ce3 in
                     (* Inclusive loops must stop at the endpoint BEFORE the
                        increment/decrement, including unsigned max and zero. *)
                     let body := Ssequence (fst ce3)
                       (Sifthenelse
                         (Ebinop Cop.Oeq
                           (Evalof (Evar i (typeof (fst ce1))) (typeof (fst ce1)))
                           (Evalof (Evar high (typeof (fst ce2))) (typeof (fst ce2)))
                           tint)
                         Sbreak Sskip) in
                     match d with 
                     | Up => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof (fst ce1))) (fst ce1) (typeof (fst ce1))))
                                                       (Sdo (Eassign (Evar high (typeof (fst ce2))) (fst ce2) (typeof (fst ce2)))))
                                            (Sifthenelse (Ebinop Cop.Ole (Evalof (Evar low (typeof (fst ce1))) (typeof (fst ce1))) (Evalof (Evar high (typeof (fst ce2))) (typeof (fst ce2))) tint)
                                                         (Sfor (Sdo (Eassign (Evar i (typeof (fst ce1))) (Evalof (Evar low (typeof (fst ce1))) (typeof (fst ce1))) (typeof (fst ce1))))
                                                               (Ebinop Cop.Ole (Evalof (Evar i (typeof (fst ce2))) (typeof (fst ce2))) 
                                                                                       (Evalof (Evar high (typeof (fst ce2))) (typeof (fst ce2))) tint)
                                                               (Sdo (Epostincr Cop.Incr (Evar i (typeof (fst ce2))) (typeof (fst ce2))))
                                                          body)
                                                         Sskip), ctx6, bctx3)
                     | Down => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof (fst ce1))) (fst ce1) (typeof (fst ce1))))
                                                         (Sdo (Eassign (Evar high (typeof (fst ce2))) (fst ce2) (typeof (fst ce2)))))
                                              (Sifthenelse (Ebinop Cop.Oge (Evalof (Evar low (typeof (fst ce1))) (typeof (fst ce1))) (Evalof (Evar high (typeof (fst ce2))) (typeof (fst ce2))) tint)
                                                           (Sfor (Sdo (Eassign (Evar i (typeof (fst ce1))) (Evalof (Evar low (typeof (fst ce1))) (typeof (fst ce1))) (typeof (fst ce1))))
                                                                 (Ebinop Cop.Oge (Evalof (Evar i (typeof (fst ce2))) (typeof (fst ce2))) 
                                                                                          (Evalof (Evar high (typeof (fst ce2))) (typeof (fst ce2))) tint)
                                                                 (Sdo (Epostincr Cop.Decr (Evar i (typeof (fst ce2))) (typeof (fst ce2))))
                                                            body)
                                                            Sskip), ctx6, bctx3)
                     end
| Enone t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                           then ret (Sdo ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (transBeePL_ptr_type t'))), ctx, bctx)
                           else error (msg "COMPILER ERROR: Option type of None should contain a pointer in BeePL")
             | _ => error (msg "COMPILER ERROR: None should be of Option type")
             end
| Esome e t => match t with 
               | Ptrtype (Otype t') => if is_option_ptr_type (Otype t') && eq_type (typeof_expr e) (Ptrtype t')
                               then transBeePL_expr_st cenv e ctx bctx
                               else error (msg "COMPILER ERROR: Option type of Some should contain a pointer in BeePL")
               | _ => error (msg "COMPILER ERROR: Some should be of Option type")
              end
| Match e ps es t =>
    (* 1. Translate scrutinee *)
    do (ce, bctx') <- transBeePL_expr_expr e ctx bctx;
    let te := typeof_expr e in
    match te with

    (* ---------- OPTION POINTER: match on some / none ---------- *)
    | Ptrtype opt_t =>
        if is_option_ptr_type opt_t then
          (* opt_t must be Otype inner_pt *)
          do inner_pt <- inner_ptr_of_option opt_t;

          (* We only support exactly two branches: some / none in any order *)
          match ps, es with
          | (Pnone :: Psome x :: nil), (e_none :: e_some :: nil)
          | (Psome x :: Pnone :: nil), (e_some :: e_none :: nil) =>

              do (tmp, tmp_name) <- fresh_ident (((x :: (List.map unzip_ident (snd ce) ++ unzip1 bctx'.(arg_ctx) ++
                  free_variables e ++ free_variables e_none ++ free_variables e_some))) ++ reserved_identifiers bctx)%list max_fresh;
              let captured_ctx := (tmp, te, tmp_name) :: snd ce in
              let ct := transBeePL_type te in
              let captured := Evalof (Evar tmp ct) ct in
              let capture := Sdo (Eassign (Evar tmp ct) (fst ce) ct) in
              do (c_none, b1) <- transBeePL_expr_st cenv e_none captured_ctx bctx';

              do (binding, some_scope) <- fresh_compiler_binding x (Ptrtype inner_pt) (snd c_none) b1;
              do (c_some, b2) <- transBeePL_expr_st cenv e_some (snd binding) some_scope;

              (* Condition: scrutinee == NULL ? *)
              let is_none : Csyntax.expr :=
                Ebinop Cop.Oeq
                  captured
                  (Ecast (Eval (Values.Vint Int.zero) tint)
                         (transBeePL_type te))
                  (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr) in

              (* In SOME branch: cx = inner* scrutinee; *)
              let bind_x : Csyntax.statement :=
                match fst binding with
                | Some target => Sdo (Eassign (Evar target (transBeePL_type (Ptrtype inner_pt)))
                    (Ecast captured (transBeePL_type (Ptrtype inner_pt)))
                    (transBeePL_type (Ptrtype inner_pt)))
                | None => Sskip
                end in

              (* if (scrutinee == NULL) { none } else { cx = scrutinee; some } *)
              ret ( Ssequence capture (Sifthenelse is_none
                     (fst c_none)
                     (Ssequence bind_x (fst c_some))),
                   snd c_some, bctx)

          | _, _ =>
              error (msg "COMPILER ERROR: Match supports exactly two branches: some/none")
          end
        else
          error (msg "COMPILER ERROR: Match expression must be an option pointer")

    (* ---------- BYTES: match Pbytes only ---------- *)
    | Bytes =>
        match ps, es with
        | (Pbytes x (Stype s noattr) xts :: Pbytes fallback Bytes nil :: nil), (e1 :: e2 :: nil) =>
            let all_fields :=
              match cenv!s with
              | Some co => fold_right
                  (fun m acc => match m with
                    | Member_plain name ty => (name, transBeePL_type ty) :: acc
                    | _ => acc
                    end) nil co.(co_members)
              | None => nil
              end in
            do (header_binding, header_scope) <- fresh_compiler_binding x (BeeTypes.Stype s noattr) (snd ce) bctx';
            do (header, header_storage) <- compiler_destination (fst header_binding) (BeeTypes.Stype s noattr) (snd header_binding) bctx';
            do (fields, success_scope) <- fresh_compiler_fields xts header_storage header_scope;
            do (ce1, ignored) <- transBeePL_expr_st cenv e1 (snd fields) success_scope;
            do (fallback_binding, fallback_scope) <- fresh_compiler_binding fallback Bytes (snd ce1) bctx';
            do (ce2, ignored') <- transBeePL_expr_st cenv e2 (snd fallback_binding) fallback_scope;
            match bctx.(arg_ctx) with
            | (argi, (Ptrtype (Otype (Reftype (Bstruct istruct _) _)))) :: nil =>
                do (p, packet_storage) <- compiler_destination None (BeeTypes.Stype bytes_t noattr) (snd ce2) bctx;
                do (tmp, final_storage) <- compiler_destination None
                  (Ptrtype (Otype (Reftype (Bstruct s noattr) noattr))) packet_storage bctx;
                match transform_ctx_ebpf_ctx bctx.(arg_ctx) with
                | OK ((argi', Tpointer (Tstruct istruct' noattr) a) :: nil) =>
                    let t_ctx_ptr := Tpointer (Tstruct istruct' noattr) a in
                    let t_hdr_ptr := tptr (Tstruct s noattr) in
                    let fallback_body := match fst fallback_binding with
                      | Some target => Ssequence
                          (Sdo (Eassign (Evar target (transBeePL_type Bytes))
                            (Evalof (Evar p (transBeePL_type Bytes)) (transBeePL_type Bytes))
                            (transBeePL_type Bytes))) (fst ce2)
                      | None => fst ce2
                      end in
                    ret
                      (Ssequence (set_bytes_from_ctx p argi' t_ctx_ptr)
                        (bound_check_bytes p (Tstruct s noattr) fallback_body
                          (Ssequence (set_temp_for_copy tmp t_hdr_ptr p)
                            (Ssequence
                              (Ssequence (copy_buffer header s t_hdr_ptr all_fields tmp)
                                (bind_scoped_buffer_fields header s (fst fields)))
                              (Ssequence (incr_bytes_ptr p s) (fst ce1))))),
                        final_storage, bctx)
                | _ => error (msg "COMPILER ERROR: eBPF program supports only one argument")
                end
            | _ => error (msg "COMPILER ERROR: For now we assume this match is used only in eBPF programs where first argument is an eBPF context")
            end
        | _, _ => error (msg "COMPILER ERROR: Match on bytes requires a header and bytes fallback pattern")
        end

    (* ---------- Anything else is not supported ---------- *)
    | _ =>
        error (msg "COMPILER ERROR: Match can be only performed on option and bytes type")
    end
| Ebytes es t => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx); 
                 error (msg "COMPILER ERROR: Bitstring translation is not supported yet")
                 (*do (i, str) <- (fresh_ident (((List.map unzip_ident ctx')) ++ reserved_identifiers bctx)%list max_fresh);
                 let ctx'' := (i, trint8u, str) :: ctx' in
                 let sz := sizeof_types cenv (map typeof_expr es) in 
                 let tcs := map typeof (exprlist_list_expr ces) in 
                 do rs <- assign_array_cast i sz tcs (exprlist_list_expr ces);
                 ret (Ssequence (Sdo (Evar i (tarray tschar sz)))
                                 rs, ctx'')*)
                 (*ret (Sdo (Ecast (hd default_expr (exprlist_list_expr ces)) (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr)), ctx')*)
| Ainit _ t es t' =>
    do (destination, storage) <- compiler_destination None t ctx bctx;
    do (ces, ignored) <- transBeePL_expr_exprs transBeePL_expr_expr es storage bctx;
    do initialize <- array_init destination (transBeePL_type t) (exprlist_list_expr (fst ces));
    ret (initialize, snd ces, bctx)
| CallFrame _ _ _ | LoopFrame _ _ _ => error (msg "COMPILER ERROR: Internal runtime frames are not source expressions")
| Aaccess source t n t' => do a <- resolve_compiler_storage bctx source;
                      do al <- get_array_len t;
                      if (n <? Z.to_nat al)%nat 
                      then ret (Sreturn (Some (Evalof (Ederef (Ebinop Cop.Oadd (Evalof (Evar a (transBeePL_type t)) (transBeePL_type t))
                                                           (Eval (Values.Vint (Int.repr (Z.of_nat n))) tint) (tptr (transBeePL_type t')))
                                          (transBeePL_type t')) (transBeePL_type t'))), ctx, bctx)
                      else error (msg "The accessed index should be within array length")
     
                                
end.

Definition cc_of_variadic (v : bool) : AST.calling_convention :=
  {| cc_vararg    := if v then Some 1 else None;
     cc_unproto   := false;
     cc_structret := false |}.

(* Source parameters and global names are reserved without becoming locals. *)
Definition reserve_function_context (fd : BeePL.function)
    (names : list (ident * string)) (ctx : bcompiler_ctx) : bcompiler_ctx :=
 {| arg_ctx := arg_ctx ctx; benv := benv ctx;
    reserved_identifiers := (reserved_identifiers ctx ++
      map fst fd.(BeePL.fn_args) ++ map fst fd.(BeePL.fn_vars) ++ map fst names ++
      compiler_source_names fd.(BeePL.fn_body))%list;
    lexical_bindings := empty_compiler_bindings |}.

(* Translates the BeePL function declaration to a C function *)
Definition transBeePL_function_function
  (cenv : bcomposite_env)
  (fd   : BeePL.function)
  (iss  : list (ident * string))
  (bctx : bcompiler_ctx)
: res (Csyntax.function * list (ident * string) * bcompiler_ctx) :=
let crt := transBeePL_type fd.(BeePL.fn_return) in
let bctx := reserve_function_context fd iss bctx in
(* Build initial fn_ctx (locals + their strings) and an initial fresh-name generator *)
match create_fn_ctx nil iss (initial_generator tt) with
| Err msg => Error msg
| Res fn_ctx g0 i0 =>

  (* IMPORTANT: thread g0; do NOT reinitialize the generator here *)
  match transBeePL_expr_st cenv (BeePL.fn_body fd) fn_ctx bctx g0 with
  | Err msg => Error msg
  | Res (fbody, bctx') g1 i1 =>

    (* Locals accumulated during translation (declared locals + fresh temps) *)
    let loc_ids  := List.map unzip_ident (snd fbody) in
    let loc_btys := List.map unzip_type   (snd fbody) in
    let loc_ctys := transBeePL_types transBeePL_type loc_btys in
    let locals   := zip loc_ids loc_ctys in

    (* Extend ident->string table with any new temps introduced during translation *)
    let is' := merge_ident_string (snd fbody) iss in

    (* Params differ only for eBPF *)
    if fd.(is_ebpf) then
      match transform_ctx_ebpf_ctx (zip (unzip1 fd.(fn_args)) (unzip2 fd.(fn_args))) with
      | Error msg => Error msg
      | OK params =>
          OK ({| fn_return   := crt
               ; fn_callconv := cc_of_variadic (get_v_function fd)
               ; fn_params   := params
               ; fn_vars     := locals
               ; fn_body     := fst fbody |},
              is', bctx')
      end
    else
      let param_tys := transBeePL_types transBeePL_type (unzip2 fd.(fn_args)) in
      let params    := zip (unzip1 fd.(fn_args)) param_tys in
      OK ({| fn_return   := crt
           ; fn_callconv := cc_of_variadic (get_v_function fd)
           ; fn_params   := params
           ; fn_vars     := locals
           ; fn_body     := fst fbody |},
         is', bctx')
  end
end.


Local Open Scope error_monad_scope.


Definition transBeePL_fundef_fundef (cenv : bcomposite_env) (fd : BeePL.fundef) (iss : list (ident * string)) (bctx : bcompiler_ctx) : 
res (Csyntax.fundef * list (ident * string) * bcompiler_ctx) :=
match fd with 
| Internal f => do (tf, is') <- transBeePL_function_function cenv f iss bctx;
                OK (Ctypes.Internal (fst tf), snd tf, is')
| External ef ts t cc => let cef := (befunction_to_cefunction ef) in
                         let cts := map Ctypes.typeconv (transBeePL_types transBeePL_type ts) in
                         let ct := (transBeePL_type t) in
                         OK ((Ctypes.External cef cts ct cc), iss, bctx)
end.

(* Translates the value that is assigned to global variable to C global variable data *)

(*Definition transBeePL_init_data_init_data (g : BeePL.init_data) : AST.init_data :=
match g with 
| Init_int8 i => AST.Init_int8 i
| Init_int16 i => AST.Init_int16 i
| Init_int32 i => AST.Init_int32 i
| Init_int64 i => AST.Init_int64 i
end. 

(* Translates the list of global variable data to list of C global variable data *)
Fixpoint transBeePL_init_datas_init_datas (gs : list BeePL.init_data) : list AST.init_data :=
match gs with 
| nil => nil
| g :: gs => transBeePL_init_data_init_data g :: transBeePL_init_datas_init_datas gs
end. *)

(* Translates BeePL global variable to C global variable *)
Definition transBeePLglobvar_globvar (gv : BeePL.globvar type) : 
(AST.globvar Ctypes.type * list composite_definition) :=
let gvt := transBeePL_type (gv.(gvar_info)) in
       ({| AST.gvar_info := gvt; 
           AST.gvar_init := (gv.(gvar_init)); 
           AST.gvar_readonly := gv.(gvar_readonly); 
           AST.gvar_volatile :=  gv.(gvar_volatile)|}, nil).

Definition transBeePL_globdef_globdef
  (cenv : bcomposite_env)
  (gd   : BeePL.globdef BeePL.fundef BeeTypes.type)
  (iss  : list (ident * string))
  (bctx : bcompiler_ctx)
: res (AST.globdef fundef Ctypes.type
      * list (ident * string)
      * list composite_definition
      * bcompiler_ctx) :=
  match gd with 
  | AST.Gfun f =>
      do (cf, bctx') <- transBeePL_fundef_fundef cenv f iss bctx;
      OK (AST.Gfun (fst cf), (snd cf), nil, bctx')

  | AST.Gvar g =>
      let '(cg, comps) := transBeePLglobvar_globvar g in
      OK (AST.Gvar cg, iss, comps, bctx)
  end.


Fixpoint transBeePL_globdefs_globdefs (cenv : bcomposite_env) (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) (iss : list (ident * string)) (bctx : bcompiler_ctx) : 
res (list (AST.globdef fundef Ctypes.type) * list (ident * string) * list composite_definition * bcompiler_ctx) :=
match gds with 
| nil => OK (nil, iss, nil, bctx)
| d :: ds => do (gd, is') <-  transBeePL_globdef_globdef cenv d iss bctx; 
             do (gds, is'') <- transBeePL_globdefs_globdefs cenv ds (snd (fst gd)) is';
             OK ((fst (fst gd) :: fst (fst gds)), (snd (fst gds)), (snd gd ++ snd gds)%list, is'')
end.

(* CompCert stores section information in a global hash table called decl_atom,
   which is defined in C2C.ml. decl_atom's key is defined in Coq but it's value,
   a record called atom_info, is defined in OCaml. Until atom_info is moved from
   OCaml to Coq redefine only what is required for use of sections in eBPF 
   programs. TODO: move atom_info completely into Coq *)
Inductive section_name : Type :=
  | Section_literal : int (* literal size; zero if unknown *) -> section_name
  | Section_jumptable : section_name
  | Section_user : string -> bool (*writable*) -> bool (*executable*) -> section_name.

Inductive storage : Type :=
  | Storage_default (* used for toplevel names without explicit storage *)
  | Storage_extern
  | Storage_static
  | Storage_auto    (* used for block-scoped names without explicit storage *)
  | Storage_register.

Inductive inline_status : Type :=
  | No_specifier (* No inline specifier and no noinline attribute *)
  | Noinline     (* The atom is declared with the noinline attribute *)
  | Inline.      (* The atom is declared inline *)

(* Had to deviate from name used in atom_info due to conflict with use of 
   access_mode in BeePL_auxlemmas *)
Inductive sec_access_mode : Type := 
  | Access_default
  | Access_near
  | Access_far.

Record csyntax_atom_info : Type := {
  a_storage : storage;
  a_defined : bool;
  a_size : option int64;
  a_alignment : option int;
  a_section : list section_name;
  a_access : sec_access_mode;
  a_inline : inline_status;
  a_loc : string (*filename*) * int; (*line number*)
}.

Fixpoint get_section_info (glob_defs : list (ident * AST.globdef BeePL.fundef type * option string)) (env : bcomposite_env) : list (ident * csyntax_atom_info) :=
  match glob_defs with
  | nil => nil
  | (id, AST.Gfun _, sec) :: rest =>
      let tail := get_section_info rest env in
      match sec with
      | Some s =>
        (* User defined functions should be immutable and executable. In testing
           we found that CompCert adds Section_literal(0) and Section_jumptable 
           when __attribute__(section("section_name") is used so we do too *)
        let section_list := Section_user s false (*writable*) true (*executable*) :: 
                            Section_literal (Int.repr 0) :: 
                            Section_jumptable :: nil in
        let info := {|
          a_storage := Storage_default;
          a_defined := true; (* taking it as true, not sure as of now how ebpf backend use it *)
          (* CompCert does not specify a_size and a_alignment for functions *)
          a_size := None;
          a_alignment := None;
          a_section := section_list;
          a_access := Access_default;
          a_inline := No_specifier;
          (* Currently location information is not stored in BeePL.program. When
             we implment a parser we can decise if we should do that*)
          a_loc := ("", (Int.repr 0))
        |} in
        (id, info) :: tail
      | None => tail
      end
  | (id, AST.Gvar gv, sec) :: rest =>
      let gvar_t : BeeTypes.type := gvar_info gv in
      let tail := get_section_info rest env in
      match sec with
      | Some "license" =>
        (* License global variables should be only readable *)
        let section_list := Section_user "license" false (*not writable*) false (*executable*) :: nil in
        let info := {|
          a_storage := Storage_default;
          (* TODO: global variables do need to specify a_size and a_alignment. How does CompCert do it? *)       
          a_defined := true;
          a_size := Some (Int64.repr (BeeTypes.sizeof_type env gvar_t)); (* refers to size of global variable - not section name *)
          a_alignment := Some (Int.repr (BeeTypes.alignof_type env gvar_t));
          a_section := section_list;
          a_access := Access_default;
          a_inline := No_specifier;
          (* Currently location information is not stored in BeePL.program. When
             we implment a parser we can decise if we should do that*)
          a_loc := ("", (Int.repr 0))
        |} in
        (id, info) :: tail
      | Some s =>
        (* User defined global variables should be writable and not executable *)
        let section_list := Section_user s true (*writable*) false (*executable*) :: nil in
        let info := {|
          a_storage := Storage_default;
          (* TODO: global variables do need to specify a_size and a_alignment. How does CompCert do it? *)       
          a_defined := true;
          a_size := Some (Int64.repr (BeeTypes.sizeof_type env gvar_t)); (* refers to size of global variable - not section name *)
          a_alignment := Some (Int.repr (BeeTypes.alignof_type env gvar_t));
          a_section := section_list;
          a_access := Access_default;
          a_inline := No_specifier;
          (* Currently location information is not stored in BeePL.program. When
             we implment a parser we can decise if we should do that*)
          a_loc := ("", (Int.repr 0))
        |} in
        (id, info) :: tail
      | None => tail
      end
  end.

(* Does this BeePL program contain any eBPF function? *)
Definition program_uses_ebpf_ctx (p : BeePL.program) : bool :=
  existsb
    (fun '(_, gd, _) =>
       match gd with
       | AST.Gfun (BeePL.Internal f) =>
           if BeePL.is_ebpf f then true else false
       | _ => false
       end)
    (prog_defs p).

(* Safe lookup: first key with equality A_eqb in (key * value) list *)
Fixpoint assoc_opt {A B : Type}
         (A_eqb : A -> A -> bool)
         (k : A) (xs : list (A * B)) : option B :=
  match xs with
  | nil => None
  | (k', v) :: tl =>
      if A_eqb k k' then Some v else assoc_opt A_eqb k tl
  end.

Definition have_xdp_md_aux
           (cs : list composite_definition)
           (id2string : list (ident * string)) : bool :=
  existsb
    (fun c =>
       match c with
       | Composite id _ _ _ =>
           match assoc_opt ident_eq id id2string with
           | Some s => if String.eqb s "xdp_md" then true else false
           | None   => false
           end
       end)
    cs.

Definition is_xdp_md (id : ident) : bool :=
  ident_eq id _xdp_md.

Definition filter_out_xdp_md (cs : list composite_definition) : list composite_definition :=
  List.filter
    (fun c =>
       match c with
       | Composite id _ _ _ => negb (is_xdp_md id)
       end)
    cs.

Definition idset_of_defs (defs : list (ident * AST.globdef BeePL.fundef BeeTypes.type * option string))
  : PTree.t unit :=
  List.fold_left
    (fun acc '(id, _, _) => PTree.set id tt acc)
    defs (PTree.empty unit).

Fixpoint missing_public
         (pub : list ident) (t : PTree.t unit) : list ident :=
  match pub with
  | nil => nil
  | id :: tl =>
      match PTree.get id t with
      | Some _ => missing_public tl t
      | None   => id :: missing_public tl t
      end
  end.

(* pretty-print missing ids with their strings, if available *)
Definition show_missing
           (miss : list ident) (iss : list (ident * string)) : string :=
  let name_of id :=
    match assoc_opt ident_eq id iss with
    | Some s => s
    | None   => NilZero.string_of_uint (Nat.to_uint (Pos.to_nat id))
    end in
  String.concat ", " (List.map name_of miss).

(*Definition check_public_defined
           (defs : list (ident * AST.globdef BeePL.fundef BeeTypes.type * option string))
           (pub  : list ident)
           (iss  : list (ident * string)) : res unit :=
  let t := idset_of_defs defs in
  let miss := missing_public pub t in
  match miss with
  | nil => OK tt
  | _ =>
      Error (MSG "Unusedglob: reference to undefined global(s): "
             :: MSG (show_missing miss iss) :: nil)
  end.*)

Definition BeePL_compcert
           (p : BeePL.program)
  : res (Csyntax.program
         * list (ident * string)
         * list (ident * csyntax_atom_info)) :=
  (* alpha renaming 
  let p := rename_prog p in *)
  (* 1. Raw section info from BeePL program *)
  let section_info_all :=
    get_section_info (prog_defs p) (prog_comp_env p) in

  (* 2. Extract (id, globdef) pairs from prog_defs *)
  let defs :=
    map (fun '(id, gd, _) => (id, gd)) p.(prog_defs) in

  (* 3. Seed ident->string and compiler ctx *)
  let iss0 : list (ident * string) :=
    (ident_to_string_ctx_xdp ++ prog_ident_to_string p)%list in
  let bctx : bcompiler_ctx :=
    {| arg_ctx := get_args_ebpf_gbdefs (unzip2 defs);
       benv    := prog_comp_env p;
       reserved_identifiers := (map fst defs ++ map fst iss0)%list;
       lexical_bindings := empty_compiler_bindings |} in

  (* 4. Sanity-check structs *)
  do cp <- check_struct_from_program p;
  do represented <- check_compiler_representation p;
  do noescape <- check_reference_escapes p;

  (* 5. Translate BeePL → C *)
  do (pds, bctx') <-
       transBeePL_globdefs_globdefs
         (prog_comp_env p)
         (unzip2 defs)
         iss0
         bctx;
  let '(cdefs, id2string, extra_cs) := pds in
  let extra_cs' := filter_out_xdp_md extra_cs in

  let ncs := get_bcs_from_globdefs (unzip2 defs) in
  let cs  := map bcomposite_ccomposite_definition p.(prog_types) in
  let base_mcs := (ncs ++ extra_cs' ++ cs)%list in

  let needs_ebpf_ctx := program_uses_ebpf_ctx p in
  let has_xdp_md     := have_xdp_md_aux base_mcs id2string in
  let mcs :=
    if needs_ebpf_ctx && negb has_xdp_md
    then xdp_md_ccomposite :: base_mcs    (* ensure xdp_md exists *)
    else base_mcs in

 (* filter public ids to only those with definitions *)
  let def_ids := unzip1 defs in
  let public_ids :=
    List.filter
      (fun id => existsb (fun id' => ident_eq id id') def_ids)
      (prog_public p) in

  (* 6. Build final C program *)
  do cprog <-
       make_program
         mcs
         (zip (unzip1 defs) cdefs)
         public_ids
         (prog_main p);

  (* 7. FILTER section info to ids that actually exist in cprog *)
  let prog_ids :=
    List.map (@fst _ _) (AST.prog_defs cprog) in

  let section_info :=
    List.filter
      (fun '(id, _ai) =>
         existsb (fun id' => ident_eq id id') prog_ids)
      section_info_all in

  OK (cprog, id2string, section_info).








