(* Conservative compilation subset for stack-backed references. This is a
   syntactic gate, not a lifetime inference algorithm or a semantic simulation.
   Its interpretation assumes a well-typed source AST and the explicit external
   helper contracts in BeePL_escape_helpers. *)
Require Import List Bool String ZArith Coqlib AST Maps Errors BeeTypes BeePL.
Require Import BeePL_escape_types BeePL_escape_helpers.
Import ListNotations.

Definition escape_identifier_in (id : ident) (ids : list ident) : bool :=
  existsb (Pos.eqb id) ids.

Fixpoint escape_lookup_function (id : ident)
    (defs : list (ident * AST.globdef BeePL.fundef type * option string))
    : option BeePL.fundef :=
  match defs with
  | [] => None
  | (name, gd, _) :: rest =>
      if ident_eq id name then
        match gd with Gfun f => Some f | Gvar _ => None end
      else escape_lookup_function id rest
  end.

Definition escape_primitive_check (env : bcomposite_env)
    (op : builtin) (args : list expr) : bool :=
  match op, args with
  | Massgn, [_; value] => reference_free_type_check env (typeof_expr value)
  | Massgn, _ => false
  | Cast target, [value] =>
      reference_free_type_check env target &&
      reference_free_type_check env (typeof_expr value)
  | Cast _, _ => false
  | Uop _, _ | Bop _, _ =>
      forallb (fun value => reference_free_type_check env (typeof_expr value)) args
  | _, _ => true
  end.

Definition escape_call_check (p : BeePL.program) (locals shadow : list ident)
    (callee : expr) (args : list expr) (result : type) : bool :=
  match callee with
  | Var id annotation =>
      negb (escape_identifier_in id (locals ++ shadow)) &&
      match escape_lookup_function id (prog_defs p) with
      | Some (Internal fd) =>
          eq_type annotation (type_of_function fd) &&
          eq_types eq_type (typeof_exprs args) (map snd (fn_args fd)) &&
          eq_type result (fn_return fd) &&
          reference_free_type_check (prog_comp_env p) (fn_return fd)
      | Some (External ef ts rt cc) =>
          eq_type result rt &&
          synchronous_helper_call (prog_ident_to_string p)
            (External ef ts rt cc) args
      | None => false
      end
  | _ => false
  end.

Definition escape_local_array (p : BeePL.program) (fd : function)
    (shadow : list ident) (id : ident) (ty result : type) : bool :=
  match ty with
  | Atype _ _ _ =>
      negb (escape_identifier_in id
        (shadow ++ map fst (fn_args fd) ++
         map (fun '(name, _, _) => name) (prog_defs p))) &&
      existsb (fun '(name, declared) => Pos.eqb id name && eq_type ty declared)
        (fn_vars fd) && eq_type ty result
  | _ => false
  end.

Fixpoint escape_expression_check (p : BeePL.program) (fd : function)
    (shadow : list ident) (e : expr) {struct e} : bool :=
  let recurse := escape_expression_check p fd shadow in
  let children := fun es => forallb recurse es in
  match e with
  | Val _ ty => reference_free_type_check (prog_comp_env p) ty
  | Var _ _ | Const _ _ | Unit _ | Enone _ | Aaccess _ _ _ _ => true
  | App callee args result =>
      escape_call_check p (map fst (fn_vars fd)) shadow callee args result &&
      children args
  | Prim op args _ =>
      escape_primitive_check (prog_comp_env p) op args && children args
  | Bind id _ initializer body _ =>
      recurse initializer && escape_expression_check p fd (id :: shadow) body
  | Cond condition yes no _ => recurse condition && recurse yes && recurse no
  | Sinit _ _ args _ | Ebytes args _ => children args
  | Sfield value _ _ | Esome value _ => recurse value
  | For lower upper _ body _ => recurse lower && recurse upper && recurse body
  | Match value patterns branches _ =>
      recurse value &&
      forallb (escape_expression_check p fd (get_patterns_var patterns ++ shadow)) branches
  | Ainit id ty args result =>
      escape_local_array p fd shadow id ty result && children args
  | Addr _ _ _ | CallFrame _ _ _ | LoopFrame _ _ _ => false
  end.

Definition escape_function_check (p : BeePL.program) (fd : function) : bool :=
  reference_free_type_check (prog_comp_env p) (fn_return fd) &&
  escape_expression_check p fd (map fst (fn_args fd)) (fn_body fd).

Definition escape_program_check (p : BeePL.program) : bool :=
  (if list_norepet_dec ident_eq (map (fun '(id, _, _) => id) (prog_defs p))
   then true else false) &&
  forallb (fun '(_, gd, _) =>
    match gd with
    | Gfun (Internal fd) => escape_function_check p fd
    | _ => true
    end) (prog_defs p).

Definition check_reference_escapes (p : BeePL.program) : res unit :=
  if escape_program_check p then OK tt
  else Error [MSG "Reference escape check failed"].

Lemma checked_function_reference_free_result : forall p fd,
  escape_function_check p fd = true ->
  reference_free_type_check (prog_comp_env p) (fn_return fd) = true.
Proof. intros p fd H. apply andb_true_iff in H. exact (proj1 H). Qed.

Lemma checked_program_internal_function : forall p id fd section,
  escape_program_check p = true ->
  In (id, Gfun (Internal fd), section) (prog_defs p) ->
  escape_function_check p fd = true.
Proof.
  intros p id fd section H Hin. unfold escape_program_check in H.
  apply andb_true_iff in H as [_ H].
  rewrite forallb_forall in H. exact (H _ Hin).
Qed.

Lemma checked_store_reference_free : forall p fd shadow target value ty,
  escape_expression_check p fd shadow (Prim Massgn [target; value] ty) = true ->
  reference_free_type_check (prog_comp_env p) (typeof_expr value) = true.
Proof. intros p fd shadow target value ty H. apply andb_true_iff in H. exact (proj1 H). Qed.

Lemma check_reference_escapes_success : forall p result,
  check_reference_escapes p = OK result -> escape_program_check p = true.
Proof.
  intros p result. unfold check_reference_escapes.
  destruct (escape_program_check p); intros H; [reflexivity | discriminate].
Qed.
