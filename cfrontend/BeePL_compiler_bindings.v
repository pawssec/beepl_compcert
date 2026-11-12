(* Lexical bindings for lowering BeePL scopes to flat C local declarations.
   This environment is separate from the accumulated storage catalogue.
   Scope exit restores the incoming environment, but retains generated storage.
   In particular, fn_vars entries must not populate this environment. *)
Require Import Coqlib Maps AST Integers BeeTypes BeePL Csyntax.


Inductive compiler_binding : Type :=
| Binding_slot (target : ident)
| Binding_unit.

Definition compiler_bindings := PTree.t compiler_binding.
Definition empty_compiler_bindings : compiler_bindings := PTree.empty _.
Definition push_compiler_binding (env : compiler_bindings) (source : ident)
    (binding : compiler_binding) : compiler_bindings := PTree.set source binding env.

(* The caller retains [outer]; no inverse mutation or name-based removal is
   needed to restore a shadowed binding after translating a nested scope. *)
Definition restore_compiler_bindings (outer inner : compiler_bindings)
    : compiler_bindings := outer.

Definition compiler_bound_value (read_variable : ident -> BeeTypes.type -> Csyntax.expr) (env : compiler_bindings) (source : ident)
    (ty : BeeTypes.type) : Csyntax.expr :=
  match PTree.get source env with
  | Some (Binding_slot target) => read_variable target ty
  | Some Binding_unit => Csyntax.Eval (Values.Vint Int.zero) (transBeePL_type ty)
  | None => read_variable source ty
  end.

(* Array accesses and explicitly selected destinations require storage, unlike
   a unit-valued source variable. A missing lexical entry denotes an unchanged
   parameter/global identifier, not a declaration from fn_vars. *)
Definition compiler_bound_storage (env : compiler_bindings) (source : ident)
    : option ident :=
  match PTree.get source env with
  | Some (Binding_slot target) => Some target
  | Some Binding_unit => None
  | None => Some source
  end.

Lemma compiler_binding_shadow : forall env source binding,
  PTree.get source (push_compiler_binding env source binding) = Some binding.
Proof. intros; apply PTree.gss. Qed.

Lemma compiler_binding_other : forall env source other binding,
  other <> source ->
  PTree.get other (push_compiler_binding env source binding) = PTree.get other env.
Proof. intros; apply PTree.gso; assumption. Qed.

Lemma compiler_binding_restore : forall outer inner source,
  PTree.get source (restore_compiler_bindings outer inner) = PTree.get source outer.
Proof. reflexivity. Qed.

Lemma compiler_empty_preserves_global : forall read_variable source ty,
  compiler_bound_value read_variable empty_compiler_bindings source ty =
    read_variable source ty.
Proof. reflexivity. Qed.

Lemma compiler_bound_value_type : forall read_variable,
  (forall source ty, Csyntax.typeof (read_variable source ty) = transBeePL_type ty) ->
  forall env source ty,
  Csyntax.typeof (compiler_bound_value read_variable env source ty) = transBeePL_type ty.
Proof.
  intros read_variable Hread env source ty. unfold compiler_bound_value.
  destruct (PTree.get source env) as [[target|]|]; simpl; auto.
Qed.

Lemma compiler_unit_needs_no_storage : forall env source,
  compiler_bound_storage (push_compiler_binding env source Binding_unit) source = None.
Proof. intros; unfold compiler_bound_storage; rewrite compiler_binding_shadow; reflexivity. Qed.

Lemma compiler_fresh_slot_access : forall env source target,
  compiler_bound_storage (push_compiler_binding env source (Binding_slot target)) source = Some target.
Proof. intros; unfold compiler_bound_storage; rewrite compiler_binding_shadow; reflexivity. Qed.

Example nested_shadow_restores_outer :
  let outer := push_compiler_binding empty_compiler_bindings 1%positive (Binding_slot 10%positive) in
  let inner := push_compiler_binding outer 1%positive (Binding_slot 11%positive) in
  compiler_bound_storage inner 1%positive = Some 11%positive /\
  compiler_bound_storage (restore_compiler_bindings outer inner) 1%positive = Some 10%positive.
Proof. split; reflexivity. Qed.

Example storage_catalog_does_not_shadow_global :
  compiler_bound_storage empty_compiler_bindings 1%positive = Some 1%positive.
Proof. reflexivity. Qed.

Print Assumptions compiler_bound_value_type.
Print Assumptions compiler_binding_other.
Print Assumptions nested_shadow_restores_outer.

(* Unlike free_variables, freshness exclusions include shadowed binders and
   identifiers in branches that have not yet been translated. *)
Section SourceNamesList.
Variable names : BeePL.expr -> list ident.
Fixpoint compiler_source_names_list (es : list BeePL.expr) : list ident :=
  match es with
  | nil => nil
  | e :: tail => (names e ++ compiler_source_names_list tail)%list
  end.
End SourceNamesList.

Fixpoint compiler_source_names (e : BeePL.expr) : list ident :=
  match e with
  | Var x _ => x :: nil
  | Bind x _ rhs body _ => (x :: compiler_source_names rhs ++ compiler_source_names body)%list
  | App fn args _ => (compiler_source_names fn ++ compiler_source_names_list compiler_source_names args)%list
  | Prim _ args _ | Sinit _ _ args _ | Ebytes args _ => compiler_source_names_list compiler_source_names args
  | Cond guard yes no _ => (compiler_source_names guard ++ compiler_source_names yes ++ compiler_source_names no)%list
  | For lower upper _ body _ => (compiler_source_names lower ++ compiler_source_names upper ++ compiler_source_names body)%list
  | Sfield base _ _ | Esome base _ => compiler_source_names base
  | Match scrutinee patterns branches _ =>
      (compiler_source_names scrutinee ++ List.flat_map vars_bound_by patterns ++
       compiler_source_names_list compiler_source_names branches)%list
  | Ainit destination _ args _ => destination :: compiler_source_names_list compiler_source_names args
  | Aaccess source _ _ _ => source :: nil
  | LoopFrame _ template active => (compiler_source_names template ++ compiler_source_names active)%list
  | CallFrame _ body _ => compiler_source_names body
  | _ => nil
  end.
