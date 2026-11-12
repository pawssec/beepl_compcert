(* Executable compiler representation boundary. Surface Bool is Tbool;
   raw Coq Tint IBool has incompatible source and C storage/cast semantics.
   This check rejects that constructor wherever it occurs, without changing
   declarative source typing or imposing reference-lifetime policy. *)
Require Import List Bool String ZArith Coqlib AST Maps Ctypes Errors.
Require Import BeeTypes BeePL.
Import ListNotations.
Local Open Scope list_scope.

Definition primitive_representation_check (pt : primitive_type) : bool :=
  match pt with Tint IBool _ _ => false | _ => true end.
Definition basic_primitive_occurrences (bt : basic_type) : list primitive_type :=
  match bt with Bprim pt | Barray pt _ _ => [pt] | Bstruct _ _ => [] end.
Fixpoint type_primitive_occurrences (ty : BeeTypes.type) : list primitive_type :=
  match ty with
  | Utype | Stype _ _ | Bytes => []
  | Vtype pt => [pt]
  | Ptrtype pt => pointer_primitive_occurrences pt
  | Atype elem _ _ => type_primitive_occurrences elem
  | Ftype args _ result _ =>
      List.concat (map type_primitive_occurrences args) ++ type_primitive_occurrences result
  end
with pointer_primitive_occurrences (pt : ptr_type) : list primitive_type :=
  match pt with
  | Reftype bt _ => basic_primitive_occurrences bt
  | Otype inner => pointer_primitive_occurrences inner
  | Fptype args _ result _ =>
      List.concat (map type_primitive_occurrences args) ++ type_primitive_occurrences result
  end.
Definition representation_type_check ty :=
  forallb primitive_representation_check (type_primitive_occurrences ty).
Definition annotated_types_occurrences (fields : list(ident * BeeTypes.type)) :=
  List.concat(map (fun field=>type_primitive_occurrences(snd field)) fields).
Definition pattern_primitive_occurrences pat :=
  match pat with
  | Pnone | Psome _ => []
  | Pbytes _ ty fields => type_primitive_occurrences ty ++ annotated_types_occurrences fields
  end.
Definition builtin_primitive_occurrences op :=
  match op with Cast ty => type_primitive_occurrences ty | _=>[] end.
Fixpoint expression_primitive_occurrences (e : BeePL.expr) : list primitive_type :=
  match e with
  | Val _ ty | Var _ ty | Const _ ty | Unit ty | Addr _ _ ty | Enone ty =>
      type_primitive_occurrences ty
  | App callee args ty => type_primitive_occurrences ty ++
      expression_primitive_occurrences callee ++ List.concat(map expression_primitive_occurrences args)
  | Prim op args ty => type_primitive_occurrences ty ++ builtin_primitive_occurrences op ++
      List.concat(map expression_primitive_occurrences args)
  | Bind _ bound init body ty => type_primitive_occurrences ty ++ type_primitive_occurrences bound ++
      expression_primitive_occurrences init ++ expression_primitive_occurrences body
  | Cond guard yes no ty | For guard yes _ no ty => type_primitive_occurrences ty ++
      expression_primitive_occurrences guard ++ expression_primitive_occurrences yes ++
      expression_primitive_occurrences no
  | Sinit _ _ args ty | Ebytes args ty => type_primitive_occurrences ty ++
      List.concat(map expression_primitive_occurrences args)
  | Sfield value _ ty | Esome value ty => type_primitive_occurrences ty ++ expression_primitive_occurrences value
  | Match value patterns branches ty => type_primitive_occurrences ty ++
      expression_primitive_occurrences value ++ List.concat(map pattern_primitive_occurrences patterns) ++
      List.concat(map expression_primitive_occurrences branches)
  | Ainit _ stored args ty => type_primitive_occurrences ty ++ type_primitive_occurrences stored ++
      List.concat(map expression_primitive_occurrences args)
  | Aaccess _ stored _ ty => type_primitive_occurrences ty ++ type_primitive_occurrences stored
  | CallFrame vm body ty => type_primitive_occurrences ty ++
      List.concat(map (fun entry=>type_primitive_occurrences(snd(snd entry))) (PTree.elements vm)) ++
      expression_primitive_occurrences body
  | LoopFrame _ body template => expression_primitive_occurrences body ++ expression_primitive_occurrences template
  end.
Definition representation_expression_check e :=
  forallb primitive_representation_check (expression_primitive_occurrences e).
Definition function_primitive_occurrences fn :=
  type_primitive_occurrences(fn_return fn) ++ annotated_types_occurrences(fn_args fn) ++
  annotated_types_occurrences(fn_vars fn) ++ expression_primitive_occurrences(fn_body fn).
Definition fundef_primitive_occurrences fd :=
  match fd with
  | Internal fn => function_primitive_occurrences fn
  | External (EF_external _ signature) args result _ =>
      List.concat(map type_primitive_occurrences args) ++ type_primitive_occurrences result ++
      List.concat(map type_primitive_occurrences(bsig_args signature)) ++
      type_primitive_occurrences(bsig_res signature)
  end.
Definition members_primitive_occurrences members :=
  List.concat(map (fun member=>type_primitive_occurrences(type_bmember member)) members).
Definition composite_primitive_occurrences definition :=
  match definition with Bcomposite _ _ members _ => members_primitive_occurrences members end.
Definition global_primitive_occurrences (definition : ident * AST.globdef BeePL.fundef BeeTypes.type * option string) :=
  match definition with
  | (_,Gfun fd,_) => fundef_primitive_occurrences fd
  | (_,Gvar variable,_) => type_primitive_occurrences(gvar_info variable)
  end.
Definition program_primitive_occurrences p :=
  List.concat(map global_primitive_occurrences(prog_defs p)) ++
  List.concat(map composite_primitive_occurrences(prog_types p)) ++
  List.concat(map (fun entry=>members_primitive_occurrences(co_members(snd entry)))
    (PTree.elements(prog_comp_env p))).
Definition representation_program_check p :=
  forallb primitive_representation_check (program_primitive_occurrences p).
Definition check_compiler_representation p : res unit :=
  if representation_program_check p then OK tt
  else Error [MSG "Compiler representation check failed: raw IBool is unsupported"].

Definition primitive_representation_safe pt := forall signed attr,
  pt <> Tint IBool signed attr.
Lemma primitive_representation_check_spec : forall pt,
  primitive_representation_check pt=true <-> primitive_representation_safe pt.
Proof.
  intros [|size signed attr|signed attr]; unfold primitive_representation_safe; simpl.
  - split; intros; try reflexivity; discriminate.
  - destruct size; simpl; split; intros; try discriminate; try reflexivity.
    exfalso; eapply H; reflexivity.
  - split; intros; try reflexivity; discriminate.
Qed.
Lemma primitive_occurrences_check_spec : forall occurrences,
  forallb primitive_representation_check occurrences=true <->
  Forall primitive_representation_safe occurrences.
Proof.
  intros. rewrite forallb_forall,Forall_forall. split; intros H pt Hin;
    apply primitive_representation_check_spec; auto.
Qed.
Theorem representation_program_check_spec : forall p,
  representation_program_check p=true <->
  Forall primitive_representation_safe(program_primitive_occurrences p).
Proof. intros; apply primitive_occurrences_check_spec. Qed.
Theorem successful_representation_check_excludes_ibool : forall p result signed attr,
  check_compiler_representation p=OK result ->
  ~In (Tint IBool signed attr)(program_primitive_occurrences p).
Proof.
  intros p result signed attr H Hin. unfold check_compiler_representation in H.
  destruct(representation_program_check p) eqn:E; try discriminate.
  apply representation_program_check_spec in E.
  rewrite Forall_forall in E. specialize(E _ Hin). eapply E; reflexivity.
Qed.
Lemma primitive_type_representation_check : forall pt,
  representation_type_check(Vtype pt)=true -> primitive_representation_safe pt.
Proof. intros pt H; apply primitive_representation_check_spec. simpl in H. apply andb_true_iff in H; tauto. Qed.

Example surface_bool_representation : representation_type_check(Vtype Tbool)=true.
Proof. reflexivity. Qed.
Example nested_options_representation :
  representation_type_check(Ptrtype(Otype(Otype(Reftype(Bprim Tbool)noattr))))=true.
Proof. reflexivity. Qed.
Example nested_raw_ibool_rejected :
  representation_type_check (Atype (Ptrtype (Otype (Reftype (Bprim (Tint IBool Unsigned noattr)) noattr))) 3 noattr) = false.
Proof. reflexivity. Qed.
Example signature_raw_ibool_rejected :
  representation_type_check(Ftype [Vtype Tbool] [] (Vtype(Tint IBool Signed noattr)) false)=false.
Proof. reflexivity. Qed.
Print Assumptions representation_program_check_spec.
Print Assumptions successful_representation_check_excludes_ibool.

Theorem checked_program_internal_function_representation : forall p id fn section,
  representation_program_check p=true ->
  In (id,Gfun(Internal fn),section)(prog_defs p) ->
  Forall primitive_representation_safe(function_primitive_occurrences fn).
Proof.
  intros p id fn section Hcheck Hfn.
  apply representation_program_check_spec in Hcheck.
  rewrite Forall_forall in Hcheck |- *. intros pt Hin. apply Hcheck.
  unfold program_primitive_occurrences. apply in_or_app; left.
  apply in_concat. exists (function_primitive_occurrences fn); split; [|exact Hin].
  apply in_map_iff. exists (id,Gfun(Internal fn),section); split; [reflexivity|exact Hfn].
Qed.

Theorem checked_function_return_representation : forall fn,
  Forall primitive_representation_safe(function_primitive_occurrences fn) ->
  representation_type_check(fn_return fn)=true.
Proof.
  intros fn H. unfold function_primitive_occurrences in H.
  apply Forall_app in H as [H _]. apply primitive_occurrences_check_spec; exact H.
Qed.
Theorem checked_function_body_representation : forall fn,
  Forall primitive_representation_safe(function_primitive_occurrences fn) ->
  representation_expression_check(fn_body fn)=true.
Proof.
  intros fn H. unfold function_primitive_occurrences in H.
  repeat rewrite Forall_app in H. destruct H as [_ [_ [_ H]]].
  apply primitive_occurrences_check_spec; exact H.
Qed.

Example cast_annotation_raw_ibool_rejected : forall operand,
  representation_expression_check
    (Prim (Cast (Vtype(Tint IBool Unsigned noattr))) [operand] (Vtype Tbool))=false.
Proof. intros; reflexivity. Qed.
Example pattern_field_raw_ibool_rejected :
  representation_expression_check
    (Match (Unit Utype)
      [Pbytes 1%positive Utype [(2%positive,Vtype(Tint IBool Unsigned noattr))]]
      [Unit Utype] Utype)=false.
Proof. reflexivity. Qed.
Print Assumptions checked_program_internal_function_representation.
