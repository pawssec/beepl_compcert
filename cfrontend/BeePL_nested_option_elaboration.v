(* Typing of the core templates used by nested-option elaboration.  This is
   not a correctness theorem for the OCaml traversal or its name generator.
   Metadata and branch typing are explicit, ordinary core typing facts. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas BeePL_storage_types.
Import ListNotations.

Definition nested_option_word : primitive_type :=
 if Archi.ptr64 then Tlong Unsigned noattr else Tint I32 Unsigned noattr.
Definition nested_option_tag (present:bool) : expr :=
 let n := if present then 1 else 0 in
 if Archi.ptr64 then
 Prim(Cast(Vtype nested_option_word))
   [Const(ConsLong(Int64.repr n))(Vtype(Tlong Signed noattr))](Vtype nested_option_word)
 else
 Prim(Cast(Vtype nested_option_word))
   [Const(ConsInt(Int.repr n))(Vtype(Tint I32 Signed noattr))](Vtype nested_option_word).

Lemma nested_option_tag_typed : forall env Gamma Sigma present,
 type_expr env Gamma Sigma(nested_option_tag present)[] (Vtype nested_option_word).
Proof.
 intros. unfold nested_option_tag,nested_option_word;destruct Archi.ptr64.
 - eapply ty_cast with(source:=Tlong Signed noattr);[apply ty_constlong|reflexivity].
 - eapply ty_cast with(source:=Tint I32 Signed noattr);[apply ty_constint|reflexivity].
Qed.

Record nested_option_metadata env sid tag payload payload_type (co:bcomposite) : Prop := {
 nested_metadata_lookup : env!sid=Some co;
 nested_metadata_members : co_members co=[BeeTypes.Member_plain tag (Vtype nested_option_word);BeeTypes.Member_plain payload payload_type];
 nested_metadata_distinct : tag<>payload;
 nested_metadata_storage : storage_type_check env(Stype sid noattr)=true
}.

Lemma nested_option_source_members : forall env sid tag payload payload_type co,
 nested_option_metadata env sid tag payload payload_type co ->
 source_member_types [tag;payload](co_members co)=OK [Vtype nested_option_word;payload_type].
Proof.
 intros * [Hlookup Hmembers Hdistinct Hstorage]. rewrite Hmembers.
 simpl. destruct(ident_eq tag tag);[|contradiction].
 destruct(ident_eq payload tag);[congruence|].
 destruct(ident_eq payload payload);[reflexivity|contradiction].
Qed.

Theorem nested_option_constructor_typed : forall env Gamma Sigma sid tag payload payload_type co present body ef,
 nested_option_metadata env sid tag payload payload_type co ->
 type_expr env Gamma Sigma body ef payload_type ->
 type_expr env Gamma Sigma
 (Sinit sid [tag;payload] [nested_option_tag present;body](Stype sid noattr)) ef (Stype sid noattr).
Proof.
 intros * Hmeta Hbody. destruct Hmeta as [Hlookup Hmembers Hdistinct Hstorage].
 eapply ty_sinit with(co:=co)(bts:=[Vtype nested_option_word;payload_type])(a:=noattr).
 - reflexivity.
 - left;reflexivity.
 - change ef with([]++ef). apply ty_cons;[apply nested_option_tag_typed|].
   rewrite <- (app_nil_r ef). apply ty_cons;[exact Hbody|constructor].
 - exact Hlookup.
 - rewrite Hmembers;reflexivity.
 - reflexivity.
 - eapply nested_option_source_members;constructor;eassumption.
 - exact Hstorage.
Qed.

Theorem nested_option_none_typed : forall env Gamma Sigma sid tag payload payload_type co canonical_none,
 nested_option_metadata env sid tag payload payload_type co ->
 type_expr env Gamma Sigma canonical_none [] payload_type ->
 type_expr env Gamma Sigma
 (Sinit sid [tag;payload] [nested_option_tag false;canonical_none](Stype sid noattr)) [] (Stype sid noattr).
Proof. intros;eapply nested_option_constructor_typed;eassumption. Qed.

Theorem nested_option_some_once_typed : forall env Gamma Sigma sid tag payload payload_type co temp body ef,
 nested_option_metadata env sid tag payload payload_type co ->
 type_expr env Gamma Sigma body ef payload_type ->
 type_expr env Gamma Sigma
 (Bind temp payload_type body
   (Sinit sid [tag;payload] [nested_option_tag true;Var temp payload_type](Stype sid noattr))
   (Stype sid noattr)) ef (Stype sid noattr).
Proof.
 intros * Hmeta Hbody. rewrite <- (app_nil_r ef).
 apply ty_bind;[exact Hbody|]. eapply nested_option_constructor_typed;[exact Hmeta|].
 apply ty_var;unfold extend_context;apply PTree.gss.
Qed.

Lemma nested_option_field_typed : forall env Gamma Sigma sid tag payload payload_type co base ef name ty,
 nested_option_metadata env sid tag payload payload_type co ->
 (name=tag /\ty=Vtype nested_option_word) \/ (name=payload /\ty=payload_type) ->
 type_expr env Gamma Sigma base ef (Stype sid noattr) ->
 type_expr env Gamma Sigma(Sfield base name ty)ef ty.
Proof.
 intros * [Hlookup Hmembers Hdistinct Hstorage] Hfield Hbase.
 destruct Hfield as [[Heq Hty]|[Heq Hty]];subst name ty;
 eapply ty_sfield with(id:=sid)(a:=noattr)(co:=co);
 try exact Hbase;try exact Hlookup.
 all: try solve [left;simpl;rewrite Pos.eqb_refl;reflexivity].
 all: try rewrite Hmembers;unfold Ctyping.type_of_member;simpl;
 repeat match goal with |- context[ident_eq ?x ?y] => destruct(ident_eq x y);try congruence end;
 reflexivity.
Qed.

Definition nested_option_match_template sid tag payload payload_type temp binder scrutinee none_branch some_branch result :=
 Bind temp (Stype sid noattr) scrutinee
 (Cond
  (Prim(Bop Cop.Oeq)
    [Sfield(Var temp(Stype sid noattr))tag(Vtype nested_option_word);nested_option_tag false]
    (Vtype Tbool))
  none_branch
  (Bind binder payload_type(Sfield(Var temp(Stype sid noattr))payload payload_type)some_branch result)
  result) result.

Theorem nested_option_match_typed : forall env Gamma Sigma sid tag payload payload_type co temp binder scrutinee none_branch some_branch result ef ef_none ef_some budget,
 nested_option_metadata env sid tag payload payload_type co ->
 type_expr env Gamma Sigma scrutinee ef (Stype sid noattr) ->
 type_expr env (extend_context Gamma temp(Stype sid noattr)) Sigma none_branch ef_none result ->
 type_expr env (extend_context(extend_context Gamma temp(Stype sid noattr))binder payload_type) Sigma some_branch ef_some result ->
 sub_effect ef_none budget=true -> sub_effect ef_some budget=true ->
 type_expr env Gamma Sigma
 (nested_option_match_template sid tag payload payload_type temp binder scrutinee none_branch some_branch result)
 (ef++budget) result.
Proof.
 intros * Hmeta Hscrut Hnone Hsome HnoneBound HsomeBound.
 unfold nested_option_match_template. apply ty_bind;[exact Hscrut|].
 change budget with([]++budget).
 eapply ty_cond with(ef1:=[])(ef2:=ef_none)(ef3:=ef_some).
 - change (@nil effect_label) with((@nil effect_label)++[]).
   eapply ty_eq with(t:=Vtype nested_option_word).
   + unfold nested_option_word;destruct Archi.ptr64;reflexivity.
   + eapply nested_option_field_typed;[exact Hmeta|left;auto|]. apply ty_var;unfold extend_context;apply PTree.gss.
   + apply nested_option_tag_typed.
 - exact Hnone.
 - change ef_some with([]++ef_some). apply ty_bind;[|exact Hsome].
   eapply nested_option_field_typed;[exact Hmeta|right;auto|]. apply ty_var;unfold extend_context;apply PTree.gss.
 - exact HnoneBound.
 - exact HsomeBound.
Qed.

Print Assumptions nested_option_constructor_typed.
Print Assumptions nested_option_some_once_typed.
Print Assumptions nested_option_match_typed.

Lemma nested_option_compact_none_typed : forall env Gamma Sigma inner,
 is_option_ptr_type inner=false ->
 type_expr env Gamma Sigma(Enone(Ptrtype(Otype inner)))[](Ptrtype(Otype inner)).
Proof. intros;apply ty_none;assumption. Qed.

Definition nested_option_some_first_match_template sid tag payload payload_type temp binder scrutinee some_branch none_branch result :=
 Bind temp (Stype sid noattr) scrutinee
 (Cond
  (Prim(Bop Cop.One)
    [Sfield(Var temp(Stype sid noattr))tag(Vtype nested_option_word);nested_option_tag false]
    (Vtype Tbool))
  (Bind binder payload_type(Sfield(Var temp(Stype sid noattr))payload payload_type)some_branch result)
  none_branch result) result.

Theorem nested_option_some_first_match_typed : forall env Gamma Sigma sid tag payload payload_type co temp binder scrutinee none_branch some_branch result ef ef_none ef_some budget,
 nested_option_metadata env sid tag payload payload_type co ->
 type_expr env Gamma Sigma scrutinee ef (Stype sid noattr) ->
 type_expr env (extend_context Gamma temp(Stype sid noattr)) Sigma none_branch ef_none result ->
 type_expr env (extend_context(extend_context Gamma temp(Stype sid noattr))binder payload_type) Sigma some_branch ef_some result ->
 sub_effect ef_none budget=true -> sub_effect ef_some budget=true ->
 type_expr env Gamma Sigma
 (nested_option_some_first_match_template sid tag payload payload_type temp binder scrutinee some_branch none_branch result)
 (ef++budget) result.
Proof.
 intros * Hmeta Hscrut Hnone Hsome HnoneBound HsomeBound.
 unfold nested_option_some_first_match_template. apply ty_bind;[exact Hscrut|].
 change budget with([]++budget).
 eapply ty_cond with(ef1:=[])(ef2:=ef_some)(ef3:=ef_none).
 - change (@nil effect_label) with((@nil effect_label)++[]).
   eapply ty_ne with(t:=Vtype nested_option_word).
   + unfold nested_option_word;destruct Archi.ptr64;reflexivity.
   + eapply nested_option_field_typed;[exact Hmeta|left;auto|]. apply ty_var;unfold extend_context;apply PTree.gss.
   + apply nested_option_tag_typed.
 - change ef_some with([]++ef_some). apply ty_bind;[|exact Hsome].
   eapply nested_option_field_typed;[exact Hmeta|right;auto|]. apply ty_var;unfold extend_context;apply PTree.gss.
 - exact Hnone.
 - exact HsomeBound.
 - exact HnoneBound.
Qed.

(* Extending a source branch environment with a generated fresh binder, and
   proving the OCaml traversal supplies this metadata, remain pass-level proof
   obligations. No memory successor or successful-step premise is used above. *)
Print Assumptions nested_option_some_first_match_typed.
