(* Structural facts about successful Csyntax generation. These do not claim
   semantic simulation, environment agreement, or equality of source and
   generated local declarations. They do not use legacy compiler admissions. *)
Require Import List String Bool Integers AST Maps Ctypes Coqlib Errors SimplExpr.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax Csyntax BeePL_aux BeePL_Wrapper_Pass.
Import ListNotations.

Definition compiler_leaf (e:BeePL.expr) : bool :=
 match e with Val _ _ | Var _ _ | Const _ _ | Unit _ => true | _ => false end.

Definition expression_leaf_shape (bctx:bcompiler_ctx) (e:BeePL.expr)(ce:Csyntax.expr) : Prop :=
 match e with
 | Val v ty => ce=Eval(trans_bvalue_cvalue v)(transBeePL_type ty)
 | Var x ty => ce=trans_bound_variable bctx x ty
 | Const c ty => ce=Eval
    (match c with
     | ConsBool b => Values.Vint(if b then Int.one else Int.zero)
     | ConsInt n => Values.Vint n
     | ConsLong n => Values.Vlong n
     | ConsUnit => Values.Vint Int.zero
     end)(transBeePL_type ty)
 | Unit ty => ce=Eval(trans_bvalue_cvalue Vunit)(transBeePL_type ty)
 | _ => False
 end.

Theorem expression_leaf_translation : forall e fctx bctx ce fctx' bctx' g g' i',
 compiler_leaf e=true ->
 transBeePL_expr_expr e fctx bctx g=Res(ce,fctx',bctx')g' i' ->
 expression_leaf_shape bctx e ce /\ fctx'=fctx /\ bctx'=bctx.
Proof.
 intros e fctx bctx ce fctx' bctx' g g' i' Hleaf Htranslate.
 destruct e;try discriminate Hleaf;cbn [transBeePL_expr_expr] in Htranslate.
 - inversion Htranslate;subst;repeat split;reflexivity.
 - inversion Htranslate;subst;repeat split;reflexivity.
 - destruct c;cbn in Htranslate;try (inversion Htranslate;subst;repeat split;reflexivity).
   destruct b;cbn in Htranslate;inversion Htranslate;subst;repeat split;reflexivity.
 - inversion Htranslate;subst;repeat split;reflexivity.
Qed.

Definition statement_leaf_shape (bctx:bcompiler_ctx) (e:BeePL.expr)(cs:Csyntax.statement) : Prop :=
 match e with
 | Val v ty => cs=Sreturn(Some(Eval(trans_bvalue_cvalue v)(transBeePL_type ty)))
 | Var x ty => cs=Sreturn(Some(trans_bound_variable bctx x ty))
 | Const c ty => cs=Sreturn(Some(Eval
    (match c with
     | ConsBool b => Values.Vint(if b then Int.one else Int.zero)
     | ConsInt n => Values.Vint n
     | ConsLong n => Values.Vlong n
     | ConsUnit => Values.Vint Int.zero
     end)(transBeePL_type ty)))
 | Unit _ => cs=Sskip
 | _ => False
 end.

Theorem statement_leaf_translation : forall cenv e fctx bctx cs fctx' bctx' g g' i',
 compiler_leaf e=true ->
 transBeePL_expr_st cenv e fctx bctx g=Res(cs,fctx',bctx')g' i' ->
 statement_leaf_shape bctx e cs /\ fctx'=fctx /\ bctx'=bctx.
Proof.
 intros cenv e fctx bctx cs fctx' bctx' g g' i' Hleaf Htranslate.
 destruct e;try discriminate Hleaf;cbn [transBeePL_expr_st] in Htranslate.
 - inversion Htranslate;subst;repeat split;reflexivity.
 - inversion Htranslate;subst;repeat split;reflexivity.
 - destruct c;cbn in Htranslate;try (inversion Htranslate;subst;repeat split;reflexivity).
   destruct b;cbn in Htranslate;inversion Htranslate;subst;repeat split;reflexivity.
 - inversion Htranslate;subst;repeat split;reflexivity.
Qed.

Definition function_signature_shape (bf:BeePL.function)(cf:Csyntax.function) : Prop :=
 Csyntax.fn_return cf=transBeePL_type(BeePL.fn_return bf) /\
 Csyntax.fn_callconv cf=cc_of_variadic(get_v_function bf) /\
 (is_ebpf bf=false -> Csyntax.fn_params cf=
   seq.zip (seq.unzip1(BeePL.fn_args bf))(transBeePL_types transBeePL_type(seq.unzip2(BeePL.fn_args bf)))) /\
 (is_ebpf bf=true -> transform_ctx_ebpf_ctx(seq.zip(seq.unzip1(BeePL.fn_args bf))(seq.unzip2(BeePL.fn_args bf)))=OK(Csyntax.fn_params cf)).

Theorem function_translation_signature : forall cenv bf ids bctx cf ids' bctx',
 transBeePL_function_function cenv bf ids bctx=OK(cf,ids',bctx') ->
 function_signature_shape bf cf.
Proof.
 intros cenv bf ids bctx cf ids' bctx' Htranslate.
 unfold transBeePL_function_function in Htranslate.
 destruct(create_fn_ctx nil ids (initial_generator tt)) as [err|fctx g0 i0] eqn:Hctx;try discriminate.
 destruct(transBeePL_expr_st cenv(BeePL.fn_body bf) fctx (reserve_function_context bf ids bctx) g0) as [err|[[body locals] context] g1 i1] eqn:Hbody;try discriminate.
 destruct(is_ebpf bf) eqn:Hebpf.
 - destruct(transform_ctx_ebpf_ctx(seq.zip(seq.unzip1(BeePL.fn_args bf))(seq.unzip2(BeePL.fn_args bf)))) as [params|err] eqn:Hparams;try discriminate.
   cbn in Htranslate. inversion Htranslate;subst cf;unfold function_signature_shape;simpl;repeat split;try reflexivity.
   + rewrite Hebpf;discriminate.
   + intros;exact Hparams.
 - cbn in Htranslate. inversion Htranslate;subst cf;unfold function_signature_shape;simpl;repeat split;try reflexivity.
   rewrite Hebpf;discriminate.
Qed.

Print Assumptions expression_leaf_translation.
Print Assumptions statement_leaf_translation.
Print Assumptions function_translation_signature.

Definition fundef_signature_shape (bf:BeePL.fundef)(cf:Csyntax.fundef) : Prop :=
 match bf,cf with
 | BeePL.Internal f,Ctypes.Internal f' => function_signature_shape f f'
 | BeePL.External ef args result cc,Ctypes.External ef' args' result' cc' =>
   ef'=befunction_to_cefunction ef /\
   args'=map Ctypes.typeconv(transBeePL_types transBeePL_type args) /\
   result'=transBeePL_type result /\ cc'=cc
 | _,_ => False
 end.

Theorem fundef_translation_signature : forall cenv bf ids bctx cf ids' bctx',
 transBeePL_fundef_fundef cenv bf ids bctx=OK(cf,ids',bctx') ->
 fundef_signature_shape bf cf.
Proof.
 intros cenv bf ids bctx cf ids' bctx' Htranslate.
 destruct bf as [f|ef args result cc].
 - cbn [transBeePL_fundef_fundef] in Htranslate.
   destruct(transBeePL_function_function cenv f ids bctx) as [[[f' names] context]|err] eqn:Hfunction;
     cbn in Htranslate;try discriminate.
   inversion Htranslate;subst;cbn [fundef_signature_shape].
   eapply function_translation_signature;exact Hfunction.
 - inversion Htranslate;subst;repeat split;reflexivity.
Qed.

Print Assumptions fundef_translation_signature.

(* Locals come from the FINAL compiler context, including generated storage.
   They are not asserted equal to the source fn_vars. This records the actual
   body/context production without calling it semantic simulation. *)
Theorem function_translation_body_context : forall cenv bf ids bctx cf ids' bctx',
 transBeePL_function_function cenv bf ids bctx=OK(cf,ids',bctx') ->
 exists initial g0 i0 locals g1 i1,
 create_fn_ctx nil ids(initial_generator tt)=Res initial g0 i0 /\
 transBeePL_expr_st cenv(BeePL.fn_body bf) initial (reserve_function_context bf ids bctx) g0=
   Res(Csyntax.fn_body cf,locals,bctx')g1 i1 /\
 Csyntax.fn_vars cf=seq.zip(map unzip_ident locals)
   (transBeePL_types transBeePL_type(map unzip_type locals)).
Proof.
 intros cenv bf ids bctx cf ids' bctx' Htranslate.
 unfold transBeePL_function_function in Htranslate.
 destruct(create_fn_ctx nil ids(initial_generator tt)) as [err|initial g0 i0] eqn:Hctx;try discriminate.
 destruct(transBeePL_expr_st cenv(BeePL.fn_body bf) initial (reserve_function_context bf ids bctx) g0) as [err|[[body locals] context] g1 i1] eqn:Hbody;try discriminate.
 destruct(is_ebpf bf) eqn:Hebpf.
 - destruct(transform_ctx_ebpf_ctx(seq.zip(seq.unzip1(BeePL.fn_args bf))(seq.unzip2(BeePL.fn_args bf)))) as [params|err] eqn:Hparams;try discriminate.
   cbn in Htranslate;inversion Htranslate;subst.
   exists initial,g0,i0,locals,g1,i1;split;[reflexivity|]. split;[exact Hbody|reflexivity].
 - cbn in Htranslate;inversion Htranslate;subst.
   exists initial,g0,i0,locals,g1,i1;split;[reflexivity|]. split;[exact Hbody|reflexivity].
Qed.
Print Assumptions function_translation_body_context.

(* The source fn_vars catalogue no longer allocates C storage at entry. *)
Lemma function_body_initial_context_empty : forall ids initial g0 i0,
  create_fn_ctx nil ids (initial_generator tt) = Res initial g0 i0 -> initial = nil.
Proof. intros ids initial g0 i0 H; inversion H; reflexivity. Qed.
