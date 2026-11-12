(* Actual variable-read lowering under related memories. All target loads are
   derived from the source read and injection. Surface Tbool is canonical;
   raw Tint IBool has a separately documented representation mismatch. *)
Require Import List String ZArith Coqlib AST Maps Integers Values Memory Events Errors.
Require Import Ctypes Csyntax Csem Cstrategy SimplExpr.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_compiler_bindings.
Require Import BeePL_compiler_dereference_evaluation BeePL_compiler_bool_read.
Require Import BeePL_compiler_rvalue_audit.
Local Open Scope Z_scope.

Lemma injected_surface_primitive_read_location :
  forall ge f source target pt sb so tb tofs value,
  surface_primitive_read pt -> typeof_value value (Vtype pt) ->
  Mem.inject f source target ->
  Val.inject f (Values.Vptr sb so)(Values.Vptr tb tofs) ->
  deref_addr (Vtype pt) source sb so Full value ->
  exists targetvalue,
    Val.inject f (trans_bvalue_cvalue value) targetvalue /\
    type_is_volatile(transBeePL_type(Vtype pt))=false /\
    Csem.deref_loc ge (transBeePL_type(Vtype pt)) target tb tofs Full E0 targetvalue.
Proof.
  intros ge f source target pt sb so tb tofs value Hsurface Hshape Hinj Hptr Hread.
  destruct pt as [|sz sg attr|sg attr].
  - pose proof(source_boolean_read_is_canonical_byte _ _ _ _ Hread) as Hload.
    destruct(Mem.loadv_inject _ _ _ _ _ _ _ Hinj Hload Hptr)
      as [loaded [Hloaded Hvalue]].
    exists loaded; split; [exact Hvalue|]. split; [reflexivity|].
    eapply Csem.deref_loc_value; [reflexivity|reflexivity|exact Hloaded].
  - assert (Hcompatible : primitive_load_compatible(Tint sz sg attr)) by exact Hsurface.
    inversion Hread; subst; try discriminate.
    match goal with
    | Hload : Mem.loadv ?chunk source _=Some ?cv,
      Hdecode : decode_memory_value _ ?cv=OK value |- _ =>
      assert (Hcv : cv=trans_bvalue_cvalue value) by
        (eapply primitive_nonbool_decode_exact; eauto; discriminate);
      destruct(Mem.loadv_inject _ _ _ _ _ _ _ Hinj Hload Hptr)
        as [loaded [Hloaded Hvalue]];
      exists loaded; split; [rewrite <- Hcv; exact Hvalue|]
    end.
    split; [assumption|]. eapply Csem.deref_loc_value; [|eassumption|eassumption].
    rewrite primitive_nonbool_access_mode by exact Hcompatible. eassumption.
  - assert (Hcompatible : primitive_load_compatible(Tlong sg attr)) by exact I.
    inversion Hread; subst; try discriminate.
    match goal with
    | Hload : Mem.loadv ?chunk source _=Some ?cv,
      Hdecode : decode_memory_value _ ?cv=OK value |- _ =>
      assert (Hcv : cv=trans_bvalue_cvalue value) by
        (eapply primitive_nonbool_decode_exact; eauto; discriminate);
      destruct(Mem.loadv_inject _ _ _ _ _ _ _ Hinj Hload Hptr)
        as [loaded [Hloaded Hvalue]];
      exists loaded; split; [rewrite <- Hcv; exact Hvalue|]
    end.
    split; [assumption|]. eapply Csem.deref_loc_value; [|eassumption|eassumption].
    rewrite primitive_nonbool_access_mode by exact Hcompatible. eassumption.
Qed.

Theorem compiled_local_primitive_read_injected :
  forall (ge:Csem.genv) env f source target id target_id pt value sb tb ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr (Var id(Vtype pt))ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  surface_primitive_read pt -> typeof_value value(Vtype pt) ->
  deref_addr(Vtype pt)source sb Ptrofs.zero Full value ->
  Mem.inject f source target -> f sb=Some(tb,0) ->
  compiler_bound_storage (lexical_bindings bctx) id = Some target_id ->
  env!target_id=Some(tb,transBeePL_type(Vtype pt)) ->
  exists targetvalue, Val.inject f (trans_bvalue_cvalue value)targetvalue /\
    Cstrategy.eval_expression ge env target ce E0 target targetvalue.
Proof.
  intros ge env f source target id target_id pt value sb tb ctx bctx ce ctx' bctx' g g' inc
    Hcompile Hsurface Hshape Hread Hinj Hmap Hstorage Hlocal.
  assert (Hptr : Val.inject f (Values.Vptr sb Ptrofs.zero)(Values.Vptr tb Ptrofs.zero)).
  { eapply Val.inject_ptr; [exact Hmap|reflexivity]. }
  destruct(injected_surface_primitive_read_location ge _ _ _ _ _ _ _ _ _
    Hsurface Hshape Hinj Hptr Hread) as [loaded [Hvalue [Hvol Htarget]]].
  exists loaded; split; [exact Hvalue|].
  eapply actual_nonunit_variable_lowering_evaluates; [exact Hcompile|discriminate|exact Hstorage| |exact Hvol|exact Htarget].
  apply Cstrategy.esl_var_local; exact Hlocal.
Qed.

Theorem compiled_global_primitive_read_injected :
  forall (ge:Csem.genv) env f source target id pt value sb tb ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr (Var id(Vtype pt))ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  surface_primitive_read pt -> typeof_value value(Vtype pt) ->
  deref_addr(Vtype pt)source sb Ptrofs.zero Full value ->
  Mem.inject f source target -> f sb=Some(tb,0) ->
  compiler_bound_storage (lexical_bindings bctx) id = Some id ->
  env!id=None -> Globalenvs.Genv.find_symbol ge id=Some tb ->
  exists targetvalue, Val.inject f (trans_bvalue_cvalue value)targetvalue /\
    Cstrategy.eval_expression ge env target ce E0 target targetvalue.
Proof.
  intros ge env f source target id pt value sb tb ctx bctx ce ctx' bctx' g g' inc
    Hcompile Hsurface Hshape Hread Hinj Hmap Hstorage Hlocal Hsymbol.
  assert (Hptr : Val.inject f (Values.Vptr sb Ptrofs.zero)(Values.Vptr tb Ptrofs.zero)).
  { eapply Val.inject_ptr; [exact Hmap|reflexivity]. }
  destruct(injected_surface_primitive_read_location ge _ _ _ _ _ _ _ _ _
    Hsurface Hshape Hinj Hptr Hread) as [loaded [Hvalue [Hvol Htarget]]].
  exists loaded; split; [exact Hvalue|].
  eapply actual_nonunit_variable_lowering_evaluates; [exact Hcompile|discriminate|exact Hstorage| |exact Hvol|exact Htarget].
  apply Cstrategy.esl_var_global; assumption.
Qed.

Print Assumptions compiled_local_primitive_read_injected.
Print Assumptions compiled_global_primitive_read_injected.
