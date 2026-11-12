(* Actual target scalar reads transported by memory injection. The primitive
   theorem excludes Bool, handled separately by the checked canonical-read
   bridge in BeePL_compiler_bool_read. Mbool rejects bytes other than 0/1.
   This is a local evaluation bridge, not whole compiler simulation. *)
Require Import List ZArith Coqlib Integers AST Maps Memory Memdata Ctypes Csyntax.
Require Import Csem Cstrategy Cop Events Values Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_soundness_store.
Local Open Scope Z_scope.

Lemma primitive_nonbool_decode_exact : forall pt cv v,
  pt <> Tbool -> typeof_value v (Vtype pt) ->
  decode_memory_value (Vtype pt) cv = OK v ->
  cv = trans_bvalue_cvalue v.
Proof.
  intros pt cv v Hbool Hshape Hdecode.
  destruct pt; [contradiction| |]; destruct cv; simpl in Hdecode; try discriminate;
  inversion Hdecode; subst; simpl in Hshape; try contradiction; reflexivity.
Qed.

Definition primitive_load_compatible (pt : primitive_type) : Prop :=
  match pt with Tbool | Tint IBool _ _ => False | _ => True end.

Lemma primitive_nonbool_access_mode : forall pt,
  primitive_load_compatible pt -> access_mode (transBeePL_type (Vtype pt)) = access_mode_type (Vtype pt).
Proof.
  intros pt H. destruct pt as [|sz sg attr|sg attr]; [contradiction|destruct sz,sg; simpl in H; try contradiction; reflexivity|reflexivity].
Qed.

Lemma scalar_target_literal_dereference : forall ge env m ty pointerty chunk b ofs value,
  access_mode ty = By_value chunk -> type_is_volatile ty = false ->
  Mem.loadv chunk m (Values.Vptr b ofs) = Some value ->
  eval_expression ge env m
    (Evalof (Ederef (Eval (Values.Vptr b ofs) pointerty) ty) ty) E0 m value.
Proof.
  intros ge env m ty pointerty chunk b ofs value Hmode Hvol Hload.
  eapply eval_expression_intro.
  - apply eval_valof; [exact Hvol|]. apply eval_deref. constructor.
  - eapply esr_rvalof; [apply esl_deref; constructor|reflexivity|exact Hvol|].
    eapply deref_loc_value; eauto.
Qed.

Theorem injected_nonbool_primitive_dereference :
  forall target_ge env injection source target pt source_block source_offset
    target_block target_offset value pointerty,
  primitive_load_compatible pt -> typeof_value value (Vtype pt) ->
  Mem.inject injection source target ->
  Values.Val.inject injection (Values.Vptr source_block source_offset)
    (Values.Vptr target_block target_offset) ->
  deref_addr (Vtype pt) source source_block source_offset Full value ->
  exists target_value,
    Values.Val.inject injection (trans_bvalue_cvalue value) target_value /\
    eval_expression target_ge env target
      (Evalof (Ederef (Eval (Values.Vptr target_block target_offset) pointerty)
         (transBeePL_type (Vtype pt))) (transBeePL_type (Vtype pt)))
      E0 target target_value.
Proof.
  intros tge env injection source target pt sb so tb tofs value pointerty
    Hmode Hshape Hinject Hpointer Hread.
  assert (Hbool : pt <> Tbool) by (intro E; subst; exact Hmode).
  inversion Hread; subst.
  - match goal with Hload : Mem.loadv ?chunk source _ = Some ?cv,
      Hdecode : decode_memory_value (Vtype pt) ?cv = OK value |- _ =>
      assert (Hcv : cv = trans_bvalue_cvalue value) by
        (eapply primitive_nonbool_decode_exact; eauto);
      destruct (Mem.loadv_inject _ _ _ _ _ _ _ Hinject Hload Hpointer)
        as [loaded [Hloaded Hvalue]];
      exists loaded; split; [rewrite <- Hcv; exact Hvalue|]
    end.
    eapply scalar_target_literal_dereference; [|eassumption|eassumption].
    rewrite primitive_nonbool_access_mode by exact Hmode. eassumption.
  - discriminate.
Qed.

Print Assumptions injected_nonbool_primitive_dereference.
