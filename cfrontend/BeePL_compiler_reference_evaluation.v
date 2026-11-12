(* Operational reference-allocation bridge. This starts from the actual
   evaluated-operand lowering and keeps target local allocation separate from
   source expression-time allocation. Cast stability is an explicit scalar
   normalization premise, not a target execution or final-state assumption. *)
Require Import List String ZArith Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Csyntax Csem Cstrategy Cop SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_aux.
Require Import BeePL_compiler_memory_injection BeePL_compiler_decomposition.
Import ListNotations.
Local Open Scope Z_scope.

Definition generated_scalar_reference id ct pointertype value :=
  Ecomma (Eassign(Evar id ct)(Eval value ct)ct)
    (Eaddrof(Evar id ct)pointertype)pointertype.

Lemma generated_scalar_reference_evaluates : forall ge env target final id slot ct pointertype chunk value,
  env!id=Some(slot,ct) ->
  access_mode ct=By_value chunk -> type_is_volatile ct=false ->
  Cop.sem_cast value ct ct target=Some value ->
  Mem.store chunk target slot 0 value=Some final ->
  Cstrategy.eval_expression ge env target
    (generated_scalar_reference id ct pointertype value) E0 final (Vptr slot Ptrofs.zero).
Proof.
  intros ge env target final id slot ct pointertype chunk value Hlocal Hmode Hvol Hcast Hstore.
  assert (Hassign : Cstrategy.eval_expr ge env target RV
    (Eassign(Evar id ct)(Eval value ct)ct) E0 final (Eval value ct)).
  { eapply Cstrategy.eval_assign with (t1:=E0)(t2:=E0)(t3:=E0)
      (m1:=target)(m2:=target)(b:=slot)(ofs:=Ptrofs.zero)(bf:=Full)
      (v:=value)(v1:=value); simpl; try reflexivity.
    - constructor.
    - constructor.
    - apply Cstrategy.esl_var_local; exact Hlocal.
    - constructor.
    - exact Hcast.
    - eapply Csem.assign_loc_value; [exact Hmode|exact Hvol|].
      exact Hstore. }
  unfold generated_scalar_reference.
  eapply Cstrategy.eval_expression_intro.
  - eapply Cstrategy.eval_comma with (t1:=E0)(t2:=E0)(m1:=final)
      (r1':=Eval value ct)(v1:=value).
    + exact Hassign.
    + constructor.
    + apply Cstrategy.eval_addrof. constructor.
    + reflexivity.
  - apply Cstrategy.esr_addrof. apply Cstrategy.esl_var_local; exact Hlocal.
Qed.

Lemma evaluated_reference_translation_shape : forall pt attr value ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr
    (Prim Ref [Val value (Vtype pt)] (Ptrtype(Reftype(Bprim pt)attr))) ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  exists id name, ce=generated_scalar_reference id (transBeePL_type(Vtype pt))
      (transBeePL_type(Ptrtype(Reftype(Bprim pt)attr))) (trans_bvalue_cvalue value) /\
    ctx'=(id,Vtype pt,name)::ctx /\ bctx'=bctx.
Proof.
  intros pt attr value ctx bctx ce ctx' bctx' g g' inc H.
  pose proof (proj1 expression_translation_decomposition _ _ _ _ _ _ _ _ _ H) as D.
  cbn [fst snd] in D.
  destruct D as [ces [fctx [bc [id [pty [name [unused [g1 [i1 [g2 [i2 [i3 [ct
    [Hlist [Hlen [Hfresh [Hpty [Hct [Hce [Hctx Hbc]]]]]]]]]]]]]]]]]]]].
  cbv beta iota zeta delta [ref_to_prim ret] in Hpty.
  inversion Hpty; subst pty.
  cbv beta iota zeta delta [transBeePL_expr_exprs transBeePL_expr_expr
    SimplExpr.bind2 SimplExpr.bind ret fst snd] in Hlist.
  inversion Hlist; subst ces fctx bc.
  exists id,name. subst ce ct ctx' bctx'. repeat split; reflexivity.
Qed.

Theorem translated_scalar_reference_allocation :
  forall ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized chunk size,
  transBeePL_expr_expr
    (Prim Ref [Val value (Vtype pt)] (Ptrtype(Reftype(Bprim pt)attr))) ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  Mem.inject f source target ->
  Mem.alloc source 0 size=(allocated,fresh) ->
  Mem.store chunk allocated fresh 0 (trans_bvalue_cvalue value)=Some initialized ->
  Val.inject f (trans_bvalue_cvalue value)(trans_bvalue_cvalue value) ->
  access_mode(transBeePL_type(Vtype pt))=By_value chunk ->
  type_is_volatile(transBeePL_type(Vtype pt))=false ->
  Cop.sem_cast (trans_bvalue_cvalue value) (transBeePL_type(Vtype pt))
    (transBeePL_type(Vtype pt)) target=Some(trans_bvalue_cvalue value) ->
  (forall id name, ctx'=(id,Vtype pt,name)::ctx ->
    exists slot, env!id=Some(slot,transBeePL_type(Vtype pt)) /\
      Mem.valid_block target slot /\
      (forall ofs, 0<=ofs<size -> Mem.perm target slot ofs Cur Freeable) /\
      unused_target_slot f slot) ->
  exists slot f' targetfinal,
    Cstrategy.eval_expression ge env target ce E0 targetfinal (Vptr slot Ptrofs.zero) /\
    Mem.inject f' initialized targetfinal /\ inject_incr f f' /\
    f' fresh=Some(slot,0) /\ (forall b, b<>fresh -> f' b=f b) /\
    Val.inject f' (Vptr fresh Ptrofs.zero)(Vptr slot Ptrofs.zero).
Proof.
  intros ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized chunk size Htranslate Hinj Halloc Hstore Hvalue Hmode Hvol Hcast Hslots.
  destruct(evaluated_reference_translation_shape _ _ _ _ _ _ _ _ _ _ _ Htranslate)
    as [id [name [Hshape [Hctx Hbctx]]]].
  destruct(Hslots id name Hctx) as [slot [Hlocal [Hvalid [Hperm Hunused]]]].
  destruct(source_allocation_and_scalar_store _ _ _ _ _ _ _ _ _ _ _ _
    Hinj Halloc Hvalid Hperm Hunused Hvalue Hstore)
    as [f' [targetfinal [Hincr [Hmap [Hframe [Htarget Hfinal]]]]]].
  exists slot,f',targetfinal.
  split.
  - rewrite Hshape. eapply generated_scalar_reference_evaluates; eauto.
  - refine(conj Hfinal (conj Hincr (conj Hmap (conj Hframe _)))).
    replace (Vptr slot Ptrofs.zero) with
      (Vptr slot (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))) by reflexivity.
    eapply Val.inject_ptr; [exact Hmap|reflexivity].
Qed.

Print Assumptions evaluated_reference_translation_shape.
Print Assumptions translated_scalar_reference_allocation.

Require Import Memdata.

(* Compare semantic memory fields, rather than equating proof-carrying memory
   records. This avoids a proof-irrelevance axiom for store normalization. *)
Lemma same_encoded_stores_extend : forall chunk before b ofs raw normalized first second,
  Mem.store chunk before b ofs raw = Some first ->
  Mem.store chunk before b ofs normalized = Some second ->
  encode_val chunk raw = encode_val chunk normalized ->
  Mem.extends first second.
Proof.
  intros chunk before b ofs raw normalized first second Hfirst Hsecond Hencode.
  assert (Hcontents : Mem.mem_contents first = Mem.mem_contents second).
  { rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hfirst),
      (Mem.store_mem_contents _ _ _ _ _ _ Hsecond), Hencode. reflexivity. }
  assert (Hperm : forall block offset k p,
    Mem.perm first block offset k p <-> Mem.perm second block offset k p).
  { intros; split; intros Hp.
    - eapply Mem.perm_store_1; [exact Hsecond|].
      eapply Mem.perm_store_2; [exact Hfirst|exact Hp].
    - eapply Mem.perm_store_1; [exact Hfirst|].
      eapply Mem.perm_store_2; [exact Hsecond|exact Hp]. }
  constructor.
  - rewrite (Mem.nextblock_store _ _ _ _ _ _ Hfirst),
      (Mem.nextblock_store _ _ _ _ _ _ Hsecond). reflexivity.
  - constructor.
    + intros block target delta offset k p Hmap Hp.
      unfold inject_id in Hmap; inversion Hmap; subst.
      rewrite Z.add_0_r. apply Hperm; exact Hp.
    + intros block target delta chunk' offset p Hmap Hp.
      unfold inject_id in Hmap; inversion Hmap; subst. apply Z.divide_0_r.
    + intros block offset target delta Hmap Hp.
      unfold inject_id in Hmap; inversion Hmap; subst. rewrite Z.add_0_r,Hcontents.
      apply memval_lessdef_refl.
  - intros; left; apply Hperm; assumption.
Qed.

Lemma generated_scalar_reference_evaluates_normalized :
  forall ge env target final id slot ct pointertype chunk value normalized,
  env!id=Some(slot,ct) ->
  access_mode ct=By_value chunk -> type_is_volatile ct=false ->
  Cop.sem_cast value ct ct target=Some normalized ->
  Mem.store chunk target slot 0 normalized=Some final ->
  Cstrategy.eval_expression ge env target
    (generated_scalar_reference id ct pointertype value) E0 final (Vptr slot Ptrofs.zero).
Proof.
  intros ge env target final id slot ct pointertype chunk value normalized
    Hlocal Hmode Hvol Hcast Hstore.
  assert (Hassign : Cstrategy.eval_expr ge env target RV
    (Eassign(Evar id ct)(Eval value ct)ct) E0 final (Eval normalized ct)).
  { eapply Cstrategy.eval_assign with (t1:=E0)(t2:=E0)(t3:=E0)
      (m1:=target)(m2:=target)(b:=slot)(ofs:=Ptrofs.zero)(bf:=Full)
      (v:=value)(v1:=normalized); simpl; try reflexivity.
    - constructor.
    - constructor.
    - apply Cstrategy.esl_var_local; exact Hlocal.
    - constructor.
    - exact Hcast.
    - eapply Csem.assign_loc_value; [exact Hmode|exact Hvol|exact Hstore]. }
  unfold generated_scalar_reference. eapply Cstrategy.eval_expression_intro.
  - eapply Cstrategy.eval_comma with (t1:=E0)(t2:=E0)(m1:=final)
      (r1':=Eval normalized ct)(v1:=normalized).
    + exact Hassign.
    + constructor.
    + apply Cstrategy.eval_addrof. constructor.
    + reflexivity.
  - apply Cstrategy.esr_addrof. apply Cstrategy.esl_var_local; exact Hlocal.
Qed.

Definition scalar_reference_normalizable (pt : primitive_type) : Prop :=
  match pt with Tint IBool _ _ => False | _ => True end.

Lemma scalar_reference_cast_encoding : forall pt value chunk m,
  scalar_reference_normalizable pt -> typeof_value value (Vtype pt) ->
  access_mode(transBeePL_type(Vtype pt))=By_value chunk ->
  exists normalized,
    Cop.sem_cast (trans_bvalue_cvalue value) (transBeePL_type(Vtype pt))
      (transBeePL_type(Vtype pt)) m = Some normalized /\
    encode_val chunk (trans_bvalue_cvalue value) = encode_val chunk normalized.
Proof.
  intros pt value chunk m Hallowed Hshape Hmode.
  destruct pt as [|sz sg attr|sg attr]; destruct value; simpl in Hshape; try contradiction.
  - inversion Hmode; subst. destruct b; eexists; split; reflexivity.
  - { destruct sz,sg; simpl in Hallowed; try contradiction;
      inversion Hmode; subst; eexists; split; try reflexivity.
      all: cbn [trans_bvalue_cvalue Cop.cast_int_int].
      all: symmetry; match goal with
        | |- encode_val Mint8signed _ = _ => apply encode_val_int8_sign_ext
        | |- encode_val Mint8unsigned _ = _ => apply encode_val_int8_zero_ext
        | |- encode_val Mint16signed _ = _ => apply encode_val_int16_sign_ext
        | |- encode_val Mint16unsigned _ = _ => apply encode_val_int16_zero_ext
        end. }
  - destruct sg; inversion Hmode; subst; eexists; split; reflexivity.
Qed.

Theorem translated_typed_scalar_reference_allocation :
  forall ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized chunk size,
  transBeePL_expr_expr
    (Prim Ref [Val value (Vtype pt)] (Ptrtype(Reftype(Bprim pt)attr))) ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  Mem.inject f source target ->
  Mem.alloc source 0 size=(allocated,fresh) ->
  Mem.store chunk allocated fresh 0 (trans_bvalue_cvalue value)=Some initialized ->
  Val.inject f (trans_bvalue_cvalue value)(trans_bvalue_cvalue value) ->
  access_mode(transBeePL_type(Vtype pt))=By_value chunk ->
  type_is_volatile(transBeePL_type(Vtype pt))=false ->
  scalar_reference_normalizable pt -> typeof_value value (Vtype pt) ->
  (forall id name, ctx'=(id,Vtype pt,name)::ctx ->
    exists slot, env!id=Some(slot,transBeePL_type(Vtype pt)) /\
      Mem.valid_block target slot /\
      (forall ofs, 0<=ofs<size -> Mem.perm target slot ofs Cur Freeable) /\
      unused_target_slot f slot) ->
  exists slot f' targetfinal,
    Cstrategy.eval_expression ge env target ce E0 targetfinal (Vptr slot Ptrofs.zero) /\
    Mem.inject f' initialized targetfinal /\ inject_incr f f' /\
    f' fresh=Some(slot,0) /\ (forall b, b<>fresh -> f' b=f b) /\
    Val.inject f' (Vptr fresh Ptrofs.zero)(Vptr slot Ptrofs.zero).
Proof.
  intros ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized chunk size Htranslate Hinj Halloc Hstore Hvalue
    Hmode Hvol Hallowed Hshape Hslots.
  destruct(evaluated_reference_translation_shape _ _ _ _ _ _ _ _ _ _ _ Htranslate)
    as [id [name [Hsyntax [Hctx Hbctx]]]].
  destruct(Hslots id name Hctx) as [slot [Hlocal [Hvalid [Hperm Hunused]]]].
  destruct(source_allocation_and_scalar_store _ _ _ _ _ _ _ _ _ _ _ _
    Hinj Halloc Hvalid Hperm Hunused Hvalue Hstore)
    as [f' [rawfinal [Hincr [Hmap [Hframe [Htarget Hfinal]]]]]].
  destruct(scalar_reference_cast_encoding _ _ _ target Hallowed Hshape Hmode)
    as [normalized [Hcast Hencoding]].
  pose proof(Mem.store_valid_access_3 _ _ _ _ _ _ Htarget) as Haccess.
  destruct(Mem.valid_access_store _ _ _ _ normalized Haccess) as [targetfinal Hnormalized].
  exists slot,f',targetfinal. split.
  - rewrite Hsyntax. eapply generated_scalar_reference_evaluates_normalized; eauto.
  - split.
    + eapply Mem.inject_extends_compose; [exact Hfinal|].
      eapply same_encoded_stores_extend; eauto.
    + refine(conj Hincr (conj Hmap (conj Hframe _))).
      replace (Vptr slot Ptrofs.zero) with
        (Vptr slot (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))) by reflexivity.
      eapply Val.inject_ptr; [exact Hmap|reflexivity].
Qed.

Print Assumptions same_encoded_stores_extend.
Print Assumptions scalar_reference_cast_encoding.
Print Assumptions translated_typed_scalar_reference_allocation.
