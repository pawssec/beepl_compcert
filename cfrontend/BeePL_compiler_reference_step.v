(* Reference allocation connected to actual source small steps. Source Bool
   stores use Mbool while generated C uses unsigned bytes; their stored bytes
   agree. The final target execution and memory injection are constructed. *)
Require Import List String ZArith Lia Coqlib Maps AST Integers Values Memory Memdata Events.
Require Import Ctypes Csyntax Csem Cstrategy Cop SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_Csyntax.
Require Import BeePL_compiler_reference_evaluation BeePL_compiler_memory_injection.
Require Import BeePL_soundness_memory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma same_encoded_chunks_extend : forall chunk otherchunk before b ofs raw normalized first second,
  Mem.store chunk before b ofs raw = Some first ->
  Mem.store otherchunk before b ofs normalized = Some second ->
  encode_val chunk raw = encode_val otherchunk normalized ->
  Mem.extends first second.
Proof.
  intros chunk otherchunk before b ofs raw normalized first second Hfirst Hsecond Hencode.
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

Definition primitive_target_chunk pt :=
  match pt with Tbool => Mint8unsigned | _ => transl_bchunk_cchunk(chunk_of_ptype pt) end.

Lemma primitive_reference_storage : forall pt raw,
  scalar_reference_normalizable pt ->
  access_mode(transBeePL_type(Vtype pt))=By_value(primitive_target_chunk pt) /\
  size_chunk(transl_bchunk_cchunk(chunk_of_ptype pt))=size_chunk(primitive_target_chunk pt) /\
  align_chunk(primitive_target_chunk pt)<=align_chunk(transl_bchunk_cchunk(chunk_of_ptype pt)) /\
  encode_val(transl_bchunk_cchunk(chunk_of_ptype pt))raw=encode_val(primitive_target_chunk pt)raw.
Proof.
  intros pt raw H. destruct pt as [|sz sg attr|sg attr].
  - destruct raw; repeat split; reflexivity.
  - destruct sz,sg; simpl in H; try contradiction; repeat split; reflexivity.
  - destruct sg; repeat split; reflexivity.
Qed.

Lemma primitive_value_injects_itself : forall f pt value,
  typeof_value value(Vtype pt) ->
  Val.inject f (trans_bvalue_cvalue value)(trans_bvalue_cvalue value).
Proof.
  intros f pt value H. destruct value; destruct pt; simpl in H; try contradiction;
    simpl; try constructor; destruct b; constructor.
Qed.

Theorem compiled_reference_from_source_store :
  forall ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized size,
  transBeePL_expr_expr
    (Prim Ref [Val value(Vtype pt)](Ptrtype(Reftype(Bprim pt)attr)))ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  scalar_reference_normalizable pt -> typeof_value value(Vtype pt) ->
  type_is_volatile(transBeePL_type(Vtype pt))=false ->
  Mem.inject f source target ->
  Mem.alloc source 0 size=(allocated,fresh) ->
  Mem.store (transl_bchunk_cchunk(chunk_of_ptype pt)) allocated fresh 0
    (trans_bvalue_cvalue value)=Some initialized ->
  (forall id name, ctx'=(id,Vtype pt,name)::ctx ->
    exists slot, env!id=Some(slot,transBeePL_type(Vtype pt)) /\
      Mem.valid_block target slot /\
      (forall ofs,0<=ofs<size -> Mem.perm target slot ofs Cur Freeable) /\
      unused_target_slot f slot) ->
  exists slot f' targetfinal,
    eval_expression ge env target ce E0 targetfinal(Values.Vptr slot Ptrofs.zero) /\
    Mem.inject f' initialized targetfinal /\ inject_incr f f' /\
    f' fresh=Some(slot,0) /\ (forall b,b<>fresh -> f' b=f b) /\
    Val.inject f'(Values.Vptr fresh Ptrofs.zero)(Values.Vptr slot Ptrofs.zero).
Proof.
  intros ge env f source target pt attr value ctx bctx ce ctx' bctx' g g' inc
    allocated fresh initialized size Htranslate Hallowed Htyped Hvol Hinj Halloc Hstore Hslots.
  destruct(evaluated_reference_translation_shape _ _ _ _ _ _ _ _ _ _ _ Htranslate)
    as [id [name [Hsyntax [Hctx Hbctx]]]].
  destruct(Hslots id name Hctx) as [slot [Hlocal [Hvalid [Hperm Hunused]]]].
  pose proof(primitive_value_injects_itself f pt value Htyped) as Hvalue.
  destruct(source_allocation_and_scalar_store _ _ _ _ _ _ _ _ _ _ _ _
    Hinj Halloc Hvalid Hperm Hunused Hvalue Hstore)
    as [f' [rawfinal [Hincr [Hmap [Hframe [Htarget Hfinal]]]]]].
  destruct(primitive_reference_storage pt(trans_bvalue_cvalue value)Hallowed)
    as [Hmode [Hsize [Halign Hbytes]]].
  destruct(scalar_reference_cast_encoding _ _ _ target Hallowed Htyped Hmode)
    as [normalized [Hcast Hencoding]].
  assert (Haccess : Mem.valid_access target (primitive_target_chunk pt) slot 0 Writable).
  { eapply Mem.valid_access_compat; [exact Hsize|exact Halign|].
    eapply Mem.store_valid_access_3; exact Htarget. }
  destruct(Mem.valid_access_store _ _ _ _ normalized Haccess) as [targetfinal Hnormalized].
  exists slot,f',targetfinal. split.
  - rewrite Hsyntax. eapply generated_scalar_reference_evaluates_normalized; eauto.
  - split.
    + eapply Mem.inject_extends_compose; [exact Hfinal|].
      eapply same_encoded_chunks_extend; [exact Htarget|exact Hnormalized|].
      rewrite Hbytes. exact Hencoding.
    + refine(conj Hincr(conj Hmap(conj Hframe _))).
      eapply Val.inject_ptr; [exact Hmap|reflexivity].
Qed.

Print Assumptions compiled_reference_from_source_store.

Lemma primitive_reference_step_shape :
  forall ge p vm source pt attr value final vm' next,
  ssem_expr ge p vm source
    (Prim Ref [Val value(Vtype pt)](Ptrtype(Reftype(Bprim pt)attr)))
    final vm' next ->
  exists allocated fresh,
    Mem.alloc source 0 (sizeof_type p.(prog_comp_env)(Vtype pt))=(allocated,fresh) /\
    Mem.store(transl_bchunk_cchunk(chunk_of_ptype pt)) allocated fresh 0
      (trans_bvalue_cvalue value)=Some final /\
    vm'=vm /\ next=Val(Vloc fresh Ptrofs.zero)(Ptrtype(Reftype(Bprim pt)attr)).
Proof.
  intros ge p vm source pt attr value final vm' next Hstep.
  inversion Hstep; subst; try discriminate.
  - match goal with Hbad : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion Hbad end.
  - cbn [construct_type_btype] in *.
    match goal with Hchunk : chunk_of_type(Vtype pt)=Some _ |- _ =>
      simpl in Hchunk; inversion Hchunk; subst end.
    destruct(Mem.alloc source 0(sizeof_type p.(prog_comp_env)(Vtype pt)))
      as [allocated fresh] eqn:Halloc.
    simpl in *. exists allocated,fresh; repeat split; assumption.
Qed.

Theorem compiled_primitive_reference_step :
  forall source_ge target_ge p vm source final vm' next env f target pt attr value
    ctx bctx ce ctx' bctx' g g' inc,
  ssem_expr source_ge p vm source
    (Prim Ref [Val value(Vtype pt)](Ptrtype(Reftype(Bprim pt)attr)))
    final vm' next ->
  transBeePL_expr_expr
    (Prim Ref [Val value(Vtype pt)](Ptrtype(Reftype(Bprim pt)attr)))ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  scalar_reference_normalizable pt -> typeof_value value(Vtype pt) ->
  type_is_volatile(transBeePL_type(Vtype pt))=false ->
  Mem.inject f source target ->
  (forall id name,ctx'=(id,Vtype pt,name)::ctx ->
    exists slot,env!id=Some(slot,transBeePL_type(Vtype pt)) /\
      Mem.valid_block target slot /\
      (forall ofs,0<=ofs<sizeof_type p.(prog_comp_env)(Vtype pt) ->
        Mem.perm target slot ofs Cur Freeable) /\ unused_target_slot f slot) ->
  exists sourcevalue targetvalue f' targetfinal,
    next=Val sourcevalue(Ptrtype(Reftype(Bprim pt)attr)) /\ vm'=vm /\
    eval_expression target_ge env target ce E0 targetfinal targetvalue /\
    Mem.inject f' final targetfinal /\ inject_incr f f' /\
    Val.inject f'(trans_bvalue_cvalue sourcevalue)targetvalue.
Proof.
  intros source_ge target_ge p vm source final vm' next env f target pt attr value
    ctx bctx ce ctx' bctx' g g' inc Hstep Hcompile Hallowed Htyped Hvol Hinj Hslots.
  destruct(primitive_reference_step_shape _ _ _ _ _ _ _ _ _ _ Hstep)
    as [allocated [fresh [Halloc [Hstore [Hvm Hnext]]]]].
  destruct(compiled_reference_from_source_store target_ge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ Hcompile Hallowed Htyped Hvol Hinj Halloc Hstore Hslots)
    as [slot [f' [targetfinal [Heval [Hmemory [Hincr [Hmap [Hframe Hvalue]]]]]]]].
  exists (Vloc fresh Ptrofs.zero),(Values.Vptr slot Ptrofs.zero),f',targetfinal.
  exact(conj Hnext(conj Hvm(conj Heval(conj Hmemory(conj Hincr Hvalue))))).
Qed.

Print Assumptions primitive_reference_step_shape.
Print Assumptions compiled_primitive_reference_step.
