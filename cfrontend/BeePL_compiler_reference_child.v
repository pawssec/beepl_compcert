(* Compositional primitive Ref case.  Child evaluation/injection is the explicit
   induction hypothesis; the parent allocation, normalized target store, and
   generated assign/address evaluation are constructed here. *)
Require Import List String ZArith Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Csyntax Csem Cstrategy Cop SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_aux.
Require Import BeePL_compiler_reference_step BeePL_compiler_reference_evaluation.
Require Import BeePL_compiler_memory_injection BeePL_compiler_expression_types.
Import ListNotations.
Local Open Scope Z_scope.

Lemma generated_reference_child_evaluates : forall ge env initial child trace evaluated value
 final id slot ct pointertype chunk normalized,
 eval_expression ge env initial child trace evaluated value ->
 env!id=Some(slot,ct) -> access_mode ct=By_value chunk -> type_is_volatile ct=false ->
 Cop.sem_cast value (Csyntax.typeof child) ct evaluated=Some normalized ->
 Mem.store chunk evaluated slot 0 normalized=Some final ->
 eval_expression ge env initial
   (Ecomma (Eassign(Evar id ct)child ct)(Eaddrof(Evar id ct)pointertype)pointertype)
   trace final (Values.Vptr slot Ptrofs.zero).
Proof.
 intros * Hchild Hlocal Hmode Hvol Hcast Hstore.
 inversion Hchild as [env0 m0 a0 tr0 m1 reduced v0 Hreduce Hsimple]; subst.
 assert (Hassign : eval_expr ge env initial RV (Eassign(Evar id ct)child ct)
   trace final (Eval normalized ct)).
 { replace trace with (E0 ** trace ** E0) by (unfold E0,Eapp; simpl; apply app_nil_r).
   eapply eval_assign with (l':=Evar id ct)(r':=reduced)(b:=slot)(ofs:=Ptrofs.zero)
     (bf:=Full)(v:=value)(v1:=normalized).
   - constructor.
   - exact Hreduce.
   - apply esl_var_local; exact Hlocal.
   - exact Hsimple.
   - exact Hcast.
   - eapply assign_loc_value; eauto.
   - reflexivity. }
 replace trace with (trace ** E0) by (unfold E0,Eapp; apply app_nil_r).
 eapply eval_expression_intro.
 - eapply eval_comma with (v1:=normalized); [exact Hassign|constructor| |reflexivity].
   apply eval_addrof; constructor.
 - apply esr_addrof; apply esl_var_local; exact Hlocal.
Qed.

Lemma reference_child_translation_shape : forall e pt attr ctx bctx child middle childctx
 g gm im ce ctx' bctx' g' inc,
 transBeePL_expr_expr e ctx bctx g=Res(child,middle,childctx)gm im ->
 transBeePL_expr_expr (Prim Ref [e] (Ptrtype(Reftype(Bprim pt)attr)))ctx bctx g=
   Res(ce,ctx',bctx')g' inc ->
 exists id name,
 ce=Ecomma(Eassign(Evar id(transBeePL_type(Vtype pt)))child(transBeePL_type(Vtype pt)))
   (Eaddrof(Evar id(transBeePL_type(Vtype pt)))
     (transBeePL_type(Ptrtype(Reftype(Bprim pt)attr))))
   (transBeePL_type(Ptrtype(Reftype(Bprim pt)attr))) /\
 ctx'=(id,Vtype pt,name)::middle /\ bctx'=childctx.
Proof.
 intros * Hchild Hparent.
 cbn [transBeePL_expr_expr transBeePL_expr_exprs] in Hparent.
 unfold SimplExpr.bind2,SimplExpr.bind in Hparent.
 rewrite Hchild in Hparent.
 cbn [transBeePL_expr_exprs SimplExpr.ret fst snd] in Hparent.
 unfold SimplExpr.bind2,SimplExpr.bind in Hparent.
 cbn beta iota zeta in Hparent.
 repeat match type of Hparent with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E:=fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair:(_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hparent; try discriminate
 end;
 repeat match goal with Href:ref_to_prim _ _ = _ |- _ =>
   cbv beta iota zeta delta [ref_to_prim SimplExpr.ret] in Href; inversion Href; subst; clear Href
 end;
 cbv beta iota zeta delta [ref_to_prim SimplExpr.ret] in Hparent;
 inversion Hparent; subst; repeat eexists; reflexivity.
Qed.

Lemma primitive_injected_value_equal : forall f pt value targetvalue,
 typeof_value value(Vtype pt) -> Val.inject f (trans_bvalue_cvalue value)targetvalue ->
 targetvalue=trans_bvalue_cvalue value.
Proof.
 intros f pt value targetvalue Htype Hvalue.
 destruct value; destruct pt; simpl in Htype; try contradiction;
 simpl in Hvalue |- *; try (inversion Hvalue; reflexivity).
 destruct b; inversion Hvalue; reflexivity.
Qed.

Theorem compiled_reference_child_from_source_store :
 forall ge env f source target_initial target_child e pt attr source_value target_value trace
 ctx bctx child middle childctx g gm im ce ctx' bctx' g' inc
 allocated fresh initialized size,
 typeof_expr e=Vtype pt ->
 transBeePL_expr_expr e ctx bctx g=Res(child,middle,childctx)gm im ->
 transBeePL_expr_expr (Prim Ref [e](Ptrtype(Reftype(Bprim pt)attr)))ctx bctx g=
   Res(ce,ctx',bctx')g' inc ->
 eval_expression ge env target_initial child trace target_child target_value ->
 scalar_reference_normalizable pt -> typeof_value source_value(Vtype pt) ->
 Val.inject f (trans_bvalue_cvalue source_value)target_value ->
 type_is_volatile(transBeePL_type(Vtype pt))=false ->
 Mem.inject f source target_child ->
 Mem.alloc source 0 size=(allocated,fresh) ->
 Mem.store (transl_bchunk_cchunk(chunk_of_ptype pt)) allocated fresh 0
   (trans_bvalue_cvalue source_value)=Some initialized ->
 (forall id name,ctx'=(id,Vtype pt,name)::middle ->
   exists slot, env!id=Some(slot,transBeePL_type(Vtype pt)) /\
     Mem.valid_block target_child slot /\
     (forall ofs,0<=ofs<size -> Mem.perm target_child slot ofs Cur Freeable) /\
     unused_target_slot f slot) ->
 exists slot f' target_final,
 eval_expression ge env target_initial ce trace target_final(Values.Vptr slot Ptrofs.zero) /\
 Mem.inject f' initialized target_final /\ inject_incr f f' /\
 f' fresh=Some(slot,0) /\ (forall b,b<>fresh -> f' b=f b) /\
 Val.inject f'(Values.Vptr fresh Ptrofs.zero)(Values.Vptr slot Ptrofs.zero).
Proof.
 intros ge env f source target_initial target_child e pt attr source_value target_value trace
 ctx bctx child middle childctx g gm im ce ctx' bctx' g' inc allocated fresh initialized size
 HeType Hchild Hparent Heval Hallowed Htyped Hvalue Hvol Hinj Halloc Hstore Hslots.
 pose proof (primitive_injected_value_equal _ _ _ _ Htyped Hvalue) as Hsame; subst target_value.
 destruct (reference_child_translation_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hchild Hparent)
   as [id [name [Hsyntax [Hctx Hbctx]]]].
 destruct (Hslots id name Hctx) as [slot [Hlocal [Hvalid [Hperm Hunused]]]].
 destruct (source_allocation_and_scalar_store _ _ _ _ _ _ _ _ _ _ _ _
   Hinj Halloc Hvalid Hperm Hunused Hvalue Hstore)
   as [f' [raw_final [Hincr [Hmap [Hframe [Htarget Hfinal]]]]]].
 destruct (primitive_reference_storage pt(trans_bvalue_cvalue source_value)Hallowed)
   as [Hmode [Hsize [Halign Hbytes]]].
 destruct (scalar_reference_cast_encoding _ _ _ target_child Hallowed Htyped Hmode)
   as [normalized [Hcast Hencoding]].
 assert (Haccess : Mem.valid_access target_child (primitive_target_chunk pt) slot 0 Writable).
 { eapply Mem.valid_access_compat; [exact Hsize|exact Halign|].
   eapply Mem.store_valid_access_3; exact Htarget. }
 destruct (Mem.valid_access_store _ _ _ _ normalized Haccess) as [target_final Hnormalized].
 pose proof (compilation_preserve_type_checked _ _ _ _ _ _ _ _ _ Hchild) as Hchildtype.
 rewrite HeType in Hchildtype.
 exists slot,f',target_final; split.
 - rewrite Hsyntax. eapply generated_reference_child_evaluates;
     [exact Heval|exact Hlocal|exact Hmode|exact Hvol| |exact Hnormalized].
   rewrite <- Hchildtype. exact Hcast.
 - split.
   + eapply Mem.inject_extends_compose; [exact Hfinal|].
     eapply same_encoded_chunks_extend; [exact Htarget|exact Hnormalized|].
     rewrite Hbytes; exact Hencoding.
   + refine (conj Hincr(conj Hmap(conj Hframe _))).
     eapply Val.inject_ptr; [exact Hmap|reflexivity].
Qed.

Print Assumptions reference_child_translation_shape.
Print Assumptions primitive_injected_value_equal.
Print Assumptions compiled_reference_child_from_source_store.

Theorem compiled_primitive_reference_after_child :
 forall source_ge target_ge p vm source source_final vm' next env f target_initial target_child
 e pt attr source_value target_value trace ctx bctx child middle childctx g gm im ce ctx' bctx' g' inc,
 typeof_expr e=Vtype pt ->
 transBeePL_expr_expr e ctx bctx g=Res(child,middle,childctx)gm im ->
 transBeePL_expr_expr (Prim Ref [e](Ptrtype(Reftype(Bprim pt)attr)))ctx bctx g=
   Res(ce,ctx',bctx')g' inc ->
 eval_expression target_ge env target_initial child trace target_child target_value ->
 BeePL_sem.ssem_expr source_ge p vm source
   (Prim Ref [Val source_value(Vtype pt)](Ptrtype(Reftype(Bprim pt)attr)))
   source_final vm' next ->
 scalar_reference_normalizable pt -> typeof_value source_value(Vtype pt) ->
 Val.inject f (trans_bvalue_cvalue source_value)target_value ->
 type_is_volatile(transBeePL_type(Vtype pt))=false ->
 Mem.inject f source target_child ->
 (forall id name,ctx'=(id,Vtype pt,name)::middle ->
   exists slot, env!id=Some(slot,transBeePL_type(Vtype pt)) /\
     Mem.valid_block target_child slot /\
     (forall ofs,0<=ofs<sizeof_type p.(prog_comp_env)(Vtype pt) ->
       Mem.perm target_child slot ofs Cur Freeable) /\ unused_target_slot f slot) ->
 exists source_result target_result f' target_final,
 next=Val source_result(Ptrtype(Reftype(Bprim pt)attr)) /\ vm'=vm /\
 eval_expression target_ge env target_initial ce trace target_final target_result /\
 Mem.inject f' source_final target_final /\ inject_incr f f' /\
 Val.inject f'(trans_bvalue_cvalue source_result)target_result.
Proof.
 intros source_ge target_ge p vm source source_final vm' next env f target_initial target_child
 e pt attr source_value target_value trace ctx bctx child middle childctx g gm im ce ctx' bctx' g' inc
 Het Hchild Hparent Heval Hstep Hallowed Htyped Hvalue Hvol Hinj Hslots.
 destruct (primitive_reference_step_shape _ _ _ _ _ _ _ _ _ _ Hstep)
   as [allocated [fresh [Halloc [Hstore [Hvm Hnext]]]]].
 destruct (compiled_reference_child_from_source_store target_ge env f source target_initial target_child
   e pt attr source_value target_value trace ctx bctx child middle childctx g gm im ce ctx' bctx' g' inc
   allocated fresh source_final (sizeof_type p.(prog_comp_env)(Vtype pt))
   Het Hchild Hparent Heval Hallowed Htyped Hvalue Hvol Hinj Halloc Hstore Hslots)
   as [slot [f' [target_final [Htarget [Hmemory [Hincr [Hmap [Hframe Hresult]]]]]]]].
 exists (Vloc fresh Ptrofs.zero),(Values.Vptr slot Ptrofs.zero),f',target_final.
 exact (conj Hnext(conj Hvm(conj Htarget(conj Hmemory(conj Hincr Hresult))))).
Qed.
Print Assumptions compiled_primitive_reference_after_child.
