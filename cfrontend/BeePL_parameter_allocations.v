(* Parameter allocation facts concern permissions and fresh slots, not
   initialized contents. Initialization is proved in BeePL_call_bindings. *)
Require Import List ZArith Lia AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_allocation_proofs BeePL_call_bindings.
Import ListNotations.
Local Open Scope Z_scope.

Lemma parameter_allocations_access_frame : forall bge Sigma vm m params vm' m' Sigma',
  alloc_variables bge Sigma vm m params vm' m' Sigma' ->
  forall chunk b ofs permission, Mem.valid_access m chunk b ofs permission ->
    Mem.valid_access m' chunk b ofs permission.
Proof.
  intros bge Sigma vm m params vm' m' Sigma' Halloc.
  induction Halloc; intros chunk b ofs permission Haccess; auto.
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty)) as [allocated fresh] eqn:Hmem.
  inversion H; subst. eapply Mem.valid_access_alloc_other; eauto.
Qed.

Lemma parameter_allocations_block_frame : forall bge Sigma vm m params vm' m' Sigma',
  alloc_variables bge Sigma vm m params vm' m' Sigma' ->
  forall b, Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  intros bge Sigma vm m params vm' m' Sigma' Halloc.
  induction Halloc; intros b Hvalid; auto.
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty)) as [allocated fresh] eqn:Hmem.
  inversion H; subst. eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma parameter_allocation_slots : forall bge Sigma vm m params vm' m' Sigma',
  alloc_variables bge Sigma vm m params vm' m' Sigma' ->
  NoDup (map fst params) ->
  (forall id ty, In (id, ty) params -> exists b,
    PTree.get id vm' = Some (b, ty) /\ ~ Mem.valid_block m b /\
    Mem.valid_block m' b /\
    (forall pt, ty = Vtype pt ->
      Mem.valid_access m' (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Freeable)) /\
  parameter_targets_distinct vm' params.
Proof.
  intros bge Sigma vm m params vm' m' Sigma' Halloc.
  induction Halloc as [Sigma vm m|Sigma vm m id ty params allocated fresh final result Sigma1 Sigma'
    Hballoc Htail IH]; intros Hnames.
  - split; [intros name t Hin; contradiction|].
    split; [exact Hnames|intros name t name' t' b Hin; contradiction].
  - inversion Hnames as [|? ? Hnotin Htailnames]; subst.
    destruct (IH Htailnames) as [Hslots [Hdup Hinjective]].
    unfold balloc in Hballoc.
    destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty)) as [first block] eqn:Hmem.
    inversion Hballoc; subst first block Sigma1.
    assert (Hhead : PTree.get id result = Some (fresh, ty)).
    { rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Htail id Hnotin).
      apply PTree.gss. }
    assert (Hfreshvalid : Mem.valid_block allocated fresh) by (eapply Mem.valid_new_block; eauto).
    split.
    + intros name t [Heq|Hin].
      * inversion Heq; subst name t. exists fresh.
        split; [exact Hhead|]. split; [eapply Mem.fresh_block_alloc; eauto|].
        split; [eapply parameter_allocations_block_frame; eauto|].
        intros pt Hty. subst ty.
        eapply parameter_allocations_access_frame; [exact Htail|].
        eapply Mem.valid_access_alloc_same; [exact Hmem|lia| |].
        -- rewrite primitive_chunk_size. simpl. lia.
        -- exists 0. lia.
      * destruct (Hslots name t Hin) as [b [Hlookup [Hfresh [Hvalid Haccess]]]].
        exists b. split; [exact Hlookup|]. split.
        -- intro Hold. apply Hfresh. eapply Mem.valid_block_alloc; eauto.
        -- split; assumption.
    + split; [exact Hnames|].
      intros name t name' t' b Hin Hin' Hget Hget'.
      destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin'].
      * congruence.
      * inversion Heq; subst name t.
        destruct (Hslots name' t' Hin') as [b' [Hlookup [Hfresh Hrest]]].
        assert (b = fresh) by congruence. assert (b' = b) by congruence.
        subst b b'. contradiction.
      * inversion Heq'; subst name' t'.
        destruct (Hslots name t Hin) as [b' [Hlookup [Hfresh Hrest]]].
        assert (b = fresh) by congruence. assert (b' = b) by congruence.
        subst b b'. contradiction.
      * eapply Hinjective; eauto.
Qed.

Theorem allocate_primitive_parameters : forall bge Sigma m params values,
  NoDup (map fst params) ->
  Forall2 (fun param v => exists pt,
    snd param = Vtype pt /\ typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params values ->
  exists callee allocated Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    primitive_parameter_inputs callee allocated params values /\
    parameter_targets_distinct callee params /\
    (forall b, parameter_binding_target callee params b -> ~ Mem.valid_block m b).
Proof.
  intros bge Sigma m params values Hnames Hvalues.
  destruct (alloc_variables_total bge params Sigma empty_vmap m)
    as [callee [allocated [Sigma' Halloc]]].
  destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames) as [Hslots Hdistinct].
  exists callee, allocated, Sigma'. split; [exact Halloc|].
  split.
  - unfold primitive_parameter_inputs.
    assert (Hinputs : forall ps vs,
      Forall2 (fun param v => exists pt, snd param = Vtype pt /\
        typeof_value v (Vtype pt) /\ type_is_volatile (transBeePL_type (Vtype pt)) = false) ps vs ->
      (forall param, In param ps -> In param params) ->
      primitive_parameter_inputs callee allocated ps vs).
    { intros ps vs Hshape. induction Hshape; intros Hincluded; constructor.
      - destruct x as [id ty]. destruct H as [pt [Hty [Hvalue Hvolatile]]]. simpl in Hty. subst ty.
        destruct (Hslots id (Vtype pt) (Hincluded _ (or_introl eq_refl)))
          as [b [Hget [Hfresh [Hvalid Haccess]]]].
        exists pt, b. simpl. split; [reflexivity|]. split; [exact Hget|].
        split; [exact Hvalue|]. split; [exact Hvolatile|]. apply Haccess. reflexivity.
      - apply IHHshape. intros param Hin. apply Hincluded. right; exact Hin. }
    apply Hinputs; [exact Hvalues|auto].
  - split; [exact Hdistinct|].
    intros b [id [ty [Hin Hget]]].
    destruct (Hslots id ty Hin) as [target [Hlookup [Hfresh Hrest]]].
    assert (target = b) by congruence. subst target. exact Hfresh.
Qed.

Print Assumptions allocate_primitive_parameters.
