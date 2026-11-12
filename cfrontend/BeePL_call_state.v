(* Lookup evidence for a callee's initialized parameter slots and globals.
   These lemmas do not assert initialization or memory contents. *)
Require Import List ZArith AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_soundness_variables.
Require Import BeePL_allocation_proofs BeePL_parameter_allocations.
Import ListNotations.

Definition primitive_parameter_layout (callee : vmap)
    (params : list (ident * type)) : scalar_layout :=
  fun b ofs ty chunk => exists id pt,
    In (id, Vtype pt) params /\
    PTree.get id callee = Some (b, Vtype pt) /\
    ofs = Ptrofs.zero /\ ty = Vtype pt /\ chunk = chunk_of_ptype pt.

Definition extended_call_layout (old : scalar_layout) (callee : vmap)
    (params : list (ident * type)) : scalar_layout :=
  fun b ofs ty chunk => old b ofs ty chunk \/
    primitive_parameter_layout callee params b ofs ty chunk.

Lemma bind_vars_lookup_origin : forall params Gamma x ty,
  PTree.get x (bind_vars Gamma params) = Some ty ->
  In (x, ty) params \/
    (PTree.get x Gamma = Some ty /\ ~ In x (map fst params)).
Proof.
  induction params as [|[id t] params IH]; intros Gamma x ty Hlookup.
  - right. split; [exact Hlookup|simpl; tauto].
  - simpl in Hlookup. destruct (IH _ _ _ Hlookup) as [Hin|[Hget Hmissing]].
    + left. right; exact Hin.
    + destruct (Pos.eq_dec x id) as [Heq|Hneq].
      * subst x. rewrite PTree.gss in Hget. inversion Hget; subst ty.
        left. left; reflexivity.
      * rewrite PTree.gso in Hget by exact Hneq.
        right. split; [exact Hget|]. simpl. intros [Heq|Hin]; [congruence|contradiction].
Qed.

Lemma parameter_allocation_missing_lookup : forall bge Sigma m params callee allocated Sigma' x,
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  ~ In x (map fst params) -> PTree.get x callee = None.
Proof.
  intros bge Sigma m params callee allocated Sigma' x Halloc Hmissing.
  rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Halloc x Hmissing).
  apply PTree.gempty.
Qed.

Theorem callee_mixed_variable_layout :
  forall bge Sigma Sigma' Gamma old params callee m allocated,
  mixed_variable_layout Gamma Sigma bge empty_vmap old ->
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => exists pt, snd param = Vtype pt) params ->
  store_context_extends Sigma Sigma' ->
  mixed_variable_layout (bind_vars Gamma params) Sigma' bge callee
    (extended_call_layout old callee params).
Proof.
  intros bge Sigma Sigma' Gamma old params callee m allocated
    Hglobals Halloc Hnames Hprimitive Hextends x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - rewrite Forall_forall in Hprimitive.
    destruct (Hprimitive (x, ty) Hin) as [pt Hty]. simpl in Hty. subst ty.
    destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots x (Vtype pt) Hin) as [b [Hget Hrest]].
    exists b. split; [left; exact Hget|].
    apply heap_variable_scalar with (chunk := chunk_of_ptype pt).
    right. exists x, pt. repeat split; assumption.
  - destruct (Hglobals x ty Hglobal) as [b [Hlocation Hbinding]].
    exists b. split.
    + destruct Hlocation as [Hlocal|[Hnone Hsymbol]].
      * unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
      * right. split; [eapply parameter_allocation_missing_lookup; eauto|exact Hsymbol].
    + eapply heap_variable_binding_extend; [exact Hextends| |exact Hbinding].
      intros block ofs t chunk Hentry. left; exact Hentry.
Qed.

Theorem caller_mixed_variable_layout_extended :
  forall Gamma Sigma Sigma' bge caller old callee params,
  store_context_extends Sigma Sigma' ->
  mixed_variable_layout Gamma Sigma bge caller old ->
  mixed_variable_layout Gamma Sigma' bge caller (extended_call_layout old callee params).
Proof.
  intros. eapply mixed_variable_layout_extend; [eassumption| |eassumption].
  intros b ofs ty chunk Hentry. left; exact Hentry.
Qed.

Print Assumptions callee_mixed_variable_layout.
Print Assumptions caller_mixed_variable_layout_extended.
