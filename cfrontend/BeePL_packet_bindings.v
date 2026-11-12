(* Shared runtime locations and variable bindings include tracked Bytes
   descriptors and initialized aggregate objects, without scalarizing them. *)
Require Import Coqlib List ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_variables.
Require Import BeePL_callable_locations BeePL_callable_variables BeePL_initialized_variables.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_structure_variables.
Require Import BeePL_packet_state BeePL_bytes_execution.

Definition packet_heap_locations (ge : genv) (cells : scalar_layout)
    (objects : aggregate_object_context) (packets : packet_locations) : location_context :=
  fun b ofs ty => descriptor_heap_locations ge cells objects b ofs ty \/
    (ty = Bytes /\ packets b ofs).

Lemma packet_descriptor_embedding : forall ge cells objects packets,
  location_context_includes (descriptor_heap_locations ge cells objects)
    (packet_heap_locations ge cells objects packets).
Proof. intros ge cells objects packets b ofs ty H; left; exact H. Qed.

Lemma packet_callable_embedding : forall ge cells objects packets,
  location_context_includes (callable_heap_locations ge cells)
    (packet_heap_locations ge cells objects packets).
Proof. intros ge cells objects packets b ofs ty H; left; left; exact H. Qed.

Lemma packet_heap_locations_nonbytes : forall ge cells objects packets b ofs ty,
  ty <> Bytes -> packet_heap_locations ge cells objects packets b ofs ty ->
  descriptor_heap_locations ge cells objects b ofs ty.
Proof. intros * Hne [H|[Heq H]]; [exact H|contradiction]. Qed.

Lemma packet_heap_locations_monotone : forall ge cells cells' objects objects' packets packets',
  (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) ->
  (forall b ofs ty, objects b ofs ty -> objects' b ofs ty) ->
  (forall b ofs, packets b ofs -> packets' b ofs) ->
  location_context_includes (packet_heap_locations ge cells objects packets)
    (packet_heap_locations ge cells' objects' packets').
Proof.
  intros ge cells cells' objects objects' packets packets' Hc Ho Hp b ofs ty [H|[Ht H]].
  - left; eapply descriptor_heap_locations_monotone; eauto.
  - right; split; auto.
Qed.

Inductive packet_variable_binding (ge : genv) (Sigma : store_context)
    (vm : vmap) (cells : scalar_layout) (objects : aggregate_object_context)
    (packets : packet_locations) (x : ident) (ty : type) : Prop :=
| packet_variable_callable : callable_variable_binding ge Sigma vm cells x ty ->
    packet_variable_binding ge Sigma vm cells objects packets x ty
| packet_variable_aggregate : forall b,
    variable_location ge vm x ty b -> is_aggregate_type ty = true ->
    objects b Ptrofs.zero ty ->
    packet_variable_binding ge Sigma vm cells objects packets x ty
| packet_variable_bytes : forall b,
    variable_location ge vm x ty b -> ty = Bytes -> packets b Ptrofs.zero ->
    packet_variable_binding ge Sigma vm cells objects packets x ty.

Definition packet_variable_layout Gamma Sigma ge vm cells objects packets :=
  forall x ty, PTree.get x Gamma = Some ty ->
    packet_variable_binding ge Sigma vm cells objects packets x ty.

Lemma packet_variable_layout_extend : forall Gamma Sigma Sigma' ge vm cells cells' objects objects' packets packets',
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) ->
  (forall b ofs ty, objects b ofs ty -> objects' b ofs ty) ->
  (forall b ofs, packets b ofs -> packets' b ofs) ->
  packet_variable_layout Gamma Sigma ge vm cells objects packets ->
  packet_variable_layout Gamma Sigma' ge vm cells' objects' packets'.
Proof.
  intros * Hs Hc Ho Hp Hv x ty Hx. destruct (Hv x ty Hx).
  - constructor; eapply callable_variable_binding_extend; eauto.
  - eapply packet_variable_aggregate; eauto.
  - eapply packet_variable_bytes; eauto.
Qed.

Lemma callable_packet_variable_embedding : forall Gamma Sigma ge vm cells objects packets,
  callable_variable_layout Gamma Sigma ge vm cells ->
  packet_variable_layout Gamma Sigma ge vm cells objects packets.
Proof. intros * H x ty Hx; constructor; eauto. Qed.

Lemma singleton_callable_layout : forall ge Sigma vm cells x ty,
  callable_variable_binding ge Sigma vm cells x ty ->
  callable_variable_layout (PTree.set x ty empty_context) Sigma ge vm cells.
Proof.
  intros * H y t Hy. rewrite PTree.gsspec in Hy. destruct (peq y x); subst.
  - inversion Hy; subst; exact H.
  - rewrite PTree.gempty in Hy; discriminate.
Qed.

Lemma variable_step_value : forall ge p vm m x ty m' vm' e',
  ssem_expr ge p vm m (Var x ty) m' vm' e' -> exists v, e' = Val v ty.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma aggregate_variable_step_exact : forall ge p vm m x ty b m' vm' e',
  is_aggregate_type ty = true -> variable_location ge vm x ty b ->
  ssem_expr ge p vm m (Var x ty) m' vm' e' ->
  m'=m /\ vm'=vm /\ e'=Val (Vloc b Ptrofs.zero) ty.
Proof.
  intros * Hkind Hloc Hstep. destruct ty; try discriminate Hkind;
    inversion Hstep; subst;
    try solve [exfalso; eapply array_full_deref_impossible; eauto];
    try solve [exfalso; eapply structure_full_deref_impossible; eauto].
  all: assert (b0=b) by (eapply variable_location_deterministic; [unfold variable_location; eauto|exact Hloc]);
    subst; repeat split.
Qed.

Theorem packet_variable_progress : forall Gamma Sigma ge vm cells objects packets p m x ty,
  packet_variable_layout Gamma Sigma ge vm cells objects packets ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m ->
  memory_locations (packet_heap_locations ge cells objects packets) cells m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  packet_state_valid m packets -> packet_state_typed ge.(genv_cenv) Sigma packets ->
  PTree.get x Gamma = Some ty ->
  exists v, ssem_expr ge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations (packet_heap_locations ge cells objects packets) (Val v ty).
Proof.
  intros * Hv Hcells Hstored Ho Hp Hpt Hx. destruct (Hv x ty Hx) as [Hcall|b Hl Hkind Hob|b Hl Hty Hpacket].
  - destruct (located_callable_variable_progress (PTree.set x ty empty_context) Sigma ge vm cells
      (packet_heap_locations ge cells objects packets) p m x ty
      (packet_callable_embedding _ _ _ _) (singleton_callable_layout _ _ _ _ _ _ Hcall)
      Hcells Hstored (PTree.gss x ty empty_context)) as [v [Hs [Ht Hloc]]].
    exists v; split; [exact Hs|]. split; [eapply value_typing_context_independent; exact Ht|exact Hloc].
  - exists (Vloc b Ptrofs.zero). split.
    + destruct ty; try discriminate Hkind; destruct Hl as [Hl|[Hnone Hsymbol]];
        [eapply ssem_lvar_struct|eapply ssem_gbvar_struct|eapply ssem_lvar_array|eapply ssem_gbvar_array]; eauto.
    + split.
      * destruct ty; try discriminate Hkind; constructor; eapply aggregate_object_typing; eauto.
      * left; apply aggregate_descriptor_direct; auto.
  - subst ty. exists (Vloc b Ptrofs.zero).
    destruct (Hp _ _ Hpacket) as [Hbound [view [bytes [Hd Hdata]]]].
    assert (Hr : deref_addr Bytes m b Ptrofs.zero Full (Vloc b Ptrofs.zero)) by
      (eapply bytes_descriptor_read; eauto).
    split.
    + destruct Hl as [Hl|[Hnone Hsymbol]]; [eapply ssem_lvar|eapply ssem_gbvar]; eauto.
    + split; [constructor; eapply Hpt; eauto|right; auto].
Qed.

Theorem packet_variable_preservation : forall Gamma Sigma ge vm cells objects packets p m x ty m' vm' e',
  packet_variable_layout Gamma Sigma ge vm cells objects packets ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m ->
  memory_locations (packet_heap_locations ge cells objects packets) cells m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  packet_state_valid m packets -> packet_state_typed ge.(genv_cenv) Sigma packets ->
  PTree.get x Gamma = Some ty ->
  ssem_expr ge p vm m (Var x ty) m' vm' e' ->
  m'=m /\ vm'=vm /\ type_expr ge.(genv_cenv) Gamma Sigma e' nil ty /\
  runtime_locations (packet_heap_locations ge cells objects packets) e'.
Proof.
  intros * Hv Hcells Hstored Ho Hp Hpt Hx Hstep.
  destruct (Hv x ty Hx) as [Hcall|b Hl Hkind Hob|b Hl Hty Hpacket].
  - destruct (located_callable_variable_preservation (PTree.set x ty empty_context) Sigma ge vm cells
      (packet_heap_locations ge cells objects packets) p m x ty m' vm' e'
      (packet_callable_embedding _ _ _ _) (singleton_callable_layout _ _ _ _ _ _ Hcall)
      Hcells Hstored (PTree.gss x ty empty_context) Hstep) as [Hm [Hvm [Ht Hloc]]].
    destruct (variable_step_value _ _ _ _ _ _ _ _ _ Hstep) as [v He]; subst e'.
    split; [exact Hm|]. split; [exact Hvm|]. split;
      [eapply value_typing_context_independent; exact Ht|exact Hloc].
  - destruct (aggregate_variable_step_exact _ _ _ _ _ _ _ _ _ _ Hkind Hl Hstep) as [Hm [Hvm He]].
    subst m' vm' e'. repeat split; auto.
    + destruct ty; try discriminate Hkind; constructor; eapply aggregate_object_typing; eauto.
    + left; apply aggregate_descriptor_direct; auto.
  - subst ty. inversion Hstep; subst.
    all: assert (l=b) by (eapply variable_location_deterministic; [unfold variable_location; eauto|exact Hl]); subst l.
    all: match goal with Hread : deref_addr Bytes _ _ _ Full _ |- _ =>
      apply bytes_read_exact in Hread; subst end.
    all: split; [reflexivity|]; split; [reflexivity|]; split;
      [constructor; eapply Hpt; eauto|right; auto].
Qed.

Print Assumptions packet_variable_progress.
Print Assumptions packet_variable_preservation.
