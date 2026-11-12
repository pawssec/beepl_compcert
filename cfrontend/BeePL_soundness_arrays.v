(* Array locations and references share an initialized heap layout. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_array_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Definition array_reference_locations (cenv : bcomposite_env) (layout : scalar_layout)
    : location_context :=
  fun b ofs ty => exists elem len attr,
    ty = Atype elem len attr /\ 0 <= len /\
    forall i, (i < Z.to_nat len)%nat -> exists chunk,
      layout b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i * sizeof_type cenv elem))) elem chunk.

Definition array_heap_locations (cenv : bcomposite_env) (layout : scalar_layout)
    : location_context :=
  fun b ofs ty => scalar_reference_locations layout b ofs ty \/
    array_reference_locations cenv layout b ofs ty.

Lemma array_heap_locations_monotone : forall cenv layout layout',
  (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) ->
  location_context_includes (array_heap_locations cenv layout)
    (array_heap_locations cenv layout').
Proof.
  intros cenv layout layout' Hinc b ofs ty [Href | Harr].
  - left. destruct Href as [pt [chunk [Ht Hcell]]]. exists pt, chunk. auto.
  - right. destruct Harr as [elem [len [a [Ht [Hlen Hcells]]]]].
    exists elem, len, a. repeat split; auto.
    intros i Hi. destruct (Hcells i Hi) as [chunk Hcell]. exists chunk; auto.
Qed.

Lemma array_heap_element_cell_at : forall cenv layout b base elem len a n,
  array_heap_locations cenv layout b base (Atype elem len a) ->
  (n < Z.to_nat len)%nat -> exists chunk,
    layout b (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type cenv elem))) elem chunk.
Proof.
  intros cenv layout b base elem len a n [Href | Harr] Hbound.
  - destruct Href as [pt [chunk [Hbad _]]]. discriminate.
  - destruct Harr as [e [l [attr [Ht [_ Hcells]]]]].
    inversion Ht; subst. apply Hcells; exact Hbound.
Qed.

Lemma array_heap_element_cell : forall cenv layout b elem len a n,
  array_heap_locations cenv layout b Ptrofs.zero (Atype elem len a) ->
  (n < Z.to_nat len)%nat -> exists chunk,
    layout b (Ptrofs.repr (Z.of_nat n * sizeof_type cenv elem)) elem chunk.
Proof.
  intros cenv layout b elem len a n Hlocation Hbound.
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hlocation Hbound) as [chunk Hcell].
  rewrite Ptrofs.add_zero_l in Hcell. exists chunk; exact Hcell.
Qed.

Lemma array_heap_fresh_array : forall cenv layout b pt count attr,
  array_heap_locations cenv (extend_array_layout layout b pt count)
    b Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr).
Proof.
  intros. right. exists (Vtype pt), (Z.of_nat count), attr.
  repeat split; try reflexivity; try apply Nat2Z.is_nonneg.
  intros i Hi. rewrite Nat2Z.id in Hi. exists (chunk_of_ptype pt).
  rewrite Ptrofs.add_zero_l. right. exists i. repeat split; auto.
Qed.

Lemma typed_array_value_read_bound : forall cenv Gamma Sigma b base elem len a n ef,
  type_expr cenv Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) ef elem ->
  ef = nil /\ (n < Z.to_nat len)%nat.
Proof.
  intros cenv Gamma Sigma b base elem len a n ef Htyped. inversion Htyped; subst.
  match goal with H : type_expr _ _ _ (Val _ _) _ _ |- _ => inversion H; subst end.
  auto.
Qed.

Theorem located_array_read_progress :
  forall bge Gamma Sigma layout p vm m b base elem len a n ef,
  type_expr bge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) ef elem ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  runtime_locations (array_heap_locations bge.(genv_cenv) layout)
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) ->
  exists v,
    ssem_expr bge p vm m
      (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem)
      m vm (Val v elem) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v elem) ef elem /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) (Val v elem).
Proof.
  intros bge Gamma Sigma layout p vm m b base elem len a n ef Htyped Hmemory Hstored Hlocations.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hbound].
  subst ef. destruct Hlocations as [Hlocation _].
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hlocation Hbound) as [chunk Hcell].
  destruct (typed_memory_cell_read bge.(genv_cenv) Gamma Sigma m b
    (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem))) elem chunk
    (Hmemory _ _ _ _ Hcell)) as [v [Hread Hvalue]].
  exists v. split; [eapply ssem_array_read_value; eauto |].
  split; [exact Hvalue |]. eapply Hstored; eauto.
Qed.

Theorem located_array_read_preservation :
  forall bge Gamma Sigma layout p vm m b base elem len a n ef m' vm' e',
  type_expr bge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) ef elem ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  runtime_locations (array_heap_locations bge.(genv_cenv) layout)
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) ->
  ssem_expr bge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len a)] elem) m' vm' e' ->
  m' = m /\ vm' = vm /\
  type_expr bge.(genv_cenv) Gamma Sigma e' ef elem /\
  runtime_locations (array_heap_locations bge.(genv_cenv) layout) e'.
Proof.
  intros bge Gamma Sigma layout p vm m b base elem len a n ef m' vm' e'
    Htyped Hmemory Hstored Hlocations Hstep.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hbound].
  subst ef. destruct Hlocations as [Hlocation _].
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hlocation Hbound) as [chunk Hcell].
  assert (Hscalar : is_aggregate_type elem = false).
  { eapply by_value_type_not_aggregate. destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hrest]. exact Hmode. }
  assert (Hnonunit : elem <> Utype).
  { intro Heq. subst elem. pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
    discriminate Hmode. }
  inversion Hstep; subst; try contradiction;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _] end; congruence].
  repeat split; try reflexivity.
  - eapply typed_memory_cell_read_preservation; [apply Hmemory; exact Hcell | eassumption].
  - eapply Hstored; eauto.
Qed.

Print Assumptions located_array_read_progress.
Print Assumptions located_array_read_preservation.

Lemma assignment_load_other_block :
  forall bge ty m target ofs bf stored m' result b chunk offset,
  assign_addr bge ty m target ofs bf stored m' result -> b <> target ->
  Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros bge ty m target ofs bf stored m' result b chunk offset Hassign Hneq.
  inversion Hassign; subst.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.load_store_other; [exact H | left; exact Hneq]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.load_store_other; [exact H | left; exact Hneq]
    end.
  - eapply Mem.load_storebytes_other; [eassumption | left; exact Hneq].
  - match goal with H : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.load_store_other; [exact H | left; exact Hneq]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.load_store_other; [exact H | left; exact Hneq]
    end.
  - eapply Mem.load_storebytes_other; [eassumption | left; exact Hneq].
Qed.

Lemma array_elements_load_other_block : forall bge m target ofs vs elem m',
  sem_array_init_helper bge m target ofs vs elem m' ->
  forall b chunk offset, b <> target ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros bge m target ofs vs elem m' Hinit. induction Hinit; intros; auto.
  rewrite IHHinit by assumption. eapply assignment_load_other_block; eauto.
Qed.

Lemma array_initialization_load_old_block :
  forall bge bookkeeping arr ty vs vm m vm' m' bookkeeping',
  sem_array_init bge bookkeeping arr ty vs vm m vm' m' bookkeeping' ->
  forall b chunk offset, Mem.valid_block m b ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros bge bookkeeping arr ty vs vm m vm' m' bookkeeping' Hinit b chunk offset Hvalid.
  inversion Hinit; subst.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc)
      as [fresh [Hmap [_ Hallocmem]]]
  end.
  assert (Hloc : loc = fresh).
  { match goal with Hlookup : PTree.get arr vm' = Some (loc, _) |- _ =>
      rewrite Hmap, PTree.gss in Hlookup; congruence
    end. }
  subst loc.
  assert (Hneq : b <> fresh).
  { intro Heq. subst b. eapply Mem.fresh_block_alloc; eauto. }
  match goal with H : sem_array_init_helper _ _ _ _ _ _ _ |- _ =>
    rewrite (array_elements_load_other_block _ _ _ _ _ _ _ H b chunk offset Hneq)
  end.
  eapply Mem.load_alloc_unchanged; eauto.
Qed.

Lemma array_value_initializer_load_frame :
  forall bge p vm m arr ty es m' vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  forall b chunk offset, Mem.valid_block m b ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros bge p vm m arr ty es m' vm' e' Hvalues Hstep b chunk offset Hvalid.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]].
  - subst; reflexivity.
  - subst e'. inversion Hstep; subst. eapply array_initialization_load_old_block; eauto.
Qed.

Lemma array_elements_permission_frame : forall ge m b ofs vs ty final,
  sem_array_init_helper ge m b ofs vs ty final ->
  forall block offset k permission,
    Mem.perm m block offset k permission -> Mem.perm final block offset k permission.
Proof.
  intros ge m b ofs vs ty final Hinit. induction Hinit; intros; auto.
  apply IHHinit. inversion H; subst;
    try solve [match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in Hstore; eapply Mem.perm_store_1; eauto end];
    try solve [eapply Mem.perm_storebytes_1; eauto].
Qed.

Lemma array_value_initializer_extent_frame :
  forall ge p vm m arr ty es final vm' e' b,
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Ainit arr ty es ty) final vm' e' ->
  Mem.valid_block m b ->
  Mem.valid_block final b /\
  (forall offset k permission, Mem.perm m b offset k permission ->
    Mem.perm final b offset k permission).
Proof.
  intros ge p vm m arr ty es final vm' e' b Hvalues Hstep Hvalid.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]]; [subst; auto|].
  subst e'. inversion Hstep; subst.
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    inversion Hinit; subst end.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc)
      as [allocatedBlock [Hmap [Hsigma Hallocmem]]] end.
  split.
  - eapply array_initialization_preserves_valid_blocks; [eassumption|].
    eapply Mem.valid_block_alloc; eauto.
  - intros. eapply array_elements_permission_frame; [eassumption|].
    eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma array_value_initializer_read_frame :
  forall bge p vm m arr ty es m' vm' e' b ofs elem v,
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  deref_addr elem m b ofs Full v -> deref_addr elem m' b ofs Full v.
Proof.
  intros bge p vm m arr ty es m' vm' e' b ofs elem v Hvalues Hstep Hread.
  inversion Hread; subst.
  - match goal with Hload : Mem.loadv _ _ _ = Some _ |- _ =>
    simpl in Hload;
    assert (Hvalid : Mem.valid_block m b) by
      (apply Mem.load_valid_access in Hload; eapply Mem.valid_access_valid_block;
       eapply Mem.valid_access_implies; [exact Hload | constructor]);
    eapply deref_addr_value; eauto; simpl;
    rewrite (array_value_initializer_load_frame _ _ _ _ _ _ _ _ _ _ Hvalues Hstep b _ _ Hvalid);
    exact Hload
  end.
  - destruct (array_value_initializer_extent_frame bge p vm m arr ty es m' vm' e' b Hvalues Hstep ltac:(assumption))
      as [Hvalid Hpermissions].
    eapply deref_addr_bytes; eauto.
    intros offset Hin. apply Hpermissions. eauto.
Qed.

Lemma array_initialization_memory_locations :
  forall bge cenv Sigma Sigma' layout p vm m arr ty es m' vm' e' fresh pt count,
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (array_heap_locations cenv layout) layout m ->
  typed_memory_layout cenv Sigma' (extend_array_layout layout fresh pt count) m' ->
  memory_locations (array_heap_locations cenv (extend_array_layout layout fresh pt count))
    (extend_array_layout layout fresh pt count) m'.
Proof.
  intros bge cenv Sigma Sigma' layout p vm m arr ty es m' vm' e' fresh pt count
    Hvalues Hstep Hmemory Hstored Hmemory' b ofs elem chunk Hentry v Hread.
  destruct Hentry as [Hold | [i [Hi [Hb [Hofs [Htype Hchunk]]]]]].
  - destruct (typed_memory_cell_read cenv empty_context Sigma m b ofs elem chunk
      (Hmemory _ _ _ _ Hold)) as [old [Hreadold Htyped]].
    assert (Heq : v = old).
    { eapply deref_full_deterministic; [exact Hread |].
      eapply array_value_initializer_read_frame; eauto. }
    subst v. eapply value_locations_monotone with (L := array_heap_locations cenv layout).
    + apply array_heap_locations_monotone. intros; left; assumption.
    + eapply Hstored; eauto.
  - subst b ofs elem chunk. apply primitive_value_locations.
    eapply declarative_value_shape with (cenv := cenv) (Gamma := empty_context) (Sigma := Sigma').
    eapply typed_memory_cell_read_preservation; [apply Hmemory' | exact Hread].
    right. exists i. repeat split; auto.
Qed.

Print Assumptions array_value_initializer_load_frame.
Print Assumptions array_initialization_memory_locations.

Theorem located_primitive_array_preservation :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  memory_locations (array_heap_locations cenv layout) layout m ->
  runtime_locations (array_heap_locations cenv layout)
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' layout',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' ef (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma' layout' m' /\
    memory_locations (array_heap_locations cenv layout') layout' m' /\
    runtime_locations (array_heap_locations cenv layout') e' /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    vm' = vm /\
    location_context_includes (array_heap_locations cenv layout) (array_heap_locations cenv layout').
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e'
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstored Hlocations Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [b He]].
  - subst m' vm' e'. exists Sigma, layout.
    split; [apply store_context_extends_refl |]. split; [exact Hvalid |].
    split; [exact Htyped |]. split; [exact Hmemory |]. split; [exact Hstored |].
    split; [exact Hlocations |]. split; [auto |].
    split; [reflexivity | intros old ofs ty H; exact H].
  - subst e'.
    destruct (completed_primitive_array_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstep)
      as [Sigma' [Hext [Hblocks [Hresult [Hbinding Hmemory']]]]].
    exists Sigma', (extend_array_layout layout b pt (List.length es)).
    split; [exact Hext |]. split; [exact Hblocks |]. split; [exact Hresult |].
    split; [exact Hmemory' |]. split.
    + eapply array_initialization_memory_locations; eauto.
    + split.
      * destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
          as [Hlength _].
        rewrite extracted_value_arguments_length in Hlength by exact Hvalues.
        subst len. apply array_heap_fresh_array.
      * split; [intros; left; assumption |]. split; [exact Hbinding |].
        apply array_heap_locations_monotone. intros; left; assumption.
Qed.

Theorem located_primitive_array_progress :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  memory_locations (array_heap_locations cenv layout) layout m ->
  runtime_locations (array_heap_locations cenv layout)
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ->
  exists vm' m' Sigma' layout' b,
    ssem_expr bge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr))
      m' vm' (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma'
      (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma' layout' m' /\
    memory_locations (array_heap_locations cenv layout') layout' m' /\
    runtime_locations (array_heap_locations cenv layout')
      (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    vm' = vm /\
    location_context_includes (array_heap_locations cenv layout) (array_heap_locations cenv layout').
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstored Hlocations.
  destruct (source_primitive_array_progress bge cenv Gamma Sigma layout p vm m arr pt len attr es ef
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory)
    as [vm' [m' [allocated [b [Hstep Hrest]]]]].
  destruct (located_primitive_array_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstored Hlocations Hstep)
    as [Sigma' [layout' Hresult]].
  exists vm', m', Sigma', layout', b. split; assumption.
Qed.

Print Assumptions located_primitive_array_preservation.
Print Assumptions located_primitive_array_progress.


(* The old context may describe any preexisting scalar variables, independently
   of the source context used to type the newly allocated array. *)
Lemma array_value_initializer_variable_frame :
  forall bge p vm m arr ty es m' vm' e' Gamma layout layout',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  (forall b ofs t chunk, layout b ofs t chunk -> layout' b ofs t chunk) ->
  variable_layout Gamma bge vm layout -> variable_layout Gamma bge vm' layout'.
Proof.
  intros bge p vm m arr ty es m' vm' e' Gamma layout layout' Hvalues Hstep Hinclusion Hvars.
  assert (Hvm : vm' = vm) by (eapply array_value_initializer_preserves_vmap; eauto).
  subst vm'. intros x t Hlookup.
  destruct (Hvars x t Hlookup) as [b [chunk [Hlocation Hcell]]].
  exists b, chunk. split; [exact Hlocation | apply Hinclusion; exact Hcell].
Qed.

Lemma array_value_initializer_existing_arrays_frame :
  forall bge p vm m arr ty es m' vm' e' layout layout',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  (forall b ofs t chunk, layout b ofs t chunk -> layout' b ofs t chunk) ->
  primitive_array_bindings vm layout -> primitive_array_bindings vm' layout'.
Proof.
  intros bge p vm m arr ty es m' vm' e' layout layout' Hvalues Hstep Hinclusion Hvars.
  assert (Hvm : vm' = vm) by (eapply array_value_initializer_preserves_vmap; eauto).
  subst vm'. intros x b pt len a Hlookup.
  destruct (Hvars _ _ _ _ _ Hlookup) as [Hlen Hcells].
  split; [exact Hlen |]. intros i Hi. apply Hinclusion. apply Hcells; exact Hi.
Qed.

Print Assumptions array_value_initializer_variable_frame.
Print Assumptions array_value_initializer_existing_arrays_frame.

Lemma completed_array_allocation_fresh :
  forall bge p vm m arr ty es m' vm' b,
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm'
    (Val (Vloc b Ptrofs.zero) ty) ->
  ~ Mem.valid_block m b /\ vm' = vm.
Proof.
  intros bge p vm m arr ty es m' vm' b Hstep.
  inversion Hstep; subst. split; [|reflexivity].
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    inversion Hinit; subst
  end.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc)
      as [fresh [Hmap [_ Hallocmem]]]
  end.
  match goal with Hlookup : PTree.get arr _ = Some (b, _) |- _ =>
    rewrite Hmap, PTree.gss in Hlookup; inversion Hlookup; subst
  end.
  eapply Mem.fresh_block_alloc; eauto.
Qed.

(* A collision with an existing source name neither redirects that name nor
   reuses the existing object's block. *)
Theorem array_allocation_name_collision_safe :
  forall bge p vm m arr ty es m' vm' b old oldty,
  PTree.get arr vm = Some (old, oldty) -> Mem.valid_block m old ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm'
    (Val (Vloc b Ptrofs.zero) ty) ->
  PTree.get arr vm' = Some (old, oldty) /\ b <> old.
Proof.
  intros bge p vm m arr ty es m' vm' b old oldty Hlookup Hvalid Hstep.
  destruct (completed_array_allocation_fresh _ _ _ _ _ _ _ _ _ _ Hstep) as [Hfresh Hvm].
  subst vm'. split; [exact Hlookup |]. intro Heq. subst b. contradiction.
Qed.

Print Assumptions completed_array_allocation_fresh.
Print Assumptions array_allocation_name_collision_safe.

(* Only array entries are constrained here, so scalar and array bindings may
   coexist in Gamma. Local bindings take precedence over global symbols. *)
Definition array_variable_layout (Gamma : ty_context) (Sigma : store_context)
    (bge : genv) (vm : vmap) (layout : scalar_layout) : Prop :=
  forall x elem len a, PTree.get x Gamma = Some (Atype elem len a) ->
  exists b, variable_location bge vm x (Atype elem len a) b /\
    object_type_at bge.(genv_cenv) Sigma b (Ptrofs.unsigned Ptrofs.zero) (Atype elem len a) /\
    array_heap_locations bge.(genv_cenv) layout b Ptrofs.zero (Atype elem len a).

Lemma array_variable_layout_extend : forall Gamma Sigma Sigma' bge vm layout layout',
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) ->
  array_variable_layout Gamma Sigma bge vm layout ->
  array_variable_layout Gamma Sigma' bge vm layout'.
Proof.
  intros Gamma Sigma Sigma' bge vm layout layout' Hext Hinc Hvars x elem len a Hlookup.
  destruct (Hvars _ _ _ _ Hlookup) as [b [Hlocation [Hstore Harray]]].
  exists b. split; [exact Hlocation |]. split; [eapply object_type_at_store_extension; eauto |].
  eapply array_heap_locations_monotone; eauto.
Qed.

Lemma array_full_deref_impossible : forall elem len a m b ofs v,
  ~ deref_addr (Atype elem len a) m b ofs Full v.
Proof.
  intros elem len a m b ofs v Hread. inversion Hread; subst; try discriminate.
Qed.

Theorem array_variable_progress : forall Gamma Sigma bge vm layout p m x elem len a,
  array_variable_layout Gamma Sigma bge vm layout ->
  PTree.get x Gamma = Some (Atype elem len a) ->
  exists b,
    ssem_expr bge p vm m (Var x (Atype elem len a)) m vm
      (Val (Vloc b Ptrofs.zero) (Atype elem len a)) /\
    type_expr bge.(genv_cenv) Gamma Sigma
      (Val (Vloc b Ptrofs.zero) (Atype elem len a)) nil (Atype elem len a) /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout)
      (Val (Vloc b Ptrofs.zero) (Atype elem len a)).
Proof.
  intros Gamma Sigma bge vm layout p m x elem len a Hvars Hlookup.
  destruct (Hvars _ _ _ _ Hlookup) as [b [Hlocation [Hstore Harray]]].
  exists b. split.
  - destruct Hlocation as [Hlocal | [Hmissing Hglobal]].
    + apply ssem_lvar_array; exact Hlocal.
    + apply ssem_gbvar_array; assumption.
  - split; [apply ty_valarray; exact Hstore | exact Harray].
Qed.

Theorem array_variable_preservation :
  forall Gamma Sigma bge vm layout p m x elem len a m' vm' e',
  array_variable_layout Gamma Sigma bge vm layout ->
  PTree.get x Gamma = Some (Atype elem len a) ->
  ssem_expr bge p vm m (Var x (Atype elem len a)) m' vm' e' ->
  m' = m /\ vm' = vm /\
  type_expr bge.(genv_cenv) Gamma Sigma e' nil (Atype elem len a) /\
  runtime_locations (array_heap_locations bge.(genv_cenv) layout) e'.
Proof.
  intros Gamma Sigma bge vm layout p m x elem len a m' vm' e' Hvars Hlookup Hstep.
  destruct (Hvars _ _ _ _ Hlookup) as [b [Hlocation [Hstore Harray]]].
  inversion Hstep; subst;
    try solve [exfalso; eapply array_full_deref_impossible; eauto].
  - assert (b0 = b).
    { eapply variable_location_deterministic; [left; eassumption | exact Hlocation]. }
    subst b0. repeat split; try reflexivity; [apply ty_valarray; exact Hstore | exact Harray].
  - assert (b0 = b).
    { eapply variable_location_deterministic; [right; split; eassumption | exact Hlocation]. }
    subst b0. repeat split; try reflexivity; [apply ty_valarray; exact Hstore | exact Harray].
Qed.

Print Assumptions array_variable_progress.
Print Assumptions array_variable_preservation.

Lemma named_array_read_typing : forall cenv Gamma Sigma x elem len a n ef,
  type_expr cenv Gamma Sigma (Aaccess x (Atype elem len a) n elem) ef elem ->
  ef = nil /\ PTree.get x Gamma = Some (Atype elem len a) /\ (n < Z.to_nat len)%nat.
Proof.
  intros cenv Gamma Sigma x elem len a n ef Htyped. inversion Htyped; subst.
  match goal with H : exists len attr, _ = Atype _ len attr /\ _ |- _ =>
    destruct H as [size [attr [Heq Hbound]]]; inversion Heq; subst
  end. auto.
Qed.

Lemma named_array_step_location : forall bge p vm m x elem len a n m' vm' e',
  is_aggregate_type elem = false -> elem <> Utype ->
  ssem_expr bge p vm m (Aaccess x (Atype elem len a) n elem) m' vm' e' ->
  m' = m /\ vm' = vm /\ exists b v,
    e' = Val v elem /\ variable_location bge vm x (Atype elem len a) b /\
    deref_addr elem m b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) Full v.
Proof.
  intros bge p vm m x elem len a n m' vm' e' Hscalar Hnonunit Hstep.
  inversion Hstep; subst; try contradiction;
    try solve [match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _] end; congruence].
  all: do 2 (split; [reflexivity |]).
  all: (eexists; eexists; split; [reflexivity |]; split;
    [unfold variable_location; eauto | eassumption]).
Qed.

Theorem named_array_read_progress : forall Gamma Sigma bge vm layout p m x elem len a n ef,
  type_expr bge.(genv_cenv) Gamma Sigma (Aaccess x (Atype elem len a) n elem) ef elem ->
  array_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  exists v,
    ssem_expr bge p vm m (Aaccess x (Atype elem len a) n elem) m vm (Val v elem) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v elem) ef elem /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) (Val v elem).
Proof.
  intros Gamma Sigma bge vm layout p m x elem len a n ef Htyped Hvars Hmemory Hstored.
  destruct (named_array_read_typing _ _ _ _ _ _ _ _ _ Htyped) as [Hef [Hlookup Hbound]].
  subst ef. destruct (Hvars _ _ _ _ Hlookup) as [b [Hlocation [Hstore Harray]]].
  destruct (array_heap_element_cell _ _ _ _ _ _ _ Harray Hbound) as [chunk Hcell].
  destruct (typed_memory_cell_read bge.(genv_cenv) Gamma Sigma m b
    (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk
    (Hmemory _ _ _ _ Hcell)) as [v [Hread Hvalue]].
  exists v. split.
  - destruct Hlocation as [Hlocal | [Hmissing Hglobal]].
    + eapply ssem_array_access; eauto.
    + eapply ssem_array_access_global; eauto.
  - split; [exact Hvalue |]. eapply Hstored; eauto.
Qed.

Theorem named_array_read_preservation :
  forall Gamma Sigma bge vm layout p m x elem len a n ef m' vm' e',
  type_expr bge.(genv_cenv) Gamma Sigma (Aaccess x (Atype elem len a) n elem) ef elem ->
  array_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  ssem_expr bge p vm m (Aaccess x (Atype elem len a) n elem) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr bge.(genv_cenv) Gamma Sigma e' ef elem /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) e'.
Proof.
  intros Gamma Sigma bge vm layout p m x elem len a n ef m' vm' e'
    Htyped Hvars Hmemory Hstored Hstep.
  destruct (named_array_read_typing _ _ _ _ _ _ _ _ _ Htyped) as [Hef [Hlookup Hbound]].
  subst ef. destruct (Hvars _ _ _ _ Hlookup) as [b [Hlocation [Hstore Harray]]].
  destruct (array_heap_element_cell _ _ _ _ _ _ _ Harray Hbound) as [chunk Hcell].
  assert (Hscalar : is_aggregate_type elem = false).
  { eapply by_value_type_not_aggregate. destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hrest]. exact Hmode. }
  assert (Hnonunit : elem <> Utype).
  { intro Heq. subst elem. pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
    discriminate Hmode. }
  destruct (named_array_step_location _ _ _ _ _ _ _ _ _ _ _ _ Hscalar Hnonunit Hstep)
    as [Hm [Hvm [actual [v [He [Hactual Hread]]]]]].
  assert (actual = b) by (eapply variable_location_deterministic; eauto).
  subst actual m' vm' e'. split; [reflexivity |]. split; [reflexivity |]. split.
  - eapply typed_memory_cell_read_preservation; [apply Hmemory; exact Hcell | exact Hread].
  - eapply Hstored; eauto.
Qed.

Print Assumptions named_array_read_progress.
Print Assumptions named_array_read_preservation.

Lemma array_allocation_preserves_named_arrays :
  forall Gamma Sigma Sigma' bge p vm m arr ty es m' vm' e' layout layout',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  store_context_extends Sigma Sigma' ->
  (forall b ofs t chunk, layout b ofs t chunk -> layout' b ofs t chunk) ->
  array_variable_layout Gamma Sigma bge vm layout ->
  array_variable_layout Gamma Sigma' bge vm' layout'.
Proof.
  intros Gamma Sigma Sigma' bge p vm m arr ty es m' vm' e' layout layout'
    Hvalues Hstep Hext Hinc Hvars.
  assert (Hvm : vm' = vm) by (eapply array_value_initializer_preserves_vmap; eauto).
  subst vm'. eapply array_variable_layout_extend; eauto.
Qed.

Print Assumptions array_allocation_preserves_named_arrays.
