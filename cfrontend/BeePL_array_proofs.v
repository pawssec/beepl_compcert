(* Array operational regressions and typed element reads. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_storage_types.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_initialization_proofs
  BeePL_structure_proofs BeePL_allocation_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma empty_array_initialization_identity : forall bge m b ofs ty m',
  sem_array_init_helper bge m b ofs [] ty m' -> m' = m.
Proof. intros bge m b ofs ty m' H; inversion H; reflexivity. Qed.

Lemma singleton_array_initialization : forall bge m b ofs ty v m',
  sem_array_init_helper bge m b ofs [v] ty m' -> ty <> Utype ->
  assign_addr bge ty m b ofs Full v m' v.
Proof.
  intros bge m b ofs ty v m' H Hnonunit. inversion H; subst; try contradiction.
  match goal with Htail : sem_array_init_helper _ _ _ _ [] _ _ |- _ =>
    apply empty_array_initialization_identity in Htail; subst
  end. assumption.
Qed.

Lemma array_initialization_preserves_valid_blocks : forall bge m b ofs vs ty m',
  sem_array_init_helper bge m b ofs vs ty m' ->
  forall old, Mem.valid_block m old -> Mem.valid_block m' old.
Proof.
  intros bge m b ofs vs ty m' Hinit. induction Hinit; intros old Hvalid; auto.
  apply IHHinit. eapply assignment_preserves_valid_blocks; eauto.
Qed.

Lemma array_initialization_length : forall bge Sigma arr ty vs vm m vm' m' Sigma',
  sem_array_init bge Sigma arr ty vs vm m vm' m' Sigma' ->
  exists elem len a b, ty = Atype elem len a /\
    len = Z.of_nat (List.length vs) /\ PTree.get arr vm' = Some (b, ty).
Proof. intros bge Sigma arr ty vs vm m vm' m' Sigma' H; inversion H; subst; eauto 8. Qed.

Lemma typed_array_access_progress : forall bge cenv Gamma Sigma layout p vm m arr elem len a n b chunk,
  PTree.get arr vm = Some (b, Atype elem len a) ->
  (n < Z.to_nat len)%nat ->
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk ->
  exists v,
    ssem_expr bge p vm m (Aaccess arr (Atype elem len a) n elem) m vm (Val v elem) /\
    type_expr cenv Gamma Sigma (Val v elem) nil elem.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr elem len a n b chunk Hlookup Hbound Hmemory Hcell.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b
    (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk
    (Hmemory _ _ _ _ Hcell)) as [v [Hread Htyped]].
  exists v. split; [eapply ssem_array_access with (len := len) (a := a) (loc := b); eauto | exact Htyped].
Qed.

Lemma typed_array_access_preservation : forall bge cenv Gamma Sigma layout p vm m arr elem len a n b chunk m' vm' e',
  PTree.get arr vm = Some (b, Atype elem len a) ->
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk ->
  ssem_expr bge p vm m (Aaccess arr (Atype elem len a) n elem) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil elem.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr elem len a n b chunk m' vm' e'
    Hlookup Hmemory Hcell Hstep.
  assert (Hscalar : is_aggregate_type elem = false).
  { eapply by_value_type_not_aggregate. destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hrest]. exact Hmode. }
  assert (Hnonunit : elem <> Utype).
  { intro Heq. subst elem. pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
    discriminate Hmode. }
  inversion Hstep; subst; try contradiction;
    try solve [match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _] end; congruence].
  -
  assert (loc = b) by congruence. subst loc.
  split; [reflexivity |]. split; [reflexivity |].
  eapply typed_memory_cell_read_preservation; [apply Hmemory; exact Hcell | eassumption].
  - exfalso. change (PTree.get arr vm' = Some (b, Atype elem len a)) in Hlookup.
    match goal with Hnone : PTree.get arr vm' = None |- _ =>
      rewrite Hlookup in Hnone; discriminate
    end.
Qed.

Lemma int32_array_second_element_offset : forall bge,
  Ptrofs.repr (Z.of_nat 1 * sizeof_type bge.(genv_cenv) (Vtype (Tint I32 Signed noattr))) =
    Ptrofs.repr 4.
Proof. reflexivity. Qed.

Lemma int32_array_third_element_offset : forall bge,
  Ptrofs.repr (Z.of_nat 2 * sizeof_type bge.(genv_cenv) (Vtype (Tint I32 Signed noattr))) =
    Ptrofs.repr 8.
Proof. reflexivity. Qed.

Print Assumptions empty_array_initialization_identity.
Print Assumptions singleton_array_initialization.
Print Assumptions array_initialization_length.
Print Assumptions typed_array_access_progress.
Print Assumptions typed_array_access_preservation.

Lemma out_of_bounds_array_access_stuck : forall bge p vm m arr elem len a n m' vm' e',
  (Z.to_nat len <= n)%nat ->
  ~ ssem_expr bge p vm m (Aaccess arr (Atype elem len a) n elem) m' vm' e'.
Proof.
  intros bge p vm m arr elem len a n m' vm' e' Hbound Hstep.
  inversion Hstep; subst;
    try match goal with H : Atype _ _ _ = Atype _ _ _ |- _ => inversion H; subst end; lia.
Qed.

Lemma initialize_int32_pair : forall bge m b first second,
  Mem.valid_access m Mint32 b 0 Freeable ->
  Mem.valid_access m Mint32 b 4 Freeable ->
  exists m',
    sem_array_init_helper bge m b Ptrofs.zero [Vint first; Vint second]
      (Vtype (Tint I32 Signed noattr)) m' /\
    initialized_scalar_cell m' b Ptrofs.zero (Vtype (Tint I32 Signed noattr)) BMint32 /\
    initialized_scalar_cell m' b (Ptrofs.repr 4) (Vtype (Tint I32 Signed noattr)) BMint32 /\
    deref_addr (Vtype (Tint I32 Signed noattr)) m' b Ptrofs.zero Full (Vint first) /\
    deref_addr (Vtype (Tint I32 Signed noattr)) m' b (Ptrofs.repr 4) Full (Vint second).
Proof.
  intros bge m b first second Hfirst Hsecond.
  destruct (initialize_primitive_cell bge m b Ptrofs.zero (Tint I32 Signed noattr) (Vint first)
    I eq_refl Hfirst) as [written [Hstore1 [Hassign1 Hcell1]]].
  assert (Hsecond' : Mem.valid_access written Mint32 b 4 Freeable).
  { eapply Mem.store_valid_access_1; [exact Hstore1 | exact Hsecond]. }
  destruct (initialize_primitive_cell bge written b (Ptrofs.repr 4)
    (Tint I32 Signed noattr) (Vint second) I eq_refl Hsecond')
    as [finished [Hstore2 [Hassign2 Hcell2]]].
  change (Mem.store Mint32 m b 0 (Values.Vint first) = Some written) in Hstore1.
  change (Mem.store Mint32 written b 4 (Values.Vint second) = Some finished) in Hstore2.
  assert (Hread1 : Mem.load Mint32 finished b 0 = Some (Values.Vint first)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore2).
    - exact (Mem.load_store_same _ _ _ _ _ _ Hstore1).
    - right; left. simpl; lia. }
  assert (Hread2 : Mem.load Mint32 finished b 4 = Some (Values.Vint second)).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hstore2). }
  exists finished. split.
  - eapply sem_allocate_array_elm; [exact Hassign1 |].
    change (sem_array_init_helper bge written b (Ptrofs.repr 4) [Vint second]
      (Vtype (Tint I32 Signed noattr)) finished).
    eapply sem_allocate_array_elm; [exact Hassign2 | constructor].
  - split.
    + eapply initialized_scalar_store_disjoint; [exact Hcell1 | exact Hstore2 |].
      right; right. change (0 + 4 <= 4). lia.
    + split; [exact Hcell2 |]. split.
      * eapply deref_addr_value with (chunk := BMint32) (v := Values.Vint first);
          try reflexivity. exact Hread1.
      * eapply deref_addr_value with (chunk := BMint32) (v := Values.Vint second);
          try reflexivity. exact Hread2.
Qed.

Print Assumptions out_of_bounds_array_access_stuck.
Print Assumptions initialize_int32_pair.

Lemma typed_array_initializer_extent : forall cenv Gamma Sigma arr ty es result ef,
  type_expr cenv Gamma Sigma (Ainit arr ty es result) ef result ->
  ty = result /\ exists elem attr, ty = Atype elem (Z.of_nat (List.length es)) attr.
Proof.
  intros cenv Gamma Sigma arr ty es result ef Htyped. inversion Htyped; subst.
  split; [reflexivity |].
  match goal with
  | Hargs : type_exprs _ _ _ es _ ?ts,
    Hextent : exists attr, _ = Atype _ (Z.of_nat (List.length ?ts)) attr |- _ =>
    rewrite <- (typed_arguments_length _ _ _ _ _ _ Hargs) in Hextent;
    destruct Hextent as [a Hextent]; eexists; exists a; exact Hextent
  end.
Qed.

Lemma typed_array_access_bound : forall cenv Gamma Sigma arr ty n result ef,
  type_expr cenv Gamma Sigma (Aaccess arr ty n result) ef result ->
  exists len attr, ty = Atype result len attr /\ (n < Z.to_nat len)%nat.
Proof.
  intros cenv Gamma Sigma arr ty n result ef Htyped. inversion Htyped; subst. assumption.
Qed.

Lemma out_of_bounds_array_access_untypable : forall cenv Gamma Sigma arr elem len attr n result ef,
  (Z.to_nat len <= n)%nat ->
  ~ type_expr cenv Gamma Sigma (Aaccess arr (Atype elem len attr) n result) ef result.
Proof.
  intros cenv Gamma Sigma arr elem len attr n result ef Hbound Htyped.
  destruct (typed_array_access_bound _ _ _ _ _ _ _ _ Htyped) as [len' [attr' [Heq Hlt]]].
  inversion Heq; subst. lia.
Qed.

Lemma mismatched_array_initializer_annotation_untypable : forall cenv Gamma Sigma arr ty es result ef,
  ty <> result -> ~ type_expr cenv Gamma Sigma (Ainit arr ty es result) ef result.
Proof.
  intros cenv Gamma Sigma arr ty es result ef Hneq Htyped.
  apply Hneq. exact (proj1 (typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped)).
Qed.

Lemma undersized_int32_initializer_untypable : forall cenv Gamma Sigma arr i ef,
  ~ type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr)
      [Val (Vint i) (Vtype (Tint I32 Signed noattr))]
      (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr)) ef
    (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr).
Proof.
  intros cenv Gamma Sigma arr i ef Htyped.
  destruct (typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped) as [_ [elem [attr Hextent]]].
  discriminate Hextent.
Qed.

Print Assumptions typed_array_initializer_extent.
Print Assumptions typed_array_access_bound.
Print Assumptions out_of_bounds_array_access_untypable.
Print Assumptions mismatched_array_initializer_annotation_untypable.
Print Assumptions undersized_int32_initializer_untypable.

Lemma singleton_allocation_maps : forall bge Sigma vm m arr ty vm' m' Sigma',
  alloc_variables bge Sigma vm m [(arr, ty)] vm' m' Sigma' ->
  exists b, vm' = PTree.set arr (b, ty) vm /\ Sigma' = PTree.set b ty Sigma /\
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) ty) = (m', b).
Proof.
  intros bge Sigma vm m arr ty vm' m' Sigma' Halloc. inversion Halloc; subst.
  match goal with Htail : alloc_variables _ _ _ _ [] _ _ _ |- _ => inversion Htail; subst end.
  match goal with Hballoc : balloc _ _ _ _ _ _ = _ |- _ =>
    unfold balloc in Hballoc;
    destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) ty)) as [allocated b] eqn:Hmem;
    inversion Hballoc; subst
  end.
  eexists. repeat split; eauto.
Qed.

Lemma primitive_array_size_nonnegative : forall cenv pt len attr,
  (0 <= sizeof_type cenv (Atype (Vtype pt) len attr))%Z.
Proof.
  intros cenv pt len attr. simpl.
  assert (Hwidth : (0 <= sizeof_ptype pt)%Z).
  { destruct pt as [|sz sign attrs|sign attrs]; try destruct sz; simpl; lia. }
  apply Z.mul_nonneg_nonneg; [exact Hwidth | lia].
Qed.

Lemma array_initialization_store_typing :
  forall bge cenv Gamma Sigma arr elem len attr vs vm m vm' m' Sigma',
  sem_array_init bge Sigma arr (Atype elem len attr) vs vm m vm' m' Sigma' ->
  store_blocks_valid Sigma m ->
  (0 <= sizeof_type cenv (Atype elem len attr))%Z ->
  exists b,
    PTree.get arr vm' = Some (b, Atype elem len attr) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' (Val (Vloc b Ptrofs.zero) (Atype elem len attr)) nil
      (Atype elem len attr).
Proof.
  intros bge cenv Gamma Sigma arr elem len attr vs vm m vm' m' Sigma' Hinit Hvalid Hsize.
  inversion Hinit; subst.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc) as [b [Hvm [HS Hallocmem]]];
    destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hvalid) as [Hext Hvalid']
  end.
  exists b. split; [rewrite Hvm; apply PTree.gss |]. split; [exact Hext |]. split.
  - intros old ty Hget. eapply array_initialization_preserves_valid_blocks; [eassumption |].
    eapply Hvalid'; exact Hget.
  - apply ty_valarray_root; [rewrite HS; apply PTree.gss | exact Hsize].
Qed.

Print Assumptions singleton_allocation_maps.
Print Assumptions array_initialization_store_typing.

Lemma array_location_typing_entry : forall cenv Gamma Sigma b ofs elem len attr ef,
  type_expr cenv Gamma Sigma (Val (Vloc b ofs) (Atype elem len attr)) ef (Atype elem len attr) ->
  object_type_at cenv Sigma b (Ptrofs.unsigned ofs) (Atype elem len attr).
Proof. intros cenv Gamma Sigma b ofs elem len attr ef Htyped; inversion Htyped; subst; auto. Qed.

Lemma two_element_int32_initializer_typable : forall cenv Gamma Sigma arr first second,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr)
      [Val (Vint first) (Vtype (Tint I32 Signed noattr));
       Val (Vint second) (Vtype (Tint I32 Signed noattr))]
      (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr)) nil
    (Atype (Vtype (Tint I32 Signed noattr)) 2 noattr).
Proof.
  intros. eapply ty_ainit with (aty := Vtype (Tint I32 Signed noattr))
    (ts := [Vtype (Tint I32 Signed noattr); Vtype (Tint I32 Signed noattr)]).
  - eapply ty_cons with (ef := nil) (efs := nil); [apply ty_vali |].
    eapply ty_cons with (ef := nil) (efs := nil); [apply ty_vali | apply ty_nil].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eexists; reflexivity.
  - reflexivity.
  - apply storage_array_admissible.
    + vm_compute; reflexivity.
    + lia.
    + apply storage_type_leaf_admissible; [reflexivity|]. vm_compute; reflexivity.
Qed.

Print Assumptions array_location_typing_entry.
Print Assumptions two_element_int32_initializer_typable.

Lemma singleton_allocation_rebase : forall bge bookkeeping vm m arr ty vm' m' bookkeeping',
  alloc_variables bge bookkeeping vm m [(arr, ty)] vm' m' bookkeeping' ->
  forall Sigma, exists Sigma', alloc_variables bge Sigma vm m [(arr, ty)] vm' m' Sigma'.
Proof.
  intros bge bookkeeping vm m arr ty vm' m' bookkeeping' Halloc Sigma.
  destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc) as [b [Hvm [_ Hmem]]].
  subst vm'. exists (PTree.set b ty Sigma).
  eapply alloc_variables_con; [unfold balloc; rewrite Hmem; reflexivity | constructor].
Qed.

Lemma array_initialization_rebase : forall bge bookkeeping arr ty vs vm m vm' m' bookkeeping',
  sem_array_init bge bookkeeping arr ty vs vm m vm' m' bookkeeping' ->
  forall Sigma, exists Sigma', sem_array_init bge Sigma arr ty vs vm m vm' m' Sigma'.
Proof.
  intros bge bookkeeping arr ty vs vm m vm' m' bookkeeping' Hinit Sigma.
  inversion Hinit; subst.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_rebase _ _ _ _ _ _ _ _ _ Halloc Sigma) as [Sigma' Halloc']
  end.
  exists Sigma'. econstructor; eauto.
Qed.

Lemma completed_array_store_preservation :
  forall bge cenv Gamma Sigma p vm m arr elem len attr es vm' m' b,
  (0 <= sizeof_type cenv (Atype elem len attr))%Z ->
  store_blocks_valid Sigma m ->
  ssem_expr bge p vm m
    (Ainit arr (Atype elem len attr) es (Atype elem len attr)) m' vm'
    (Val (Vloc b Ptrofs.zero) (Atype elem len attr)) ->
  exists Sigma', store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' (Val (Vloc b Ptrofs.zero) (Atype elem len attr)) nil
      (Atype elem len attr).
Proof.
  intros bge cenv Gamma Sigma p vm m arr elem len attr es vm' m' b Hsize Hvalid Hstep.
  inversion Hstep; subst.
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_rebase _ _ _ _ _ _ _ _ _ _ Hinit Sigma) as [realSigma Hreal]
  end.
  destruct (array_initialization_store_typing bge cenv Gamma Sigma arr elem len attr
    (extract_values_exprs es) _ _ _ _ realSigma Hreal Hvalid Hsize)
    as [actual [Hlookup [Hext [Hblocks Htyped]]]].
  assert (actual = b) by congruence. subst actual. exists realSigma. auto.
Qed.

Lemma array_value_initializer_step_shape : forall bge p vm m arr ty es m' vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  (m' = m /\ vm' = vm /\ e' = Ainit arr ty es ty) \/
  exists b, e' = Val (Vloc b Ptrofs.zero) ty.
Proof.
  intros bge p vm m arr ty es m' vm' e' Hvalues Hstep. inversion Hstep; subst.
  - inversion Hvalues; subst.
    match goal with H : exists v t, _ = Val v t |- _ => destruct H as [v [t He]]; subst end.
    exfalso. eapply value_has_no_small_step; eauto.
  - inversion Hvalues; subst.
    match goal with Htail : ssem_exprs _ _ _ _ _ _ _ _ |- _ =>
      destruct (value_list_step_identity _ _ _ _ _ _ _ _ Htail ltac:(assumption))
        as [Hm [Hvm Hes]]
    end. subst. left; repeat split; reflexivity.
  - right. eexists; reflexivity.
Qed.

(* Allocation uses an internal map to name the fresh block, but its result
   does not change the source variable environment. *)
Lemma array_value_initializer_preserves_vmap : forall bge p vm m arr ty es m' vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' -> vm' = vm.
Proof.
  intros bge p vm m arr ty es m' vm' e' Hvalues Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [b He]]; [exact Hvm |].
  subst e'. inversion Hstep; reflexivity.
Qed.

Print Assumptions array_value_initializer_preserves_vmap.

Theorem array_value_initializer_type_preservation :
  forall bge cenv Gamma Sigma p vm m arr elem len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma (Ainit arr (Atype elem len attr) es (Atype elem len attr)) ef
    (Atype elem len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  (0 <= sizeof_type cenv (Atype elem len attr))%Z ->
  store_blocks_valid Sigma m ->
  ssem_expr bge p vm m (Ainit arr (Atype elem len attr) es (Atype elem len attr)) m' vm' e' ->
  exists Sigma', store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' ef (Atype elem len attr).
Proof.
  intros bge cenv Gamma Sigma p vm m arr elem len attr es ef vm' m' e' Htyped Hvalues Hsize Hvalid Hstep.
  assert (Hef : ef = nil).
  { inversion Htyped; subst. eapply value_arguments_effect_nil; eauto. }
  subst ef.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [b He]].
  - subst m' vm' e'. exists Sigma. split; [apply store_context_extends_refl | auto].
  - subst e'. eapply completed_array_store_preservation; eauto.
Qed.

Print Assumptions array_initialization_rebase.
Print Assumptions completed_array_store_preservation.
Print Assumptions array_value_initializer_step_shape.
Print Assumptions array_value_initializer_type_preservation.

Lemma typed_cell_storebytes_other_block : forall cenv Sigma m m' b ofs ty chunk target offset bytes,
  typed_memory_cell cenv Sigma m b ofs ty chunk ->
  Mem.storebytes m target offset bytes = Some m' -> b <> target ->
  typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  intros cenv Sigma m m' b ofs ty chunk target offset bytes
    [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Htyped]]]]] Hstore Hneq.
  constructor; try assumption.
  - eapply Mem.storebytes_valid_access_1; eauto.
  - exists cv, v. split.
    + rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore); [exact Hload | left; exact Hneq].
    + split; assumption.
Qed.

Lemma assignment_typed_cell_frame : forall bge assigned m target offset bf v m' v'
    cenv Sigma b ofs ty chunk,
  assign_addr bge assigned m target offset bf v m' v' ->
  typed_memory_cell cenv Sigma m b ofs ty chunk -> b <> target ->
  typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  intros bge assigned m target offset bf v m' v' cenv Sigma b ofs ty chunk Hassign Hcell Hneq.
  inversion Hassign; subst.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply typed_memory_cell_store_disjoint; [exact Hcell | exact H | left; exact Hneq]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply typed_memory_cell_store_disjoint; [exact Hcell | exact H | left; exact Hneq]
    end.
  - eapply typed_cell_storebytes_other_block; eauto.
  - match goal with H : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply typed_memory_cell_store_disjoint; [exact Hcell | exact H | left; exact Hneq]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply typed_memory_cell_store_disjoint; [exact Hcell | exact H | left; exact Hneq]
    end.
  - eapply typed_cell_storebytes_other_block; eauto.
Qed.

Lemma array_elements_typed_cell_frame : forall bge m target offset vs elem m',
  sem_array_init_helper bge m target offset vs elem m' ->
  forall cenv Sigma b ofs ty chunk,
    typed_memory_cell cenv Sigma m b ofs ty chunk -> b <> target ->
    typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  intros bge m target offset vs elem m' Hinit. induction Hinit;
    intros cenv Sigma old oldofs cellty cellchunk Hcell Hneq; auto.
  apply IHHinit; [|exact Hneq]. eapply assignment_typed_cell_frame; eauto.
Qed.

Lemma array_initialization_old_memory_frame :
  forall bge bookkeeping arr ty vs vm m vm' m' bookkeeping' cenv Sigma layout,
  sem_array_init bge bookkeeping arr ty vs vm m vm' m' bookkeeping' ->
  typed_memory_layout cenv Sigma layout m -> typed_memory_layout cenv Sigma layout m'.
Proof.
  intros bge bookkeeping arr ty vs vm m vm' m' bookkeeping' cenv Sigma layout Hinit Hmemory.
  inversion Hinit; subst.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc) as [fresh [Hvm [_ Hmem]]]
  end.
  assert (loc = fresh).
  { match goal with Hlookup : PTree.get arr vm' = Some (loc, _) |- _ =>
      rewrite Hvm, PTree.gss in Hlookup; congruence
    end. }
  subst loc. intros b ofs t chunk Hentry.
  eapply array_elements_typed_cell_frame; [eassumption | |].
  - eapply typed_memory_cell_alloc_frame; [exact Hmem | apply Hmemory; exact Hentry].
  - intro Heq. subst b. eapply Mem.fresh_block_alloc; [exact Hmem |].
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure.
    apply Hmemory; exact Hentry.
Qed.

Print Assumptions assignment_typed_cell_frame.
Print Assumptions array_initialization_old_memory_frame.

Lemma array_value_initializer_old_state_frame : forall bge cenv Sigma layout p vm m arr ty es m' vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  typed_memory_layout cenv Sigma layout m' /\
  (forall other, other <> arr -> PTree.get other vm' = PTree.get other vm).
Proof.
  intros bge cenv Sigma layout p vm m arr ty es m' vm' e' Hvalues Hmemory Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [b He]].
  - subst m' vm' e'. split; [exact Hmemory | reflexivity].
  - subst e'. inversion Hstep; subst. split.
    + eapply array_initialization_old_memory_frame; eauto.
    + intros; reflexivity.
Qed.

Theorem array_value_initializer_frame_preservation :
  forall bge cenv Gamma Sigma layout p vm m arr elem len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma (Ainit arr (Atype elem len attr) es (Atype elem len attr)) ef
    (Atype elem len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  (0 <= sizeof_type cenv (Atype elem len attr))%Z ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m (Ainit arr (Atype elem len attr) es (Atype elem len attr)) m' vm' e' ->
  exists Sigma', store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    typed_memory_layout cenv Sigma' layout m' /\
    type_expr cenv Gamma Sigma' e' ef (Atype elem len attr) /\
    (forall other, other <> arr -> PTree.get other vm' = PTree.get other vm).
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr elem len attr es ef vm' m' e'
    Htyped Hvalues Hsize Hvalid Hmemory Hstep.
  destruct (array_value_initializer_type_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvalues Hsize Hvalid Hstep) as [Sigma' [Hext [Hblocks Hresult]]].
  destruct (array_value_initializer_old_state_frame _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalues Hmemory Hstep) as [Hmemory' Hbindings].
  exists Sigma'. split; [exact Hext |]. split; [exact Hblocks |]. split.
  - eapply typed_memory_layout_context_extension; eauto.
  - split; assumption.
Qed.

Print Assumptions array_value_initializer_old_state_frame.
Print Assumptions array_value_initializer_frame_preservation.

Lemma array_repr_step : forall start width,
  Ptrofs.add (Ptrofs.repr start) (Ptrofs.repr width) = Ptrofs.repr (start + width).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma primitive_size_positive : forall pt, 0 < sizeof_ptype pt.
Proof. intros [|sz sign attr|sign attr]; try destruct sz; simpl; lia. Qed.

Lemma primitive_array_frame_before : forall vs bge m b start pt m',
  sem_array_init_helper bge m b (Ptrofs.repr start) vs (Vtype pt) m' ->
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  0 <= start -> start + sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  forall cenv Sigma ofs ty chunk,
  typed_memory_cell cenv Sigma m b ofs ty chunk ->
  Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= start ->
  typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  induction vs as [|v vs IH]; intros bge m b start pt m' Hinit Hvalues Hstart Hbound
    cenv Sigma ofs ty chunk Hcell Hbefore.
  - apply empty_array_initialization_identity in Hinit. subst; exact Hcell.
  - inversion Hinit; subst. inversion Hvalues; subst.
    pose proof (primitive_size_positive pt) as Hwidth.
    assert (Hrange : 0 <= start <= Ptrofs.max_unsigned).
    { change (start + sizeof_ptype pt * Z.of_nat (S (List.length vs)) <= Ptrofs.max_unsigned) in Hbound. rewrite Nat2Z.inj_succ in Hbound. nia. }
    match goal with Hshape : typeof_value v (Vtype pt),
      Hassign : assign_addr _ _ _ _ _ Full _ ?written _ |- _ =>
      pose proof (primitive_assignment_to_store bge m written b (Ptrofs.repr start) pt v Hshape Hassign) as Hstore
    end.
    rewrite Ptrofs.unsigned_repr in Hstore by exact Hrange.
    match goal with Htail : sem_array_init_helper _ _ _ _ vs _ _ |- _ =>
      cbn [sizeof_type] in Htail; rewrite array_repr_step in Htail;
      eapply IH; [exact Htail | assumption | | | |]
    end.
    + lia.
    + change (start + sizeof_ptype pt * Z.of_nat (S (List.length vs)) <= Ptrofs.max_unsigned) in Hbound. rewrite Nat2Z.inj_succ in Hbound. nia.
    + eapply typed_memory_cell_store_disjoint; [exact Hcell | exact Hstore |].
      right; right. exact Hbefore.
    + lia.
Qed.

Print Assumptions array_repr_step.
Print Assumptions primitive_array_frame_before.

Theorem primitive_array_initialized_cells : forall vs bge cenv Sigma m b start pt m',
  sem_array_init_helper bge m b (Ptrofs.repr start) vs (Vtype pt) m' ->
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  0 <= start -> start + sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  (forall i, (i < List.length vs)%nat ->
    Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
      (start + Z.of_nat i * sizeof_ptype pt) Freeable) ->
  forall i, (i < List.length vs)%nat ->
    typed_memory_cell cenv Sigma m' b (Ptrofs.repr (start + Z.of_nat i * sizeof_ptype pt))
      (Vtype pt) (chunk_of_ptype pt).
Proof.
  induction vs as [|v vs IH]; intros bge cenv Sigma m b start pt m'
    Hinit Hvalues Hstart Hbound Hvolatile Haccess i Hin; [simpl in Hin; lia |].
  inversion Hinit; subst. inversion Hvalues; subst.
  pose proof (primitive_size_positive pt) as Hwidth.
  change (start + sizeof_ptype pt * Z.of_nat (S (List.length vs)) <= Ptrofs.max_unsigned) in Hbound.
  rewrite Nat2Z.inj_succ in Hbound.
  assert (Hrange : 0 <= start <= Ptrofs.max_unsigned) by nia.
  assert (Htailbound : start + sizeof_ptype pt + sizeof_ptype pt * Z.of_nat (List.length vs)
    <= Ptrofs.max_unsigned) by nia.
  assert (Hfree : Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
    (Ptrofs.unsigned (Ptrofs.repr start)) Freeable).
  { rewrite Ptrofs.unsigned_repr by exact Hrange.
    specialize (Haccess O ltac:(simpl; lia)). simpl in Haccess. rewrite Z.add_0_r in Haccess. exact Haccess. }
  match goal with Hshape : typeof_value v (Vtype pt),
    Hassign : assign_addr _ _ _ _ _ Full _ ?written _ |- _ =>
    pose proof (primitive_assignment_to_store bge m written b (Ptrofs.repr start) pt v Hshape Hassign) as Hstore;
    destruct (initialize_primitive_cell bge m b (Ptrofs.repr start) pt v Hshape Hvolatile Hfree)
      as [computed [Hcomputed [_ Hhead]]];
    assert (computed = written) by congruence; subst computed
  end.
  match goal with Htail : sem_array_init_helper _ _ _ _ vs _ _ |- _ =>
    cbn [sizeof_type] in Htail; rewrite array_repr_step in Htail
  end.
  destruct i as [|i].
  - rewrite Z.mul_0_l, Z.add_0_r.
    eapply primitive_array_frame_before; [eassumption | assumption | lia | exact Htailbound | |].
    + apply primitive_cell_declarative_typing. exact Hhead.
    + rewrite Ptrofs.unsigned_repr by exact Hrange. rewrite primitive_chunk_size. lia.
  - replace (start + Z.of_nat (S i) * sizeof_ptype pt)
      with (start + sizeof_ptype pt + Z.of_nat i * sizeof_ptype pt)
      by (rewrite Nat2Z.inj_succ; ring).
    eapply IH; [eassumption | assumption | lia | exact Htailbound | exact Hvolatile | | simpl in Hin; lia].
    intros index Hindex. eapply Mem.store_valid_access_1; [exact Hstore |].
    replace (start + sizeof_ptype pt + Z.of_nat index * sizeof_ptype pt)
      with (start + Z.of_nat (S index) * sizeof_ptype pt)
      by (rewrite Nat2Z.inj_succ; ring).
    apply Haccess. simpl; lia.
Qed.

Print Assumptions primitive_array_initialized_cells.

Lemma primitive_chunk_alignment : forall pt,
  align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) = sizeof_ptype pt.
Proof. intros [|sz sign attr|sign attr]; try destruct sz; try destruct sign; reflexivity. Qed.

Lemma allocated_primitive_array_access : forall pt count m allocated b,
  Mem.alloc m 0 (sizeof_ptype pt * Z.of_nat count) = (allocated, b) ->
  forall i, (i < count)%nat ->
    Mem.valid_access allocated (transl_bchunk_cchunk (chunk_of_ptype pt)) b
      (Z.of_nat i * sizeof_ptype pt) Freeable.
Proof.
  intros pt count m allocated b Halloc i Hi.
  pose proof (primitive_size_positive pt) as Hwidth.
  eapply Mem.valid_access_alloc_same; [exact Halloc | | |].
  - nia.
  - rewrite primitive_chunk_size. apply Nat2Z.inj_lt in Hi. nia.
  - rewrite primitive_chunk_alignment. exists (Z.of_nat i). reflexivity.
Qed.

Definition extend_array_layout (layout : scalar_layout) b pt count : scalar_layout :=
  fun old ofs ty chunk => layout old ofs ty chunk \/
    exists i, (i < count)%nat /\ old = b /\
      ofs = Ptrofs.repr (Z.of_nat i * sizeof_ptype pt) /\
      ty = Vtype pt /\ chunk = chunk_of_ptype pt.

Theorem primitive_array_initialization_memory_layout :
  forall bge bookkeeping arr pt len attr vs vm m vm' m' bookkeeping' cenv Sigma layout,
  sem_array_init bge bookkeeping arr (Atype (Vtype pt) len attr) vs vm m vm' m' bookkeeping' ->
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  typed_memory_layout cenv Sigma layout m ->
  exists b, PTree.get arr vm' = Some (b, Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma (extend_array_layout layout b pt (List.length vs)) m'.
Proof.
  intros bge bookkeeping arr pt len attr vs vm m vm' m' bookkeeping' cenv Sigma layout
    Hinit Hvalues Hvolatile Hbound Hmemory.
  pose proof (array_initialization_old_memory_frame _ _ _ _ _ _ _ _ _ _ _ _ _ Hinit Hmemory) as Hold.
  inversion Hinit; subst.
  match goal with Heq : Atype _ _ _ = Atype _ _ _ |- _ => inversion Heq; subst end.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc) as [b [Hvm [_ Hallocmem]]]
  end.
  assert (loc = b).
  { match goal with Hlookup : PTree.get arr vm' = Some (loc, _) |- _ =>
      rewrite Hvm, PTree.gss in Hlookup; congruence
    end. }
  subst loc.
  cbn [sizeof_type] in Hallocmem.
  rewrite Z.max_r in Hallocmem by apply Nat2Z.is_nonneg.
  exists b. split; [rewrite Hvm; apply PTree.gss |].
  intros old ofs ty chunk [Hentry | [i [Hi [Hb [Hofs [Hty Hchunk]]]]]].
  - apply Hold; exact Hentry.
  - subst old ofs ty chunk.
    eapply (primitive_array_initialized_cells vs bge cenv Sigma _ b 0 pt m');
      try eassumption; try lia.
    intros index Hindex. simpl. eapply allocated_primitive_array_access; eauto.
Qed.

Print Assumptions allocated_primitive_array_access.
Print Assumptions primitive_array_initialization_memory_layout.

Corollary initialized_primitive_array_read :
  forall bge bookkeeping arr pt len attr vs vm m vm' m' bookkeeping' cenv Gamma Sigma layout p index,
  sem_array_init bge bookkeeping arr (Atype (Vtype pt) len attr) vs vm m vm' m' bookkeeping' ->
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  typed_memory_layout cenv Sigma layout m ->
  (index < Z.to_nat len)%nat ->
  exists v,
    ssem_expr bge p vm' m' (Aaccess arr (Atype (Vtype pt) len attr) index (Vtype pt))
      m' vm' (Val v (Vtype pt)) /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros bge bookkeeping arr pt len attr vs vm m vm' m' bookkeeping' cenv Gamma Sigma layout p index
    Hinit Hvalues Hvolatile Hbound Hmemory Hindex.
  destruct (primitive_array_initialization_memory_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinit Hvalues Hvolatile Hbound Hmemory) as [b [Hlookup Hcells]].
  destruct (array_initialization_length _ _ _ _ _ _ _ _ _ _ Hinit)
    as [elem [len' [attr' [block [Heq [Hlength Hbinding]]]]]].
  inversion Heq; subst elem len' attr'.
  assert (Hlen : len = Z.of_nat (List.length vs)) by congruence.
  assert (Hi : (index < List.length vs)%nat).
  { rewrite Hlen, Nat2Z.id in Hindex. exact Hindex. }
  rewrite <- Hlen.
  eapply (typed_array_access_progress bge cenv Gamma Sigma
    (extend_array_layout layout b pt (List.length vs)) p vm' m' arr (Vtype pt) len attr index b
    (chunk_of_ptype pt)); try eassumption.
  right. exists index. repeat split; auto.
Qed.

Print Assumptions initialized_primitive_array_read.

Lemma primitive_array_elements_progress : forall vs bge m b start pt,
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  0 <= start -> start + sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  (forall i, (i < List.length vs)%nat ->
    Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
      (start + Z.of_nat i * sizeof_ptype pt) Freeable) ->
  exists m', sem_array_init_helper bge m b (Ptrofs.repr start) vs (Vtype pt) m'.
Proof.
  induction vs as [|v vs IH]; intros bge m b start pt Hvalues Hvolatile Hstart Hbound Haccess.
  - exists m. constructor.
  - inversion Hvalues; subst.
    pose proof (primitive_size_positive pt) as Hwidth.
    change (start + sizeof_ptype pt * Z.of_nat (S (List.length vs)) <= Ptrofs.max_unsigned) in Hbound.
    rewrite Nat2Z.inj_succ in Hbound.
    assert (Hrange : 0 <= start <= Ptrofs.max_unsigned) by nia.
    assert (Hfree : Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
      (Ptrofs.unsigned (Ptrofs.repr start)) Freeable).
    { rewrite Ptrofs.unsigned_repr by exact Hrange.
      specialize (Haccess O ltac:(simpl; lia)). simpl in Haccess. rewrite Z.add_0_r in Haccess. exact Haccess. }
    destruct (initialize_primitive_cell bge m b (Ptrofs.repr start) pt v ltac:(assumption) Hvolatile Hfree)
      as [written [Hstore [Hassign Hcell]]].
    assert (Haccess' : forall i, (i < List.length vs)%nat ->
      Mem.valid_access written (transl_bchunk_cchunk (chunk_of_ptype pt)) b
        (start + sizeof_ptype pt + Z.of_nat i * sizeof_ptype pt) Freeable).
    { intros i Hi. eapply Mem.store_valid_access_1; [exact Hstore |].
      replace (start + sizeof_ptype pt + Z.of_nat i * sizeof_ptype pt)
        with (start + Z.of_nat (S i) * sizeof_ptype pt) by (rewrite Nat2Z.inj_succ; ring).
      apply Haccess. simpl; lia. }
    destruct (IH bge written b (start + sizeof_ptype pt) pt ltac:(assumption) Hvolatile
      ltac:(lia) ltac:(nia) Haccess') as [finished Htail].
    exists finished. eapply sem_allocate_array_elm; [exact Hassign |].
    cbn [sizeof_type]. rewrite array_repr_step. exact Htail.
Qed.

Theorem primitive_array_initialization_progress : forall bge Sigma vm m arr pt attr vs,
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * Z.of_nat (List.length vs) <= Ptrofs.max_unsigned ->
  exists vm' m' Sigma',
    sem_array_init bge Sigma arr (Atype (Vtype pt) (Z.of_nat (List.length vs)) attr)
      vs vm m vm' m' Sigma'.
Proof.
  intros bge Sigma vm m arr pt attr vs Hvalues Hvolatile Hbound.
  destruct (alloc_variables_single bge Sigma vm m arr
    (Atype (Vtype pt) (Z.of_nat (List.length vs)) attr)) as [allocated [b [Halloc Hvars]]].
  assert (Hsize : Mem.alloc m 0 (sizeof_ptype pt * Z.of_nat (List.length vs)) = (allocated, b)).
  { cbn [sizeof_type] in Halloc. rewrite Z.max_r in Halloc by apply Nat2Z.is_nonneg. exact Halloc. }
  destruct (primitive_array_elements_progress vs bge allocated b 0 pt Hvalues Hvolatile ltac:(lia)
    Hbound ltac:(intros i Hi; simpl; eapply allocated_primitive_array_access; eauto)) as [finished Hinit].
  do 3 eexists. eapply sem_allocate_array; [exact Hvars | apply PTree.gss | reflexivity | reflexivity | exact Hinit].
Qed.

Print Assumptions primitive_array_elements_progress.
Print Assumptions primitive_array_initialization_progress.

Lemma primitive_type_equality_sound : forall pt ty,
  eq_type (Vtype pt) ty = true -> ty = Vtype pt.
Proof.
  intros pt ty. destruct ty; simpl; try discriminate.
  destruct pt; destruct p; simpl; try discriminate; try reflexivity;
    repeat match goal with
    | |- context [Ctyping.intsize_eq ?x ?y] => destruct (Ctyping.intsize_eq x y)
    | |- context [Ctyping.signedness_eq ?x ?y] => destruct (Ctyping.signedness_eq x y)
    | |- context [attr_eq ?x ?y] => destruct (attr_eq x y)
    end; intros H; try discriminate; subst; reflexivity.
Qed.

Lemma extracted_value_arguments_length : forall es,
  Forall (fun e => exists v t, e = Val v t) es ->
  List.length (extract_values_exprs es) = List.length es.
Proof.
  intros es Hvalues. induction Hvalues as [|e es [v [t He]] Htail IH];
    subst; simpl; congruence.
Qed.

Lemma primitive_value_arguments_shape : forall cenv Gamma Sigma es ef ts pt,
  type_exprs cenv Gamma Sigma es ef ts ->
  Forall (fun e => exists v t, e = Val v t) es ->
  all_eq_type (Vtype pt) ts = true ->
  Forall (fun v => typeof_value v (Vtype pt)) (extract_values_exprs es).
Proof.
  intros cenv Gamma Sigma es ef ts pt Htyped.
  induction Htyped; intros Hvalues Hequal; [constructor |].
  inversion Hvalues; subst.
  match goal with H : exists v t, e = Val v t |- _ =>
    destruct H as [v [annotation He]]; subst e
  end.
  simpl in Hequal. apply Bool.andb_true_iff in Hequal. destruct Hequal as [Hhead Htail].
  apply primitive_type_equality_sound in Hhead. subst t.
  simpl. constructor.
  - inversion H; subst; exact I.
  - apply IHHtyped; assumption.
Qed.

Print Assumptions primitive_value_arguments_shape.

Lemma typed_primitive_array_arguments : forall cenv Gamma Sigma arr pt len attr es ef,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  len = Z.of_nat (List.length (extract_values_exprs es)) /\
  Forall (fun v => typeof_value v (Vtype pt)) (extract_values_exprs es) /\ ef = nil.
Proof.
  intros cenv Gamma Sigma arr pt len attr es ef Htyped Hvalues.
  pose proof (typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped) as [_ [elem [a Hextent]]].
  inversion Hextent.
  split.
  - rewrite extracted_value_arguments_length by exact Hvalues. congruence.
  - inversion Htyped; subst.
    match goal with Hget : get_array_elm_ty _ = OK _ |- _ => simpl in Hget; inversion Hget; subst end.
    split.
    + eapply primitive_value_arguments_shape; eauto.
    + eapply value_arguments_effect_nil; eauto.
Qed.

Theorem source_primitive_array_progress :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  exists vm' m' Sigma' b,
    ssem_expr bge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr))
      m' vm' (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) ef
      (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma'
      (extend_array_layout layout b pt (List.length es)) m'.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory.
  destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hlength [Hshapes Heffect]]. subst ef.
  destruct (primitive_array_initialization_progress bge Sigma vm m arr pt attr
    (extract_values_exprs es) Hshapes Hvolatile ltac:(rewrite <- Hlength; exact Hbound))
    as [vm' [m' [Sigma' Hinit]]].
  rewrite <- Hlength in Hinit.
  destruct (array_initialization_store_typing bge cenv Gamma Sigma arr (Vtype pt) len attr
    (extract_values_exprs es) vm m vm' m' Sigma' Hinit Hvalid (primitive_array_size_nonnegative _ _ _ _))
    as [b [Hbinding [Hextends [Hvalid' Hresult]]]].
  destruct (primitive_array_initialization_memory_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinit Hshapes Hvolatile ltac:(rewrite <- Hlength; exact Hbound) Hmemory)
    as [b' [Hbinding' Hlayout]].
  assert (b' = b) by congruence. subst b'.
  exists vm, m', Sigma', b. split.
  - eapply ssem_array_init3; eauto.
  - split; [exact Hextends |]. split; [exact Hvalid' |]. split; [exact Hresult |].
    rewrite extracted_value_arguments_length in Hlayout by exact Hvalues.
    eapply typed_memory_layout_context_extension; eauto.
Qed.

Print Assumptions typed_primitive_array_arguments.
Print Assumptions source_primitive_array_progress.

Theorem completed_primitive_array_preservation :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' b,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm'
    (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) ->
  exists Sigma',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) ef
      (Atype (Vtype pt) len attr) /\
    vm' = vm /\
    typed_memory_layout cenv Sigma' (extend_array_layout layout b pt (List.length es)) m'.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' b
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstep.
  destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hlength [Hshapes Heffect]]. subst ef.
  inversion Hstep; subst.
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_rebase _ _ _ _ _ _ _ _ _ _ Hinit Sigma)
      as [postSigma Hreal]
  end.
  destruct (array_initialization_store_typing bge cenv Gamma Sigma arr (Vtype pt) _ attr
    (extract_values_exprs es) _ _ _ _ postSigma Hreal Hvalid (primitive_array_size_nonnegative _ _ _ _))
    as [actual [Hbinding [Hext [Hblocks Hresult]]]].
  assert (actual = b) by congruence. subst actual.
  destruct (primitive_array_initialization_memory_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hreal Hshapes Hvolatile Hbound Hmemory)
    as [actual [Hbinding' Hlayout]].
  assert (actual = b) by congruence. subst actual.
  exists postSigma. split; [exact Hext |]. split; [exact Hblocks |].
  split; [exact Hresult |]. split; [reflexivity |].
  rewrite extracted_value_arguments_length in Hlayout by exact Hvalues.
  eapply typed_memory_layout_context_extension; eauto.
Qed.

Print Assumptions completed_primitive_array_preservation.

Theorem source_primitive_array_preservation :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' layout',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' ef (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma' layout' m' /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    (forall other, other <> arr -> PTree.get other vm' = PTree.get other vm) /\
    (e' = Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr) \/
      exists b, e' = Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr) /\
        vm' = vm /\
        layout' = extend_array_layout layout b pt (List.length es)).
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e'
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstep.
  destruct (array_value_initializer_old_state_frame _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalues Hmemory Hstep) as [_ Hbindings].
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [b He]].
  - subst m' vm' e'. exists Sigma, layout.
    split; [apply store_context_extends_refl |]. split; [exact Hvalid |].
    split; [exact Htyped |]. split; [exact Hmemory |].
    split; [auto |]. split; [exact Hbindings | left; reflexivity].
  - subst e'.
    destruct (completed_primitive_array_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstep)
      as [Sigma' [Hext [Hblocks [Hresult [Hbinding Hlayout]]]]].
    exists Sigma', (extend_array_layout layout b pt (List.length es)).
    split; [exact Hext |]. split; [exact Hblocks |]. split; [exact Hresult |].
    split; [exact Hlayout |]. split; [intros; left; assumption |].
    split; [exact Hbindings |]. right. exists b. auto.
Qed.

Print Assumptions source_primitive_array_preservation.

(* Every primitive array present in the runtime map owns initialized layout
   entries. This is separate from the source expression's binding requirement. *)
Definition primitive_array_bindings (vm : vmap) (layout : scalar_layout) : Prop :=
  forall arr b pt len attr,
    PTree.get arr vm = Some (b, Atype (Vtype pt) len attr) ->
    0 <= len /\ forall i, (i < Z.to_nat len)%nat ->
      layout b (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt)) (Vtype pt) (chunk_of_ptype pt).

Lemma primitive_array_bindings_empty : forall layout,
  primitive_array_bindings (PTree.empty (positive * type)) layout.
Proof. intros layout arr b pt len attr Hget. rewrite PTree.gempty in Hget. discriminate. Qed.

Lemma primitive_array_bindings_extend : forall vm vm' layout arr b pt count attr,
  primitive_array_bindings vm layout ->
  PTree.get arr vm' = Some (b, Atype (Vtype pt) (Z.of_nat count) attr) ->
  (forall other, other <> arr -> PTree.get other vm' = PTree.get other vm) ->
  primitive_array_bindings vm' (extend_array_layout layout b pt count).
Proof.
  intros vm vm' layout arr b pt count attr Hbindings Hnew Hframe other old q len a Hget.
  destruct (Pos.eq_dec other arr) as [Heq | Hneq].
  - subst other. rewrite Hnew in Hget. inversion Hget; subst.
    split; [apply Nat2Z.is_nonneg |]. intros i Hi. rewrite Nat2Z.id in Hi.
    right. exists i. repeat split; auto.
  - rewrite Hframe in Hget by exact Hneq.
    destruct (Hbindings _ _ _ _ _ Hget) as [Hlen Hcells].
    split; [exact Hlen |]. intros i Hi. left. apply Hcells; exact Hi.
Qed.

Theorem primitive_array_bindings_read_progress :
  forall bge cenv Gamma Sigma layout p vm m arr b pt len attr i,
  primitive_array_bindings vm layout -> typed_memory_layout cenv Sigma layout m ->
  PTree.get arr vm = Some (b, Atype (Vtype pt) len attr) ->
  (i < Z.to_nat len)%nat ->
  exists v,
    ssem_expr bge p vm m (Aaccess arr (Atype (Vtype pt) len attr) i (Vtype pt))
      m vm (Val v (Vtype pt)) /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr b pt len attr i Hbindings Hmemory Hget Hi.
  eapply typed_array_access_progress with (layout := layout) (b := b) (chunk := chunk_of_ptype pt);
    try eassumption.
  apply (proj2 (Hbindings _ _ _ _ _ Hget)); exact Hi.
Qed.

Print Assumptions primitive_array_bindings_extend.
Print Assumptions primitive_array_bindings_read_progress.

Theorem source_primitive_array_bindings_preservation :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  primitive_array_bindings vm layout ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' layout',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' ef (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma' layout' m' /\ primitive_array_bindings vm' layout'.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e'
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hbindings Hstep.
  destruct (source_primitive_array_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hstep)
    as [Sigma' [layout' [Hext [Hblocks [Hresult [Hmemory' [Hinclusion [Hframe Hshape]]]]]]]].
  exists Sigma', layout'. split; [exact Hext |]. split; [exact Hblocks |].
  split; [exact Hresult |]. split; [exact Hmemory' |].
  assert (Hvm : vm' = vm) by (eapply array_value_initializer_preserves_vmap; eauto).
  subst vm'. intros other old q n a Hlookup.
  destruct (Hbindings _ _ _ _ _ Hlookup) as [Hn Hcells].
  split; [exact Hn |]. intros i Hi. apply Hinclusion. apply Hcells; exact Hi.
Qed.

Print Assumptions source_primitive_array_bindings_preservation.

(* The parser emits Bind arr ... (Ainit arr ...) body for array declarations.
   The allocated array value is substituted into the indexed-read body;
   allocation leaves all existing runtime variable bindings unchanged. *)
Theorem primitive_array_declare_read :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef index,
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  (index < Z.to_nat len)%nat ->
  exists vm' m' Sigma' b v,
    ssem_closure bge p vm m
      (Bind arr (Atype (Vtype pt) len attr)
        (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr))
        (Aaccess arr (Atype (Vtype pt) len attr) index (Vtype pt)) (Vtype pt))
      3%nat m' vm' (Val v (Vtype pt)) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' (Val v (Vtype pt)) nil (Vtype pt) /\
    typed_memory_layout cenv Sigma' (extend_array_layout layout b pt (List.length es)) m'.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef index
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hindex.
  destruct (source_primitive_array_progress bge cenv Gamma Sigma layout p vm m arr pt len attr es ef
    Htyped Hvalues Hvolatile Hbound Hvalid Hmemory)
    as [vm' [m' [Sigma' [b [Hinit [Hext [Hblocks [Hresult Hlayout]]]]]]]].
  destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hlength _].
  rewrite extracted_value_arguments_length in Hlength by exact Hvalues.
  assert (Hi : (index < List.length es)%nat).
  { rewrite Hlength, Nat2Z.id in Hindex. exact Hindex. }
  destruct (typed_memory_cell_read cenv Gamma Sigma' m' b
    (Ptrofs.repr (Z.of_nat index * sizeof_type bge.(genv_cenv) (Vtype pt)))
    (Vtype pt) (chunk_of_ptype pt)
    (Hlayout _ _ _ _ ltac:(right; exists index; repeat split; auto))) as [v [Hread Hvalue]].
  exists vm', m', Sigma', b, v. split.
  - eapply ssem_multi with (n := 2%nat).
    + apply ssem_bind1. exact Hinit.
    + eapply ssem_multi with (n := 1%nat).
      * eapply ssem_bind2. apply S_Aaccess_same.
      * apply ssem_one. eapply ssem_array_read_value; rewrite ?Ptrofs.add_zero_l; eauto.
  - split; [exact Hext |]. split; [exact Hblocks |]. split; assumption.
Qed.

Print Assumptions primitive_array_declare_read.

Lemma typed_value_annotation : forall cenv Gamma Sigma v annotation ef ty,
  type_expr cenv Gamma Sigma (Val v annotation) ef ty -> annotation = ty.
Proof. intros; inversion H; reflexivity. Qed.

(* A genuinely unevaluated argument-list step is an initializer step when the remaining
   arguments are not values. Typing ensures the head value has the element
   annotation required by the tail-evaluation rule. *)
Lemma primitive_array_argument_step :
  forall bge cenv Gamma Sigma p vm m arr pt len attr es ef ts vm' m' es',
  type_exprs cenv Gamma Sigma es ef ts ->
  all_eq_type (Vtype pt) ts = true ->
  is_values es = false -> ssem_exprs bge p vm m es m' vm' es' ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm'
    (Ainit arr (Atype (Vtype pt) len attr) es' (Atype (Vtype pt) len attr)).
Proof.
  intros bge cenv Gamma Sigma p vm m arr pt len attr es ef ts vm' m' es'
    Htyped Hequal Hnonvalues Hstep.
  inversion Hstep; subst.
  - discriminate Hnonvalues.
  - apply ssem_array_init1. assumption.
  - inversion Htyped; subst.
    simpl in Hequal. apply Bool.andb_true_iff in Hequal. destruct Hequal as [Hhead Htail].
    apply primitive_type_equality_sound in Hhead. subst.
    match goal with Hvalue : type_expr _ _ _ (Val _ _) _ _ |- _ =>
      pose proof (typed_value_annotation _ _ _ _ _ _ _ Hvalue) as Hannotation
    end.
    subst. eapply ssem_array_init2; [exact Hnonvalues |reflexivity | eassumption].
Qed.

Lemma array_initializer_retype_arguments :
  forall cenv Gamma Sigma arr ty es result ef Sigma' es' ef',
  type_expr cenv Gamma Sigma (Ainit arr ty es result) ef result ->
  (forall ts, type_exprs cenv Gamma Sigma es ef ts ->
    type_exprs cenv Gamma Sigma' es' ef' ts) ->
  type_expr cenv Gamma Sigma' (Ainit arr ty es' result) ef' result.
Proof.
  intros cenv Gamma Sigma arr ty es result ef Sigma' es' ef' Htyped Harguments.
  inversion Htyped; subst. eapply ty_ainit; eauto.
Qed.

Print Assumptions primitive_array_argument_step.
Print Assumptions array_initializer_retype_arguments.

Lemma array_initializer_step_cases : forall bge p vm m arr ty es vm' m' e',
  ssem_expr bge p vm m (Ainit arr ty es ty) m' vm' e' ->
  (exists es', e' = Ainit arr ty es' ty /\ ssem_exprs bge p vm m es m' vm' es') \/
  (Forall (fun e => exists v t, e = Val v t) es /\
    exists b, e' = Val (Vloc b Ptrofs.zero) ty).
Proof.
  intros bge p vm m arr ty es vm' m' e' Hstep. inversion Hstep; subst.
  - left. eexists. split; [reflexivity | apply ssem_cons1; assumption].
  - left. eexists. split; [reflexivity | apply ssem_cons2; assumption].
  - right. split; [assumption | eexists; reflexivity].
Qed.

(* The remaining premise is exactly the argument-evaluation obligation for a
   mutual preservation induction. Unlike the value-only theorem, this covers
   arbitrary initializer arguments and all three initializer step rules. *)
Lemma array_initializer_typing_arguments :
  forall cenv Gamma Sigma arr ty es result ef,
  type_expr cenv Gamma Sigma (Ainit arr ty es result) ef result ->
  exists ts, type_exprs cenv Gamma Sigma es ef ts /\
    forall Sigma' es' ef', type_exprs cenv Gamma Sigma' es' ef' ts ->
      type_expr cenv Gamma Sigma' (Ainit arr ty es' result) ef' result.
Proof.
  intros cenv Gamma Sigma arr ty es result ef Htyped. inversion Htyped; subst.
  eexists. split; [eassumption |]. intros. eapply ty_ainit; eauto.
Qed.

Theorem primitive_array_preservation_from_arguments :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  primitive_array_bindings vm layout ->
  (forall ts, type_exprs cenv Gamma Sigma es ef ts ->
    forall next_vm next_m next_es,
    ssem_exprs bge p vm m es next_m next_vm next_es ->
    exists next_Sigma next_layout next_ef,
      store_context_extends Sigma next_Sigma /\ store_blocks_valid next_Sigma next_m /\
      typed_memory_layout cenv next_Sigma next_layout next_m /\
      primitive_array_bindings next_vm next_layout /\
      sub_effect next_ef ef = true /\
      type_exprs cenv Gamma next_Sigma next_es next_ef ts) ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' layout' ef',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    type_expr cenv Gamma Sigma' e' ef' (Atype (Vtype pt) len attr) /\
    typed_memory_layout cenv Sigma' layout' m' /\ primitive_array_bindings vm' layout' /\
    sub_effect ef' ef = true.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e'
    Htyped Hvolatile Hbound Hvalid Hmemory Hbindings Harguments Hstep.
  destruct (array_initializer_step_cases _ _ _ _ _ _ _ _ _ _ Hstep)
    as [[es' [He Hargstep]] | [Hvalues Hresult]].
  - subst e'.
    destruct (array_initializer_typing_arguments _ _ _ _ _ _ _ _ Htyped)
      as [ts [Hargs Hretype]].
    destruct (Harguments ts Hargs _ _ _ Hargstep)
      as [Sigma' [layout' [ef' [Hext [Hblocks [Hmemory' [Hbindings' [Heffects Htypes]]]]]]]].
    exists Sigma', layout', ef'. split; [exact Hext |]. split; [exact Hblocks |].
    split; [apply Hretype; exact Htypes |].
    split; [exact Hmemory' |]. split; assumption.
  - destruct (source_primitive_array_bindings_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htyped Hvalues Hvolatile Hbound Hvalid Hmemory Hbindings Hstep)
      as [Sigma' [layout' [Hext [Hblocks [Htype [Hmem Hbind]]]]]].
    destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
      as [_ [_ Hef]]. subst ef.
    exists Sigma', layout', nil. split; [exact Hext |]. split; [exact Hblocks |].
    split; [exact Htype |]. split; [exact Hmem |]. split; [exact Hbind | reflexivity].
Qed.

Print Assumptions array_initializer_step_cases.
Print Assumptions primitive_array_preservation_from_arguments.

Definition primitive_array_state cenv Sigma vm m : Prop :=
  store_blocks_valid Sigma m /\ exists layout,
    typed_memory_layout cenv Sigma layout m /\ primitive_array_bindings vm layout.

Theorem primitive_array_preservation_from_expressions :
  forall bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  primitive_array_bindings vm layout ->
  (forall e, In e es -> forall effect ty,
    type_expr cenv Gamma Sigma e effect ty ->
    forall next_vm next_m next_e,
      ssem_expr bge p vm m e next_m next_vm next_e ->
      exists next_Sigma next_effect,
        store_context_extends Sigma next_Sigma /\
        primitive_array_state cenv next_Sigma next_vm next_m /\
        type_expr cenv Gamma next_Sigma next_e next_effect ty /\
        sub_effect next_effect effect = true) ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' ef',
    store_context_extends Sigma Sigma' /\ primitive_array_state cenv Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' (Atype (Vtype pt) len attr) /\
    sub_effect ef' ef = true.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr pt len attr es ef vm' m' e'
    Htyped Hvolatile Hbound Hvalid Hmemory Hbindings Hlocal Hstep.
  assert (Hstate : primitive_array_state cenv Sigma vm m).
  { split; [exact Hvalid |]. exists layout. split; assumption. }
  assert (Harguments : forall ts, type_exprs cenv Gamma Sigma es ef ts ->
    forall next_vm next_m next_es,
    ssem_exprs bge p vm m es next_m next_vm next_es ->
    exists next_Sigma next_layout next_ef,
      store_context_extends Sigma next_Sigma /\ store_blocks_valid next_Sigma next_m /\
      typed_memory_layout cenv next_Sigma next_layout next_m /\
      primitive_array_bindings next_vm next_layout /\ sub_effect next_ef ef = true /\
      type_exprs cenv Gamma next_Sigma next_es next_ef ts).
  { intros ts Hargs next_vm next_m next_es Hargstep.
    destruct (argument_list_preservation_from_expressions (primitive_array_state cenv)
      bge p cenv Gamma Sigma vm m es ef ts next_vm next_m next_es Hstate Hargs Hlocal Hargstep)
      as [nextSigma [nextEffect [Hext [[Hblocks [nextLayout [Hmem Hbind]]] [Htypes Hsub]]]]].
    exists nextSigma, nextLayout, nextEffect.
    split; [exact Hext |]. split; [exact Hblocks |]. split; [exact Hmem |].
    split; [exact Hbind |]. split; assumption. }
  destruct (primitive_array_preservation_from_arguments _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvolatile Hbound Hvalid Hmemory Hbindings Harguments Hstep)
    as [Sigma' [layout' [ef' [Hext [Hblocks [Htype [Hmem [Hbind Hsub]]]]]]]].
  exists Sigma', ef'. split; [exact Hext |]. split.
  - split; [exact Hblocks |]. exists layout'. split; assumption.
  - split; assumption.
Qed.

Print Assumptions primitive_array_preservation_from_expressions.

(* Expression-based reads are the substitution target for a bound array name.
   Unlike Aaccess, these rules do not depend on an entry in the variable map. *)
Lemma array_value_read_progress :
  forall bge cenv Gamma Sigma layout p vm m b elem len a n chunk,
  (n < Z.to_nat len)%nat ->
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk ->
  exists v,
    ssem_expr bge p vm m
      (Prim (ArrayRead n) [Val (Vloc b Ptrofs.zero) (Atype elem len a)] elem)
      m vm (Val v elem) /\
    type_expr cenv Gamma Sigma (Val v elem) nil elem.
Proof.
  intros bge cenv Gamma Sigma layout p vm m b elem len a n chunk Hbound Hmemory Hcell.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b
    (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk
    (Hmemory _ _ _ _ Hcell)) as [v [Hread Htyped]].
  exists v. split; [eapply ssem_array_read_value; rewrite ?Ptrofs.add_zero_l; eauto | exact Htyped].
Qed.

Lemma array_value_read_preservation :
  forall bge cenv Gamma Sigma layout p vm m b elem len a n chunk m' vm' e',
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk ->
  ssem_expr bge p vm m
    (Prim (ArrayRead n) [Val (Vloc b Ptrofs.zero) (Atype elem len a)] elem)
    m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil elem.
Proof.
  intros bge cenv Gamma Sigma layout p vm m b elem len a n chunk m' vm' e'
    Hmemory Hcell Hstep.
  assert (Hscalar : is_aggregate_type elem = false).
  { eapply by_value_type_not_aggregate. destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hrest]. exact Hmode. }
  assert (Hnonunit : elem <> Utype).
  { intro Heq. subst elem. pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
    discriminate Hmode. }
  inversion Hstep; subst; try contradiction;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _] end; congruence].
  rewrite ?Ptrofs.add_zero_l in *.
  split; [reflexivity |]. split; [reflexivity |].
  eapply typed_memory_cell_read_preservation; [apply Hmemory; exact Hcell | eassumption].
Qed.

Lemma array_read_context_preservation :
  forall bge cenv Gamma Sigma Sigma' p vm m e e' m' vm' elem len a n ef,
  type_expr cenv Gamma Sigma e ef (Atype elem len a) ->
  (n < Z.to_nat len)%nat ->
  is_funtype elem = false ->
  ssem_expr bge p vm m e m' vm' e' ->
  type_expr cenv Gamma Sigma' e' ef (Atype elem len a) ->
  ssem_expr bge p vm m (Prim (ArrayRead n) [e] elem)
    m' vm' (Prim (ArrayRead n) [e'] elem) /\
  type_expr cenv Gamma Sigma' (Prim (ArrayRead n) [e'] elem) ef elem.
Proof. intros; split; [apply ssem_array_read_context | eapply ty_arrayread]; eauto. Qed.

Lemma array_read_substitution_typing :
  forall cenv Gamma Sigma x v tx e ef elem len a n,
  type_expr cenv (extend_context Gamma x tx) Sigma e ef (Atype elem len a) ->
  type_expr cenv Gamma Sigma (Val v tx) nil tx ->
  (n < Z.to_nat len)%nat ->
  is_funtype elem = false ->
  type_expr cenv Gamma Sigma
    (subst x (Val v tx) (Prim (ArrayRead n) [e] elem)) ef elem.
Proof.
  intros. cbn [subst substs]. eapply ty_arrayread; [|eassumption|eassumption].
  eapply (proj2 value_substitution_typing); eauto.
Qed.

Print Assumptions array_value_read_progress.
Print Assumptions array_value_read_preservation.
Print Assumptions array_read_context_preservation.
Print Assumptions array_read_substitution_typing.


(* A let-bound array value remains usable even when the runtime map has no
   entry (or a shadowed entry) for the source name. *)
Theorem bound_array_value_read :
  forall bge cenv Gamma Sigma layout p vm m arr b elem len a n chunk,
  PTree.get b Sigma = Some (Atype elem len a) ->
  (n < Z.to_nat len)%nat ->
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.repr (Z.of_nat n * sizeof_type bge.(genv_cenv) elem)) elem chunk ->
  let body := Aaccess arr (Atype elem len a) n elem in
  let binding := Bind arr (Atype elem len a)
    (Val (Vloc b Ptrofs.zero) (Atype elem len a)) body elem in
  type_expr cenv Gamma Sigma binding nil elem /\
  exists v, ssem_closure bge p vm m binding 2%nat m vm (Val v elem) /\
    type_expr cenv Gamma Sigma (Val v elem) nil elem.
Proof.
  intros bge cenv Gamma Sigma layout p vm m arr b elem len a n chunk
    Hlookup Hbound Hmemory Hcell body binding.
  split.
  - unfold binding, body.
    change (type_expr cenv Gamma Sigma
      (Bind arr (Atype elem len a) (Val (Vloc b Ptrofs.zero) (Atype elem len a))
        (Aaccess arr (Atype elem len a) n elem) elem) (nil ++ nil) elem).
    apply ty_bind.
    + apply ty_valarray_root; [exact Hlookup |].
      assert (Hmode := typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)).
      assert (Hsize : (0 <= sizeof_type cenv elem)%Z).
      { destruct elem as [|prim|ptr|sid attr|elem count attr|args eff result variadic|];
          simpl in Hmode; try discriminate; simpl.
        - destruct prim as [|sz sign attrs|sign attrs]; try destruct sz; simpl; lia.
      }
      simpl. apply Z.mul_nonneg_nonneg; [exact Hsize | lia].
    + eapply ty_aaccess with (aty := elem); try reflexivity.
      * apply PTree.gss.
      * exists len, a. auto.
      * pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
        destruct elem; simpl in *; try reflexivity; discriminate.
  - destruct (array_value_read_progress bge cenv Gamma Sigma layout p vm m b elem len a n chunk
      Hbound Hmemory Hcell) as [v [Hstep Htyped]].
    exists v. split; [|exact Htyped].
    unfold binding, body. eapply ssem_multi with (n := 1%nat).
    + eapply ssem_bind2. apply S_Aaccess_same.
    + apply ssem_one. exact Hstep.
Qed.

Print Assumptions bound_array_value_read.
