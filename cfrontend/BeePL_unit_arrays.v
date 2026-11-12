(* Unit arrays have a real zero-byte allocation and no scalar storage cells.
   Initialization consumes unit values; selection checks the array descriptor
   and logical index, without inventing a memory load of Utype.
   Both source initialization and the resulting raw array value execute in
   big-step semantics; array value well-formedness records only its shape. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_storage_types.
Require Import BeePL_soundness_memory BeePL_soundness_variables BeePL_aggregate_memory BeePL_object_paths.
Import ListNotations.
Local Open Scope Z_scope.

Lemma unit_array_elements_initialize : forall ge m block base values,
  Forall (fun v => v = Vunit) values ->
  sem_array_init_helper ge m block base values Utype m.
Proof.
  intros ge m block base values Hvalues. induction Hvalues.
  - constructor.
  - subst x. apply sem_allocate_array_unit. exact IHHvalues.
Qed.

Lemma unit_full_assignment_impossible : forall ge m block base v final result,
  ~ assign_addr ge Utype m block base Full v final result.
Proof. intros ge m block base v final result H. inversion H; subst; discriminate. Qed.

Lemma unit_array_elements_identity : forall ge m block base values final,
  sem_array_init_helper ge m block base values Utype final -> final = m.
Proof.
  intros ge m block base values final Hinit. remember Utype as ty eqn:Hty.
  induction Hinit; subst; auto.
  exfalso. eapply unit_full_assignment_impossible; eauto.
Qed.

Lemma unit_array_paths : forall env len attr delta ty,
  object_path env (Atype Utype len attr) delta ty ->
  delta = 0 /\ (ty = Atype Utype len attr \/ ty = Utype).
Proof.
  intros env len attr delta ty Hpath. induction Hpath.
  - auto.
  - destruct IHHpath as [_ [Hbad | Hbad]]; discriminate Hbad.
  - destruct IHHpath as [Hbase [Hparent | Hbad]]; [|discriminate Hbad].
    inversion Hparent; subst. split; [simpl; lia | auto].
Qed.

Lemma unit_array_no_scalar_leaf : forall env len attr delta ty chunk,
  ~ scalar_object_leaf env (Atype Utype len attr) delta ty chunk.
Proof.
  intros env len attr delta ty chunk [Hpath Hmode].
  destruct (unit_array_paths _ _ _ _ _ Hpath) as [_ [Hty | Hty]]; subst ty; discriminate Hmode.
Qed.

Theorem unit_array_initialization_total : forall ge Sigma vm m arr attr values,
  Forall (fun v => v = Vunit) values ->
  exists allocated block,
    Mem.alloc m 0 0 = (allocated, block) /\
    sem_array_init ge Sigma arr (Atype Utype (Z.of_nat (length values)) attr) values vm m
      (PTree.set arr (block, Atype Utype (Z.of_nat (length values)) attr) vm) allocated
      (PTree.set block (Atype Utype (Z.of_nat (length values)) attr) Sigma) /\
    aggregate_readable ge.(genv_cenv) allocated block Ptrofs.zero
      (Atype Utype (Z.of_nat (length values)) attr).
Proof.
  intros ge Sigma vm m arr attr values Hvalues.
  destruct (Mem.alloc m 0 0) as [allocated block] eqn:Halloc.
  exists allocated, block. split; [reflexivity |]. split.
  - eapply sem_allocate_array with (aty := Utype) (loc := block).
    + eapply alloc_variables_con.
      * unfold balloc. simpl. rewrite Halloc. reflexivity.
      * constructor.
    + apply PTree.gss.
    + reflexivity.
    + reflexivity.
    + apply unit_array_elements_initialize; exact Hvalues.
  - eapply fresh_aggregate_readable; [reflexivity | | exact Halloc].
    change (0 <= 0 <= Ptrofs.modulus). pose proof Ptrofs.modulus_pos; lia.
Qed.

Theorem unit_array_read_progress : forall ge p vm m block base len attr index,
  (index < Z.to_nat len)%nat ->
  aggregate_readable ge.(genv_cenv) m block base (Atype Utype len attr) ->
  ssem_expr ge p vm m
    (Prim (ArrayRead index) [Val (Vloc block base) (Atype Utype len attr)] Utype)
    m vm (Val Vunit Utype).
Proof. intros; apply ssem_array_read_unit; assumption. Qed.

Theorem unit_array_read_preservation : forall ge p vm m block base len attr index final vm' e',
  ssem_expr ge p vm m
    (Prim (ArrayRead index) [Val (Vloc block base) (Atype Utype len attr)] Utype) final vm' e' ->
  final = m /\ vm' = vm /\ e' = Val Vunit Utype.
Proof.
  intros ge p vm m block base len attr index final vm' e' Hstep.
  inversion Hstep; subst.
  - exfalso; eapply value_has_no_small_step; eauto.
  - exfalso; eapply unit_full_deref_impossible; eauto.
  - match goal with H : aggregate_readable _ _ _ _ Utype |- _ =>
      destruct H as [Hbad _]; discriminate Hbad end.
  - repeat split; reflexivity.
Qed.

Theorem allocated_unit_pair_executes : forall ge p vm arr,
  exists allocated block,
    Mem.alloc Mem.empty 0 0 = (allocated, block) /\
    ssem_expr ge p vm Mem.empty
      (Ainit arr (Atype Utype 2 noattr) [Val Vunit Utype; Val Vunit Utype] (Atype Utype 2 noattr))
      allocated vm (Val (Vloc block Ptrofs.zero) (Atype Utype 2 noattr)) /\
    ssem_expr ge p vm allocated
      (Prim (ArrayRead 1) [Val (Vloc block Ptrofs.zero) (Atype Utype 2 noattr)] Utype)
      allocated vm (Val Vunit Utype) /\
    ssem_expr ge p (PTree.set arr (block, Atype Utype 2 noattr) vm) allocated
      (Aaccess arr (Atype Utype 2 noattr) 1 Utype)
      allocated (PTree.set arr (block, Atype Utype 2 noattr) vm) (Val Vunit Utype) /\
    bsem_expr ge p vm Mem.empty
      (Prim (ArrayRead 1)
        [Ainit arr (Atype Utype 2 noattr) [Val Vunit Utype; Val Vunit Utype] (Atype Utype 2 noattr)] Utype)
      allocated vm Vunit.
Proof.
  intros ge p vm arr.
  destruct (unit_array_initialization_total ge empty_stcontext vm Mem.empty arr noattr [Vunit; Vunit]
    ltac:(repeat constructor)) as [allocated [block [Halloc [Hinit Hreadable]]]].
  exists allocated, block. split; [exact Halloc |]. split.
  - eapply ssem_array_init3 with (Sigma := empty_stcontext).
    + repeat constructor; eauto.
    + exact Hinit.
    + apply PTree.gss.
  - split.
    + apply ssem_array_read_unit; [change (1 < 2)%nat; lia | exact Hreadable].
    + split.
      * eapply ssem_array_access_unit; [apply PTree.gss | change (1 < 2)%nat; lia | exact Hreadable].
      * eapply bsem_array_read_unit.
        -- eapply bsem_ainit with (Sigma := empty_stcontext).
           ++ eapply bsem_cons; [apply bsem_value; constructor |].
              eapply bsem_cons; [apply bsem_value; constructor | constructor].
           ++ exact Hinit.
           ++ apply PTree.gss.
        -- reflexivity.
        -- change (1 < 2)%nat; lia.
        -- exact Hreadable.
Qed.

Example unit_pair_initializer_typed : forall env Gamma Sigma arr,
  type_expr env Gamma Sigma
    (Ainit arr (Atype Utype 2 noattr) [Val Vunit Utype; Val Vunit Utype] (Atype Utype 2 noattr))
    nil (Atype Utype 2 noattr).
Proof.
  intros. eapply ty_ainit with (aty := Utype) (ts := [Utype; Utype]).
  - eapply ty_cons with (ef := nil) (efs := nil); [constructor |].
    eapply ty_cons with (ef := nil) (efs := nil); constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists noattr; reflexivity.
  - reflexivity.
  - apply storage_array_admissible; [reflexivity | lia | apply storage_unit_admissible].
Qed.
Print Assumptions unit_array_initialization_total.
Print Assumptions unit_array_read_preservation.
Print Assumptions allocated_unit_pair_executes.


(* Shape-only well-formedness does not manufacture object ancestry or bounds:
   ty_valarray supplies ancestry and each array read checks its own access. *)
Lemma typed_array_value_well_formed : forall env Gamma Sigma v elem len attr ef,
  type_expr env Gamma Sigma (Val v (Atype elem len attr)) ef (Atype elem len attr) ->
  well_formed_value v (Atype elem len attr).
Proof. intros env Gamma Sigma v elem len attr ef Htyped; inversion Htyped; subst; constructor. Qed.

Lemma typed_value_bigstep : forall ge p vm m Gamma Sigma v ty ef,
  type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) ef ty ->
  bsem_expr ge p vm m (Val v ty) m vm v.
Proof.
  intros. apply bsem_value. eapply typed_well_formed_value; eauto.
Qed.

Theorem allocated_unit_array_value_bigstep : forall ge p vm (arr : ident),
  exists allocated block,
    Mem.alloc Mem.empty 0 0 = (allocated, block) /\
    type_expr ge.(genv_cenv) empty_context
      (PTree.set block (Atype Utype 2 noattr) empty_stcontext)
      (Val (Vloc block Ptrofs.zero) (Atype Utype 2 noattr)) nil (Atype Utype 2 noattr) /\
    bsem_expr ge p vm allocated
      (Prim (ArrayRead 1) [Val (Vloc block Ptrofs.zero) (Atype Utype 2 noattr)] Utype)
      allocated vm Vunit.
Proof.
  intros ge p vm arr.
  destruct (unit_array_initialization_total ge empty_stcontext vm Mem.empty arr noattr [Vunit; Vunit]
    ltac:(repeat constructor)) as [allocated [block [Halloc [Hinit Hreadable]]]].
  exists allocated, block. split; [exact Halloc |]. split.
  - apply ty_valarray_root; [apply PTree.gss | simpl; lia].
  - eapply bsem_array_read_unit.
    + apply bsem_value; apply wf_varray.
    + reflexivity.
    + change (1 < 2)%nat; lia.
    + exact Hreadable.
Qed.
Print Assumptions typed_array_value_well_formed.
Print Assumptions allocated_unit_array_value_bigstep.

Print Assumptions typed_value_bigstep.

Print Assumptions typed_well_formed_value.
