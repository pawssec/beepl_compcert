(* Source regression: copying an initialized unit array into an outer array
   uses zero bytes, exactly its allocated source extent. C's Tarray Tvoid
   representation still has nonzero size; no compiler ABI equivalence is
   claimed by these operational source proofs. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_storage_types.
Require Import BeePL_unit_arrays BeePL_aggregate_copy BeePL_fresh_aggregate_memory.
Import ListNotations.
Local Open Scope Z_scope.

Definition nested_unit_inner := Atype Utype 2 noattr.
Definition nested_unit_outer := Atype nested_unit_inner 1 noattr.
Definition nested_unit_inner_expression name :=
  Ainit name nested_unit_inner [Val Vunit Utype; Val Vunit Utype] nested_unit_inner.
Definition nested_unit_expression outer inner :=
  Ainit outer nested_unit_outer [nested_unit_inner_expression inner] nested_unit_outer.

Example nested_unit_source_and_c_sizes_differ : forall env,
  sizeof_type env nested_unit_inner = 0 /\
  Ctypes.sizeof (bcomposite_composite_env env) (transBeePL_type nested_unit_inner) = 2.
Proof. intros; split; reflexivity. Qed.

Example nested_unit_initializer_typed : forall env Gamma Sigma outer inner,
  type_expr env Gamma Sigma (nested_unit_expression outer inner) [] nested_unit_outer.
Proof.
  intros. unfold nested_unit_expression.
  eapply ty_ainit with (aty := nested_unit_inner) (ts := [nested_unit_inner]).
  - eapply ty_cons with (ef := []) (efs := []); [apply unit_pair_initializer_typed|constructor].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists noattr; reflexivity.
  - reflexivity.
  - apply storage_array_admissible; [reflexivity|lia|].
    apply storage_array_admissible; [reflexivity|lia|apply storage_unit_admissible].
Qed.

Theorem zero_sized_aggregate_assignment_writes_empty : forall ge m ty src source dst target final,
  is_aggregate_type ty = true -> sizeof_type ge.(genv_cenv) ty = 0 ->
  assign_addr ge ty m dst target Full (Vloc src source) final (Vloc src source) ->
  Mem.storebytes m dst (Ptrofs.unsigned target) [] = Some final.
Proof.
  intros ge m ty src source dst target final Hkind Hsize Hassign.
  destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign) as [bytes [Hbytes Hstore]].
  unfold aggregate_copy_size in Hbytes. rewrite Hsize in Hbytes.
  rewrite Mem.loadbytes_empty in Hbytes by lia. inversion Hbytes; subst; exact Hstore.
Qed.

Theorem nested_unit_initializer_executes : forall ge p vm outer inner,
  exists innerMemory source allocated destination final,
    Mem.alloc Mem.empty 0 0 = (innerMemory, source) /\
    Mem.alloc innerMemory 0 0 = (allocated, destination) /\
    ssem_expr ge p vm Mem.empty (nested_unit_expression outer inner)
      innerMemory vm
      (Ainit outer nested_unit_outer [Val (Vloc source Ptrofs.zero) nested_unit_inner] nested_unit_outer) /\
    ssem_expr ge p vm innerMemory
      (Ainit outer nested_unit_outer [Val (Vloc source Ptrofs.zero) nested_unit_inner] nested_unit_outer)
      final vm (Val (Vloc destination Ptrofs.zero) nested_unit_outer) /\
    Mem.storebytes allocated destination 0 [] = Some final.
Proof.
  intros ge p vm outer inner.
  destruct (unit_array_initialization_total ge empty_stcontext vm Mem.empty inner noattr [Vunit; Vunit]
    ltac:(repeat constructor)) as [innerMemory [source [HinnerAlloc [HinnerInit Hreadable]]]].
  destruct (Mem.alloc innerMemory 0 0) as [allocated destination] eqn:HouterAlloc.
  assert (Hready : aggregate_copy_ready ge allocated nested_unit_inner source Ptrofs.zero destination Ptrofs.zero).
  { eapply fresh_aggregate_copy_ready; [exact HouterAlloc|exact Hreadable|].
    rewrite Ptrofs.unsigned_zero. exists 0; lia. }
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hready) as [final Hassign].
  assert (HouterInit : sem_array_init ge empty_stcontext outer nested_unit_outer
    [Vloc source Ptrofs.zero] vm innerMemory (PTree.set outer (destination, nested_unit_outer) vm) final
    (PTree.set destination nested_unit_outer empty_stcontext)).
  { eapply sem_allocate_array with (aty := nested_unit_inner) (len := 1) (a := noattr)
      (loc := destination) (m' := allocated).
    - eapply alloc_variables_con.
      + unfold balloc. cbn [sizeof_type nested_unit_outer nested_unit_inner]. simpl.
        rewrite HouterAlloc; reflexivity.
      + constructor.
    - apply PTree.gss.
    - reflexivity.
    - reflexivity.
    - eapply sem_allocate_array_elm; [exact Hassign|constructor]. }
  exists innerMemory, source, allocated, destination, final.
  split; [exact HinnerAlloc|]. split; [exact HouterAlloc|]. split.
  - apply ssem_array_init1. eapply ssem_array_init3 with (Sigma := empty_stcontext).
    + repeat constructor; eauto.
    + exact HinnerInit.
    + apply PTree.gss.
  - split.
    + eapply ssem_array_init3; [repeat constructor; eauto|exact HouterInit|apply PTree.gss].
    + rewrite <- Ptrofs.unsigned_zero.
      eapply zero_sized_aggregate_assignment_writes_empty with (ty := nested_unit_inner); [reflexivity|reflexivity|exact Hassign].
Qed.
Print Assumptions nested_unit_initializer_typed.
Print Assumptions zero_sized_aggregate_assignment_writes_empty.
Print Assumptions nested_unit_initializer_executes.
