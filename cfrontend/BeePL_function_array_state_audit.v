(* A heap can contain a direct-function array descriptor with no scalar leaves.
   Its unsupported read operation must be rejected by the typing rules;
   initialized heap coverage alone does not make this read executable. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_typechecker Errors Bool.
Require Import BeePL_function_array_audit BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_object_paths BeePL_aggregate_memory BeePL_object_coverage.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_bindings BeePL_heap_extents BeePL_block_extents.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_layout_coherence.
Import ListNotations.
Local Open Scope Z_scope.

Definition forged_function_array_objects (b : Values.block) : aggregate_object_context :=
  fun block base ty => block=b /\ base=Ptrofs.zero /\ ty=function_array_type.
Definition forged_function_array_read (b : Values.block) : expr :=
  Prim (ArrayRead 0) [Val(Vloc b Ptrofs.zero)function_array_type] function_array_element_type.

Lemma function_array_path_types : forall env delta ty,
  object_path env function_array_type delta ty -> ty=function_array_type \/ ty=function_array_element_type.
Proof.
  intros env delta ty Hpath. remember function_array_type as root eqn:Hroot.
  induction Hpath.
  - left; auto.
  - rewrite Hroot in IHHpath. destruct IHHpath; discriminate.
  - rewrite Hroot in IHHpath. destruct IHHpath as [Hparent|Hparent]; [|discriminate].
    unfold function_array_type in Hparent. inversion Hparent; subst. right; reflexivity.
Qed.

Lemma function_array_read_stuck : forall ge p vm m b final vm' next,
  ~ ssem_expr ge p vm m (forged_function_array_read b) final vm' next.
Proof.
  intros * Hstep. unfold forged_function_array_read in Hstep. inversion Hstep; subst.
  - eapply value_has_no_small_step; eauto.
  - match goal with Hr : deref_addr _ _ _ _ Full _ |- _ => inversion Hr; subst; discriminate end.
  - match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _]; discriminate end.
Qed.

Theorem forged_function_array_heap_admissible : forall ge p,
  exists m b Sigma,
    Mem.alloc Mem.empty 0 1=(m,b) /\
    initialized_heap_state ge empty_context Sigma empty_vmap m
      (forged_function_array_objects b) function_array_no_cells (fun _ _=>False) /\
    forall final vm' next, ~ssem_expr ge p empty_vmap m (forged_function_array_read b) final vm' next.
Proof.
  intros ge p. destruct(Mem.alloc Mem.empty 0 1) as [m b] eqn:Ha.
  set(Sigma:=PTree.set b function_array_type empty_stcontext).
  assert(Hextent:source_block_extent m b 1).
  { eapply allocated_source_block_extent; [exact Ha|]. unfold Ptrofs.max_unsigned,Ptrofs.modulus,Ptrofs.wordsize;
    destruct Archi.ptr64; vm_compute; split; congruence. }
  assert(Hroot:object_type_at ge.(genv_cenv) Sigma b 0 function_array_type).
  { change(object_type_at ge.(genv_cenv) Sigma b 0(stored_object_type function_array_type)).
    apply object_type_root; [apply PTree.gss|simpl; lia]. }
  assert(Hobjects:aggregate_objects_valid ge.(genv_cenv) Sigma m(forged_function_array_objects b)).
  { constructor; intros block base ty [Hb [Hbase Hty]]; subst block base ty.
    - rewrite Ptrofs.unsigned_zero; exact Hroot.
    - unfold aggregate_readable,function_array_type,function_array_element_type. rewrite Ptrofs.unsigned_zero.
      simpl. pose proof(source_extent_bound _ _ _ Hextent). unfold Ptrofs.max_unsigned in H.
      repeat split; try lia; [exact(source_extent_valid _ _ _ Hextent)|].
      intros ofs Hi. eapply Mem.perm_implies; [apply(source_extent_freeable _ _ _ Hextent); exact Hi|constructor].
    - rewrite Ptrofs.unsigned_zero. change(1<=Ptrofs.max_unsigned). exact(proj2(source_extent_bound _ _ _ Hextent)). }
  assert(Hmemory:initialized_object_memory ge Sigma m(forged_function_array_objects b) function_array_no_cells).
  { constructor.
    - exact Hobjects.
    - intros block base root [Hb [Hbase Hrootty]] delta ty chunk [Hpath Hmode]. subst root.
      destruct(function_array_path_types _ _ _ Hpath); subst ty; discriminate.
    - intros block ofs ty chunk Hfalse; contradiction.
    - intros block ofs ty chunk Hfalse; contradiction.
    - intros block base root Hobj delta child Hpath other ofs ty chunk Hfalse; contradiction. }
  assert(Hblocks:store_blocks_valid Sigma m).
  { intros block ty Hget. unfold Sigma in Hget. rewrite PTree.gsspec in Hget.
    destruct(peq block b); [subst block; exact(source_extent_valid _ _ _ Hextent)|].
    rewrite PTree.gempty in Hget; discriminate. }
  assert(Hpackets:packet_heap_invariant ge Sigma m(forged_function_array_objects b)function_array_no_cells(fun _ _=>False)).
  { constructor.
    - intros block base Hfalse; contradiction.
    - intros block base Hfalse; contradiction.
    - intros block base root [Hb [Hbase Hrootty]] delta Hpath. subst root.
      destruct(function_array_path_types _ _ _ Hpath); discriminate.
    - intros block ofs ty chunk Hfalse; contradiction.
    - intros block base root Hobj delta child Hpath descriptor ofs Hfalse; contradiction. }
  assert(Hextents:heap_block_extents Sigma m(forged_function_array_objects b)function_array_no_cells(fun _ _=>False)).
  { exists(PTree.set b 1(PTree.empty Z)). split.
    - intros block limit Hget. rewrite PTree.gsspec in Hget. destruct(peq block b).
      + subst block; inversion Hget; subst limit; exact Hextent.
      + rewrite PTree.gempty in Hget; discriminate.
    - intros block [[ty [Hget Hnonfun]]|[[ofs [ty [chunk Hfalse]]]|[[base [ty [Hb Hrest]]]|[base Hfalse]]]].
      + unfold Sigma in Hget. rewrite PTree.gsspec in Hget. destruct(peq block b).
        * subst block; exists 1; apply PTree.gss.
        * rewrite PTree.gempty in Hget; discriminate.
      + contradiction.
      + subst block; exists 1; apply PTree.gss.
      + contradiction. }
  exists m,b,Sigma. split; [reflexivity|]. split; [|intros; apply function_array_read_stuck].
  constructor; try assumption.
  intros x ty Hget; rewrite PTree.gempty in Hget; discriminate.
Qed.

Theorem forged_function_array_read_rejected : forall env Gamma Sigma b ef ty,
  ~ type_expr env Gamma Sigma (forged_function_array_read b) ef ty.
Proof.
  intros * Htyped. unfold forged_function_array_read in Htyped.
  inversion Htyped; subst; discriminate.
Qed.

Theorem function_array_named_access_rejected : forall env Gamma Sigma arr ef ty,
  ~ type_expr env Gamma Sigma
      (Aaccess arr function_array_type 0 function_array_element_type) ef ty.
Proof.
  intros * Htyped. inversion Htyped; subst; discriminate.
Qed.

Print Assumptions forged_function_array_heap_admissible.
Print Assumptions forged_function_array_read_rejected.
Print Assumptions function_array_named_access_rejected.

Theorem function_array_read_checker_rejected : forall env Gamma Sigma b,
  exists error, type_check_expr env Gamma Sigma (forged_function_array_read b) = Error error.
Proof.
  intros. unfold forged_function_array_read, function_array_type, function_array_element_type.
  cbn [type_check_expr].
  destruct (BeePL_value_checker.value_type_check env Sigma (Vloc b Ptrofs.zero)
    (Atype (Ftype [] [] Utype false) 1 noattr)); eexists; reflexivity.
Qed.

Theorem function_array_named_checker_rejected : forall env Gamma Sigma arr,
  exists error, type_check_expr env Gamma Sigma
    (Aaccess arr function_array_type 0 function_array_element_type) = Error error.
Proof.
  intros. unfold function_array_type, function_array_element_type.
  cbn [type_check_expr]. destruct (Gamma!arr) as [declared|]; [|eexists; reflexivity].
  rewrite andb_false_r. eexists; reflexivity.
Qed.

Print Assumptions function_array_read_checker_rejected.
Print Assumptions function_array_named_checker_rejected.
