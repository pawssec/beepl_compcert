(* The Bytes ABI follows from the intrinsic definition installed by the public
   composite builder. No arbitrary caller-supplied descriptor-layout premise
   is required. Pointer widths remain architecture-parametric. *)
Require Import List ZArith Lia Integers AST Maps Memory Memdata Ctypes Coqlib Errors.
Require Import BeeTypes BeePL BeePL_layout_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Definition intrinsic_bytes_members : list bmember :=
  [Member_plain bytes_start (Ptrtype (Reftype (Bprim (Tint I8 Unsigned noattr)) noattr));
   Member_plain bytes_end (Ptrtype (Reftype (Bprim (Tint I8 Unsigned noattr)) noattr))].

Definition intrinsic_bytes_initial_env : bcomposite_env :=
  match build_bcomposite_env [] with OK env => env | Error _ => PTree.empty _ end.

Lemma intrinsic_bytes_initial_layout : exists co,
  PTree.get bytes_t intrinsic_bytes_initial_env = Some co /\
  co.(BeeTypes.co_members) = intrinsic_bytes_members /\
  co.(BeeTypes.co_su) = Struct /\
  co.(BeeTypes.co_sizeof) = 2 * size_chunk Mptr /\
  co.(BeeTypes.co_alignof) = align_chunk Mptr.
Proof. eexists; repeat split; reflexivity. Qed.

Lemma built_bytes_initial_preserved : forall defs env name co,
  build_bcomposite_env defs = OK env ->
  PTree.get name intrinsic_bytes_initial_env = Some co -> PTree.get name env = Some co.
Proof.
  intros defs env name co Hbuild Hlookup.
  change (add_bcomposite_definitions intrinsic_bytes_initial_env defs = OK env) in Hbuild.
  eapply add_source_composites_preserves; eauto.
Qed.

Theorem built_bytes_layout : forall defs env,
  build_bcomposite_env defs = OK env -> exists co,
  PTree.get bytes_t env = Some co /\
  co.(BeeTypes.co_members) = intrinsic_bytes_members /\
  co.(BeeTypes.co_su) = Struct /\
  co.(BeeTypes.co_sizeof) = 2 * size_chunk Mptr /\
  co.(BeeTypes.co_alignof) = align_chunk Mptr.
Proof.
  intros defs env Hbuild.
  destruct intrinsic_bytes_initial_layout as [co [Hlookup Hlayout]].
  exists co. split; [eapply built_bytes_initial_preserved; eauto|exact Hlayout].
Qed.

Theorem built_bytes_c_size : forall defs env,
  build_bcomposite_env defs = OK env ->
  Ctypes.sizeof (bcomposite_composite_env env) (transBeePL_type Bytes) = 2 * size_chunk Mptr.
Proof.
  intros defs env Hbuild.
  destruct (built_bytes_layout _ _ Hbuild) as [co [Hlookup [Hmembers [Hstruct [Hsize Halign]]]]].
  simpl. rewrite translated_composite_lookup, Hlookup. exact Hsize.
Qed.

Theorem built_bytes_copy_alignment : forall defs env,
  build_bcomposite_env defs = OK env ->
  alignof_blockcopy (bcomposite_composite_env env) (transBeePL_type Bytes) = align_chunk Mptr.
Proof.
  intros defs env Hbuild.
  destruct (built_bytes_layout _ _ Hbuild) as [co [Hlookup [Hmembers [Hstruct [Hsize Halign]]]]].
  simpl. rewrite translated_composite_lookup, Hlookup. simpl.
  rewrite Halign. unfold Mptr. destruct Archi.ptr64; reflexivity.
Qed.

Theorem built_bytes_field_offsets : forall defs env co,
  build_bcomposite_env defs = OK env -> PTree.get bytes_t env = Some co ->
  field_offset (bcomposite_composite_env env) bytes_start
    (bmembers_cmembers (BeeTypes.co_members co)) = OK (0, Full) /\
  field_offset (bcomposite_composite_env env) bytes_end
    (bmembers_cmembers (BeeTypes.co_members co)) = OK (size_chunk Mptr, Full).
Proof.
  intros defs env co Hbuild Hlookup.
  destruct (built_bytes_layout _ _ Hbuild) as [intrinsic [Hget [Hmembers Hrest]]].
  assert (co = intrinsic) by congruence. subst co. rewrite Hmembers.
  unfold intrinsic_bytes_members. split; reflexivity.
Qed.

Corollary program_bytes_c_size : forall p,
  Ctypes.sizeof (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type Bytes) =
    2 * size_chunk Mptr.
Proof. intro p. eapply built_bytes_c_size; apply prog_comp_env_eq. Qed.

Corollary program_bytes_copy_alignment : forall p,
  alignof_blockcopy (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type Bytes) =
    align_chunk Mptr.
Proof. intro p. eapply built_bytes_copy_alignment; apply prog_comp_env_eq. Qed.

Corollary program_bytes_copy_pointer_alignment : forall p offset,
  (alignof_blockcopy (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type Bytes) | offset) <->
  (align_chunk Mptr | offset).
Proof. intros. rewrite program_bytes_copy_alignment. reflexivity. Qed.

Lemma bytes_second_pointer_alignment : forall offset,
  (align_chunk Mptr | offset) -> (align_chunk Mptr | offset + size_chunk Mptr).
Proof.
  intros offset H. apply Z.divide_add_r; [exact H|].
  unfold Mptr. destruct Archi.ptr64; simpl; apply Z.divide_refl.
Qed.

Print Assumptions built_bytes_layout.
Print Assumptions program_bytes_c_size.
Print Assumptions program_bytes_copy_alignment.
Print Assumptions built_bytes_field_offsets.
