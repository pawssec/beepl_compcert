(* Aggregate descriptors certify identity and readable extent. They do not
   certify initialized fields; that is a separate scalar/object layout duty.
   In particular, descriptors are not inferred from arbitrary Sigma entries:
   Sigma also contains reference-typed parameter slots. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_callable_locations.

Definition aggregate_object_context := Values.block -> ptrofs -> type -> Prop.

Record aggregate_objects_valid (cenv : bcomposite_env) (Sigma : store_context)
    (m : Mem.mem) (objects : aggregate_object_context) : Prop := {
  aggregate_object_typing : forall b base ty, objects b base ty ->
    object_type_at cenv Sigma b (Ptrofs.unsigned base) ty;
  aggregate_object_readable : forall b base ty, objects b base ty ->
    aggregate_readable cenv m b base ty;
  (* Source allocations have representable extents; retaining this bound for
     their subobjects also makes the address of an empty trailing field valid. *)
  aggregate_object_address_bound : forall b base ty, objects b base ty ->
    (Ptrofs.unsigned base + sizeof_type cenv ty <= Ptrofs.max_unsigned)%Z
}.

Definition aggregate_descriptor_locations (objects : aggregate_object_context)
    : location_context :=
  fun b base ty =>
    (is_aggregate_type ty = true /\ objects b base ty) \/
    (exists basic attr, ty = Ptrtype (Reftype basic attr) /\
      is_aggregate_type (construct_type_btype basic) = true /\
      objects b base (construct_type_btype basic)).

Definition descriptor_heap_locations (bge : genv) (cells : scalar_layout)
    (objects : aggregate_object_context) : location_context :=
  fun b base ty => callable_heap_locations bge cells b base ty \/
    aggregate_descriptor_locations objects b base ty.

Lemma aggregate_descriptor_direct : forall bge cells objects b base ty,
  is_aggregate_type ty = true -> objects b base ty ->
  descriptor_heap_locations bge cells objects b base ty.
Proof. intros. right; left; auto. Qed.

Lemma aggregate_descriptor_reference : forall bge cells objects b base basic attr,
  is_aggregate_type (construct_type_btype basic) = true ->
  objects b base (construct_type_btype basic) ->
  descriptor_heap_locations bge cells objects b base (Ptrtype (Reftype basic attr)).
Proof. intros. right; right. exists basic, attr. auto. Qed.

Lemma callable_descriptor_embedding : forall bge cells objects,
  location_context_includes (callable_heap_locations bge cells)
    (descriptor_heap_locations bge cells objects).
Proof. intros bge cells objects b base ty H; left; exact H. Qed.

Lemma descriptor_heap_locations_monotone : forall bge cells cells' objects objects',
  (forall b base ty chunk, cells b base ty chunk -> cells' b base ty chunk) ->
  (forall b base ty, objects b base ty -> objects' b base ty) ->
  location_context_includes (descriptor_heap_locations bge cells objects)
    (descriptor_heap_locations bge cells' objects').
Proof.
  intros bge cells cells' objects objects' Hcells Hobjects b base ty [Hcall | Hobject].
  - left. eapply callable_heap_locations_monotone; eauto.
  - right. destruct Hobject as [[Hkind Hentry] | [basic [attr [Hty [Hkind Hentry]]]]].
    + left. split; [exact Hkind | eauto].
    + right. exists basic, attr. split; [exact Hty |]. split; [exact Hkind | eauto].
Qed.

Lemma aggregate_readable_memory_frame : forall cenv m m' b base ty,
  aggregate_readable cenv m b base ty ->
  (forall block, Mem.valid_block m block -> Mem.valid_block m' block) ->
  (forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p) ->
  aggregate_readable cenv m' b base ty.
Proof.
  intros cenv m m' b base ty [Hkind [Hsize [Hbound [Hblock Hrange]]]] Hblocks Hperms.
  split; [exact Hkind |]. split; [exact Hsize |]. split; [exact Hbound |].
  split; [apply Hblocks; exact Hblock |]. intros ofs Hwithin. apply Hperms.
  apply Hrange; exact Hwithin.
Qed.

Lemma aggregate_objects_valid_frame : forall cenv Sigma Sigma' m m' objects,
  aggregate_objects_valid cenv Sigma m objects -> store_context_extends Sigma Sigma' ->
  (forall block, Mem.valid_block m block -> Mem.valid_block m' block) ->
  (forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p) ->
  aggregate_objects_valid cenv Sigma' m' objects.
Proof.
  intros cenv Sigma Sigma' m m' objects [Htyping Hreadable Haddress] Hext Hblocks Hperms.
  constructor; intros b base ty Hentry.
  - eapply object_type_at_store_extension; eauto.
  - eapply aggregate_readable_memory_frame; eauto.
  - eapply Haddress; exact Hentry.
Qed.

Lemma aggregate_objects_valid_store : forall cenv Sigma m m' objects chunk b ofs v,
  aggregate_objects_valid cenv Sigma m objects ->
  Mem.store chunk m b ofs v = Some m' ->
  aggregate_objects_valid cenv Sigma m' objects.
Proof.
  intros. eapply aggregate_objects_valid_frame; [eassumption | | |].
  - intros block ty Hget; exact Hget.
  - intros. eapply Mem.store_valid_block_1; eauto.
  - intros. eapply Mem.perm_store_1; eauto.
Qed.

Lemma aggregate_objects_valid_storebytes : forall cenv Sigma m m' objects b ofs bytes,
  aggregate_objects_valid cenv Sigma m objects ->
  Mem.storebytes m b ofs bytes = Some m' ->
  aggregate_objects_valid cenv Sigma m' objects.
Proof.
  intros. eapply aggregate_objects_valid_frame; [eassumption | | |].
  - intros block ty Hget; exact Hget.
  - intros. eapply Mem.storebytes_valid_block_1; eauto.
  - intros. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma fresh_aggregate_readable : forall cenv m allocated b ty,
  is_aggregate_type ty = true ->
  (0 <= sizeof_type cenv ty <= Ptrofs.modulus)%Z ->
  Mem.alloc m 0 (sizeof_type cenv ty) = (allocated, b) ->
  aggregate_readable cenv allocated b Ptrofs.zero ty.
Proof.
  intros cenv m allocated b ty Hkind [Hsize Hbound] Halloc.
  unfold aggregate_readable. rewrite Ptrofs.unsigned_zero.
  split; [exact Hkind |]. split; [exact Hsize |]. split; [lia |].
  split; [eapply Mem.valid_new_block; eauto |]. intros ofs Hwithin.
  eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto | constructor].
Qed.

Print Assumptions aggregate_objects_valid_frame.
Print Assumptions fresh_aggregate_readable.

Require Import BeePL_soundness_fields.

Lemma aggregate_field_descriptor_readable :
  forall cenv m b base base_type field ty result,
  aggregate_field_access cenv m b base base_type field ty result ->
  is_aggregate_type ty = true -> aggregate_readable cenv m b result ty.
Proof.
  intros cenv m b base base_type field ty result Haccess Hkind.
  inversion Haccess; subst. unfold aggregate_readable.
  rewrite Ptrofs.unsigned_repr.
  - split; [exact Hkind |]. split; [assumption |]. split.
    + unfold Ptrofs.max_unsigned in *. lia.
    + split; assumption.
  - pose proof (Ptrofs.unsigned_range base). lia.
Qed.

Definition add_aggregate_descriptor (objects : aggregate_object_context)
    (block : Values.block) (base : ptrofs) (ty : type) : aggregate_object_context :=
  fun b ofs t => objects b ofs t \/ (b = block /\ ofs = base /\ t = ty).

Theorem aggregate_objects_valid_field_extension :
  forall cenv Sigma m objects b base base_type field ty result,
  aggregate_objects_valid cenv Sigma m objects ->
  aggregate_field_access cenv m b base base_type field ty result ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    objects b base (Stype sid attr)) ->
  is_aggregate_type ty = true ->
  aggregate_objects_valid cenv Sigma m (add_aggregate_descriptor objects b result ty).
Proof.
  intros cenv Sigma m objects b base base_type field ty result
    [Htyping Hreadable Haddress] Haccess Hbase Hkind.
  constructor; intros block ofs t [Hold | [Hb [Hofs Hty]]].
  - apply Htyping; exact Hold.
  - subst block ofs t. eapply aggregate_field_access_layout; [exact Haccess |].
    intros sid attr Hshape. apply Htyping. apply Hbase; exact Hshape.
  - apply Hreadable; exact Hold.
  - subst block ofs t. eapply aggregate_field_descriptor_readable; eauto.
  - eapply Haddress; exact Hold.
  - subst block ofs t. inversion Haccess; subst.
    rewrite Ptrofs.unsigned_repr; [assumption|].
    pose proof (Ptrofs.unsigned_range base). lia.
Qed.

Print Assumptions aggregate_objects_valid_field_extension.
