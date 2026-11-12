Require Import BeePL_heap_extents.
(* Field layouts are derived from the actual checked program environment.
   Runtime coverage supplies initialized contents rather than an assumed
   successful read or a caller-selected field plan. *)
Require Import List Bool ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_type_equality BeePL_substitution_proofs BeePL_array_proofs.
Require Import BeePL_layout_proofs BeePL_bytes_layout BeePL_program_member_types.
Require Import BeePL_structure_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_fields.
Require Import BeePL_callable_locations BeePL_aggregate_memory BeePL_object_paths.
Require Import BeePL_object_coverage BeePL_covered_reads BeePL_fresh_copy.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap BeePL_packet_coverage.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Import ListNotations.
Local Open Scope Z_scope.

Definition union_field_audit_word : type := Vtype (Tint I32 Unsigned noattr).
Definition union_field_audit_members : list bmember :=
  [BeeTypes.Member_plain 7002%positive union_field_audit_word;
   BeeTypes.Member_plain 7003%positive union_field_audit_word].
Definition union_field_audit_definitions : list bcomposite_definition :=
  [Bcomposite 7001%positive Union union_field_audit_members noattr].

Lemma union_field_audit_builder_rejected :
  exists err, build_bcomposite_env union_field_audit_definitions = Error err.
Proof. vm_compute; eexists; reflexivity. Qed.

Lemma source_size_nonnegative : forall env ty, 0 <= sizeof_type env ty.
Proof.
  intros env ty. induction ty; simpl.
  - lia.
  - destruct p; try destruct i; simpl; lia.
  - destruct Archi.ptr64; lia.
  - destruct (PTree.get i env) as [co|]; [pose proof (co_sizeof_pos co)|]; lia.
  - apply Z.mul_nonneg_nonneg; [assumption|lia].
  - lia.
  - unfold Mptr; destruct Archi.ptr64; simpl; lia.
Qed.

Lemma source_pointer_c_size : forall env pt,
  Ctypes.sizeof env (transBeePL_ptr_type pt) = if Archi.ptr64 then 8 else 4.
Proof.
  intros env pt; induction pt as [bt a|pt IH|args effects result variadic]; simpl; auto.
  destruct bt as [pt|sid a'|pt len a']; try destruct pt; reflexivity.
Qed.

Lemma program_source_size_bound : forall p ty,
  sizeof_type p.(prog_comp_env) ty <=
  Ctypes.sizeof (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type ty).
Proof.
  intros p ty; induction ty; simpl.
  - lia.
  - destruct p0; try destruct i; simpl; lia.
  - rewrite source_pointer_c_size. lia.
  - rewrite translated_composite_lookup. destruct (PTree.get i (prog_comp_env p)); reflexivity.
  - apply Z.mul_le_mono_nonneg_r; [lia|assumption].
  - lia.
  - change (2 * size_chunk Mptr <= Ctypes.sizeof (bcomposite_composite_env (prog_comp_env p)) (transBeePL_type Bytes)).
    rewrite program_bytes_c_size; lia.
Qed.

Lemma located_structure_object : forall ge Sigma m objects cells packets b base sid attr receiver,
  initialized_object_memory ge Sigma m objects cells ->
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  packet_heap_locations ge cells objects packets b base receiver ->
  objects b base (Stype sid attr).
Proof.
  intros ge Sigma m objects cells packets b base sid attr receiver Hmemory Hreceiver Hlocation.
  destruct Hreceiver; subst receiver;
    apply packet_heap_locations_nonbytes in Hlocation; try discriminate;
    destruct Hlocation as [Hcall|[[Hkind Hobject]|[basic [pa [Htype [Hkind Hobject]]]]]].
  - destruct Hcall as [[pt [chunk [Hbad Hcell]]]|[elem [len [a [Hbad Hrest]]]]]; discriminate Hbad.
  - exact Hobject.
  - discriminate Htype.
  - destruct Hcall as [[pt [chunk [Htype Hcell]]]|[elem [len [a [Hbad Hrest]]]]]; [|discriminate Hbad].
    inversion Htype; subst. pose proof (typed_cell_access _ _ _ _ _ _ _
      (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode. discriminate Hmode.
  - discriminate Hkind.
  - inversion Htype; subst; exact Hobject.
Qed.

Lemma program_field_layout : forall p sid attr co field ty,
  PTree.get sid p.(prog_comp_env) = Some co ->
  source_member_type field co.(co_members) = OK ty ->
  exists delta,
    field_offset (bcomposite_composite_env p.(prog_comp_env)) field
      (bmembers_cmembers co.(co_members)) = OK (delta, Full) /\
    0 <= delta /\ 0 <= sizeof_type p.(prog_comp_env) ty /\
    delta + sizeof_type p.(prog_comp_env) ty <= sizeof_type p.(prog_comp_env) (Stype sid attr).
Proof.
  intros p sid attr co field ty Hco Hsource.
  pose proof (program_composite_shape p sid co Hco) as [Hstruct Hplain].
  assert (HplainC : plain_members (bmembers_cmembers co.(co_members))).
  { clear Hsource Hco. unfold plain_members. induction Hplain as [|member rest Hhead Htail IH]; simpl; constructor.
    - destruct member; simpl in Hhead; try contradiction. do 2 eexists; reflexivity.
    - exact IH. }
  pose proof (source_member_type_translation _ _ _ Hsource) as Hfield.
  destruct (plain_field_offset_exists (bcomposite_composite_env p.(prog_comp_env))
    (bmembers_cmembers co.(co_members)) field (transBeePL_type ty) HplainC Hfield 0) as [delta Hoffset].
  change (field_offset (bcomposite_composite_env p.(prog_comp_env)) field
    (bmembers_cmembers co.(co_members)) = OK (delta, Full)) in Hoffset.
  pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Hfield) as [Hlo Hhi].
  pose proof (consistent_struct_size_bound _ _ (program_composites_consistent p sid co Hco) Hstruct).
  pose proof (program_source_size_bound p ty).
  pose proof (source_size_nonnegative p.(prog_comp_env) ty).
  exists delta. split; [exact Hoffset|]. repeat split; try assumption.
  simpl. rewrite Hco. lia.
Qed.

Lemma typed_located_field_layout : forall ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef,
  ge.(genv_cenv) = p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Sfield (Val (Vloc b base) receiver) field ty) ef ty ->
  ef = nil /\ exists sid attr co ct delta,
    (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) /\
    objects b base (Stype sid attr) /\
    PTree.get sid ge.(genv_cenv) = Some co /\
    Ctyping.type_of_member attr field (bmembers_cmembers co.(co_members)) = OK ct /\
    source_member_type field co.(co_members) = OK ty /\
    field_offset (bcomposite_composite_env ge.(genv_cenv)) field
      (bmembers_cmembers co.(co_members)) = OK (delta, Full) /\
    object_path ge.(genv_cenv) (Stype sid attr) delta ty /\
    bcomplete_type ge.(genv_cenv) ty = true.
Proof.
  intros ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef Henv
    [[[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocated Hframes] Hcoherent].
  destruct (type_infer_sfield _ _ _ _ _ _ _ _ Htyped)
    as [_ [sid [attr [co [ct [te [Hoperand [Hreceiver [Hco [Hct Hsource]]]]]]]]]].
  pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hoperand) as Hef. subst ef.
  pose proof (typed_value_annotation _ _ _ _ _ _ _ Hoperand) as Heq. subst te.
  assert (Hreceiver' : receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)).
  { destruct Hreceiver; [left|right]; apply eq_type_sound; assumption. }
  pose proof (located_structure_object _ _ _ _ _ _ _ _ _ _ _ Hmemory Hreceiver' Hlocated) as Hobject.
  destruct (program_field_layout p sid attr co field ty ltac:(rewrite <- Henv; exact Hco) Hsource)
    as [delta [Hoffset [Hdelta [Hsize Hbound]]]]. rewrite <- Henv in Hoffset,Hsize,Hbound.
  split; [reflexivity|]. exists sid,attr,co,ct,delta. repeat split; try assumption.
  - replace delta with (0+delta) by lia. eapply path_field; eauto.
    constructor; apply source_size_nonnegative.
  - rewrite Henv. eapply program_source_member_complete; eauto. rewrite <- Henv; exact Hco.
Qed.

Lemma complete_field_runtime_kind : forall env ty,
  bcomplete_type env ty = true ->
  (exists chunk, access_mode_type ty = By_value (transl_bchunk_cchunk chunk)) \/
  is_aggregate_type ty = true \/ ty = Bytes.
Proof.
  intros env ty Hcomplete; destruct ty; try discriminate Hcomplete.
  - left; exists (chunk_of_ptype p); apply primitive_chunk_access.
  - left. exists (if Archi.ptr64 then BMint64 else BMint32).
    simpl. unfold Mptr. destruct Archi.ptr64; reflexivity.
  - right; left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.

Lemma covered_field_address : forall ge Sigma m objects cells b base root delta ty,
  initialized_object_memory ge Sigma m objects cells -> objects b base root ->
  object_path ge.(genv_cenv) root delta ty ->
  0 <= Ptrofs.unsigned base + delta <= Ptrofs.max_unsigned /\
  Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned base + delta)) = Ptrofs.unsigned base + delta /\
  Ptrofs.add base (Ptrofs.repr delta) = Ptrofs.repr (Ptrofs.unsigned base + delta).
Proof.
  intros ge Sigma m objects cells b base root delta ty Hmemory Hobject Hpath.
  pose proof (aggregate_object_address_bound _ _ _ _
    (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobject) as Hbound.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hd [Ht Hwithin]].
  pose proof (Ptrofs.unsigned_range base).
  split; [lia|]. split; [apply Ptrofs.unsigned_repr; lia|].
  unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr by lia; reflexivity.
Qed.

Lemma covered_aggregate_field_access : forall ge Sigma m objects cells b base sid attr receiver field ty co ct delta,
  initialized_object_memory ge Sigma m objects cells -> objects b base (Stype sid attr) ->
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  Ctyping.type_of_member attr field (bmembers_cmembers co.(co_members)) = OK ct ->
  source_member_type field co.(co_members) = OK ty ->
  field_offset (bcomposite_composite_env ge.(genv_cenv)) field (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  object_path ge.(genv_cenv) (Stype sid attr) delta ty ->
  (is_aggregate_type ty || is_bytes ty)%bool = true ->
  aggregate_field_access ge.(genv_cenv) m b base receiver field ty (Ptrofs.repr (Ptrofs.unsigned base + delta)).
Proof.
  intros ge Sigma m objects cells b base sid attr receiver field ty co ct delta
    Hmemory Hobject Hreceiver Hco Hct Hsource Hoffset Hpath Hkind.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hd [Ht Hwithin]].
  pose proof (aggregate_object_address_bound _ _ _ _
    (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobject) as Hbound.
  destruct (aggregate_object_readable _ _ _ _
    (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobject)
    as [_ [_ [_ [Hvalid Hread]]]].
  eapply aggregate_field_access_intro; eauto; try lia.
  intros offset Hin; apply Hread; lia.
Qed.

Lemma address_field_full_read : forall ty m b ofs v,
  (is_aggregate_type ty || is_bytes ty)%bool = true ->
  deref_addr ty m b ofs Full v -> v = Vloc b ofs.
Proof.
  intros ty m b ofs v Hkind Hread. inversion Hread; subst; try reflexivity;
    destruct ty; simpl in Hkind; try discriminate;
    match goal with Hmode : access_mode_type _ = _ |- _ => discriminate Hmode end.
Qed.

Lemma address_field_step_exact : forall ge p vm m b base sid attr receiver field ty co delta final vm' e',
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env ge.(genv_cenv)) field (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  (is_aggregate_type ty || is_bytes ty)%bool = true ->
  Ptrofs.add base (Ptrofs.repr delta) = Ptrofs.repr (Ptrofs.unsigned base + delta) ->
  ssem_expr ge p vm m (Sfield (Val (Vloc b base) receiver) field ty) final vm' e' ->
  final=m /\ vm'=vm /\ e'=Val (Vloc b (Ptrofs.repr (Ptrofs.unsigned base+delta))) ty.
Proof.
  intros ge p vm m b base sid attr receiver field ty co delta final vm' e'
    Hreceiver Hco Hoffset Hkind Hadd Hstep.
  destruct Hreceiver; subst receiver; inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: try match goal with Hr : deref_addr _ _ _ _ _ _ |- _ =>
    assert (co0=co) by congruence; subst co0;
    assert (Hd : delta0=delta /\ bf=Full) by (split; congruence);
    destruct Hd; subst delta0 bf;
    pose proof (address_field_full_read _ _ _ _ _ Hkind Hr) as Hv;
    subst; rewrite Hadd; repeat split end.
  all: match goal with Ha : aggregate_field_access _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  all: match goal with Hshape : _ = Stype _ _ \/ _ = Ptrtype _ |- _ =>
    destruct Hshape as [Hshape|Hshape]; inversion Hshape; subst end.
  all: match goal with Ha : PTree.get ?id ?env = Some ?a, Hb : PTree.get ?id ?env = Some ?c |- _ =>
    assert (a=c) by congruence; subst end.
  all: match goal with Ha : field_offset _ _ _ = OK (?d, Full), Hb : field_offset _ _ _ = OK (?d', Full) |- _ =>
    assert (d=d') by congruence; subst end.
  all: repeat split.
Qed.

Require Import BeePL_aggregate_dereference BeePL_packet_object_layout.

Lemma initialized_heap_register_subobject : forall ge Gamma Sigma vm m objects cells packets b base root delta ty result,
  initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  objects b base root -> object_path ge.(genv_cenv) root delta ty ->
  is_aggregate_type ty = true -> Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  initialized_heap_state ge Gamma Sigma vm m (add_aggregate_descriptor objects b result ty) cells packets /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma m
    (add_aggregate_descriptor objects b result ty) cells packets.
Proof.
  intros ge Gamma Sigma vm m objects cells packets b base root delta ty result
    [Hblocks Hmemory Hbindings Hpacket Hextents] Hobject Hpath Hkind Hresult.
  assert (Hmemory' : initialized_object_memory ge Sigma m (add_aggregate_descriptor objects b result ty) cells).
  { eapply initialized_object_subobject_extension; eauto. }
  assert (Hpacket' : packet_heap_invariant ge Sigma m (add_aggregate_descriptor objects b result ty) cells packets).
  { destruct Hpacket as [Hv Ht Hcoverage Hseparation Hcoherence]. constructor; try assumption.
    - eapply packet_coverage_subobject_extension; eauto.
    - eapply packet_object_coherence_subobject_extension; eauto. }
  assert (Hextents' : heap_block_extents Sigma m (add_aggregate_descriptor objects b result ty) cells packets).
  { eapply heap_extents_add_object; [exact Hextents|].
    right; right; left. exists base, root; exact Hobject. }
  split.
  - constructor; try assumption. eapply packet_variable_layout_extend with
      (Sigma:=Sigma) (cells:=cells) (objects:=objects) (packets:=packets);
      eauto using store_context_extends_refl. intros; left; assumption.
  - constructor; auto using store_context_extends_refl. intros; left; assumption.
Qed.

Theorem coherent_field_read_progress : forall ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef,
  ge.(genv_cenv) = p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Sfield (Val (Vloc b base) receiver) field ty) ef ty ->
  exists objects' v,
    ssem_expr ge p vm m (Sfield (Val (Vloc b base) receiver) field ty) m vm (Val v ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects' cells packets (Val v ty) nil ty.
Proof.
  intros ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef Henv Hconfig.
  destruct (typed_located_field_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hconfig)
    as [Hef [sid [attr [co [ct [delta [Hreceiver [Hobject [Hco [Hct [Hsource [Hoffset [Hpath Hcomplete]]]]]]]]]]]]].
  pose proof Hconfig as [[Hheap Htyped Hlocated Hframes] Hcoherent].
  pose proof Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  destruct (complete_field_runtime_kind _ _ Hcomplete) as [[chunk Hmode]|[Hkind|Hbytes]].
  - destruct (covered_field_read_progress ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk
      Hmemory Hobject Hreceiver Hco Hoffset Hpath Hmode) as [v [Hstep [Hv Hloc]]].
    exists objects,v. split; [exact Hstep|]. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [|exact Hcoherent]. constructor; [exact Hheap|exact Hv| |exact I].
      eapply runtime_locations_monotone; [apply packet_descriptor_embedding|exact Hloc].
  - destruct (covered_field_address _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hpath) as [Hraw [Hresult Hadd]].
    pose proof (covered_aggregate_field_access ge Sigma m objects cells b base sid attr receiver field ty co ct delta
      Hmemory Hobject Hreceiver Hco Hct Hsource Hoffset Hpath ltac:(rewrite Hkind; reflexivity)) as Haccess.
    destruct (initialized_heap_register_subobject _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hheap Hobject Hpath Hkind Hresult) as [Hheap' Hevolution].
    exists (add_aggregate_descriptor objects b (Ptrofs.repr (Ptrofs.unsigned base+delta)) ty),
      (Vloc b (Ptrofs.repr (Ptrofs.unsigned base+delta))).
    split; [apply ssem_sfield_aggregate; exact Haccess|]. split; [exact Hevolution|].
    split; [|exact Hcoherent]. constructor; [exact Hheap'| | |exact I].
    + eapply aggregate_descriptor_value_typed; [exact (initialized_object_descriptors _ _ _ _ _
        (initialized_heap_memory _ _ _ _ _ _ _ _ Hheap'))|right; auto].
    + left; apply aggregate_descriptor_direct; [exact Hkind|right; auto].
  - subst ty.
    destruct (covered_packet_leaf_read _ Gamma _ _ _ _ _ _ _ _
      (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject
      (packet_heap_coverage _ _ _ _ _ _ Hpacket) (packet_heap_valid _ _ _ _ _ _ Hpacket) Hpath)
      as [Hin [Hidentity [Hv Hread]]].
    destruct (covered_field_address _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hpath) as [Hraw [Hresult Hadd]].
    exists objects, (Vloc b (Ptrofs.repr (Ptrofs.unsigned base+delta))). split.
    + rewrite <- Hadd in Hread |- *. destruct Hreceiver; subst receiver;
        [eapply ssem_sfield_struct|eapply ssem_sfield2]; eauto.
    + split; [eapply initialized_heap_evolution_refl; exact Hheap|].
      split; [|exact Hcoherent]. constructor; [exact Hheap|exact Hv|right; auto|exact I].
Qed.

Theorem coherent_field_read_preservation : forall ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef final vm' e',
  ge.(genv_cenv) = p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Sfield (Val (Vloc b base) receiver) field ty) ef ty ->
  ssem_expr ge p vm m (Sfield (Val (Vloc b base) receiver) field ty) final vm' e' ->
  final=m /\ vm'=vm /\ exists objects',
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects' cells packets e' nil ty.
Proof.
  intros ge p Gamma Sigma vm m objects cells packets b base receiver field ty ef final vm' e' Henv Hconfig Hstep.
  destruct (typed_located_field_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hconfig)
    as [Hef [sid [attr [co [ct [delta [Hreceiver [Hobject [Hco [Hct [Hsource [Hoffset [Hpath Hcomplete]]]]]]]]]]]]].
  pose proof Hconfig as [[Hheap Htyped Hlocated Hframes] Hcoherent].
  pose proof Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  destruct (complete_field_runtime_kind _ _ Hcomplete) as [[chunk Hmode]|Haddress].
  - destruct (covered_field_read_preservation ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk final vm' e'
      Hmemory Hobject Hreceiver Hco Hoffset Hpath Hmode Hstep) as [Hm [Hvm [Hv Hloc]]].
    subst final vm'. split; [reflexivity|]. split; [reflexivity|]. exists objects. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [|exact Hcoherent]. constructor; [exact Hheap|exact Hv| |].
      * eapply runtime_locations_monotone; [apply packet_descriptor_embedding|exact Hloc].
      * inversion Hstep; subst; try exact I. exfalso; eapply value_has_no_small_step; eauto.
  - assert (Hkind : (is_aggregate_type ty || is_bytes ty)%bool = true).
    { destruct Haddress as [Hkind|Hbytes]; [rewrite Hkind|subst ty]; reflexivity. }
    destruct (covered_field_address _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hpath) as [Hraw [Hresult Hadd]].
    destruct (address_field_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hreceiver Hco Hoffset Hkind Hadd Hstep) as [Hm [Hvm He]]. subst final vm' e'.
    destruct (coherent_field_read_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hconfig)
      as [objects' [v [Hchosen [Hevolution Hfinal]]]].
    destruct (address_field_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hreceiver Hco Hoffset Hkind Hadd Hchosen) as [_ [_ Hvalue]]. inversion Hvalue; subst v.
    split; [reflexivity|]. split; [reflexivity|]. exists objects'; split; assumption.
Qed.

Print Assumptions coherent_field_read_progress.
Print Assumptions coherent_field_read_preservation.
