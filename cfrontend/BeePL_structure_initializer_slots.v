(* A repeated field name writes the same declared scalar slot. It need not be
   rejected: existing exact aliases are updated together; other cells frame. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initializer_slot BeePL_general_array_initialization.
Require Import BeePL_layout_coherence BeePL_packet_state BeePL_packet_heap.
Import ListNotations.
Local Open Scope Z_scope.

Lemma compatible_scalar_slot_coherent : forall cells block offset ty chunk,
  coherent_layout cells -> layout_write_compatible cells block offset ty chunk ->
  coherent_layout (extend_scalar_layout cells block offset ty chunk).
Proof.
  intros * Hcoherent Hcompatible b ofs t ch Hcell old off t' ch' Hold.
  destruct Hcell as [Hcell|[Hb [Ho [Ht Hch]]]];
    destruct Hold as [Hold|[Holdb [Holdo [Holdt Holdch]]]].
  - eapply Hcoherent; eauto.
  - subst old off t' ch'. destruct (Hcompatible _ _ _ _ Hcell) as [[Hb [Ho [Ht Hch]]]|Haway].
    + subst; left; auto.
    + right; destruct Haway as [Hneq|Haway]; [left; congruence|right; tauto].
  - subst b ofs t ch. destruct (Hcompatible _ _ _ _ Hold) as [[Hb [Ho [Ht Hch]]]|Haway].
    + subst; left; auto.
    + right; destruct Haway as [Hneq|Haway]; [left; congruence|right; tauto].
  - subst; left; auto.
Qed.

Lemma compatible_scalar_slot_frame :
  forall env Sigma L cells m final block offset ty chunk v,
  typed_memory_layout env Sigma cells m -> memory_locations L cells m ->
  layout_write_compatible cells block offset ty chunk ->
  Mem.store (transl_bchunk_cchunk chunk) m block (Ptrofs.unsigned offset) (trans_bvalue_cvalue v) = Some final ->
  typed_memory_cell env Sigma final block offset ty chunk ->
  (forall loaded, deref_addr ty final block offset Full loaded -> value_locations L loaded ty) ->
  typed_memory_layout env Sigma (extend_scalar_layout cells block offset ty chunk) final /\
  memory_locations L (extend_scalar_layout cells block offset ty chunk) final.
Proof.
  intros * Hcells Hlocations Hcompatible Hstore Hnew HnewLocated.
  assert (Hold : forall b ofs t ch, cells b ofs t ch ->
    typed_memory_cell env Sigma final b ofs t ch /\
    forall loaded, deref_addr t final b ofs Full loaded -> value_locations L loaded t).
  { intros b ofs t ch Hin.
    destruct (Hcompatible _ _ _ _ Hin) as [[Hb [Ho [Ht Hch]]]|Haway].
    - subst; split; assumption.
    - split.
      + eapply typed_memory_cell_store_disjoint; [apply Hcells; exact Hin|exact Hstore|tauto].
      + intros value Hread.
        destruct (Hcells _ _ _ _ Hin) as [Hmode Hvol Hperm [cv [old [Hload [Hdecode Htyped]]]]].
        assert (HoldRead : deref_addr t final b ofs Full old).
        { eapply deref_addr_value; eauto. simpl.
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload|tauto]. }
        assert (value=old) by (eapply deref_full_deterministic; eauto). subst value.
        eapply Hlocations; [exact Hin|]. eapply deref_addr_value; eauto. }
  split.
  - intros b ofs t ch [Hin|[Hb [Ho [Ht Hch]]]];
      [apply (proj1 (Hold _ _ _ _ Hin))|subst; exact Hnew].
  - intros b ofs t ch [Hin|[Hb [Ho [Ht Hch]]]] value Hread;
      [eapply (proj2 (Hold _ _ _ _ Hin)); exact Hread|subst; eapply HnewLocated; exact Hread].
Qed.

Theorem initialize_compatible_scalar_slot :
  forall ge env Gamma Sigma L cells packets m block offset ty chunk v,
  type_expr env Gamma Sigma (Val v ty) [] ty -> value_locations L v ty ->
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile (transBeePL_type ty) = false ->
  typed_memory_layout env Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets ->
  Mem.valid_access m (transl_bchunk_cchunk chunk) block (Ptrofs.unsigned offset) Freeable ->
  layout_write_compatible cells block offset ty chunk ->
  packet_write_separated m packets block (Ptrofs.unsigned offset)
    (size_chunk (transl_bchunk_cchunk chunk)) ->
  exists final,
    Mem.store (transl_bchunk_cchunk chunk) m block (Ptrofs.unsigned offset) (trans_bvalue_cvalue v) = Some final /\
    assign_addr ge ty m block offset Full v final v /\
    typed_memory_layout env Sigma (extend_scalar_layout cells block offset ty chunk) final /\
    memory_locations L (extend_scalar_layout cells block offset ty chunk) final /\
    coherent_layout (extend_scalar_layout cells block offset ty chunk) /\
    packet_state_valid final packets.
Proof.
  intros * Htyped Hlocated Hmode Hvolatile Hcells Hlocations Hcoherent Hpackets Haccess Hcompatible Hseparated.
  destruct (initialize_typed_scalar_array_cell ge env Gamma Sigma L m block offset ty chunk v
    Htyped Hlocated Hmode Hvolatile Haccess) as [final [Hstore [Hassign [Hnew HnewLocated]]]].
  destruct (compatible_scalar_slot_frame _ _ _ _ _ _ _ _ _ _ _
    Hcells Hlocations Hcompatible Hstore Hnew HnewLocated) as [Hcells' Hlocations'].
  exists final. split; [exact Hstore|]. split; [exact Hassign|]. split; [exact Hcells'|].
  split; [exact Hlocations'|]. split.
  - eapply compatible_scalar_slot_coherent; eauto.
  - eapply packet_state_store_preserved; eauto.
Qed.

Print Assumptions initialize_compatible_scalar_slot.

Require Import BeePL_object_paths BeePL_object_separation BeePL_scalar_object_layout.

Lemma declared_scalar_slot_compatible : forall p cells block start root delta ty chunk offset,
  scalar_object_region_coherent p.(prog_comp_env) cells block start root ->
  scalar_object_leaf p.(prog_comp_env) root delta ty chunk ->
  Ptrofs.unsigned offset = start + delta ->
  layout_write_compatible cells block offset ty chunk.
Proof.
  intros * Hregion Hleaf Hoffset b ofs t ch Hin.
  pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Hs Hbound]].
  destruct (Hregion _ _ _ _ Hin) as [[Hblock|[Hbefore|Hafter]]|[old [Hold [Hb Hofs]]]].
  - right; left; exact Hblock.
  - right; right; right; lia.
  - right; right; left; lia.
  - subst b.
    destruct (program_scalar_leaf_subobject _ _ _ _ _ _ _ Hold (proj1 Hleaf))
      as [[Hbefore|Hafter]|[relative [[Hpath Hmode] Heq]]].
    + right; right; right; lia.
    + pose proof (scalar_type_chunk_size p.(prog_comp_env) ty _ (proj2 Hleaf)) as Hsize.
      right; right; left; lia.
    + destruct (scalar_object_descent_identity _ _ _ _ _ _ (proj2 Hleaf)
        (object_path_descent _ _ _ _ Hpath)) as [Hrelative Hty].
      subst relative t.
      assert (Hchunk : ch=chunk) by (apply initialized_scalar_chunk_unique; pose proof (proj2 Hleaf); congruence).
      subst ch. left. split; [reflexivity|]. split; [|auto].
      rewrite <- (Ptrofs.repr_unsigned ofs), <- (Ptrofs.repr_unsigned offset).
      f_equal; lia.
Qed.

Lemma declared_scalar_slot_region : forall env cells block start root delta ty chunk offset,
  scalar_object_region_coherent env cells block start root ->
  scalar_object_leaf env root delta ty chunk ->
  Ptrofs.unsigned offset = start + delta ->
  scalar_object_region_coherent env (extend_scalar_layout cells block offset ty chunk) block start root.
Proof.
  intros * Hregion Hleaf Hoffset b ofs t ch [Hold|[Hb [Ho [Ht Hch]]]].
  - apply Hregion; exact Hold.
  - subst; right. exists delta; auto.
Qed.

Print Assumptions declared_scalar_slot_compatible.

Require Import BeePL_block_extents BeePL_scalar_object_coherence.

Theorem initialize_declared_scalar_slot :
  forall p Gamma Sigma L cells packets m block root delta ty chunk v,
  type_expr p.(prog_comp_env) Gamma Sigma (Val v ty) [] ty -> value_locations L v ty ->
  type_is_volatile (transBeePL_type ty) = false ->
  typed_memory_layout p.(prog_comp_env) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets ->
  source_block_extent m block (sizeof_type p.(prog_comp_env) root) ->
  scalar_object_region_coherent p.(prog_comp_env) cells block 0 root ->
  scalar_object_leaf p.(prog_comp_env) root delta ty chunk ->
  packet_write_separated m packets block delta (size_chunk (transl_bchunk_cchunk chunk)) ->
  exists final,
    assign_addr (globalenv p) ty m block (Ptrofs.repr delta) Full v final v /\
    typed_memory_layout p.(prog_comp_env) Sigma
      (extend_scalar_layout cells block (Ptrofs.repr delta) ty chunk) final /\
    memory_locations L (extend_scalar_layout cells block (Ptrofs.repr delta) ty chunk) final /\
    coherent_layout (extend_scalar_layout cells block (Ptrofs.repr delta) ty chunk) /\
    packet_state_valid final packets /\
    source_block_extent final block (sizeof_type p.(prog_comp_env) root) /\
    scalar_object_region_coherent p.(prog_comp_env)
      (extend_scalar_layout cells block (Ptrofs.repr delta) ty chunk) block 0 root.
Proof.
  intros * Htyped Hlocated Hvol Hcells Hlocations Hcoherent Hpackets Hextent Hregion Hleaf Hseparated.
  pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Hs Hbound]].
  pose proof (source_extent_bound _ _ _ Hextent) as Htotal.
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)) as Hpositive.
  assert (Hrepr : Ptrofs.unsigned (Ptrofs.repr delta) = delta) by (apply Ptrofs.unsigned_repr; lia).
  assert (Haccess : Mem.valid_access m (transl_bchunk_cchunk chunk) block delta Freeable).
  { split.
    - intros ofs Hrange. apply (source_extent_freeable _ _ _ Hextent); lia.
    - eapply program_scalar_object_leaf_alignment; exact Hleaf. }
  assert (Hcompatible : layout_write_compatible cells block (Ptrofs.repr delta) ty chunk).
  { eapply declared_scalar_slot_compatible; [exact Hregion|exact Hleaf|rewrite Hrepr; lia]. }
  destruct (initialize_compatible_scalar_slot (globalenv p) p.(prog_comp_env) Gamma Sigma L cells packets m
    block (Ptrofs.repr delta) ty chunk v Htyped Hlocated (proj2 Hleaf) Hvol Hcells Hlocations Hcoherent
    Hpackets ltac:(rewrite Hrepr; exact Haccess) Hcompatible ltac:(rewrite Hrepr; exact Hseparated))
    as [final [Hstore [Hassign [Hcells' [Hlocations' [Hcoherent' Hpackets']]]]]].
  exists final. split; [exact Hassign|]. split; [exact Hcells'|]. split; [exact Hlocations'|].
  split; [exact Hcoherent'|]. split; [exact Hpackets'|]. split.
  - eapply source_block_extent_store; [exact Hstore|exact Hextent].
  - eapply declared_scalar_slot_region; [exact Hregion|exact Hleaf|rewrite Hrepr; lia].
Qed.

Print Assumptions initialize_declared_scalar_slot.

Record scalar_field_slot := {
  scalar_field_name : ident;
  scalar_field_offset : Z;
  scalar_field_type : type;
  scalar_field_chunk : bmemory_chunk;
  scalar_field_value : value
}.

Definition scalar_field_slot_valid p Gamma Sigma L sid attr co (slot : scalar_field_slot) : Prop :=
  type_expr p.(prog_comp_env) Gamma Sigma
    (Val slot.(scalar_field_value) slot.(scalar_field_type)) [] slot.(scalar_field_type) /\
  value_locations L slot.(scalar_field_value) slot.(scalar_field_type) /\
  type_is_volatile (transBeePL_type slot.(scalar_field_type)) = false /\
  scalar_object_leaf p.(prog_comp_env) (Stype sid attr)
    slot.(scalar_field_offset) slot.(scalar_field_type) slot.(scalar_field_chunk) /\
  field_offset (bcomposite_composite_env p.(prog_comp_env)) slot.(scalar_field_name)
    (bmembers_cmembers co.(co_members)) = Errors.OK (slot.(scalar_field_offset), Full).

Theorem initialize_scalar_structure_fields :
  forall slots p Gamma Sigma L sid attr co cells packets m block,
  PTree.get sid p.(prog_comp_env) = Some co ->
  Forall (scalar_field_slot_valid p Gamma Sigma L sid attr co) slots ->
  typed_memory_layout p.(prog_comp_env) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets -> packet_block_disjoint m packets block ->
  source_block_extent m block (sizeof_type p.(prog_comp_env) (Stype sid attr)) ->
  scalar_object_region_coherent p.(prog_comp_env) cells block 0 (Stype sid attr) ->
  exists final after,
    sem_allocate_fields (globalenv p) block Ptrofs.zero sid
      (map scalar_field_name slots) (map scalar_field_value slots) (map scalar_field_type slots) m final /\
    typed_memory_layout p.(prog_comp_env) Sigma after final /\ memory_locations L after final /\ coherent_layout after /\
    packet_state_valid final packets /\ packet_block_disjoint final packets block /\
    source_block_extent final block (sizeof_type p.(prog_comp_env) (Stype sid attr)) /\
    scalar_object_region_coherent p.(prog_comp_env) after block 0 (Stype sid attr) /\
    (forall b ofs ty chunk, cells b ofs ty chunk -> after b ofs ty chunk) /\
    (forall slot, In slot slots -> after block (Ptrofs.repr slot.(scalar_field_offset)) slot.(scalar_field_type) slot.(scalar_field_chunk)) /\
    (forall b ofs ty chunk, after b ofs ty chunk -> cells b ofs ty chunk \/
      exists slot, In slot slots /\ b=block /\ ofs=Ptrofs.repr slot.(scalar_field_offset) /\
        ty=slot.(scalar_field_type) /\ chunk=slot.(scalar_field_chunk)).
Proof.
  induction slots as [|slot slots IH]; intros p Gamma Sigma L sid attr co cells packets m block
    Hco Hslots Hcells Hlocations Hcoherent Hpackets Hdisjoint Hextent Hregion.
  - exists m, cells. split; [constructor|]. split; [exact Hcells|].
    split; [exact Hlocations|]. split; [exact Hcoherent|]. split; [exact Hpackets|].
    split; [exact Hdisjoint|]. split; [exact Hextent|]. split; [exact Hregion|].
    split; [auto|]. split; [intros item Hin; contradiction|intros; left; assumption].
  - inversion Hslots as [|head tail Hslot Htail]; subst head tail.
    destruct Hslot as [Htyped [Hlocated [Hvol [Hleaf Hoffset]]]].
    destruct (initialize_declared_scalar_slot p Gamma Sigma L cells packets m block (Stype sid attr)
      slot.(scalar_field_offset) slot.(scalar_field_type) slot.(scalar_field_chunk) slot.(scalar_field_value)
      Htyped Hlocated Hvol Hcells Hlocations Hcoherent Hpackets Hextent Hregion Hleaf
      ltac:(apply packet_block_disjoint_write; exact Hdisjoint))
      as [next [Hassign [Hcells' [Hlocations' [Hcoherent' [Hpackets' [Hextent' Hregion']]]]]]].
    assert (Hdisjoint' : packet_block_disjoint next packets block).
    { destruct (packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hpackets Hdisjoint Hassign) as [_ Hviews].
      exact (packet_block_disjoint_frame m next packets block Hpackets Hviews Hdisjoint). }
    destruct (IH p Gamma Sigma L sid attr co _ packets next block
      Hco Htail Hcells' Hlocations' Hcoherent' Hpackets' Hdisjoint' Hextent' Hregion')
      as [final [after [Hinit [Hcells'' [Hlocations'' [Hcoherent'' [Hpackets'' [Hdisjoint'' [Hextent'' [Hregion'' [Hold [Hcovered Horigin]]]]]]]]]]]].
    exists final, after. split.
    + cbn [map]. eapply sem_allocate_struct with (co := co) (delta := scalar_field_offset slot) (bf := Full).
      * exact Hco.
      * exact Hoffset.
      * rewrite Ptrofs.add_zero_l. exact Hassign.
      * exact Hinit.
    + split; [exact Hcells''|]. split; [exact Hlocations''|]. split; [exact Hcoherent''|].
      split; [exact Hpackets''|]. split; [exact Hdisjoint''|]. split; [exact Hextent''|]. split; [exact Hregion''|].
      split.
      * intros b ofs ty chunk Hin. apply Hold; left; exact Hin.
      * split.
        -- intros item [Heq|Hin].
           ++ subst item. apply Hold; right; auto.
           ++ apply Hcovered; exact Hin.
        -- intros b ofs ty chunk Hin. destruct (Horigin _ _ _ _ Hin) as [Hprevious|[item [Hitem Hcoordinates]]].
           ++ destruct Hprevious as [Holdcell|[Hb [Ho [Ht Hch]]]].
              ** left; exact Holdcell.
              ** right; exists slot; split; [left; reflexivity|auto].
           ++ right; exists item; split; [right; exact Hitem|exact Hcoordinates].
Qed.

Print Assumptions initialize_scalar_structure_fields.
