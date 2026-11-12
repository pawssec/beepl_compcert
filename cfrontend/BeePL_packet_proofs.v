Require Import ZArith Bool Lia Integers AST Memory BeePL_packet.
Local Open Scope Z_scope.

Lemma read_packet_view_total : forall m descriptor offset view,
  packet_descriptor_valid m descriptor offset view ->
  read_packet_view m descriptor offset = Some view.
Proof.
  intros m descriptor offset [block first last] [Hfirst [Hlast [Horder Hvalid]]].
  unfold read_packet_view. simpl in *. rewrite Hfirst, Hlast, Pos.eqb_refl.
  assert (Hle : Z.leb (Ptrofs.unsigned first) (Ptrofs.unsigned last) = true)
    by (apply Z.leb_le; exact Horder).
  rewrite Hle. reflexivity.
Qed.

Lemma read_packet_view_sound : forall m descriptor offset view,
  read_packet_view m descriptor offset = Some view ->
  Mem.load Mptr m descriptor (Ptrofs.unsigned offset) =
    Some (Values.Vptr view.(packet_block) view.(packet_first)) /\
  Mem.load Mptr m descriptor (Ptrofs.unsigned offset + size_chunk Mptr) =
    Some (Values.Vptr view.(packet_block) view.(packet_last)) /\
  Ptrofs.unsigned view.(packet_first) <= Ptrofs.unsigned view.(packet_last).
Proof.
  intros m descriptor offset view Hread. unfold read_packet_view in Hread.
  destruct (Mem.load Mptr m descriptor (Ptrofs.unsigned offset)) as [first |] eqn:Hfirst;
    try discriminate.
  destruct first; try discriminate.
  destruct (Mem.load Mptr m descriptor (Ptrofs.unsigned offset + size_chunk Mptr)) as [last |] eqn:Hlast;
    try discriminate.
  destruct last; try discriminate.
  match goal with H : (if ?guard then _ else _) = Some _ |- _ =>
    destruct guard eqn:Hguard; try discriminate
  end.
  apply andb_true_iff in Hguard. destruct Hguard as [Hblock Horder].
  apply Pos.eqb_eq in Hblock. subst.
  inversion Hread; subst. simpl. repeat split; try assumption. apply Z.leb_le; exact Horder.
Qed.

Lemma packet_header_fits_spec : forall view size,
  packet_header_fits view size = true <->
  0 <= size /\ Ptrofs.unsigned view.(packet_first) + size <= Ptrofs.unsigned view.(packet_last).
Proof.
  intros. unfold packet_header_fits. rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.

Theorem packet_header_bounds : forall view size,
  packet_header_fits view size = true ->
  0 <= Ptrofs.unsigned view.(packet_first) /\ 0 <= size /\
  Ptrofs.unsigned view.(packet_first) + size <= Ptrofs.unsigned view.(packet_last) /\
  Ptrofs.unsigned view.(packet_first) + size <= Ptrofs.max_unsigned /\
  Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned view.(packet_first) + size)) =
    Ptrofs.unsigned view.(packet_first) + size.
Proof.
  intros view size Hfits. apply packet_header_fits_spec in Hfits.
  pose proof (Ptrofs.unsigned_range view.(packet_first)).
  pose proof (Ptrofs.unsigned_range_2 view.(packet_last)).
  repeat split; try lia. apply Ptrofs.unsigned_repr. lia.
Qed.

Theorem packet_header_readable : forall m view size,
  packet_view_valid m view -> packet_header_fits view size = true ->
  Mem.range_perm m view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_first) + size) Cur Readable.
Proof.
  intros m view size [Horder [Hvalid Hread]] Hfits.
  apply packet_header_fits_spec in Hfits.
  unfold Mem.range_perm in *. intros offset Hoffset. apply Hread. lia.
Qed.

Theorem packet_header_loadbytes_exists : forall m view size,
  packet_view_valid m view -> packet_header_fits view size = true ->
  exists bytes, Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first)) size = Some bytes.
Proof.
  intros. apply Mem.range_perm_loadbytes. eapply packet_header_readable; eassumption.
Qed.

Lemma packet_header_rejects_oversize : forall view size,
  Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first) < size ->
  packet_header_fits view size = false.
Proof.
  intros view size Hlarge. unfold packet_header_fits.
  assert (Hbound : Z.leb (Ptrofs.unsigned view.(packet_first) + size)
    (Ptrofs.unsigned view.(packet_last)) = false) by (apply Z.leb_gt; lia).
  rewrite Hbound. apply andb_false_r.
Qed.

Print Assumptions read_packet_view_total.
Print Assumptions read_packet_view_sound.
Print Assumptions packet_header_bounds.
Print Assumptions packet_header_loadbytes_exists.
Print Assumptions packet_header_rejects_oversize.

Theorem read_packet_header_total : forall m descriptor offset view size,
  packet_descriptor_valid m descriptor offset view ->
  exists result, read_packet_header m descriptor offset size = Some result.
Proof.
  intros m descriptor offset view size Hdescriptor.
  unfold read_packet_header. rewrite (read_packet_view_total _ _ _ _ Hdescriptor).
  destruct (packet_header_fits view size) eqn:Hfits.
  - destruct Hdescriptor as [_ [_ Hvalid]].
    destruct (packet_header_loadbytes_exists _ _ _ Hvalid Hfits) as [bytes Hload].
    rewrite Hload. eauto.
  - eauto.
Qed.

Theorem read_packet_header_success : forall m descriptor offset size view bytes,
  read_packet_header m descriptor offset size = Some (PacketHeaderFits view bytes) ->
  read_packet_view m descriptor offset = Some view /\
  packet_header_fits view size = true /\
  Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first)) size = Some bytes.
Proof.
  intros m descriptor offset size view bytes Hread. unfold read_packet_header in Hread.
  destruct (read_packet_view m descriptor offset) as [actual |] eqn:Hview; try discriminate.
  destruct (packet_header_fits actual size) eqn:Hfits; try discriminate.
  destruct (Mem.loadbytes m (packet_block actual) (Ptrofs.unsigned (packet_first actual)) size)
    as [actual_bytes |] eqn:Hbytes; try discriminate.
  inversion Hread; subst. auto.
Qed.

Theorem read_packet_header_fallback : forall m descriptor offset size view,
  read_packet_header m descriptor offset size = Some (PacketHeaderShort view) ->
  read_packet_view m descriptor offset = Some view /\ packet_header_fits view size = false.
Proof.
  intros m descriptor offset size view Hread. unfold read_packet_header in Hread.
  destruct (read_packet_view m descriptor offset) as [actual |] eqn:Hview; try discriminate.
  destruct (packet_header_fits actual size) eqn:Hfits.
  - destruct (Mem.loadbytes m (packet_block actual) (Ptrofs.unsigned (packet_first actual)) size);
      discriminate.
  - inversion Hread; subst. auto.
Qed.

Lemma read_packet_header_short_no_header_read : forall m descriptor offset view size,
  read_packet_view m descriptor offset = Some view ->
  packet_header_fits view size = false ->
  read_packet_header m descriptor offset size = Some (PacketHeaderShort view).
Proof. intros; unfold read_packet_header; rewrite H, H0; reflexivity. Qed.

Print Assumptions read_packet_header_total.
Print Assumptions read_packet_header_success.
Print Assumptions read_packet_header_fallback.
Print Assumptions read_packet_header_short_no_header_read.

Theorem copy_packet_header_total : forall m bytes,
  exists allocated copied block,
    Mem.alloc m 0 (Z.of_nat (List.length bytes)) = (allocated, block) /\
    Mem.storebytes allocated block 0 bytes = Some copied /\
    copy_packet_header m bytes = Some (copied, block) /\
    Mem.loadbytes copied block 0 (Z.of_nat (List.length bytes)) = Some bytes.
Proof.
  intros m bytes.
  destruct (Mem.alloc m 0 (Z.of_nat (List.length bytes))) as [allocated block] eqn:Halloc.
  assert (Hwrite : Mem.range_perm allocated block 0 (0 + Z.of_nat (List.length bytes)) Cur Writable).
  { intros offset Hoffset. eapply Mem.perm_implies.
    - eapply Mem.perm_alloc_2; [exact Halloc | lia].
    - constructor. }
  destruct (Mem.range_perm_storebytes allocated block 0 bytes Hwrite) as [copied Hstore].
  exists allocated, copied, block. split; [reflexivity |]. split; [exact Hstore |]. split.
  - unfold copy_packet_header. rewrite Halloc, Hstore. reflexivity.
  - eapply Mem.loadbytes_storebytes_same; exact Hstore.
Qed.

Lemma copy_packet_header_steps : forall m bytes copied block,
  copy_packet_header m bytes = Some (copied, block) ->
  exists allocated,
    Mem.alloc m 0 (Z.of_nat (List.length bytes)) = (allocated, block) /\
    Mem.storebytes allocated block 0 bytes = Some copied.
Proof.
  intros m bytes copied block Hcopy. unfold copy_packet_header in Hcopy.
  destruct (Mem.alloc m 0 (Z.of_nat (List.length bytes))) as [allocated fresh] eqn:Halloc.
  destruct (Mem.storebytes allocated fresh 0 bytes) as [written |] eqn:Hstore; try discriminate.
  inversion Hcopy; subst. eauto.
Qed.

Theorem copy_packet_header_preserves_old_bytes : forall m bytes copied block old offset length,
  copy_packet_header m bytes = Some (copied, block) ->
  Mem.valid_block m old -> 0 <= length ->
  Mem.loadbytes copied old offset length = Mem.loadbytes m old offset length.
Proof.
  intros m bytes copied block old offset length Hcopy Hold Hlength.
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  assert (Hfresh : old <> block).
  { intro Heq. subst old. eapply Mem.fresh_block_alloc; eassumption. }
  rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore old offset length) by (auto; lia).
  eapply Mem.loadbytes_alloc_unchanged; eassumption.
Qed.

Theorem read_and_copy_packet_header : forall m descriptor offset size view bytes,
  read_packet_header m descriptor offset size = Some (PacketHeaderFits view bytes) ->
  exists copied block,
    copy_packet_header m bytes = Some (copied, block) /\
    Mem.loadbytes copied block 0 size = Some bytes /\
    ~ Mem.valid_block m block.
Proof.
  intros m descriptor offset size view bytes Hread.
  destruct (read_packet_header_success _ _ _ _ _ _ Hread) as [Hview [Hfits Hload]].
  apply packet_header_fits_spec in Hfits.
  pose proof (Mem.loadbytes_length _ _ _ _ _ Hload) as Hlength.
  assert (Hsize : Z.of_nat (List.length bytes) = size) by (rewrite Hlength, Z2Nat.id; lia).
  destruct (copy_packet_header_total m bytes) as [allocated [copied [block [Halloc [Hstore [Hcopy Hback]]]]]].
  exists copied, block. split; [exact Hcopy |]. split.
  - rewrite <- Hsize. exact Hback.
  - eapply Mem.fresh_block_alloc; exact Halloc.
Qed.

Print Assumptions copy_packet_header_total.
Print Assumptions copy_packet_header_preserves_old_bytes.
Print Assumptions read_and_copy_packet_header.

Require Import List Errors BeeTypes BeePL_values BeePL BeePL_typesystem.

Lemma initialized_packet_contents_app : forall first last,
  initialized_packet_contents (first ++ last) <->
  initialized_packet_contents first /\ initialized_packet_contents last.
Proof.
  intros first last. unfold initialized_packet_contents. rewrite Memdata.proj_bytes_append.
  destruct (Memdata.proj_bytes first) as [rawFirst |];
    destruct (Memdata.proj_bytes last) as [rawLast |];
    split; intros H; try solve [destruct H as [raw H]; discriminate];
    try solve [destruct H as [[raw H] _]; discriminate];
    try solve [destruct H as [_ [raw H]]; discriminate]; eauto.
Qed.

Theorem initialized_packet_subrange : forall m b start size bytes delta count,
  Mem.loadbytes m b start size = Some bytes ->
  initialized_packet_contents bytes ->
  0 <= delta -> 0 <= count -> delta + count <= size ->
  exists fieldBytes, Mem.loadbytes m b (start + delta) count = Some fieldBytes /\
    initialized_packet_contents fieldBytes.
Proof.
  intros m b start size bytes delta count Hload Hinitialized Hdelta Hcount Hwithin.
  assert (Hsplit : Mem.loadbytes m b start (delta + (size - delta)) = Some bytes)
    by (replace (delta + (size - delta)) with size by lia; exact Hload).
  destruct (Mem.loadbytes_split m b start delta (size - delta) bytes Hsplit ltac:(lia) ltac:(lia))
    as [prefix [suffix [Hprefix [Hsuffix Heq]]]].
  rewrite Heq in Hinitialized. apply initialized_packet_contents_app in Hinitialized.
  destruct Hinitialized as [_ Hinitialized].
  assert (Hsplit2 : Mem.loadbytes m b (start + delta) (count + (size - delta - count)) = Some suffix)
    by (replace (count + (size - delta - count)) with (size - delta) by lia; exact Hsuffix).
  destruct (Mem.loadbytes_split m b (start + delta) count (size - delta - count) suffix Hsplit2 ltac:(lia) ltac:(lia))
    as [fieldBytes [tail [Hfield [Htail Heq2]]]].
  rewrite Heq2 in Hinitialized. apply initialized_packet_contents_app in Hinitialized.
  exists fieldBytes. tauto.
Qed.

Theorem decode_initialized_packet_scalar : forall pt bytes cenv Gamma Sigma,
  initialized_packet_contents bytes ->
  exists v, decode_packet_scalar pt bytes = OK v /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros pt bytes cenv Gamma Sigma [raw Hraw].
  unfold decode_packet_scalar, Memdata.decode_val. rewrite Hraw.
  destruct pt as [|sz sign attr|sign attr].
  - eexists. split; [reflexivity | apply ty_valb].
  - destruct sz, sign; (eexists; split; [reflexivity | apply ty_vali]).
  - destruct sign; (eexists; split; [reflexivity | apply ty_vall]).
Qed.

Lemma packet_boolean_two_is_true :
  decode_packet_scalar Tbool (Memdata.Byte (Byte.repr 2) :: nil) = OK (Vbool true).
Proof. vm_compute. reflexivity. Qed.

Lemma ordinary_boolean_chunk_rejects_two :
  Memdata.decode_val Mbool (Memdata.Byte (Byte.repr 2) :: nil) = Values.Vundef.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions initialized_packet_subrange.
Print Assumptions decode_initialized_packet_scalar.
Print Assumptions packet_boolean_two_is_true.
Print Assumptions ordinary_boolean_chunk_rejects_two.

Theorem read_initialized_packet_scalar :
  forall m b start size bytes delta pt cenv Gamma Sigma,
  Mem.loadbytes m b start size = Some bytes ->
  initialized_packet_contents bytes ->
  0 <= delta -> delta + size_chunk (packet_scalar_chunk pt) <= size ->
  exists v, read_packet_scalar m b (start + delta) pt = OK v /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros m b start size bytes delta pt cenv Gamma Sigma Hload Hinitialized Hdelta Hwithin.
  pose proof (size_chunk_pos (packet_scalar_chunk pt)) as Hpositive.
  destruct (initialized_packet_subrange m b start size bytes delta
    (size_chunk (packet_scalar_chunk pt)) Hload Hinitialized Hdelta ltac:(lia) Hwithin)
    as [fieldBytes [Hfield Hfield_initialized]].
  destruct (decode_initialized_packet_scalar pt fieldBytes cenv Gamma Sigma Hfield_initialized)
    as [v [Hdecode Htyped]].
  exists v. split; [unfold read_packet_scalar; rewrite Hfield; exact Hdecode | exact Htyped].
Qed.

Theorem read_copied_packet_scalar :
  forall m bytes copied block delta pt cenv Gamma Sigma,
  copy_packet_header m bytes = Some (copied, block) ->
  initialized_packet_contents bytes ->
  0 <= delta -> delta + size_chunk (packet_scalar_chunk pt) <= Z.of_nat (List.length bytes) ->
  exists v, read_packet_scalar copied block delta pt = OK v /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros m bytes copied block delta pt cenv Gamma Sigma Hcopy Hinitialized Hdelta Hwithin.
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  assert (Hload : Mem.loadbytes copied block 0 (Z.of_nat (List.length bytes)) = Some bytes)
    by (eapply Mem.loadbytes_storebytes_same; exact Hstore).
  exact (read_initialized_packet_scalar copied block 0 (Z.of_nat (List.length bytes)) bytes
    delta pt cenv Gamma Sigma Hload Hinitialized Hdelta Hwithin).
Qed.

Print Assumptions read_initialized_packet_scalar.
Print Assumptions read_copied_packet_scalar.

Lemma copied_packet_header_writable : forall m bytes copied block,
  copy_packet_header m bytes = Some (copied, block) ->
  Mem.range_perm copied block 0 (Z.of_nat (List.length bytes)) Cur Writable.
Proof.
  intros m bytes copied block Hcopy.
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  intros offset Hoffset. eapply Mem.perm_storebytes_1; [exact Hstore |].
  eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eassumption | constructor].
Qed.

Theorem normalize_copied_packet_boolean : forall m bytes copied block delta,
  copy_packet_header m bytes = Some (copied, block) ->
  initialized_packet_contents bytes ->
  0 <= delta < Z.of_nat (List.length bytes) ->
  exists normalized flag,
    read_packet_scalar copied block delta Tbool = OK (Vbool flag) /\
    normalize_packet_boolean copied block delta = OK (normalized, flag) /\
    Mem.store Mbool copied block delta (Values.Val.of_bool flag) = Some normalized /\
    Mem.load Mbool normalized block delta = Some (Values.Val.of_bool flag).
Proof.
  intros m bytes copied block delta Hcopy Hinitialized Hbounds.
  destruct (read_copied_packet_scalar m bytes copied block delta Tbool
    (Maps.PTree.empty bcomposite) empty_context empty_stcontext Hcopy Hinitialized
    ltac:(lia) ltac:(simpl; lia)) as [v [Hread Htyped]].
  inversion Htyped; subst.
  assert (Hwrite : Mem.valid_access copied Mbool block delta Writable).
  { split.
    - intros offset Hoffset. eapply copied_packet_header_writable; [exact Hcopy |].
      simpl in Hoffset. lia.
    - change (1 | delta). exists delta. lia. }
  match goal with Hread : read_packet_scalar _ _ _ Tbool = OK (Vbool ?flag) |- _ =>
    destruct (Mem.valid_access_store copied Mbool block delta (Values.Val.of_bool flag) Hwrite)
      as [normalized Hstore];
    exists normalized, flag
  end.
  split; [exact Hread |]. split.
  - unfold normalize_packet_boolean. rewrite Hread, Hstore. reflexivity.
  - split; [exact Hstore |].
    pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore) as Hload.
    match goal with flag : bool |- _ => destruct flag; exact Hload end.
Qed.

Lemma normalize_packet_boolean_store : forall m block offset normalized flag,
  normalize_packet_boolean m block offset = OK (normalized, flag) ->
  Mem.store Mbool m block offset (Values.Val.of_bool flag) = Some normalized.
Proof.
  intros m block offset normalized flag Hnormalized. unfold normalize_packet_boolean in Hnormalized.
  destruct (read_packet_scalar m block offset Tbool) as [v | error]; try discriminate.
  destruct v; try discriminate.
  match goal with H : context [Mem.store Mbool m block offset ?cv] |- _ =>
    destruct (Mem.store Mbool m block offset cv) eqn:Hstore; try discriminate
  end.
  inversion Hnormalized; subst; exact Hstore.
Qed.

Theorem normalize_packet_boolean_preserves_other_bytes :
  forall m block offset normalized flag other otherOffset length,
  normalize_packet_boolean m block offset = OK (normalized, flag) ->
  (other <> block \/ otherOffset + length <= offset \/ offset + 1 <= otherOffset) ->
  Mem.loadbytes normalized other otherOffset length = Mem.loadbytes m other otherOffset length.
Proof.
  intros m block offset normalized flag other otherOffset length Hnormalized Hdisjoint.
  pose proof (normalize_packet_boolean_store _ _ _ _ _ Hnormalized) as Hstore.
  eapply Mem.loadbytes_store_other; [exact Hstore |]. simpl. tauto.
Qed.

Print Assumptions copied_packet_header_writable.
Print Assumptions normalize_copied_packet_boolean.
Print Assumptions normalize_packet_boolean_preserves_other_bytes.

Lemma initialized_boolean_encoding : forall flag,
  initialized_packet_contents (Memdata.encode_val Mbool (Values.Val.of_bool flag)).
Proof.
  intros []; unfold initialized_packet_contents; vm_compute; eexists; reflexivity.
Qed.

Theorem normalize_packet_boolean_preserves_initialization :
  forall m block start size bytes offset normalized flag,
  Mem.loadbytes m block start size = Some bytes ->
  initialized_packet_contents bytes ->
  start <= offset -> offset + 1 <= start + size ->
  normalize_packet_boolean m block offset = OK (normalized, flag) ->
  exists newBytes, Mem.loadbytes normalized block start size = Some newBytes /\
    initialized_packet_contents newBytes.
Proof.
  intros m block start size bytes offset normalized flag Hload Hinit Hlo Hhi Hnormalize.
  destruct (initialized_packet_subrange m block start size bytes 0 (offset - start)
    Hload Hinit ltac:(lia) ltac:(lia) ltac:(lia)) as [prefix [Hprefix Hiprefix]].
  replace (start + 0) with start in Hprefix by lia.
  destruct (initialized_packet_subrange m block start size bytes (offset + 1 - start)
    (start + size - (offset + 1)) Hload Hinit ltac:(lia) ltac:(lia) ltac:(lia))
    as [suffix [Hsuffix Hisuffix]].
  replace (start + (offset + 1 - start)) with (offset + 1) in Hsuffix by lia.
  assert (Hprefix' : Mem.loadbytes normalized block start (offset - start) = Some prefix).
  { rewrite (normalize_packet_boolean_preserves_other_bytes _ _ _ _ _ _ _ _ Hnormalize)
      by (right; left; lia). exact Hprefix. }
  assert (Hsuffix' : Mem.loadbytes normalized block (offset + 1)
    (start + size - (offset + 1)) = Some suffix).
  { rewrite (normalize_packet_boolean_preserves_other_bytes _ _ _ _ _ _ _ _ Hnormalize)
      by (right; right; lia). exact Hsuffix. }
  pose proof (normalize_packet_boolean_store _ _ _ _ _ Hnormalize) as Hstore.
  pose proof (Mem.loadbytes_store_same _ _ _ _ _ _ Hstore) as Hbyte.
  change (Mem.loadbytes normalized block offset 1 =
    Some (Memdata.encode_val Mbool (Values.Val.of_bool flag))) in Hbyte.
  assert (Htail : Mem.loadbytes normalized block offset (1 + (start + size - (offset + 1))) =
    Some (Memdata.encode_val Mbool (Values.Val.of_bool flag) ++ suffix)).
  { eapply Mem.loadbytes_concat; eauto; lia. }
  exists (prefix ++ (Memdata.encode_val Mbool (Values.Val.of_bool flag) ++ suffix)).
  split.
  - replace size with ((offset - start) + (1 + (start + size - (offset + 1)))) by lia.
    eapply Mem.loadbytes_concat; [exact Hprefix' | | lia | lia].
    replace (start + (offset - start)) with offset by lia. exact Htail.
  - apply initialized_packet_contents_app. split; [exact Hiprefix |].
    apply initialized_packet_contents_app. split; [apply initialized_boolean_encoding | exact Hisuffix].
Qed.

Print Assumptions normalize_packet_boolean_preserves_initialization.

Theorem normalize_packet_boolean_total : forall m block size offset,
  initialized_writable_packet_buffer m block size ->
  0 <= offset < size ->
  exists normalized flag,
    normalize_packet_boolean m block offset = OK (normalized, flag) /\
    initialized_writable_packet_buffer normalized block size /\
    Mem.load Mbool normalized block offset = Some (Values.Val.of_bool flag).
Proof.
  intros m block size offset [[bytes [Hload Hinit]] Hwrite] Hbounds.
  destruct (read_initialized_packet_scalar m block 0 size bytes offset Tbool
    (Maps.PTree.empty bcomposite) empty_context empty_stcontext Hload Hinit
    ltac:(lia) ltac:(simpl; lia)) as [v [Hread Htyped]].
  inversion Htyped; subst.
  assert (Haccess : Mem.valid_access m Mbool block offset Writable).
  { split.
    - intros i Hi. apply Hwrite. simpl in Hi; lia.
    - change (1 | offset). exists offset; lia. }
  match goal with Hread : read_packet_scalar _ _ _ Tbool = OK (Vbool ?flag) |- _ =>
    destruct (Mem.valid_access_store m Mbool block offset (Values.Val.of_bool flag) Haccess)
      as [normalized Hstore]; exists normalized, flag
  end.
  replace (0 + offset) with offset in Hread by lia.
  assert (Hnormalize : normalize_packet_boolean m block offset = OK (normalized, b)).
  { unfold normalize_packet_boolean. rewrite Hread, Hstore. reflexivity. }
  split; [exact Hnormalize |]. split.
  - split.
    + eapply normalize_packet_boolean_preserves_initialization; eauto; lia.
    + intros i Hi. eapply Mem.perm_store_1; [exact Hstore | apply Hwrite; exact Hi].
  - pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore) as Hsame.
    destruct b; exact Hsame.
Qed.

Theorem normalize_packet_booleans_total : forall offsets m block size,
  initialized_writable_packet_buffer m block size ->
  Forall (fun offset => 0 <= offset < size) offsets ->
  exists normalized,
    normalize_packet_booleans m block offsets = OK normalized /\
    initialized_writable_packet_buffer normalized block size.
Proof.
  induction offsets as [|offset rest IH]; intros m block size Hbuffer Hbounds.
  - exists m; split; [reflexivity | exact Hbuffer].
  - inversion Hbounds as [|? ? Hoffset HrestBounds]; subst.
    destruct (normalize_packet_boolean_total m block size offset Hbuffer Hoffset)
      as [next [flag [Hnext [Hbuffer' Hload]]]].
    destruct (IH next block size Hbuffer' HrestBounds) as [normalized [Hrest Hvalid]].
    exists normalized. split; [simpl; rewrite Hnext; exact Hrest | exact Hvalid].
Qed.

Print Assumptions normalize_packet_boolean_total.
Print Assumptions normalize_packet_booleans_total.

Lemma normalize_packet_boolean_canonical : forall m block offset normalized flag,
  normalize_packet_boolean m block offset = OK (normalized, flag) ->
  Mem.load Mbool normalized block offset = Some (Values.Val.of_bool flag).
Proof.
  intros m block offset normalized flag Hnormalize.
  pose proof (normalize_packet_boolean_store _ _ _ _ _ Hnormalize) as Hstore.
  pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore) as Hload.
  destruct flag; exact Hload.
Qed.

Lemma normalize_packet_boolean_preserves_canonical :
  forall m block offset normalized flag other previous,
  normalize_packet_boolean m block offset = OK (normalized, flag) ->
  Mem.load Mbool m block other = Some (Values.Val.of_bool previous) ->
  exists current, Mem.load Mbool normalized block other = Some (Values.Val.of_bool current).
Proof.
  intros m block offset normalized flag other previous Hnormalize Hprevious.
  destruct (Z.eq_dec other offset) as [Heq | Hneq].
  - subst other. exists flag. eapply normalize_packet_boolean_canonical; exact Hnormalize.
  - exists previous.
    pose proof (normalize_packet_boolean_store _ _ _ _ _ Hnormalize) as Hstore.
    rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore Mbool block other).
    + exact Hprevious.
    + simpl; lia.
Qed.

Lemma normalize_packet_booleans_preserves_canonical :
  forall offsets m block normalized other previous,
  normalize_packet_booleans m block offsets = OK normalized ->
  Mem.load Mbool m block other = Some (Values.Val.of_bool previous) ->
  exists current, Mem.load Mbool normalized block other = Some (Values.Val.of_bool current).
Proof.
  induction offsets as [|offset rest IH]; intros m block normalized other previous Hnormalize Hprevious.
  - simpl in Hnormalize; inversion Hnormalize; subst. exists previous; exact Hprevious.
  - simpl in Hnormalize.
    destruct (normalize_packet_boolean m block offset) as [[next flag] | error] eqn:Hnext;
      try discriminate.
    destruct (normalize_packet_boolean_preserves_canonical _ _ _ _ _ _ _ Hnext Hprevious)
      as [current Hcurrent].
    eapply IH; eauto.
Qed.

Theorem normalize_packet_booleans_canonical : forall offsets m block normalized,
  normalize_packet_booleans m block offsets = OK normalized ->
  forall offset, In offset offsets ->
    exists flag, Mem.load Mbool normalized block offset = Some (Values.Val.of_bool flag).
Proof.
  induction offsets as [|first rest IH]; intros m block normalized Hnormalize offset Hin.
  - inversion Hin.
  - simpl in Hnormalize.
    destruct (normalize_packet_boolean m block first) as [[next flag] | error] eqn:Hnext;
      try discriminate.
    destruct Hin as [Heq | Hin].
    + subst offset. eapply normalize_packet_booleans_preserves_canonical; [exact Hnormalize |].
      eapply normalize_packet_boolean_canonical; exact Hnext.
    + eapply IH; eauto.
Qed.

Theorem normalize_copied_packet_booleans : forall m bytes copied block offsets,
  copy_packet_header m bytes = Some (copied, block) ->
  initialized_packet_contents bytes ->
  Forall (fun offset => 0 <= offset < Z.of_nat (List.length bytes)) offsets ->
  exists normalized,
    normalize_packet_booleans copied block offsets = OK normalized /\
    initialized_writable_packet_buffer normalized block (Z.of_nat (List.length bytes)) /\
    (forall offset, In offset offsets -> exists flag,
      Mem.load Mbool normalized block offset = Some (Values.Val.of_bool flag)).
Proof.
  intros m bytes copied block offsets Hcopy Hinit Hbounds.
  assert (Hbuffer : initialized_writable_packet_buffer copied block (Z.of_nat (List.length bytes))).
  { split.
    - exists bytes. split; [|exact Hinit].
      destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
      eapply Mem.loadbytes_storebytes_same; exact Hstore.
    - eapply copied_packet_header_writable; exact Hcopy. }
  destruct (normalize_packet_booleans_total offsets copied block _ Hbuffer Hbounds)
    as [normalized [Hnormalize Hvalid]].
  exists normalized. split; [exact Hnormalize |]. split; [exact Hvalid |].
  eapply normalize_packet_booleans_canonical; exact Hnormalize.
Qed.

Print Assumptions normalize_packet_booleans_canonical.
Print Assumptions normalize_copied_packet_booleans.

Theorem normalize_packet_booleans_preserves_other_bytes :
  forall offsets m block normalized other start size,
  normalize_packet_booleans m block offsets = OK normalized ->
  Forall (fun offset => other <> block \/ start + size <= offset \/ offset + 1 <= start) offsets ->
  Mem.loadbytes normalized other start size = Mem.loadbytes m other start size.
Proof.
  induction offsets as [|offset rest IH]; intros m block normalized other start size Hnormalize Hdisjoint.
  - simpl in Hnormalize; inversion Hnormalize; subst; reflexivity.
  - simpl in Hnormalize.
    destruct (normalize_packet_boolean m block offset) as [[next flag] | error] eqn:Hnext;
      try discriminate.
    inversion Hdisjoint as [|? ? Hoffset Hrest]; subst.
    rewrite (IH next block normalized other start size Hnormalize Hrest).
    eapply normalize_packet_boolean_preserves_other_bytes; eauto.
Qed.

Theorem normalize_packet_booleans_preserves_scalar :
  forall offsets m block normalized start pt,
  normalize_packet_booleans m block offsets = OK normalized ->
  Forall (fun offset => start + size_chunk (packet_scalar_chunk pt) <= offset \/
    offset + 1 <= start) offsets ->
  read_packet_scalar normalized block start pt = read_packet_scalar m block start pt.
Proof.
  intros offsets m block normalized start pt Hnormalize Hdisjoint.
  unfold read_packet_scalar.
  rewrite (normalize_packet_booleans_preserves_other_bytes offsets m block normalized
    block start (size_chunk (packet_scalar_chunk pt)) Hnormalize); [reflexivity |].
  eapply Forall_impl; [|exact Hdisjoint]. intros offset Hoffset; tauto.
Qed.

Print Assumptions normalize_packet_booleans_preserves_scalar.

Require Import BeePL_substitution_proofs.

Theorem read_packet_fields_total : forall fields env members m block size bytes cenv Gamma Sigma,
  packet_fields_bounded env members size fields ->
  Mem.loadbytes m block 0 size = Some bytes ->
  initialized_packet_contents bytes ->
  exists values,
    read_packet_fields env members m block fields = OK values /\
    typed_field_values cenv Gamma Sigma fields values.
Proof.
  induction fields as [|[name ty] fields IH];
    intros env members m block size bytes cenv Gamma Sigma Hbounds Hload Hinit.
  - exists nil; split; [reflexivity | constructor].
  - inversion Hbounds as [|? ? Hfield Hrest]; subst.
    destruct Hfield as [pt [offset [Hty [Hoffset [Hlo Hhi]]]]]. simpl in Hty; subst ty.
    destruct (read_initialized_packet_scalar m block 0 size bytes offset pt cenv Gamma Sigma
      Hload Hinit Hlo Hhi) as [v [Hread Htyped]].
    replace (0 + offset) with offset in Hread by lia.
    destruct (IH env members m block size bytes cenv Gamma Sigma Hrest Hload Hinit)
      as [values [Hvalues Htypes]].
    exists (v :: values). split.
    + cbn [read_packet_fields]. simpl in Hoffset. rewrite Hoffset, Hread, Hvalues. reflexivity.
    + constructor; assumption.
Qed.

Theorem read_packet_fields_instantiate_header :
  forall env members m block size bytes fields cenv Gamma Sigma header schema headerValue body ef rt,
  packet_fields_bounded env members size fields ->
  Mem.loadbytes m block 0 size = Some bytes ->
  initialized_packet_contents bytes ->
  type_expr cenv Gamma Sigma (Val headerValue schema) nil schema ->
  type_expr cenv (pattern_context Gamma (Pbytes header schema fields) Bytes) Sigma body ef rt ->
  exists values body',
    read_packet_fields env members m block fields = OK values /\
    instantiate_bytes_header header schema fields headerValue values body = OK body' /\
    type_expr cenv Gamma Sigma body' ef rt.
Proof.
  intros env members m block size bytes fields cenv Gamma Sigma header schema headerValue body ef rt
    Hbounds Hload Hinit Hheader Hbody.
  destruct (read_packet_fields_total fields env members m block size bytes cenv Gamma Sigma
    Hbounds Hload Hinit) as [values [Hread Hvalues]].
  destruct (instantiate_bytes_header_preserves_typing cenv Gamma Sigma header schema fields
    headerValue values body ef rt Hheader Hvalues Hbody) as [body' [Hinstantiate Htyped]].
  exists values, body'. auto.
Qed.

Print Assumptions read_packet_fields_total.
Print Assumptions read_packet_fields_instantiate_header.

Require Import BeePL_layout_proofs BeePL_structure_proofs.

Lemma packet_scalar_size_translation : forall env pt,
  size_chunk (packet_scalar_chunk pt) = Ctypes.sizeof env (transBeePL_type (Vtype pt)).
Proof.
  intros env pt. destruct pt; [reflexivity | |]; apply primitive_chunk_size_translation.
Qed.

Theorem packet_fields_bounded_from_schema : forall env co fields,
  Ctypes.composite_consistent env (bcomposite_ccomposite co) ->
  co.(co_su) = Ctypes.Struct ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun field => exists pt,
    snd field = Vtype pt /\
    Ctypes.field_type (fst field) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype pt))) fields ->
  packet_fields_bounded env (bmembers_cmembers co.(co_members)) co.(co_sizeof) fields.
Proof.
  intros env co fields Hconsistent Hstruct Hplain Hfields.
  unfold packet_fields_bounded. eapply Forall_impl; [|exact Hfields].
  intros [name ty] [pt [Hty Htype]]. simpl in Hty, Htype; subst ty.
  destruct (plain_field_offset_exists env (bmembers_cmembers co.(co_members)) name
    (transBeePL_type (Vtype pt)) Hplain Htype 0) as [offset Hoffset].
  change (Ctypes.field_offset env name (bmembers_cmembers co.(co_members)) =
    OK (offset, Ctypes.Full)) in Hoffset.
  pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Htype) as [Hlo Hhi].
  pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as Hsize.
  exists pt, offset. split; [reflexivity |]. split; [exact Hoffset |]. split; [exact Hlo |].
  rewrite (packet_scalar_size_translation env pt).
  eapply Z.le_trans; [exact Hhi | exact Hsize].
Qed.

Theorem read_packet_schema_fields : forall env co fields m block bytes cenv Gamma Sigma,
  Ctypes.composite_consistent env (bcomposite_ccomposite co) ->
  co.(co_su) = Ctypes.Struct ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun field => exists pt,
    snd field = Vtype pt /\
    Ctypes.field_type (fst field) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype pt))) fields ->
  Mem.loadbytes m block 0 co.(co_sizeof) = Some bytes ->
  initialized_packet_contents bytes ->
  exists values,
    read_packet_fields env (bmembers_cmembers co.(co_members)) m block fields = OK values /\
    typed_field_values cenv Gamma Sigma fields values.
Proof.
  intros env co fields m block bytes cenv Gamma Sigma Hconsistent Hstruct Hplain Hfields Hload Hinit.
  eapply read_packet_fields_total; [|exact Hload |exact Hinit].
  eapply packet_fields_bounded_from_schema; eauto.
Qed.

Print Assumptions packet_fields_bounded_from_schema.
Print Assumptions read_packet_schema_fields.

Require Import BeePL_soundness_memory.

Theorem copy_packet_header_binding_typing :
  forall cenv Gamma Sigma m bytes sid co fields header body ef rt,
  Maps.PTree.get sid cenv = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env cenv) (bcomposite_ccomposite co) ->
  co.(co_su) = Ctypes.Struct ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun field => exists pt,
    snd field = Vtype pt /\
    Ctypes.field_type (fst field) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype pt))) fields ->
  Z.of_nat (List.length bytes) = co.(co_sizeof) ->
  initialized_packet_contents bytes ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  type_expr cenv (pattern_context Gamma (Pbytes header (Stype sid Ctypes.noattr) fields) Bytes)
    Sigma body ef rt ->
  exists copied block values body',
    copy_packet_header m bytes = Some (copied, block) /\
    read_packet_fields (bcomposite_composite_env cenv) (bmembers_cmembers co.(co_members))
      copied block fields = OK values /\
    instantiate_bytes_header header (Stype sid Ctypes.noattr) fields (Vloc block Ptrofs.zero)
      values body = OK body' /\
    store_context_extends Sigma (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma) /\
    type_expr cenv Gamma (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma) body' ef rt.
Proof.
  intros cenv Gamma Sigma m bytes sid co fields header body ef rt Hco Hconsistent Hstruct
    Hplain Hfields Hsize Hinit Hvalid Hbody.
  destruct (copy_packet_header_total m bytes)
    as [allocated [copied [block [Halloc [Hstore [Hcopy Hload]]]]]].
  assert (Hfresh : Maps.PTree.get block Sigma = None).
  { destruct (Maps.PTree.get block Sigma) as [ty |] eqn:Hentry; [|reflexivity].
    exfalso. eapply Mem.fresh_block_alloc; [exact Halloc |]. eapply Hvalid; exact Hentry. }
  assert (Hextends : store_context_extends Sigma (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma))
    by (apply store_context_extends_fresh; exact Hfresh).
  assert (Hheader : type_expr cenv Gamma (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma)
    (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) nil (Stype sid Ctypes.noattr)).
  { apply ty_valstruct. rewrite Ptrofs.unsigned_zero.
    change (object_type_at cenv (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma) block 0
      (stored_object_type (Stype sid Ctypes.noattr))).
    apply object_type_root; [apply Maps.PTree.gss |].
    simpl. rewrite Hco. rewrite <- Hsize. lia. }
  pose proof (proj2 typing_store_extension _ _ _ _ _ _ Hbody _ Hextends) as Hbody'.
  rewrite Hsize in Hload.
  destruct (read_packet_schema_fields (bcomposite_composite_env cenv) co fields copied block
    bytes cenv Gamma (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma)
    Hconsistent Hstruct Hplain Hfields Hload Hinit) as [values [Hread Hvalues]].
  destruct (instantiate_bytes_header_preserves_typing cenv Gamma
    (Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma) header (Stype sid Ctypes.noattr) fields
    (Vloc block Ptrofs.zero) values body ef rt Hheader Hvalues Hbody')
    as [body' [Hinstantiate Htyped]].
  exists copied, block, values, body'. repeat split; assumption.
Qed.

Print Assumptions copy_packet_header_binding_typing.

Lemma packet_schema_layout_facts : forall cenv sid fields,
  packet_schema_valid cenv sid fields ->
  exists co, Maps.PTree.get sid cenv = Some co /\
    co.(co_su) = Ctypes.Struct /\
    plain_members (bmembers_cmembers co.(co_members)) /\
    Forall (fun field => exists pt, snd field = Vtype pt /\
      Ctypes.field_type (fst field) (bmembers_cmembers co.(co_members)) =
        OK (transBeePL_type (Vtype pt))) fields.
Proof.
  intros cenv sid fields [co [Hco [Hstruct [Hmembers [Hfields Hstorage]]]]].
  exists co. split; [exact Hco |]. split; [exact Hstruct |]. split.
  - clear Hfields. induction Hmembers as [|member members Hmember Hmembers IH].
    + constructor.
    + destruct Hmember as [name [pt Heq]]; subst member. constructor; [|exact IH].
      exists name, (transBeePL_type (Vtype pt)); reflexivity.
  - eapply Forall_impl; [|exact Hfields].
    intros field [pt [Hty Hlookup]]. exists pt. split; [exact Hty |].
    apply packet_member_type_translation; exact Hlookup.
Qed.

Theorem typed_bytes_match_field_bounds :
  forall p Gamma Sigma scrutinee header sid fields rest yes no rt ef,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Match scrutinee (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  exists co, Maps.PTree.get sid p.(prog_comp_env) = Some co /\
    packet_fields_bounded (bcomposite_composite_env p.(prog_comp_env))
      (bmembers_cmembers co.(co_members)) co.(co_sizeof) fields.
Proof.
  intros p Gamma Sigma scrutinee header sid fields rest yes no rt ef Htyped.
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  inversion Hschemas as [|? ? Hschema Hrest]; subst.
  destruct (packet_schema_layout_facts _ _ _ Hschema)
    as [co [Hco [Hstruct [Hplain Hfields]]]].
  exists co. split; [exact Hco |].
  eapply packet_fields_bounded_from_schema; eauto.
  eapply program_composites_consistent; exact Hco.
Qed.

Print Assumptions packet_schema_layout_facts.
Print Assumptions typed_bytes_match_field_bounds.

Theorem typed_bytes_match_fields_total :
  forall p Gamma Sigma scrutinee header sid fields rest yes no rt ef co m block bytes,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Match scrutinee (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  Maps.PTree.get sid p.(prog_comp_env) = Some co ->
  Mem.loadbytes m block 0 co.(co_sizeof) = Some bytes ->
  initialized_packet_contents bytes ->
  exists values,
    read_packet_fields (bcomposite_composite_env p.(prog_comp_env))
      (bmembers_cmembers co.(co_members)) m block fields = OK values /\
    typed_field_values p.(prog_comp_env) Gamma Sigma fields values.
Proof.
  intros p Gamma Sigma scrutinee header sid fields rest yes no rt ef co m block bytes
    Htyped Hco Hload Hinit.
  destruct (typed_bytes_match_field_bounds _ _ _ _ _ _ _ _ _ _ _ _ Htyped)
    as [actual [Hactual Hbounds]].
  assert (actual = co) by congruence. subst actual.
  eapply read_packet_fields_total; eauto.
Qed.

Print Assumptions typed_bytes_match_fields_total.

Lemma primitive_packet_member_names : forall members,
  Forall (fun member => exists name pt,
    member = BeeTypes.Member_plain name (Vtype pt)) members ->
  forall name, In name (packet_member_names members) ->
    exists pt, packet_member_type name members = Some (Vtype pt).
Proof.
  intros members Hmembers. induction Hmembers as [|member members Hmember Hmembers IH];
    intros name Hin; [inversion Hin |].
  destruct Hmember as [id [pt Heq]]; subst member.
  simpl in Hin |- *. destruct (ident_eq name id) as [Heq | Hneq].
  - exists pt; reflexivity.
  - apply IH. destruct Hin as [Heq | Hin]; [congruence | exact Hin].
Qed.

Theorem packet_boolean_offsets_total : forall names env co,
  Ctypes.composite_consistent env (bcomposite_ccomposite co) ->
  co.(co_su) = Ctypes.Struct ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun name => exists pt,
    packet_member_type name co.(co_members) = Some (Vtype pt)) names ->
  exists offsets,
    packet_boolean_offsets env co.(co_members) names = OK offsets /\
    Forall (fun offset => 0 <= offset < co.(co_sizeof)) offsets /\
    (forall name, In name names ->
      packet_member_type name co.(co_members) = Some (Vtype Tbool) ->
      exists offset, Ctypes.field_offset env name (bmembers_cmembers co.(co_members)) =
        OK (offset, Ctypes.Full) /\ In offset offsets).
Proof.
  induction names as [|name names IH]; intros env co Hconsistent Hstruct Hplain Hnames.
  - exists nil. split; [reflexivity |]. split; [constructor | intros name Hin; inversion Hin].
  - inversion Hnames as [|? ? Hname Hrest]; subst.
    destruct Hname as [pt Hlookup].
    destruct (IH env co Hconsistent Hstruct Hplain Hrest)
      as [offsets [Hoffsets [Hbounds Hcoverage]]].
    destruct pt as [|sz sign attr|sign attr].
    + pose proof (packet_member_type_translation _ _ _ Hlookup) as Htype.
      destruct (plain_field_offset_exists env (bmembers_cmembers co.(co_members)) name
        (transBeePL_type (Vtype Tbool)) Hplain Htype 0) as [offset Hoffset].
      change (Ctypes.field_offset env name (bmembers_cmembers co.(co_members)) =
        OK (offset, Ctypes.Full)) in Hoffset.
      pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Htype) as [Hlo Hhi].
      pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as Hsize.
      exists (offset :: offsets). split.
      * cbn [packet_boolean_offsets]. rewrite Hlookup, Hoffsets, Hoffset. reflexivity.
      * split.
        -- constructor; [simpl in Hhi; lia | exact Hbounds].
        -- intros other [Heq | Hin] Hbool.
           ++ subst other. exists offset. split; [exact Hoffset | left; reflexivity].
           ++ destruct (Hcoverage other Hin Hbool) as [found [Hfound Hmember]].
              exists found. split; [exact Hfound | right; exact Hmember].
    + exists offsets. split.
      * cbn [packet_boolean_offsets]. rewrite Hlookup, Hoffsets. reflexivity.
      * split; [exact Hbounds |]. intros other [Heq | Hin] Hbool.
        -- subst other; congruence.
        -- apply Hcoverage; assumption.
    + exists offsets. split.
      * cbn [packet_boolean_offsets]. rewrite Hlookup, Hoffsets. reflexivity.
      * split; [exact Hbounds |]. intros other [Heq | Hin] Hbool.
        -- subst other; congruence.
        -- apply Hcoverage; assumption.
Qed.

Print Assumptions primitive_packet_member_names.
Print Assumptions packet_boolean_offsets_total.

Lemma packet_member_type_name : forall members name ty,
  packet_member_type name members = Some ty -> In name (packet_member_names members).
Proof.
  induction members as [|member members IH]; intros name ty Hlookup; [discriminate |].
  destruct member as [id declared |id sz sign attr width padding]; [|discriminate].
  simpl in Hlookup |- *. destruct (ident_eq name id) as [Heq | Hneq].
  - left; symmetry; exact Heq.
  - right. eapply IH; exact Hlookup.
Qed.

Theorem prepare_packet_header_total : forall cenv sid fields co m bytes,
  packet_schema_valid cenv sid fields ->
  Maps.PTree.get sid cenv = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env cenv) (bcomposite_ccomposite co) ->
  Z.of_nat (List.length bytes) = co.(co_sizeof) ->
  initialized_packet_contents bytes ->
  exists prepared block,
    prepare_packet_header (bcomposite_composite_env cenv) co.(co_members) m bytes =
      OK (prepared, block) /\
    initialized_writable_packet_buffer prepared block co.(co_sizeof) /\
    ~ Mem.valid_block m block /\
    (forall name, packet_member_type name co.(co_members) = Some (Vtype Tbool) ->
      exists offset flag,
        Ctypes.field_offset (bcomposite_composite_env cenv) name
          (bmembers_cmembers co.(co_members)) = OK (offset, Ctypes.Full) /\
        Mem.load Mbool prepared block offset = Some (Values.Val.of_bool flag)).
Proof.
  intros cenv sid fields co m bytes Hschema Hco Hconsistent Hsize Hinit.
  destruct (packet_schema_layout_facts _ _ _ Hschema)
    as [actual [Hactual [Hstruct [Hplain Hfields]]]].
  assert (actual = co) by congruence; subst actual.
  destruct Hschema as [declared [Hdeclared [_ [Hmembers _]]]].
  assert (declared = co) by congruence; subst declared.
  assert (Hnames : Forall (fun name => exists pt,
    packet_member_type name co.(co_members) = Some (Vtype pt))
      (packet_member_names co.(co_members))).
  { apply Forall_forall. intros name Hin. eapply primitive_packet_member_names; eauto. }
  destruct (packet_boolean_offsets_total (packet_member_names co.(co_members))
    (bcomposite_composite_env cenv) co Hconsistent Hstruct Hplain Hnames)
    as [offsets [Hoffsets [Hbounds Hcoverage]]].
  destruct (copy_packet_header_total m bytes)
    as [allocated [copied [block [Halloc [Hstore [Hcopy Hload]]]]]].
  assert (Hbounds' : Forall (fun offset => 0 <= offset < Z.of_nat (List.length bytes)) offsets)
    by (rewrite Hsize; exact Hbounds).
  destruct (normalize_copied_packet_booleans m bytes copied block offsets Hcopy Hinit Hbounds')
    as [prepared [Hnormalize [Hbuffer Hcanonical]]].
  exists prepared, block. split.
  - unfold prepare_packet_header. rewrite Hoffsets, Hcopy, Hnormalize. reflexivity.
  - split; [rewrite <- Hsize; exact Hbuffer |]. split.
    + eapply Mem.fresh_block_alloc; exact Halloc.
    + intros name Hbool.
      destruct (Hcoverage name (packet_member_type_name _ _ _ Hbool) Hbool)
        as [offset [Hoffset Hin]].
      destruct (Hcanonical offset Hin) as [flag Hflag].
      exists offset, flag. auto.
Qed.

Print Assumptions packet_member_type_name.
Print Assumptions prepare_packet_header_total.

Lemma prepare_packet_header_steps : forall env members m bytes prepared block,
  prepare_packet_header env members m bytes = OK (prepared, block) ->
  exists offsets copied,
    packet_boolean_offsets env members (packet_member_names members) = OK offsets /\
    copy_packet_header m bytes = Some (copied, block) /\
    normalize_packet_booleans copied block offsets = OK prepared.
Proof.
  intros env members m bytes prepared block Hprepare. unfold prepare_packet_header in Hprepare.
  destruct (packet_boolean_offsets env members (packet_member_names members))
    as [offsets | error] eqn:Hoffsets; try discriminate.
  destruct (copy_packet_header m bytes) as [[copied fresh] |] eqn:Hcopy; try discriminate.
  destruct (normalize_packet_booleans copied fresh offsets) as [normalized | error]
    eqn:Hnormalize; try discriminate.
  inversion Hprepare; subst. exists offsets, copied. auto.
Qed.

Theorem prepare_packet_header_preserves_old_bytes :
  forall env members m bytes prepared block old offset length,
  prepare_packet_header env members m bytes = OK (prepared, block) ->
  Mem.valid_block m old -> 0 <= length ->
  Mem.loadbytes prepared old offset length = Mem.loadbytes m old offset length.
Proof.
  intros env members m bytes prepared block old offset length Hprepare Hold Hlength.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  assert (Hdifferent : old <> block).
  { intro Heq; subst old. eapply Mem.fresh_block_alloc; eassumption. }
  rewrite (normalize_packet_booleans_preserves_other_bytes offsets copied block prepared
    old offset length Hnormalize).
  - eapply copy_packet_header_preserves_old_bytes; eauto.
  - apply Forall_forall. intros; left; exact Hdifferent.
Qed.

Print Assumptions prepare_packet_header_preserves_old_bytes.

Lemma normalize_packet_booleans_unchanged_on : forall offsets P m block after,
  (forall offset, ~ P block offset) ->
  normalize_packet_booleans m block offsets = OK after ->
  Mem.unchanged_on P m after.
Proof.
  induction offsets as [|offset offsets IH]; intros P m block after Houtside Hnormalize.
  - inversion Hnormalize; subst. apply Mem.unchanged_on_refl.
  - cbn [normalize_packet_booleans] in Hnormalize.
    destruct (normalize_packet_boolean m block offset) as [[next flag] |error] eqn:Hnext;
      try discriminate.
    eapply Mem.unchanged_on_trans.
    + eapply Mem.store_unchanged_on.
      * eapply normalize_packet_boolean_store; exact Hnext.
      * intros; apply Houtside.
    + eapply IH; eauto.
Qed.

Theorem prepare_packet_header_unchanged_old : forall env members m bytes after block,
  prepare_packet_header env members m bytes = OK (after, block) ->
  Mem.unchanged_on (fun old _ => Mem.valid_block m old) m after.
Proof.
  intros env members m bytes after block Hprepare.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  assert (Hfresh : ~ Mem.valid_block m block) by (eapply Mem.fresh_block_alloc; exact Halloc).
  eapply Mem.unchanged_on_trans.
  - eapply Mem.alloc_unchanged_on; exact Halloc.
  - eapply Mem.unchanged_on_trans.
    + eapply Mem.storebytes_unchanged_on; [exact Hstore | intros; exact Hfresh].
    + eapply normalize_packet_booleans_unchanged_on; [intros; exact Hfresh | exact Hnormalize].
Qed.

Theorem execute_packet_match_unchanged_old :
  forall cenv m descriptor offset sid header rest fields yes no after body,
  execute_packet_match cenv m descriptor offset sid header rest fields yes no = OK (after, body) ->
  Mem.unchanged_on (fun old _ => Mem.valid_block m old) m after.
Proof.
  intros cenv m descriptor offset sid header rest fields yes no after body Hexecute.
  unfold execute_packet_match in Hexecute.
  destruct (Maps.PTree.get sid cenv) as [co |]; try discriminate.
  destruct (read_packet_header m descriptor offset (co_sizeof co)) as [result |]; try discriminate.
  destruct result as [view bytes |view].
  - destruct (prepare_packet_header (bcomposite_composite_env cenv) (co_members co) m bytes)
      as [[prepared block] |error] eqn:Hprepare; try discriminate.
    destruct (read_packet_fields (bcomposite_composite_env cenv)
      (bmembers_cmembers (co_members co)) prepared block fields) as [values |error]; try discriminate.
    destruct (instantiate_bytes_header header (Stype sid Ctypes.noattr) fields
      (Vloc block Ptrofs.zero) values yes) as [result |error]; try discriminate.
    inversion Hexecute; subst. eapply prepare_packet_header_unchanged_old; exact Hprepare.
  - inversion Hexecute; subst. apply Mem.unchanged_on_refl.
Qed.

Print Assumptions execute_packet_match_unchanged_old.

Lemma prepare_packet_header_valid_store : forall env members m bytes after block (Sigma : store_context) ty,
  prepare_packet_header env members m bytes = OK (after, block) ->
  (forall old t, Maps.PTree.get old Sigma = Some t -> Mem.valid_block m old) ->
  forall old t, Maps.PTree.get old (Maps.PTree.set block ty Sigma) = Some t ->
    Mem.valid_block after old.
Proof.
  intros env members m bytes after block Sigma ty Hprepare Hvalid old t Hentry.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  destruct (Pos.eq_dec old block) as [Heq |Hneq].
  - subst old. eapply Mem.valid_block_unchanged_on.
    + eapply normalize_packet_booleans_unchanged_on with (P := fun _ _ => False);
        [tauto | exact Hnormalize].
    + eapply Mem.storebytes_valid_block_1; [exact Hstore |].
      eapply Mem.valid_new_block; exact Halloc.
  - rewrite Maps.PTree.gso in Hentry by exact Hneq.
    eapply Mem.valid_block_unchanged_on.
    + eapply prepare_packet_header_unchanged_old; exact Hprepare.
    + eapply Hvalid; exact Hentry.
Qed.

Theorem execute_packet_match_typed_total :
  forall cenv Gamma Sigma m descriptor offset view sid header rest fields yes no yesEffect noEffect rt,
  packet_schema_valid cenv sid fields ->
  source_composites_consistent cenv ->
  packet_descriptor_valid m descriptor offset view ->
  (forall size packet bytes,
    read_packet_header m descriptor offset size = Some (PacketHeaderFits packet bytes) ->
    initialized_packet_contents bytes) ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  type_expr cenv Gamma Sigma (Val (Vloc descriptor offset) Bytes) nil Bytes ->
  type_expr cenv (pattern_context Gamma (Pbytes header (Stype sid Ctypes.noattr) fields) Bytes)
    Sigma yes yesEffect rt ->
  type_expr cenv (pattern_context Gamma (Pbytes rest Bytes nil) Bytes) Sigma no noEffect rt ->
  exists after body Sigma' effect,
    execute_packet_match cenv m descriptor offset sid header rest fields yes no = OK (after, body) /\
    store_context_extends Sigma Sigma' /\
    type_expr cenv Gamma Sigma' body effect rt /\
    (effect = yesEffect \/ effect = noEffect) /\
    (forall block ty, Maps.PTree.get block Sigma' = Some ty -> Mem.valid_block after block).
Proof.
  intros cenv Gamma Sigma m descriptor offset view sid header rest fields yes no yesEffect noEffect rt
    Hschema Hconsistent Hdescriptor Hinitialized Hvalid Hbytes Hyes Hno.
  destruct (packet_schema_layout_facts _ _ _ Hschema)
    as [co [Hco [Hstruct [Hplain Hfields]]]].
  destruct (read_packet_header_total m descriptor offset view (co_sizeof co) Hdescriptor)
    as [result Hread].
  destruct result as [packet bytes | packet].
  - pose proof (Hinitialized _ _ _ Hread) as Hinit.
    destruct (read_packet_header_success _ _ _ _ _ _ Hread) as [_ [_ Hload]].
    pose proof (Mem.loadbytes_length _ _ _ _ _ Hload) as Hlength.
    assert (Hsize : Z.of_nat (List.length bytes) = co_sizeof co).
    { rewrite Hlength, Z2Nat.id; [reflexivity | pose proof (co_sizeof_pos co); lia]. }
    destruct (prepare_packet_header_total cenv sid fields co m bytes Hschema Hco
      (Hconsistent sid co Hco) Hsize Hinit)
      as [prepared [block [Hprepare [Hbuffer [Hfresh Hbooleans]]]]].
    assert (HfreshSigma : Maps.PTree.get block Sigma = None).
    { destruct (Maps.PTree.get block Sigma) as [ty |] eqn:Hentry; [|reflexivity].
      exfalso. apply Hfresh. eapply Hvalid; exact Hentry. }
    set (Sigma' := Maps.PTree.set block (Stype sid Ctypes.noattr) Sigma).
    assert (Hextends : store_context_extends Sigma Sigma')
      by (apply store_context_extends_fresh; exact HfreshSigma).
    assert (Hheader : type_expr cenv Gamma Sigma'
      (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) nil (Stype sid Ctypes.noattr)).
    { apply ty_valstruct. rewrite Ptrofs.unsigned_zero.
      change (object_type_at cenv Sigma' block 0 (stored_object_type (Stype sid Ctypes.noattr))).
      apply object_type_root; [apply Maps.PTree.gss |].
      simpl. rewrite Hco. pose proof (co_sizeof_pos co); lia. }
    destruct Hbuffer as [[preparedBytes [HpreparedBytes HpreparedInit]] Hwrite].
    destruct (read_packet_schema_fields (bcomposite_composite_env cenv) co fields prepared block
      preparedBytes cenv Gamma Sigma' (Hconsistent sid co Hco) Hstruct Hplain Hfields
      HpreparedBytes HpreparedInit) as [values [Hvalues HtypedValues]].
    pose proof (proj2 typing_store_extension _ _ _ _ _ _ Hyes _ Hextends) as Hyes'.
    destruct (instantiate_bytes_header_preserves_typing cenv Gamma Sigma' header
      (Stype sid Ctypes.noattr) fields (Vloc block Ptrofs.zero) values yes yesEffect rt
      Hheader HtypedValues Hyes') as [body [Hinstantiate Htyped]].
    exists prepared, body, Sigma', yesEffect. split.
    + unfold execute_packet_match. rewrite Hco, Hread, Hprepare, Hvalues, Hinstantiate. reflexivity.
    + split; [exact Hextends |]. split; [exact Htyped |]. split; [left; reflexivity |].
      eapply prepare_packet_header_valid_store; eauto.
  - exists m, (subst rest (Val (Vloc descriptor offset) Bytes) no), Sigma, noEffect.
    split; [unfold execute_packet_match; rewrite Hco, Hread; reflexivity |].
    split; [apply store_context_extends_refl |]. split; [|split; [right; reflexivity |exact Hvalid]].
    eapply value_substitution_preserves_typing; [exact Hno | exact Hbytes].
Qed.

Print Assumptions execute_packet_match_typed_total.

Require Import BeePL_sem.

Theorem packet_match_value_progress :
  forall bge p Gamma Sigma m vm descriptor offset view sid header rest fields yes no rt ef,
  type_expr bge.(genv_cenv) Gamma Sigma
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  source_composites_consistent bge.(genv_cenv) ->
  packet_descriptor_valid m descriptor offset view ->
  (forall size packet bytes,
    read_packet_header m descriptor offset size = Some (PacketHeaderFits packet bytes) ->
    initialized_packet_contents bytes) ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  exists after body Sigma' effect,
    execute_packet_match bge.(genv_cenv) m descriptor offset sid header rest fields yes no =
      OK (after, body) /\
    ssem_expr bge p vm m
      (Match (Val (Vloc descriptor offset) Bytes)
        (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
        (yes :: no :: nil) rt) after vm body /\
    store_context_extends Sigma Sigma' /\
    type_expr bge.(genv_cenv) Gamma Sigma' body effect rt /\ sub_effect effect ef = true /\
    (forall block ty, Maps.PTree.get block Sigma' = Some ty -> Mem.valid_block after block).
Proof.
  intros bge p Gamma Sigma m vm descriptor offset view sid header rest fields yes no rt ef
    Htyped Hconsistent Hdescriptor Hinitialized Hvalid.
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  inversion Hschemas as [|? ? Hschema Hrest]; subst.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hscrut) as Hte.
  cbn [typeof_expr] in Hte; subst te.
  pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hscrut) as Hnil; subst efe.
  simpl in Heffect; subst ef.
  pose proof (Hbranches 0%nat _ _ eq_refl eq_refl) as Hyes.
  pose proof (Hbranches 1%nat _ _ eq_refl eq_refl) as Hno.
  destruct (execute_packet_match_typed_total (genv_cenv bge) Gamma Sigma m descriptor offset view
    sid header rest fields yes no (effects 0%nat) (effects 1%nat) rt
    Hschema Hconsistent Hdescriptor Hinitialized Hvalid Hscrut Hyes Hno)
    as [after [body [Sigma' [effect [Hexecute [Hextends [Hbody [Hchoice HvalidAfter]]]]]]]].
  exists after, body, Sigma', effect. split; [exact Hexecute |].
  split; [apply ssem_match_bytes; exact Hexecute |].
  split; [exact Hextends |]. split; [exact Hbody |]. split; [|exact HvalidAfter].
  destruct Hchoice as [Heq | Heq]; subst effect.
  - apply (Heffects 0%nat); reflexivity.
  - apply (Heffects 1%nat); reflexivity.
Qed.

Print Assumptions packet_match_value_progress.

Lemma packet_match_value_step_result :
  forall bge p vm m descriptor offset sid header rest fields yes no rt after vm' body,
  ssem_expr bge p vm m
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) after vm' body ->
  execute_packet_match bge.(genv_cenv) m descriptor offset sid header rest fields yes no =
    OK (after, body) /\ vm' = vm.
Proof.
  intros bge p vm m descriptor offset sid header rest fields yes no rt after vm' body Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - split; [assumption | reflexivity].
Qed.

Theorem execute_packet_match_preserves_old_bytes :
  forall cenv m descriptor offset sid header rest fields yes no after body old start length,
  execute_packet_match cenv m descriptor offset sid header rest fields yes no = OK (after, body) ->
  Mem.valid_block m old -> 0 <= length ->
  Mem.loadbytes after old start length = Mem.loadbytes m old start length.
Proof.
  intros cenv m descriptor offset sid header rest fields yes no after body old start length
    Hexecute Hold Hlength.
  unfold execute_packet_match in Hexecute.
  destruct (Maps.PTree.get sid cenv) as [co |] eqn:Hco; try discriminate.
  destruct (read_packet_header m descriptor offset (co_sizeof co)) as [result |] eqn:Hread;
    try discriminate.
  destruct result as [view bytes | view].
  - destruct (prepare_packet_header (bcomposite_composite_env cenv) (co_members co) m bytes)
      as [[prepared block] | error] eqn:Hprepare; try discriminate.
    destruct (read_packet_fields (bcomposite_composite_env cenv)
      (bmembers_cmembers (co_members co)) prepared block fields) as [values | error]; try discriminate.
    destruct (instantiate_bytes_header header (Stype sid Ctypes.noattr) fields
      (Vloc block Ptrofs.zero) values yes) as [result | error]; try discriminate.
    inversion Hexecute; subst. eapply prepare_packet_header_preserves_old_bytes; eauto.
  - inversion Hexecute; subst; reflexivity.
Qed.

Theorem packet_match_value_preservation :
  forall bge p Gamma Sigma m vm descriptor offset view sid header rest fields yes no rt ef after vm' body,
  type_expr bge.(genv_cenv) Gamma Sigma
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  source_composites_consistent bge.(genv_cenv) ->
  packet_descriptor_valid m descriptor offset view ->
  (forall size packet bytes,
    read_packet_header m descriptor offset size = Some (PacketHeaderFits packet bytes) ->
    initialized_packet_contents bytes) ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  ssem_expr bge p vm m
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) after vm' body ->
  exists Sigma' effect,
    store_context_extends Sigma Sigma' /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma' body effect rt /\ sub_effect effect ef = true /\
    (forall old start length, Mem.valid_block m old -> 0 <= length ->
      Mem.loadbytes after old start length = Mem.loadbytes m old start length) /\
    (forall block ty, Maps.PTree.get block Sigma' = Some ty -> Mem.valid_block after block).
Proof.
  intros bge p Gamma Sigma m vm descriptor offset view sid header rest fields yes no rt ef
    after vm' body Htyped Hconsistent Hdescriptor Hinitialized Hvalid Hstep.
  destruct (packet_match_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hactual Hvm].
  destruct (packet_match_value_progress bge p Gamma Sigma m vm descriptor offset view
    sid header rest fields yes no rt ef Htyped Hconsistent Hdescriptor Hinitialized Hvalid)
    as [chosenM [chosenBody [Sigma' [effect [Hexecute [Hchosen [Hextends [Hbody [Heffect HvalidAfter]]]]]]]]].
  rewrite Hactual in Hexecute. inversion Hexecute; subst chosenM chosenBody.
  exists Sigma', effect. split; [exact Hextends |]. split; [exact Hvm |].
  split; [exact Hbody |]. split; [exact Heffect |]. split; [|exact HvalidAfter].
  intros old start length Hold Hlength. eapply execute_packet_match_preserves_old_bytes; eauto.
Qed.

Print Assumptions packet_match_value_step_result.
Print Assumptions packet_match_value_preservation.

Definition initialized_packet_state (m : Mem.mem) (descriptor : Values.block)
    (offset : ptrofs) (view : packet_view) : Prop :=
  packet_descriptor_valid m descriptor offset view /\
  exists bytes, Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some bytes /\
    initialized_packet_contents bytes.

Theorem initialized_packet_state_header : forall m descriptor offset view size packet bytes,
  initialized_packet_state m descriptor offset view ->
  read_packet_header m descriptor offset size = Some (PacketHeaderFits packet bytes) ->
  initialized_packet_contents bytes.
Proof.
  intros m descriptor offset view size packet bytes [Hdescriptor [allBytes [Hall Hinit]]] Hread.
  destruct (read_packet_header_success _ _ _ _ _ _ Hread) as [Hview [Hfits Hload]].
  pose proof (read_packet_view_total _ _ _ _ Hdescriptor) as Hview'.
  assert (packet = view) by congruence; subst packet.
  apply packet_header_fits_spec in Hfits.
  destruct (initialized_packet_subrange m (packet_block view) (Ptrofs.unsigned (packet_first view))
    (Ptrofs.unsigned (packet_last view) - Ptrofs.unsigned (packet_first view)) allBytes 0 size
    Hall Hinit ltac:(lia) ltac:(lia) ltac:(lia)) as [headerBytes [Hheader HheaderInit]].
  rewrite Z.add_0_r in Hheader. assert (headerBytes = bytes) by congruence; subst; exact HheaderInit.
Qed.

Theorem initialized_packet_state_unchanged : forall m after descriptor offset view,
  Mem.unchanged_on (fun old _ => Mem.valid_block m old) m after ->
  initialized_packet_state m descriptor offset view ->
  initialized_packet_state after descriptor offset view.
Proof.
  intros m after descriptor offset view Hunchanged
    [[Hfirst [Hlast [Horder [Hblock Hrange]]]] [bytes [Hbytes Hinit]]].
  assert (Hdescriptor : Mem.valid_block m descriptor).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies.
    - eapply Mem.load_valid_access; exact Hfirst.
    - constructor. }
  split.
  - split.
    + eapply Mem.load_unchanged_on; [exact Hunchanged | intros; exact Hdescriptor | exact Hfirst].
    + split.
      * eapply Mem.load_unchanged_on; [exact Hunchanged | intros; exact Hdescriptor | exact Hlast].
      * split; [exact Horder |]. split.
        -- eapply Mem.valid_block_unchanged_on; eauto.
        -- intros i Hi. eapply Mem.perm_unchanged_on; [exact Hunchanged |exact Hblock |].
           apply Hrange; exact Hi.
  - exists bytes. split; [|exact Hinit].
    eapply Mem.loadbytes_unchanged_on; [exact Hunchanged |intros; exact Hblock |exact Hbytes].
Qed.

Theorem packet_match_preserves_packet_state :
  forall cenv m descriptor offset sid header rest fields yes no after body other otherOffset view,
  execute_packet_match cenv m descriptor offset sid header rest fields yes no = OK (after, body) ->
  initialized_packet_state m other otherOffset view ->
  initialized_packet_state after other otherOffset view.
Proof.
  intros. eapply initialized_packet_state_unchanged; [|eassumption].
  eapply execute_packet_match_unchanged_old; eassumption.
Qed.

Print Assumptions initialized_packet_state_header.
Print Assumptions packet_match_preserves_packet_state.

Require Import BeePL_soundness_store.

Theorem packet_match_preserves_old_layout :
  forall cenv Gamma Sigma layout bge p m vm descriptor offset view sid header rest fields yes no rt ef
    after vm' body,
  bge.(genv_cenv) = cenv ->
  type_expr cenv Gamma Sigma
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  source_composites_consistent cenv ->
  initialized_packet_state m descriptor offset view ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) after vm' body ->
  exists Sigma' effect,
    store_context_extends Sigma Sigma' /\
    type_expr cenv Gamma Sigma' body effect rt /\ sub_effect effect ef = true /\
    typed_memory_layout cenv Sigma' layout after /\
    (forall other otherOffset otherView, initialized_packet_state m other otherOffset otherView ->
      initialized_packet_state after other otherOffset otherView) /\
    (forall block ty, Maps.PTree.get block Sigma' = Some ty -> Mem.valid_block after block).
Proof.
  intros cenv Gamma Sigma layout bge p m vm descriptor offset view sid header rest fields yes no rt ef
    after vm' body Henv Htyped Hconsistent Hpacket Hvalid Hmemory Hstep.
  subst cenv.
  destruct (packet_match_value_preservation bge p Gamma Sigma m vm descriptor offset view
    sid header rest fields yes no rt ef after vm' body Htyped Hconsistent (proj1 Hpacket)
    ltac:(intros; eapply initialized_packet_state_header; eauto) Hvalid Hstep)
    as [Sigma' [effect [Hextends [Hvm [Hbody [Heffect [Hframe HvalidAfter]]]]]]].
  destruct (packet_match_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hexecute _].
  pose proof (execute_packet_match_unchanged_old _ _ _ _ _ _ _ _ _ _ _ _ Hexecute) as Hunchanged.
  exists Sigma', effect. split; [exact Hextends |]. split; [exact Hbody |].
  split; [exact Heffect |]. split.
  - eapply typed_memory_layout_unchanged_old; eauto.
  - split; [|exact HvalidAfter].
    intros. eapply initialized_packet_state_unchanged; eauto.
Qed.

Print Assumptions packet_match_preserves_old_layout.

Lemma normalize_packet_booleans_preserves_permissions : forall offsets m block after,
  normalize_packet_booleans m block offsets = OK after ->
  forall b offset kind permission, Mem.perm m b offset kind permission ->
    Mem.perm after b offset kind permission.
Proof.
  induction offsets as [|offset offsets IH]; intros m block after Hnormalize b i kind permission Hperm.
  - inversion Hnormalize; subst; exact Hperm.
  - cbn [normalize_packet_booleans] in Hnormalize.
    destruct (normalize_packet_boolean m block offset) as [[next flag] |error] eqn:Hnext;
      try discriminate.
    eapply IH; [exact Hnormalize |]. eapply Mem.perm_store_1; [|exact Hperm].
    eapply normalize_packet_boolean_store; exact Hnext.
Qed.

Theorem prepare_packet_header_freeable : forall env members m bytes after block,
  prepare_packet_header env members m bytes = OK (after, block) ->
  Mem.range_perm after block 0 (Z.of_nat (List.length bytes)) Cur Freeable.
Proof.
  intros env members m bytes after block Hprepare.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare)
    as [offsets [copied [Hoffsets [Hcopy Hnormalize]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc Hstore]].
  intros i Hi. eapply normalize_packet_booleans_preserves_permissions; [exact Hnormalize |].
  eapply Mem.perm_storebytes_1; [exact Hstore |]. eapply Mem.perm_alloc_2; eassumption.
Qed.

Lemma decode_initialized_nonboolean_scalar : forall pt bytes cenv Gamma Sigma,
  pt <> Tbool -> initialized_packet_contents bytes ->
  exists v,
    decode_memory_value (Vtype pt)
      (Memdata.decode_val (transl_bchunk_cchunk (chunk_of_ptype pt)) bytes) = OK v /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros pt bytes cenv Gamma Sigma Hnotbool [raw Hraw].
  unfold Memdata.decode_val. rewrite Hraw.
  destruct pt as [|sz sign attr|sign attr]; [contradiction | |].
  - destruct sz, sign; (eexists; split; [reflexivity |apply ty_vali]).
  - destruct sign; (eexists; split; [reflexivity |apply ty_vall]).
Qed.

Print Assumptions prepare_packet_header_freeable.
Print Assumptions decode_initialized_nonboolean_scalar.

Theorem prepared_packet_field_cell :
  forall cenv Sigma sid fields co m bytes after block name pt delta,
  packet_schema_valid cenv sid fields ->
  Maps.PTree.get sid cenv = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env cenv) (bcomposite_ccomposite co) ->
  co.(co_sizeof) <= Ptrofs.max_unsigned ->
  Z.of_nat (List.length bytes) = co.(co_sizeof) ->
  initialized_packet_contents bytes ->
  prepare_packet_header (bcomposite_composite_env cenv) co.(co_members) m bytes = OK (after, block) ->
  packet_member_type name co.(co_members) = Some (Vtype pt) ->
  Ctypes.field_offset (bcomposite_composite_env cenv) name (bmembers_cmembers co.(co_members)) =
    OK (delta, Ctypes.Full) ->
  (align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) | delta) ->
  Ctypes.type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  typed_memory_cell cenv Sigma after block (Ptrofs.repr delta) (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros cenv Sigma sid fields co m bytes after block name pt delta Hschema Hco Hconsistent Hmax
    Hsize Hinit Hprepare Hlookup Hoffset Halign Hvolatile.
  destruct (packet_schema_layout_facts _ _ _ Hschema) as [actual [Hactual [Hstruct Hrest]]].
  assert (actual = co) by congruence; subst actual.
  pose proof (packet_member_type_translation _ _ _ Hlookup) as Htype.
  pose proof (primitive_field_offset_representable _ _ _ _ _
    Hconsistent Hstruct Hmax Hoffset Htype) as Hrepresent.
  pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Htype) as [Hlo Hhi].
  pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as HstructSize.
  assert (Hwithin : delta + size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) <= co_sizeof co).
  { rewrite (primitive_chunk_size_translation (bcomposite_composite_env cenv) pt).
    eapply Z.le_trans; [exact Hhi |exact HstructSize]. }
  destruct (prepare_packet_header_total cenv sid fields co m bytes Hschema Hco Hconsistent Hsize Hinit)
    as [prepared [fresh [Hprepared [Hbuffer [Hfresh Hbooleans]]]]].
  rewrite Hprepare in Hprepared. inversion Hprepared; subst prepared fresh.
  pose proof (prepare_packet_header_freeable _ _ _ _ _ _ Hprepare) as Hfreeable.
  rewrite Hsize in Hfreeable.
  destruct Hbuffer as [[preparedBytes [Hbytes Hinitialized]] Hwrite].
  constructor; [apply primitive_chunk_access |exact Hvolatile | |].
  - rewrite Ptrofs.unsigned_repr by exact Hrepresent. split; [|exact Halign].
    intros i Hi. apply Hfreeable; lia.
  - rewrite Ptrofs.unsigned_repr by exact Hrepresent.
    assert (Hcase : pt = Tbool \/ pt <> Tbool).
    { destruct pt; [left; reflexivity |right; discriminate |right; discriminate]. }
    destruct Hcase as [Heq |Hnotbool].
    + subst pt. destruct (Hbooleans name Hlookup) as [actual [flag [HactualOffset Hload]]].
      assert (actual = delta) by congruence; subst actual.
      exists (Values.Val.of_bool flag), (Vbool flag). split; [exact Hload |].
      split; [destruct flag; reflexivity |apply ty_valb].
    + destruct (initialized_packet_subrange after block 0 (co_sizeof co) preparedBytes delta
        (size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt))) Hbytes Hinitialized Hlo
        ltac:(pose proof (size_chunk_pos (transl_bchunk_cchunk (chunk_of_ptype pt))); lia) Hwithin)
        as [fieldBytes [Hfield HfieldInit]].
      replace (0 + delta) with delta in Hfield by lia.
      destruct (decode_initialized_nonboolean_scalar pt fieldBytes cenv empty_context Sigma Hnotbool HfieldInit)
        as [v [Hdecode Htyped]].
      exists (Memdata.decode_val (transl_bchunk_cchunk (chunk_of_ptype pt)) fieldBytes), v.
      split; [eapply Mem.loadbytes_load; eassumption |]. split; assumption.
Qed.

Print Assumptions prepared_packet_field_cell.

Definition packet_header_layout (old : scalar_layout) (cenv : bcomposite_env)
    (co : bcomposite) (headerBlock : Values.block) : scalar_layout :=
  fun block offset ty chunk => old block offset ty chunk \/
    exists name pt delta,
      block = headerBlock /\ offset = Ptrofs.repr delta /\ ty = Vtype pt /\ chunk = chunk_of_ptype pt /\
      packet_member_type name co.(co_members) = Some (Vtype pt) /\
      Ctypes.field_offset (bcomposite_composite_env cenv) name (bmembers_cmembers co.(co_members)) =
        OK (delta, Ctypes.Full).

Theorem prepare_packet_header_typed_layout :
  forall cenv Sigma Sigma' layout sid fields co m bytes after block,
  packet_schema_valid cenv sid fields ->
  Maps.PTree.get sid cenv = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env cenv) (bcomposite_ccomposite co) ->
  co.(co_sizeof) <= Ptrofs.max_unsigned ->
  Archi.align_int64 = 8 ->
  (forall name pt, packet_member_type name co.(co_members) = Some (Vtype pt) ->
    Ctypes.attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) = None /\
    Ctypes.type_is_volatile (transBeePL_type (Vtype pt)) = false) ->
  Z.of_nat (List.length bytes) = co.(co_sizeof) ->
  initialized_packet_contents bytes ->
  prepare_packet_header (bcomposite_composite_env cenv) co.(co_members) m bytes = OK (after, block) ->
  typed_memory_layout cenv Sigma layout m ->
  store_context_extends Sigma Sigma' ->
  typed_memory_layout cenv Sigma' (packet_header_layout layout cenv co block) after.
Proof.
  intros cenv Sigma Sigma' layout sid fields co m bytes after block Hschema Hco Hconsistent Hmax
    Harch Hattributes Hsize Hinit Hprepare Hmemory Hextends b ofs ty chunk Hentry.
  destruct Hentry as [Hold |[name [pt [delta [Hb [Hofs [Hty [Hchunk [Hlookup Hoffset]]]]]]]]].
  - eapply typed_memory_layout_unchanged_old; [exact Hmemory |exact Hextends | |exact Hold].
    eapply prepare_packet_header_unchanged_old; exact Hprepare.
  - subst b ofs ty chunk. destruct (Hattributes name pt Hlookup) as [HalignAttr Hvolatile].
    eapply prepared_packet_field_cell; eauto.
    rewrite <- (primitive_default_alignment (bcomposite_composite_env cenv) pt Harch HalignAttr).
    eapply Ctypes.field_offset_aligned; [exact Hoffset |].
    eapply packet_member_type_translation; exact Hlookup.
Qed.

Theorem prepared_packet_header_field_read :
  forall cenv Gamma Sigma layout co after block name pt delta,
  typed_memory_layout cenv Sigma (packet_header_layout layout cenv co block) after ->
  packet_member_type name co.(co_members) = Some (Vtype pt) ->
  Ctypes.field_offset (bcomposite_composite_env cenv) name (bmembers_cmembers co.(co_members)) =
    OK (delta, Ctypes.Full) ->
  exists v, deref_addr (Vtype pt) after block (Ptrofs.repr delta) Ctypes.Full v /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma layout co after block name pt delta Hmemory Hlookup Hoffset.
  eapply typed_memory_cell_read. apply Hmemory. right.
  exists name, pt, delta. repeat split; assumption || reflexivity.
Qed.

Print Assumptions prepare_packet_header_typed_layout.
Print Assumptions prepared_packet_header_field_read.

Lemma packet_member_type_source : forall members name ty,
  packet_member_type name members = Some ty -> source_member_type name members = OK ty.
Proof.
  induction members as [|member members IH]; intros name ty Hlookup; [discriminate |].
  destruct member as [id declared |id sz sign attr width padding]; [|discriminate].
  simpl in Hlookup |- *. destruct (ident_eq name id).
  - inversion Hlookup; subst; reflexivity.
  - eapply IH; exact Hlookup.
Qed.

Theorem prepared_header_field_progress :
  forall cenv Gamma Sigma layout co after block name pt delta sid bge p vm,
  bge.(genv_cenv) = cenv ->
  Maps.PTree.get sid cenv = Some co ->
  typed_memory_layout cenv Sigma (packet_header_layout layout cenv co block) after ->
  packet_member_type name co.(co_members) = Some (Vtype pt) ->
  Ctypes.field_offset (bcomposite_composite_env cenv) name (bmembers_cmembers co.(co_members)) =
    OK (delta, Ctypes.Full) ->
  exists v,
    ssem_expr bge p vm after
      (Sfield (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) name (Vtype pt))
      after vm (Val v (Vtype pt)) /\
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma layout co after block name pt delta sid bge p vm Henv Hco Hmemory Hlookup Hoffset.
  destruct (prepared_packet_header_field_read cenv Gamma Sigma layout co after block name pt delta
    Hmemory Hlookup Hoffset) as [v [Hread Htyped]].
  exists v. split; [|exact Htyped].
  eapply ssem_sfield_struct; [rewrite Henv; exact Hco |rewrite Henv; exact Hoffset |].
  rewrite Ptrofs.add_zero_l. exact Hread.
Qed.

Print Assumptions prepared_header_field_progress.

Theorem prepared_header_field_typing : forall cenv Gamma Sigma block sid co name pt,
  type_expr cenv Gamma Sigma (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) nil
    (Stype sid Ctypes.noattr) ->
  Maps.PTree.get sid cenv = Some co ->
  packet_member_type name co.(co_members) = Some (Vtype pt) ->
  type_expr cenv Gamma Sigma
    (Sfield (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) name (Vtype pt)) nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma block sid co name pt Hheader Hco Hlookup.
  eapply ty_sfield with (id := sid) (a := Ctypes.noattr) (co := co)
    (ct := Ctypes.change_attributes (Ctyping.attr_add_volatile false) (transBeePL_type (Vtype pt))).
  - exact Hheader.
  - left; simpl; rewrite Pos.eqb_refl; reflexivity.
  - exact Hco.
  - unfold Ctyping.type_of_member. rewrite (packet_member_type_translation _ _ _ Hlookup). reflexivity.
  - eapply packet_member_type_source; exact Hlookup.
Qed.

Theorem prepared_header_field_preservation :
  forall cenv Gamma Sigma layout co m block name pt delta sid bge p vm after vm' result,
  bge.(genv_cenv) = cenv ->
  Maps.PTree.get sid cenv = Some co ->
  typed_memory_layout cenv Sigma (packet_header_layout layout cenv co block) m ->
  packet_member_type name co.(co_members) = Some (Vtype pt) ->
  Ctypes.field_offset (bcomposite_composite_env cenv) name (bmembers_cmembers co.(co_members)) =
    OK (delta, Ctypes.Full) ->
  ssem_expr bge p vm m
    (Sfield (Val (Vloc block Ptrofs.zero) (Stype sid Ctypes.noattr)) name (Vtype pt)) after vm' result ->
  after = m /\ vm' = vm /\ type_expr cenv Gamma Sigma result nil (Vtype pt).
Proof.
  intros cenv Gamma Sigma layout co m block name pt delta sid bge p vm after vm' result
    Henv Hco Hmemory Hlookup Hoffset Hstep. subst cenv.
  assert (Hcell : typed_memory_cell (genv_cenv bge) Sigma m block (Ptrofs.repr delta)
    (Vtype pt) (chunk_of_ptype pt)).
  { apply Hmemory. right. exists name, pt, delta. repeat split; assumption || reflexivity. }
  inversion Hstep; subst.
  - exfalso; eapply value_has_no_small_step; eauto.
  - assert (co0 = co) by congruence; subst co0.
    assert (HfieldOffset : delta0 = delta /\ bf = Ctypes.Full) by (split; congruence).
    destruct HfieldOffset as [Hdelta Hbf]; subst delta0 bf.
    split; [reflexivity |]. split; [reflexivity |].
    eapply typed_memory_cell_read_preservation; [exact Hcell |].
    match goal with Hread : deref_addr _ _ _ (Ptrofs.add Ptrofs.zero _) _ _ |- _ =>
      rewrite Ptrofs.add_zero_l in Hread; exact Hread
    end.
  - match goal with Haccess : aggregate_field_access _ _ _ _ _ _ _ _ |- _ =>
      inversion Haccess; subst; discriminate
    end.
Qed.

Print Assumptions prepared_header_field_typing.
Print Assumptions prepared_header_field_preservation.

(* The resulting layout is determined by the actual packet branch. *)
Inductive packet_match_layout_result (cenv : bcomposite_env) (before : Mem.mem)
    (descriptor : Values.block) (offset : ptrofs) (sid : ident)
    (after : Mem.mem) (old : scalar_layout) : scalar_layout -> Prop :=
| packet_layout_short : forall co view,
    Maps.PTree.get sid cenv = Some co ->
    read_packet_header before descriptor offset co.(co_sizeof) = Some (PacketHeaderShort view) ->
    after = before -> packet_match_layout_result cenv before descriptor offset sid after old old
| packet_layout_prepared : forall co view bytes block,
    Maps.PTree.get sid cenv = Some co ->
    read_packet_header before descriptor offset co.(co_sizeof) = Some (PacketHeaderFits view bytes) ->
    prepare_packet_header (bcomposite_composite_env cenv) co.(co_members) before bytes = OK (after, block) ->
    packet_match_layout_result cenv before descriptor offset sid after old
      (packet_header_layout old cenv co block).

Theorem execute_packet_match_layout :
  forall cenv Sigma Sigma' layout m descriptor offset view sid header rest fields yes no after body,
  packet_schema_valid cenv sid fields ->
  source_composites_consistent cenv ->
  initialized_packet_state m descriptor offset view ->
  Archi.align_int64 = 8 ->
  (forall co name pt, Maps.PTree.get sid cenv = Some co ->
    packet_member_type name co.(co_members) = Some (Vtype pt) ->
    Ctypes.attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) = None /\
    Ctypes.type_is_volatile (transBeePL_type (Vtype pt)) = false) ->
  typed_memory_layout cenv Sigma layout m ->
  store_context_extends Sigma Sigma' ->
  execute_packet_match cenv m descriptor offset sid header rest fields yes no = OK (after, body) ->
  exists layout', packet_match_layout_result cenv m descriptor offset sid after layout layout' /\
    typed_memory_layout cenv Sigma' layout' after.
Proof.
  intros cenv Sigma Sigma' layout m descriptor offset view sid header rest fields yes no after body
    Hschema Hconsistent Hpacket Harch Hattributes Hmemory Hextends Hexecute.
  unfold execute_packet_match in Hexecute.
  destruct (Maps.PTree.get sid cenv) as [co |] eqn:Hco; try discriminate.
  destruct (read_packet_header m descriptor offset (co_sizeof co)) as [result |] eqn:Hread;
    try discriminate.
  destruct result as [packet bytes |packet].
  - destruct (prepare_packet_header (bcomposite_composite_env cenv) (co_members co) m bytes)
      as [[prepared block] |error] eqn:Hprepare; try discriminate.
    destruct (read_packet_fields (bcomposite_composite_env cenv)
      (bmembers_cmembers (co_members co)) prepared block fields) as [values |error]; try discriminate.
    destruct (instantiate_bytes_header header (Stype sid Ctypes.noattr) fields
      (Vloc block Ptrofs.zero) values yes) as [result |error]; try discriminate.
    inversion Hexecute; subst prepared result.
    exists (packet_header_layout layout cenv co block). split.
    + eapply packet_layout_prepared; eauto.
    + destruct (read_packet_header_success _ _ _ _ _ _ Hread) as [Hview [Hfits Hload]].
      destruct (packet_header_bounds _ _ Hfits) as [Hfirst [Hnonnegative [Hend [Hmax Hrepr]]]].
      pose proof (Mem.loadbytes_length _ _ _ _ _ Hload) as Hlength.
      eapply prepare_packet_header_typed_layout.
      * exact Hschema.
      * exact Hco.
      * exact (Hconsistent sid co Hco).
      * lia.
      * exact Harch.
      * intros; eapply Hattributes; eauto.
      * rewrite Hlength, Z2Nat.id; [reflexivity |exact Hnonnegative].
      * eapply initialized_packet_state_header; eauto.
      * exact Hprepare.
      * exact Hmemory.
      * exact Hextends.
  - inversion Hexecute; subst. exists layout. split.
    + eapply packet_layout_short; eauto.
    + eapply typed_memory_layout_context_extension; eauto.
Qed.

Lemma packet_match_layout_includes_old : forall cenv m descriptor offset sid after layout layout',
  packet_match_layout_result cenv m descriptor offset sid after layout layout' ->
  forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk.
Proof. intros cenv m descriptor offset sid after layout layout' Hresult; inversion Hresult; subst; intros; auto; left; assumption. Qed.

Print Assumptions execute_packet_match_layout.

Theorem packet_match_preserves_extended_layout :
  forall cenv Gamma Sigma layout bge p m vm descriptor offset view sid header rest fields yes no rt ef
    after vm' body,
  bge.(genv_cenv) = cenv ->
  type_expr cenv Gamma Sigma
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) ef rt ->
  source_composites_consistent cenv ->
  initialized_packet_state m descriptor offset view ->
  Archi.align_int64 = 8 ->
  (forall co name pt, Maps.PTree.get sid cenv = Some co ->
    packet_member_type name co.(co_members) = Some (Vtype pt) ->
    Ctypes.attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) = None /\
    Ctypes.type_is_volatile (transBeePL_type (Vtype pt)) = false) ->
  (forall block ty, Maps.PTree.get block Sigma = Some ty -> Mem.valid_block m block) ->
  typed_memory_layout cenv Sigma layout m ->
  ssem_expr bge p vm m
    (Match (Val (Vloc descriptor offset) Bytes)
      (Pbytes header (Stype sid Ctypes.noattr) fields :: Pbytes rest Bytes nil :: nil)
      (yes :: no :: nil) rt) after vm' body ->
  exists Sigma' effect layout',
    store_context_extends Sigma Sigma' /\ vm' = vm /\
    type_expr cenv Gamma Sigma' body effect rt /\ sub_effect effect ef = true /\
    packet_match_layout_result cenv m descriptor offset sid after layout layout' /\
    typed_memory_layout cenv Sigma' layout' after /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    (forall other otherOffset otherView, initialized_packet_state m other otherOffset otherView ->
      initialized_packet_state after other otherOffset otherView) /\
    (forall block ty, Maps.PTree.get block Sigma' = Some ty -> Mem.valid_block after block).
Proof.
  intros cenv Gamma Sigma layout bge p m vm descriptor offset view sid header rest fields yes no rt ef
    after vm' body Henv Htyped Hconsistent Hpacket Harch Hattributes Hvalid Hmemory Hstep.
  destruct (packet_match_preserves_old_layout cenv Gamma Sigma layout bge p m vm descriptor offset view
    sid header rest fields yes no rt ef after vm' body Henv Htyped Hconsistent Hpacket Hvalid Hmemory Hstep)
    as [Sigma' [effect [Hextends [Hbody [Heffect [HoldLayout [Hpackets HvalidAfter]]]]]]].
  destruct (packet_match_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hexecute Hvm]. rewrite Henv in Hexecute. clear Henv.
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  inversion Hschemas as [|? ? Hschema Hrest]; subst.
  destruct (execute_packet_match_layout cenv Sigma Sigma' layout m descriptor offset view
    sid header rest fields yes no after body Hschema Hconsistent Hpacket Harch Hattributes
    Hmemory Hextends Hexecute) as [layout' [Hresult Hlayout]].
  exists Sigma', effect, layout'. split; [exact Hextends |]. split; [reflexivity |].
  split; [exact Hbody |]. split; [exact Heffect |]. split; [exact Hresult |].
  split; [exact Hlayout |]. split.
  - eapply packet_match_layout_includes_old; exact Hresult.
  - split; assumption.
Qed.

Print Assumptions packet_match_preserves_extended_layout.
