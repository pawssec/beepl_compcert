(* Actual Bytes descriptor reads, copies, and parameter initialization. This
   transports packet state; unified whole-language call soundness is separate. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_state.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bytes_size_is_descriptor_size : forall env,
  sizeof_type env Bytes = packet_descriptor_size.
Proof. reflexivity. Qed.

Lemma bytes_descriptor_size_fits : packet_descriptor_size <= Ptrofs.modulus.
Proof. vm_compute; congruence. Qed.

Lemma packet_descriptor_alignment : forall m block offset view,
  packet_descriptor_valid m block offset view ->
  (align_chunk Mptr | Ptrofs.unsigned offset).
Proof. intros m block offset view [Hfirst _]. apply Mem.load_valid_access in Hfirst; destruct Hfirst as [Hperm Halign]; exact Halign. Qed.

Theorem bytes_descriptor_read : forall m block offset view,
  packet_descriptor_valid m block offset view ->
  Ptrofs.unsigned offset + packet_descriptor_size <= Ptrofs.modulus ->
  deref_addr Bytes m block offset Full (Vloc block offset).
Proof.
  intros m block offset view Hdescriptor Hbound.
  destruct (packet_descriptor_loadbytes _ _ _ _ Hdescriptor) as [bytes Hread].
  apply deref_addr_bytes; [reflexivity| |exact Hbound| |].
  - eapply packet_descriptor_source_block; eauto.
  - eapply packet_descriptor_alignment; eauto.
  - eapply Mem.loadbytes_range_perm; exact Hread.
Qed.

Theorem bytes_descriptor_copy_execution : forall ge m src source dst target view,
  packet_descriptor_valid m src source view ->
  Ptrofs.unsigned source + packet_descriptor_size <= Ptrofs.modulus ->
  Ptrofs.unsigned target + packet_descriptor_size <= Ptrofs.modulus ->
  Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + packet_descriptor_size) Cur Writable ->
  (align_chunk Mptr | Ptrofs.unsigned target) ->
  (src <> dst \/ Ptrofs.unsigned source = Ptrofs.unsigned target \/
    Ptrofs.unsigned source + packet_descriptor_size <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + packet_descriptor_size <= Ptrofs.unsigned source) ->
  exists final,
    assign_addr ge Bytes m dst target Full (Vloc src source) final (Vloc src source) /\
    packet_descriptor_valid final dst target view.
Proof.
  intros ge m src source dst target view Hdescriptor Hsource Htarget Hwrite Halign Hapart.
  destruct (packet_descriptor_copy_into _ _ _ _ _ _ Hdescriptor Hwrite Halign)
    as [bytes [final [Hread [Hstore Hvalid]]]].
  exists final. split; [|exact Hvalid].
  eapply assign_addr_bytes_copy; eauto using packet_descriptor_source_block, packet_descriptor_alignment.
  eapply Mem.perm_valid_block with (ofs := Ptrofs.unsigned target) (k := Cur) (p := Writable). apply Hwrite. pose proof packet_descriptor_size_positive; lia.
Qed.

Theorem bytes_variable_read : forall ge p vm m id block view,
  PTree.get id vm = Some (block, Bytes) ->
  packet_descriptor_valid m block Ptrofs.zero view ->
  ssem_expr ge p vm m (Var id Bytes) m vm (Val (Vloc block Ptrofs.zero) Bytes) /\
  bsem_expr ge p vm m (Var id Bytes) m vm (Vloc block Ptrofs.zero).
Proof.
  intros ge p vm m id block view Hlookup Hdescriptor.
  assert (Hread : deref_addr Bytes m block Ptrofs.zero Full (Vloc block Ptrofs.zero)).
  { eapply bytes_descriptor_read; [exact Hdescriptor|].
    rewrite Ptrofs.unsigned_zero. simpl. apply bytes_descriptor_size_fits. }
  split; [eapply ssem_lvar|eapply bsem_lvar]; eauto.
Qed.

Theorem fresh_bytes_parameter_execution : forall ge Gamma Sigma p m locations id src source,
  packet_state_valid m locations -> locations src source ->
  exists allocated fresh final callee,
    Mem.alloc m 0 packet_descriptor_size = (allocated, fresh) /\
    alloc_variables ge Sigma empty_vmap m [(id, Bytes)] callee allocated (PTree.set fresh Bytes Sigma) /\
    bind_variables ge callee allocated [(id, Bytes)] [Vloc src source] final /\
    ssem_expr ge p callee final (Var id Bytes) final callee (Val (Vloc fresh Ptrofs.zero) Bytes) /\
    bsem_expr ge p callee final (Var id Bytes) final callee (Vloc fresh Ptrofs.zero) /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh Bytes Sigma)
      (Val (Vloc fresh Ptrofs.zero) Bytes) [] Bytes /\
    packet_state_valid final (extend_packet_locations locations fresh Ptrofs.zero).
Proof.
  intros ge Gamma Sigma p m locations id src source Hstate Hsource.
  destruct (Hstate _ _ Hsource) as [Hbound [view [contents [Hdescriptor Hcontents]]]].
  destruct (packet_state_fresh_descriptor_copy _ _ _ _ Hstate Hsource)
    as [allocated [fresh [bytes [final [Halloc [Hread [Hstore [Hfresh [Hstate' Hframe]]]]]]]]].
  set (callee := PTree.set id (fresh, Bytes) empty_vmap).
  assert (Hsource' : packet_descriptor_valid allocated src source view).
  { eapply packet_descriptor_alloc_frame; eauto. }
  assert (Hassign : assign_addr ge Bytes allocated fresh Ptrofs.zero Full
    (Vloc src source) final (Vloc src source)).
  { eapply assign_addr_bytes_copy; [reflexivity| | |exact Hbound| | | | |exact Hread|].
    - eapply packet_descriptor_source_block; exact Hsource'.
    - eapply Mem.valid_new_block; exact Halloc.
    - rewrite Ptrofs.unsigned_zero. simpl. apply bytes_descriptor_size_fits.
    - eapply packet_descriptor_alignment; exact Hsource'.
    - rewrite Ptrofs.unsigned_zero. exists 0; reflexivity.
    - left. intro Heq; subst src. apply Hfresh. eapply packet_descriptor_source_block; exact Hdescriptor.
    - rewrite Ptrofs.unsigned_zero. exact Hstore. }
  assert (Hlookup : PTree.get id callee = Some (fresh, Bytes)) by apply PTree.gss.
  assert (HnewEntry : extend_packet_locations locations fresh Ptrofs.zero fresh Ptrofs.zero)
    by (right; auto).
  destruct (Hstate' _ _ HnewEntry) as [HnewBound [newview [newcontents [HnewDescriptor HnewContents]]]].
  destruct (bytes_variable_read ge p callee final id fresh newview Hlookup HnewDescriptor)
    as [Hsmall Hbig].
  exists allocated, fresh, final, callee. split; [exact Halloc|]. split.
  - eapply alloc_variables_con.
    + unfold balloc. change (Mem.alloc m 0 (sizeof_type ge.(genv_cenv) Bytes) = (allocated, fresh)) in Halloc.
      rewrite Halloc. reflexivity.
    + constructor.
  - split.
    + eapply bind_variables_cons; [exact Hlookup|exact Hassign|constructor].
    + split; [exact Hsmall|]. split; [exact Hbig|]. split; [|exact Hstate'].
      apply ty_valbytes. rewrite Ptrofs.unsigned_zero.
      eapply object_type_root with (stored := Bytes); [apply PTree.gss|]. change (0 <= packet_descriptor_size). pose proof packet_descriptor_size_positive; lia.
Qed.

Print Assumptions bytes_descriptor_copy_execution.
Print Assumptions fresh_bytes_parameter_execution.

Lemma bytes_read_exact : forall m block offset result,
  deref_addr Bytes m block offset Full result -> result = Vloc block offset.
Proof. intros; inversion H; subst; try discriminate; reflexivity. Qed.

Theorem bytes_assignment_descriptor_preservation : forall ge m final src source dst target view result,
  packet_descriptor_valid m src source view ->
  assign_addr ge Bytes m dst target Full (Vloc src source) final result ->
  result = Vloc src source /\ packet_descriptor_valid final dst target view.
Proof.
  intros ge m final src source dst target view result Hdescriptor Hassign.
  inversion Hassign; subst; try discriminate.
  split; [reflexivity|]. eapply copied_packet_descriptor_valid; eauto.
Qed.

Print Assumptions bytes_assignment_descriptor_preservation.
