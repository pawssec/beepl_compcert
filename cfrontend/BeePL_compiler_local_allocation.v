(* Run-scoped target local allocation. No claim of source/target memory
   equality or of expression simulation is made. The final compiler context
   belongs to one actual body translation, not every possible translation. *)
Require Import List String ZArith Lia Coqlib Maps AST Memory Ctypes Csyntax Csem.
Require Import BeeTypes BeePL BeePL_Csyntax BeePL_compiler_structure.
Import ListNotations.

Definition compiled_context_locals (ctx : list (ident * BeeTypes.type * string)) :=
 seq.zip (map unzip_ident ctx)
   (transBeePL_types transBeePL_type (map unzip_type ctx)).

Lemma compiled_context_locals_map : forall ctx,
 compiled_context_locals ctx = map(fun entry =>
 (unzip_ident entry,transBeePL_type(unzip_type entry))) ctx.
Proof. intros ctx; induction ctx as [|[[id ty] tag] rest IH]; simpl; [reflexivity|].
 unfold compiled_context_locals in *; simpl in *; rewrite IH; reflexivity. Qed.

Lemma c_local_allocation_exists : forall ge vars e m,
 exists e' m', Csem.alloc_variables ge e m vars e' m'.
Proof.
 intros ge vars; induction vars as [|[id ty] rest IH]; intros e m.
 - exists e,m; constructor.
 - destruct(Mem.alloc m 0 (Ctypes.sizeof ge ty)) as [allocated b] eqn:E.
   destruct(IH (PTree.set id (b,ty) e) allocated) as [e' [m' H]].
   exists e',m'; econstructor; eauto.
Qed.

Lemma c_local_allocation_lookup_frame : forall ge e m vars e' m',
 Csem.alloc_variables ge e m vars e' m' -> forall id,
 ~In id (map fst vars) -> PTree.get id e'=PTree.get id e.
Proof.
 intros ge e m vars e' m' H; induction H; intros x Hnot; [reflexivity|].
 rewrite IHalloc_variables by (simpl in Hnot; tauto).
 rewrite PTree.gso; [reflexivity|]. intro E; subst; simpl in Hnot; tauto.
Qed.

Lemma c_local_allocation_blocks_frame : forall ge e m vars e' m',
 Csem.alloc_variables ge e m vars e' m' -> forall b,
 Mem.valid_block m b -> Mem.valid_block m' b.
Proof. intros ge e m vars e' m' H; induction H; intros b Hb; auto.
 apply IHalloc_variables. eapply Mem.valid_block_alloc; eauto. Qed.

Lemma c_local_allocation_permissions_frame : forall ge e m vars e' m',
 Csem.alloc_variables ge e m vars e' m' -> forall b ofs k perm,
 Mem.perm m b ofs k perm -> Mem.perm m' b ofs k perm.
Proof. intros ge e m vars e' m' H; induction H; intros b ofs k perm Hp; auto.
 apply IHalloc_variables. eapply Mem.perm_alloc_1; eauto. Qed.

Lemma c_local_allocation_loadbytes_frame : forall ge e m vars e' m',
 Csem.alloc_variables ge e m vars e' m' -> forall b ofs count,
 Mem.valid_block m b -> Mem.loadbytes m' b ofs count=Mem.loadbytes m b ofs count.
Proof.
 intros ge e m vars e' m' H; induction H; intros b ofs count Hv; [reflexivity|].
 rewrite IHalloc_variables by (eapply Mem.valid_block_alloc; eauto).
 eapply Mem.loadbytes_alloc_unchanged; eauto.
Qed.

Theorem c_local_allocation_declared : forall ge e m vars e' m',
 Csem.alloc_variables ge e m vars e' m' ->
 NoDup(map fst vars) -> forall id ty, In(id,ty) vars -> exists b,
 PTree.get id e'=Some(b,ty) /\ Mem.valid_block m' b /\
 (forall ofs k, (0<=ofs<Ctypes.sizeof ge ty)%Z -> Mem.perm m' b ofs k Freeable).
Proof.
 intros ge e m vars e' m' H; induction H; intros Hnodup x t Hin;
 [contradiction|]. inversion Hnodup as [|? ? Hfresh Htail]; subst.
 destruct Hin as [E|Hin].
 - inversion E; subst x t. exists b1; split.
   + rewrite(c_local_allocation_lookup_frame _ _ _ _ _ _ H0 id Hfresh).
     apply PTree.gss.
   + split.
     * eapply c_local_allocation_blocks_frame; [exact H0|]. eapply Mem.valid_new_block; eauto.
     * intros ofs k Hrange. eapply c_local_allocation_permissions_frame; [exact H0|].
       eapply Mem.perm_alloc_2; eauto.
 - eapply IHalloc_variables; eauto.
Qed.

Definition allocated_context_valid ge (ctx : list (ident * BeeTypes.type * string)) e m := forall id ty tag,
 In(id,ty,tag) ctx -> exists b,
 PTree.get id e=Some(b,transBeePL_type ty) /\ Mem.valid_block m b /\
 (forall ofs k, (0<=ofs<Ctypes.sizeof ge (transBeePL_type ty))%Z ->
 Mem.perm m b ofs k Freeable).

Theorem actual_context_allocation_valid : forall ge ctx e m e' m',
 NoDup(map unzip_ident ctx) ->
 Csem.alloc_variables ge e m (compiled_context_locals ctx) e' m' ->
 allocated_context_valid ge ctx e' m'.
Proof.
 intros ge ctx e m e' m' Hdup Halloc id ty tag Hin.
 eapply c_local_allocation_declared; [exact Halloc| |].
 - rewrite compiled_context_locals_map, map_map.
   change (NoDup(map unzip_ident ctx)); exact Hdup.
 - rewrite compiled_context_locals_map. apply in_map_iff.
   exists(id,ty,tag); split; [reflexivity|exact Hin].
Qed.

Theorem context_allocation_constructive : forall ge ctx e m,
 NoDup(map unzip_ident ctx) -> exists e' m',
 Csem.alloc_variables ge e m (compiled_context_locals ctx) e' m' /\
 allocated_context_valid ge ctx e' m' /\
 (forall id, ~In id(map unzip_ident ctx) -> PTree.get id e'=PTree.get id e) /\
 (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
 intros ge ctx e m Hdup.
 destruct(c_local_allocation_exists ge (compiled_context_locals ctx) e m) as [e' [m' H]].
 exists e',m'; split; [exact H|]. split.
 - eapply actual_context_allocation_valid; eauto.
 - split; [|eapply c_local_allocation_blocks_frame; exact H].
   intros id Hnot. eapply c_local_allocation_lookup_frame; [exact H|].
   rewrite compiled_context_locals_map,map_map. exact Hnot.
Qed.

(* Relate the above allocation to a particular successful function translation.
   NoDup remains an explicit compiler freshness obligation, not a simulation
   oracle. The empty context satisfies it, as does any singleton context. *)
Theorem translated_function_context_allocatable : forall cenv bf ids bctx cf ids' bctx',
 transBeePL_function_function cenv bf ids bctx=Errors.OK(cf,ids',bctx') ->
 exists ctx, Csyntax.fn_vars cf=compiled_context_locals ctx /\
 (forall ge e m, NoDup(map unzip_ident ctx) -> exists e' m',
 Csem.alloc_variables ge e m (Csyntax.fn_vars cf) e' m' /\
 allocated_context_valid ge ctx e' m').
Proof.
 intros cenv bf ids bctx cf ids' bctx' H.
 destruct(function_translation_body_context _ _ _ _ _ _ _ H)
 as [initial [g0 [i0 [ctx [g1 [i1 [Hctx [Hbody Hlocals]]]]]]]].
 exists ctx; split; [exact Hlocals|]. intros ge e m Hdup.
 destruct(context_allocation_constructive ge ctx e m Hdup)
 as [e' [m' [Ha [Hv Hrest]]]]. exists e',m'; split; [rewrite Hlocals; exact Ha|exact Hv].
Qed.

Example singleton_context_allocation_witness : forall ge m,
 exists e' m', Csem.alloc_variables ge (PTree.empty _) m
 (compiled_context_locals [(1%positive,Utype,EmptyString)]) e' m' /\
 allocated_context_valid ge [(1%positive,Utype,EmptyString)] e' m'.
Proof.
 intros ge m. destruct(context_allocation_constructive ge [(1%positive,Utype,EmptyString)]
 (PTree.empty _) m) as [e' [m' [Ha [Hv Hrest]]]].
 - repeat constructor; simpl; tauto.
 - exists e',m'; auto.
Qed.
Print Assumptions context_allocation_constructive.
Print Assumptions translated_function_context_allocatable.
