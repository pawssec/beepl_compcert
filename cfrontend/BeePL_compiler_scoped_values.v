(* The source substitutes closed values while C retains the original body and
   reads lexical slots. This relation covers unit and By_value storage,
   including pointers/options. Aggregate copied views require a distinct
   representation relation and are deliberately not claimed here. *)
Require Import List ZArith Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Csyntax Csem Cstrategy SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_Csyntax BeePL_compiler_bindings.
Require Import BeePL_compiler_rvalue_audit BeePL_compiler_binding_evaluation.
Local Open Scope Z_scope.

Definition source_value_bindings := PTree.t (BeePL_values.value * BeeTypes.type).

Inductive scoped_value (bc : bcompiler_ctx) (env : Csem.env)
    (f : meminj) (m : mem) (x : ident) : BeePL_values.value -> BeeTypes.type -> Prop :=
| scoped_unit :
    (lexical_bindings bc)!x = Some Binding_unit ->
    scoped_value bc env f m x Vunit Utype
| scoped_slot : forall sv ty target slot chunk tv,
    ty <> Utype ->
    (lexical_bindings bc)!x = Some (Binding_slot target) ->
    env!target = Some (slot,transBeePL_type ty) ->
    access_mode (transBeePL_type ty) = By_value chunk ->
    type_is_volatile (transBeePL_type ty) = false ->
    Mem.load chunk m slot 0 = Some tv ->
    Val.inject f (trans_bvalue_cvalue sv) tv ->
    scoped_value bc env f m x sv ty.

Definition scoped_values (rho : source_value_bindings) bc env f m : Prop :=
  forall x sv ty, rho!x = Some (sv,ty) -> scoped_value bc env f m x sv ty.

(* Separation concerns the prestate's live lexical slots, not the eventual
   memory. Actual local-allocation distinctness can discharge this premise. *)
Definition new_slot_separated (rho : source_value_bindings) bc (env : Csem.env) fresh : Prop :=
  forall x sv ty target block,
    rho!x = Some (sv,ty) ->
    (lexical_bindings bc)!x = Some (Binding_slot target) ->
    env!target = Some (block,transBeePL_type ty) -> block <> fresh.

Lemma scoped_values_empty : forall bc env f m,
  scoped_values (PTree.empty _) bc env f m.
Proof. intros bc env f m x sv ty H; rewrite PTree.gempty in H; discriminate. Qed.

Lemma scoped_value_other_binding : forall bc env f m x sv ty y binding,
  x <> y -> scoped_value bc env f m x sv ty ->
  scoped_value (with_compiler_bindings bc
    (push_compiler_binding (lexical_bindings bc) y binding)) env f m x sv ty.
Proof.
  intros bc env f m x sv ty y binding Hneq Hvalue.
  inversion Hvalue; subst.
  - constructor. cbn [lexical_bindings with_compiler_bindings].
    rewrite compiler_binding_other by exact Hneq. assumption.
  - econstructor 2; eauto. cbn [lexical_bindings with_compiler_bindings].
    rewrite compiler_binding_other by exact Hneq. assumption.
Qed.

Theorem scoped_values_extend_unit : forall rho bc env f m x,
  scoped_values rho bc env f m ->
  scoped_values (PTree.set x (Vunit,Utype) rho)
    (with_compiler_bindings bc (push_compiler_binding (lexical_bindings bc) x Binding_unit)) env f m.
Proof.
  intros rho bc env f m x Hold y sv ty Hlookup.
  destruct (peq y x) as [->|Hneq].
  - rewrite PTree.gss in Hlookup; inversion Hlookup; subst.
    constructor; apply compiler_binding_shadow.
  - rewrite PTree.gso in Hlookup by exact Hneq.
    eapply scoped_value_other_binding; [exact Hneq|eapply Hold; exact Hlookup].
Qed.

Theorem scoped_values_extend_slot :
  forall rho bc env f before after x sv ty target slot chunk tv,
  scoped_values rho bc env f before -> new_slot_separated rho bc env slot ->
  ty <> Utype -> env!target = Some(slot,transBeePL_type ty) ->
  access_mode (transBeePL_type ty) = By_value chunk ->
  type_is_volatile (transBeePL_type ty) = false ->
  Val.inject f (trans_bvalue_cvalue sv) tv ->
  Val.load_result chunk tv = tv ->
  Mem.store chunk before slot 0 tv = Some after ->
  scoped_values (PTree.set x (sv,ty) rho)
    (with_compiler_bindings bc
      (push_compiler_binding (lexical_bindings bc) x (Binding_slot target))) env f after.
Proof.
  intros rho bc env f before after x sv ty target slot chunk tv
    Hold Hseparated Hnonunit Hlocal Hmode Hvolatile Hinject Hnormalized Hstore
    y oldvalue oldtype Hlookup.
  destruct (peq y x) as [->|Hneq].
  - rewrite PTree.gss in Hlookup; inversion Hlookup; subst oldvalue oldtype.
    econstructor 2; eauto.
    + apply compiler_binding_shadow.
    + rewrite <- Hnormalized. eapply Mem.load_store_same; exact Hstore.
  - rewrite PTree.gso in Hlookup by exact Hneq.
    apply scoped_value_other_binding; [exact Hneq|].
    specialize (Hold y oldvalue oldtype Hlookup). inversion Hold; subst.
    + constructor; assumption.
    + econstructor 2; eauto.
      erewrite Mem.load_store_other by (eauto; left; eapply Hseparated; eauto).
      eassumption.
Qed.

(* Compose real fresh-binding output, an actual writable target local, and an
   injection-private store. Both the new lexical relation and Mem.inject are
   derived, rather than supplied as final-state hypotheses. *)
Theorem actual_binding_extends_scoped_values :
  forall rho bc env f source targetmem x sv ty locals selected slots scope g g' inc
    local block chunk tv,
  fresh_compiler_binding x ty locals bc g = Res ((selected,slots),scope) g' inc ->
  ty <> Utype -> selected = Some local ->
  scoped_values rho bc env f targetmem -> new_slot_separated rho bc env block ->
  Mem.inject f source targetmem ->
  (forall b delta, f b <> Some (block,delta)) ->
  env!local = Some (block,transBeePL_type ty) ->
  access_mode (transBeePL_type ty) = By_value chunk ->
  type_is_volatile (transBeePL_type ty) = false ->
  Val.inject f (trans_bvalue_cvalue sv) tv -> Val.load_result chunk tv = tv ->
  Mem.valid_access targetmem chunk block 0 Writable ->
  exists after, Mem.store chunk targetmem block 0 tv = Some after /\
    Mem.inject f source after /\
    scoped_values (PTree.set x (sv,ty) rho) scope env f after.
Proof.
  intros rho bc env f source targetmem x sv ty locals selected slots scope g g' inc
    local block chunk tv Hfresh Hnonunit Hselected Hold Hseparated Hinject Hprivate
    Hlocal Hmode Hvolatile Hvalue Hnormal Haccess.
  destruct (actual_nonunit_binding_scope _ _ _ _ _ _ _ _ _ _ Hnonunit Hfresh)
    as [id [name [Hid [Hslots [Hscope Hrest]]]]].
  rewrite Hselected in Hid; inversion Hid; subst id scope.
  destruct (private_binding_store_preserves_injection f source targetmem chunk block tv
    Hinject Hprivate Haccess) as [after [Hstore Hafter]].
  exists after; split; [exact Hstore|]. split; [exact Hafter|].
  eapply scoped_values_extend_slot; eauto.
Qed.

Theorem compiled_scoped_variable_reads_substituted_value :
  forall rho bc env f m x sv ty locals ce locals' bc' g g' inc,
  scoped_values rho bc env f m -> rho!x = Some(sv,ty) ->
  transBeePL_expr_expr (Var x ty) locals bc g = Res(ce,locals',bc')g' inc ->
  forall ge, exists tv,
    Val.inject f (trans_bvalue_cvalue sv) tv /\
    Cstrategy.eval_expression ge env m ce E0 m tv /\
    SubstE x (Val sv ty) (Var x ty) (Val sv ty).
Proof.
  intros rho bc env f m x sv ty locals ce locals' bc' g g' inc Hold Hlookup Hcompile ge.
  specialize (Hold _ _ _ Hlookup). inversion Hold; subst.
  - exists (trans_bvalue_cvalue Vunit). split; [constructor|]. split.
    + eapply actual_unit_variable_lowering_evaluates; exact Hcompile.
    + constructor.
  - exists tv; split; [assumption|]. split; [|constructor].
    eapply actual_nonunit_variable_lowering_evaluates; [exact Hcompile|eassumption| | |eassumption|].
    + unfold compiler_bound_storage; rewrite H0; reflexivity.
    + apply Cstrategy.esl_var_local; eassumption.
    + eapply Csem.deref_loc_value; eauto.
Qed.

Print Assumptions actual_binding_extends_scoped_values.
Print Assumptions compiled_scoped_variable_reads_substituted_value.
