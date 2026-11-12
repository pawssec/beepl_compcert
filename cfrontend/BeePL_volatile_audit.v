(* The ordinary-memory language excludes volatile primitive accesses. The
   operational counterexample below records why typing/checking must reject
   this attributed AST (the source parser already emits only noattr). *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_typechecker.
Require Import BeePL_soundness_memory BeePL_value_checker.
Import ListNotations.

Definition audit_volatile_attr : attr :=
  {| attr_volatile := true; attr_alignas := None |}.
Definition audit_volatile_int : primitive_type := Tint I32 Signed audit_volatile_attr.
Definition audit_volatile_pointer : ptr_type :=
  Reftype (Bprim audit_volatile_int) audit_volatile_attr.
Definition audit_volatile_ref : expr :=
  Prim Ref [Val (Vint (Int.repr 7)) (Vtype audit_volatile_int)]
    (Ptrtype audit_volatile_pointer).
Definition audit_volatile_deref_ref : expr :=
  Prim Deref [audit_volatile_ref] (Vtype audit_volatile_int).

Lemma audit_volatile_ref_rejected : forall cenv Gamma Sigma ef ty,
  ~ type_expr cenv Gamma Sigma audit_volatile_ref ef ty.
Proof.
  intros cenv Gamma Sigma ef ty Htyped.
  unfold audit_volatile_ref, audit_volatile_pointer in Htyped.
  inversion Htyped; subst; discriminate.
Qed.

Lemma audit_volatile_deref_ref_rejected : forall cenv Gamma Sigma ef ty,
  ~ type_expr cenv Gamma Sigma audit_volatile_deref_ref ef ty.
Proof.
  intros cenv Gamma Sigma ef ty Htyped.
  unfold audit_volatile_deref_ref in Htyped. inversion Htyped; subst.
  eapply audit_volatile_ref_rejected; eauto.
Qed.

Lemma audit_volatile_checker_rejects : forall cenv Gamma Sigma,
  exists error,
    type_check_expr cenv Gamma Sigma audit_volatile_deref_ref = Error error.
Proof. intros; eexists; reflexivity. Qed.

(* The rejected expression can start with an ordinary constant; the Val
   above is the scalar evaluation result, not a forged location. *)
Definition audit_volatile_source : expr :=
  Prim Deref
    [Prim Ref [Const (ConsInt (Int.repr 7)) (Vtype audit_volatile_int)]
      (Ptrtype audit_volatile_pointer)] (Vtype audit_volatile_int).

Lemma audit_volatile_source_checker_rejects : forall cenv Gamma Sigma,
  exists error,
    type_check_expr cenv Gamma Sigma audit_volatile_source = Error error.
Proof. intros; eexists; reflexivity. Qed.

Lemma audit_volatile_reference_allocates : forall ge p vm m,
  exists allocated fresh final,
    Mem.alloc m 0 4 = (allocated, fresh) /\
    Mem.store Mint32 allocated fresh 0 (Values.Vint (Int.repr 7)) = Some final /\
    ssem_expr ge p vm m audit_volatile_ref final vm
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype audit_volatile_pointer)).
Proof.
  intros ge p vm m. destruct (Mem.alloc m 0 4) as [allocated fresh] eqn:Halloc.
  assert (Haccess : Mem.valid_access allocated Mint32 fresh 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
    exists 0; reflexivity. }
  destruct (Mem.valid_access_store _ _ _ _ (Values.Vint (Int.repr 7)) Haccess)
    as [final Hstore].
  exists allocated, fresh, final. split; [reflexivity|]. split; [exact Hstore|].
  unfold audit_volatile_ref, audit_volatile_pointer, audit_volatile_int.
  eapply ssem_ref2 with (ml := (allocated, fresh)) (chunk := BMint32)
    (Sigma := PTree.empty type) (l := fresh)
    (bt := Bprim (Tint I32 Signed audit_volatile_attr)); simpl; eauto.
Qed.

Lemma audit_volatile_dereference_stuck : forall ge p vm m b,
  ~ exists final vm' next,
    ssem_expr ge p vm m
      (Prim Deref [Val (Vloc b Ptrofs.zero) (Ptrtype audit_volatile_pointer)]
        (Vtype audit_volatile_int)) final vm' next.
Proof.
  intros ge p vm m b [final [vm' [next Hstep]]].
  inversion Hstep; subst.
  - eapply value_has_no_small_step; eauto.
  - match goal with Hread : deref_addr _ _ _ _ Full _ |- _ =>
      inversion Hread; subst; discriminate
    end.
  - match goal with Hread : aggregate_readable _ _ _ _ _ |- _ =>
      destruct Hread as [Hkind Hrest]; discriminate
    end.
Qed.

Theorem audit_unchecked_volatile_execution_reaches_stuck : forall ge p vm m,
  exists final b,
    ssem_expr ge p vm m audit_volatile_deref_ref final vm
      (Prim Deref [Val (Vloc b Ptrofs.zero) (Ptrtype audit_volatile_pointer)]
        (Vtype audit_volatile_int)) /\
    ~ exists final' vm' next,
      ssem_expr ge p vm final
        (Prim Deref [Val (Vloc b Ptrofs.zero) (Ptrtype audit_volatile_pointer)]
          (Vtype audit_volatile_int)) final' vm' next.
Proof.
  intros ge p vm m.
  destruct (audit_volatile_reference_allocates ge p vm m)
    as [allocated [fresh [final [Halloc [Hstore Hstep]]]]].
  exists final, fresh. split.
  - unfold audit_volatile_deref_ref. apply ssem_deref1; exact Hstep.
  - apply audit_volatile_dereference_stuck.
Qed.

Print Assumptions audit_unchecked_volatile_execution_reaches_stuck.

Lemma audit_volatile_dereference_checker_rejects : forall cenv Gamma Sigma b,
  exists error, type_check_expr cenv Gamma
    (PTree.set b (Ptrtype audit_volatile_pointer) Sigma)
    (Prim Deref [Val (Vloc b Ptrofs.zero) (Ptrtype audit_volatile_pointer)]
      (Vtype audit_volatile_int)) = Error error.
Proof.
  intros. cbn [type_check_expr value_type_check audit_volatile_pointer].
  rewrite PTree.gss. eexists; reflexivity.
Qed.

Lemma audit_volatile_assignment_checker_rejects : forall cenv Gamma Sigma b,
  exists error, type_check_expr cenv Gamma
    (PTree.set b (Ptrtype audit_volatile_pointer) Sigma)
    (Prim Massgn [Val (Vloc b Ptrofs.zero) (Ptrtype audit_volatile_pointer);
      Val (Vint (Int.repr 7)) (Vtype audit_volatile_int)] Utype) = Error error.
Proof.
  intros. cbn [type_check_expr value_type_check audit_volatile_pointer].
  rewrite PTree.gss. eexists; reflexivity.
Qed.
