(* Legacy big-step Ref is not the source relation of the checked soundness API.
   This inhabited witness records why compiler correctness must simulate the
   actual ssem_expr transition system (and its closures), not bsem_expr. No
   operational rule is changed by this audit. *)
Require Import List ZArith Lia Coqlib AST Maps Integers Memory Ctypes Values.
Require Import BeeTypes BeePL_values BeePL BeePL_sem.
Import ListNotations.
Local Open Scope Z_scope.

Definition audit_ref_type := Vtype(Tint I32 Signed noattr).
Definition audit_ref_expression := Prim Ref
  [Val(BeePL_values.Vint(Int.repr 41))audit_ref_type]
  (Ptrtype(Reftype(Bprim(Tint I32 Signed noattr))noattr)).

Theorem legacy_reference_arbitrary_result_block : forall ge p vm,
  exists allocated fresh initialized,
    Mem.alloc Mem.empty 0 4=(allocated,fresh) /\
    Mem.store Mint32 allocated fresh 0 (Values.Vint(Int.repr 41))=Some initialized /\
    Mem.load Mint32 initialized fresh 0=Some(Values.Vint(Int.repr 41)) /\
    forall reported,
      bsem_expr ge p vm Mem.empty audit_ref_expression initialized vm
        (Vloc reported Ptrofs.zero).
Proof.
  intros ge p vm.
  destruct(Mem.alloc Mem.empty 0 4) as [allocated fresh] eqn:Halloc.
  assert(Haccess:Mem.valid_access allocated Mint32 fresh 0 Writable).
  { eapply Mem.valid_access_implies with (p1:=Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact Halloc|lia|simpl;lia|].
    apply Z.divide_0_r. }
  destruct(Mem.valid_access_store _ _ _ _ (Values.Vint(Int.repr 41)) Haccess)
    as [initialized Hstore].
  exists allocated,fresh,initialized. split; [reflexivity|].
  split; [exact Hstore|]. split.
  - exact(Mem.load_store_same _ _ _ _ _ _ Hstore).
  - intros reported. unfold audit_ref_expression,audit_ref_type.
    eapply bsem_ref with (bge:=ge)(ml:=(allocated,fresh))(m':=Mem.empty).
    + apply bsem_value. constructor.
    + exact Halloc.
    + eapply assign_addr_value with (chunk:=BMint32)(v:=Values.Vint(Int.repr 41));
        try reflexivity; exact Hstore.
Qed.

Corollary legacy_reference_two_distinct_results : forall ge p vm,
  exists final,
    bsem_expr ge p vm Mem.empty audit_ref_expression final vm (Vloc 1%positive Ptrofs.zero) /\
    bsem_expr ge p vm Mem.empty audit_ref_expression final vm (Vloc 2%positive Ptrofs.zero) /\
    Vloc 1%positive Ptrofs.zero <> Vloc 2%positive Ptrofs.zero.
Proof.
  intros. destruct(legacy_reference_arbitrary_result_block ge p vm)
    as [allocated [fresh [final [Ha [Hs [Hl Hany]]]]]].
  exists final; split; [apply Hany|]. split; [apply Hany|discriminate].
Qed.
Print Assumptions legacy_reference_arbitrary_result_block.
Print Assumptions legacy_reference_two_distinct_results.

Corollary legacy_reference_can_report_invalid_block : forall ge p vm,
  exists final reported,
    bsem_expr ge p vm Mem.empty audit_ref_expression final vm (Vloc reported Ptrofs.zero) /\
    ~Mem.valid_block final reported.
Proof.
  intros. destruct(legacy_reference_arbitrary_result_block ge p vm)
    as [allocated [fresh [final [Ha [Hs [Hl Hany]]]]]].
  exists final,(Mem.nextblock final); split; [apply Hany|].
  unfold Mem.valid_block. apply Pos.lt_irrefl.
Qed.
Print Assumptions legacy_reference_can_report_invalid_block.
