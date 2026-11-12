(* Actual initializer executions are functional even though the small-step
   expression relation also contains evaluation-context rules. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_call_determinism BeePL_strict_progress BeePL_soundness_memory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma raw_value_conversion_inverse : forall cv v,
  trans_cvalue_bvalue cv = OK v -> cv = trans_bvalue_cvalue v.
Proof. intros cv v H. destruct cv; inversion H; reflexivity. Qed.

Definition full_assignment_memory ge ty m block offset value : option Mem.mem :=
  match access_mode_type ty with
  | By_value chunk => Mem.store chunk m block (Ptrofs.unsigned offset) (trans_bvalue_cvalue value)
  | _ => match value with
      | Vloc source start =>
          match Mem.loadbytes m source (Ptrofs.unsigned start) (sizeof_type ge.(genv_cenv) ty) with
          | Some bytes => Mem.storebytes m block (Ptrofs.unsigned offset) bytes
          | None => None
          end
      | _ => None
      end
  end.

Lemma full_assignment_computes : forall ge ty m block offset value final result,
  assign_addr ge ty m block offset Full value final result ->
  result=value /\ full_assignment_memory ge ty m block offset value = Some final.
Proof.
  intros * Hassign. inversion Hassign; subst; split; try reflexivity;
    unfold full_assignment_memory.
  - match goal with Hmode : access_mode_type _ = By_value _,
      Hdecode : trans_cvalue_bvalue ?cv = OK ?v |- _ =>
      rewrite Hmode; pose proof (raw_value_conversion_inverse _ _ Hdecode) as Hcv;
      subst cv end. assumption.
  - simpl. destruct b; assumption.
  - assert (Hmode : access_mode_type ty=By_reference) by
      (destruct ty; simpl in *; try discriminate; reflexivity).
    rewrite Hmode. match goal with Hread : Mem.loadbytes _ _ _ _ = Some _ |- _ => rewrite Hread end.
    assumption.
  - simpl. assumption.
  - cbn [access_mode_type sizeof_type]. match goal with Hread : Mem.loadbytes _ _ _ _ = Some _ |- _ => rewrite Hread end.
    assumption.
Qed.

Theorem full_assignment_unique : forall ge ty m block offset value first result second result',
  assign_addr ge ty m block offset Full value first result ->
  assign_addr ge ty m block offset Full value second result' ->
  first=second /\ result=result'.
Proof.
  intros * Hfirst Hsecond.
  destruct (full_assignment_computes _ _ _ _ _ _ _ _ Hfirst).
  destruct (full_assignment_computes _ _ _ _ _ _ _ _ Hsecond).
  split; congruence.
Qed.

Lemma unit_full_assignment_impossible : forall ge m block offset value final result,
  ~ assign_addr ge Utype m block offset Full value final result.
Proof. intros * H; inversion H; subst; discriminate. Qed.

Theorem array_helper_unique : forall ge m block offset values ty first,
  sem_array_init_helper ge m block offset values ty first ->
  forall second, sem_array_init_helper ge m block offset values ty second -> first=second.
Proof.
  intros * Hfirst. induction Hfirst; intros second Hsecond; inversion Hsecond; subst; auto.
  - match goal with H1 : assign_addr _ _ _ _ _ Full _ ?m1 _,
      H2 : assign_addr _ _ _ _ _ Full _ ?m2 _ |- _ =>
      destruct (full_assignment_unique _ _ _ _ _ _ _ _ _ _ H1 H2) as [Hm _]; subst m2 end.
    eapply IHHfirst; eauto.
  - exfalso; eapply unit_full_assignment_impossible; eauto.
  - exfalso; eapply unit_full_assignment_impossible; eauto.
Qed.

Print Assumptions full_assignment_unique.
Print Assumptions array_helper_unique.

Theorem array_initializer_unique : forall ge Sigma arr ty values vm m vm1 first Sigma1,
  sem_array_init ge Sigma arr ty values vm m vm1 first Sigma1 ->
  forall OtherSigma vm2 second Sigma2,
  sem_array_init ge OtherSigma arr ty values vm m vm2 second Sigma2 ->
  vm2=vm1 /\ second=first.
Proof.
  intros * Hfirst OtherSigma vm2 second Sigma2 Hsecond.
  inversion Hfirst; subst. inversion Hsecond; subst.
  match goal with Halloc1 : alloc_variables _ _ _ _ _ ?vmA ?mA _,
    Halloc2 : alloc_variables _ _ _ _ _ ?vmB ?mB _ |- _ =>
    destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ Halloc1 _ _ _ _ Halloc2)
      as [Hvm Hmem]; subst vmB mB end.
  repeat match goal with
    Hget1 : PTree.get ?id ?vm = Some (?b1, ?t),
    Hget2 : PTree.get ?id ?vm = Some (?b2, ?t) |- _ =>
    assert (b1=b2) by congruence; first [progress subst|clear Hget2]
  end.
  repeat match goal with H : Atype _ _ _ = Atype _ _ _ |- _ => inversion H; clear H; subst end.
  split; [reflexivity|]. eapply array_helper_unique; eauto.
Qed.

Theorem evaluated_array_step_unique : forall ge p vm m arr ty es first vm1 e1 second vm2 e2,
  Forall (fun e => exists v annotation, e=Val v annotation) es ->
  ssem_expr ge p vm m (Ainit arr ty es ty) first vm1 e1 ->
  ssem_expr ge p vm m (Ainit arr ty es ty) second vm2 e2 ->
  first=second /\ vm1=vm2 /\ e1=e2.
Proof.
  intros * Hvalues Hfirst Hsecond.
  inversion Hfirst; subst.
  - inversion Hvalues as [|head tail Hhead Htail]; subst.
    destruct Hhead as [v [t He]]. subst e.
    exfalso. eapply value_has_no_small_step; eauto.
  - inversion Hvalues as [|head tail Hhead Htail]; subst.
    pose proof (all_value_arguments_is_values _ Htail) as Hready. congruence.
  - inversion Hsecond; subst.
    + inversion Hvalues as [|head tail Hhead Htail]; subst.
      destruct Hhead as [v [t He]]. subst e.
      exfalso. eapply value_has_no_small_step; eauto.
    + inversion Hvalues as [|head tail Hhead Htail]; subst.
      pose proof (all_value_arguments_is_values _ Htail) as Hready. congruence.
    +
  match goal with Hinit1 : sem_array_init _ _ _ _ _ _ _ ?stored1 ?final1 _,
    Hinit2 : sem_array_init _ _ _ _ _ _ _ ?stored2 ?final2 _ |- _ =>
    destruct (array_initializer_unique _ _ _ _ _ _ _ _ _ _ Hinit1 _ _ _ _ Hinit2)
      as [Hvm Hmem]; subst stored2 final2 end.
  repeat split; try reflexivity. f_equal; congruence.
Qed.

Print Assumptions array_initializer_unique.
Print Assumptions evaluated_array_step_unique.
