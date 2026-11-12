(* Target-side capture foundation.  The left store is constructed first; the
   right operand is then evaluated in that actual intermediate memory.  The
   right child must frame the left slot, and the two temporary blocks must be
   distinct.  These are explicit local-allocation / child-simulation obligations,
   not a hypothesis that the complete generated expression evaluates.

   The prefix theorem ends by reading the right temporary and also establishes
   the left load.  It does not yet compose the conditional guard continuation
   or establish these framing conditions for arbitrary translated children. *)
Require Import Coqlib List ZArith Integers AST Maps Memory Ctypes Csyntax.
Require Import Csem Cstrategy Cop Events Values BeePL_option_capture_evaluation.
Require Import SimplExpr Csyntaxdefs BeePL_Csyntax BeePL_compiler_binary_translation.
Local Open Scope Z_scope.

Lemma local_capture_read : forall ge env m temp block ty chunk value,
 PTree.get temp env = Some (block, ty) ->
 access_mode ty = By_value chunk -> type_is_volatile ty = false ->
 Mem.load chunk m block 0 = Some value ->
 eval_expression ge env m (Evalof (Evar temp ty) ty) E0 m value.
Proof.
 intros * Henv Hmode Hvolatile Hload.
 eapply eval_expression_intro.
 - apply eval_valof; [exact Hvolatile|constructor].
 - eapply esr_rvalof; [apply esl_var_local; exact Henv|reflexivity|exact Hvolatile|].
   eapply deref_loc_value; [exact Hmode|exact Hvolatile|exact Hload].
Qed.

Theorem binary_capture_prefix : forall ge env initial lhs left_trace left_evaluated
    left_value left_temp left_block left_ty left_chunk left_saved,
 eval_expression ge env initial lhs left_trace left_evaluated left_value ->
 PTree.get left_temp env = Some (left_block,left_ty) ->
 access_mode left_ty = By_value left_chunk -> type_is_volatile left_ty = false ->
 Cop.sem_cast left_value (typeof lhs) left_ty left_evaluated = Some left_saved ->
 Mem.valid_access left_evaluated left_chunk left_block 0 Writable ->
 Val.load_result left_chunk left_saved = left_saved ->
 exists left_memory,
 Mem.store left_chunk left_evaluated left_block 0 left_saved = Some left_memory /\
 eval_expr ge env initial RV (Eassign (Evar left_temp left_ty) lhs left_ty)
   left_trace left_memory (Eval left_saved left_ty) /\
 forall rhs right_trace right_evaluated right_value right_temp right_block
     right_ty right_chunk right_saved,
 eval_expression ge env left_memory rhs right_trace right_evaluated right_value ->
 Mem.unchanged_on (fun block _ => block = left_block) left_memory right_evaluated ->
 PTree.get right_temp env = Some (right_block,right_ty) ->
 left_block <> right_block ->
 access_mode right_ty = By_value right_chunk -> type_is_volatile right_ty = false ->
 Cop.sem_cast right_value (typeof rhs) right_ty right_evaluated = Some right_saved ->
 Mem.valid_access right_evaluated right_chunk right_block 0 Writable ->
 Val.load_result right_chunk right_saved = right_saved ->
 exists final,
 Mem.store right_chunk right_evaluated right_block 0 right_saved = Some final /\
 eval_expr ge env left_memory RV (Eassign (Evar right_temp right_ty) rhs right_ty)
   right_trace final (Eval right_saved right_ty) /\
 Mem.load left_chunk final left_block 0 = Some left_saved /\
 Mem.load right_chunk final right_block 0 = Some right_saved /\
 eval_expression ge env final (Evalof (Evar left_temp left_ty) left_ty)
   E0 final left_saved /\
 eval_expression ge env final (Evalof (Evar right_temp right_ty) right_ty)
   E0 final right_saved /\
 eval_expression ge env initial
   (Ecomma (Eassign (Evar left_temp left_ty) lhs left_ty)
     (Ecomma (Eassign (Evar right_temp right_ty) rhs right_ty)
       (Evalof (Evar right_temp right_ty) right_ty) right_ty) right_ty)
   (left_trace ** right_trace) final right_saved.
Proof.
 intros * Hleft Hleftenv Hleftmode Hleftvolatile Hleftcast Hleftaccess Hleftnorm.
 destruct (capture_expression_once _ _ _ _ _ _ _ _ _ _ _ _
   Hleft Hleftenv Hleftmode Hleftvolatile Hleftcast Hleftaccess Hleftnorm)
   as [left_memory [Hleftstore [Hleftcapture Hleftread]]].
 exists left_memory; split; [exact Hleftstore|]. split; [exact Hleftcapture|].
 intros * Hright Hframe Hrightenv Hdistinct Hrightmode Hrightvolatile
   Hrightcast Hrightaccess Hrightnorm.
 destruct (capture_expression_once _ _ _ _ _ _ _ _ _ _ _ _
   Hright Hrightenv Hrightmode Hrightvolatile Hrightcast Hrightaccess Hrightnorm)
   as [final [Hrightstore [Hrightcapture Hrightread]]].
 assert (Hleftload0 : Mem.load left_chunk left_memory left_block 0 = Some left_saved).
 { rewrite (Mem.load_store_same _ _ _ _ _ _ Hleftstore), Hleftnorm. reflexivity. }
 assert (Hleftload1 : Mem.load left_chunk right_evaluated left_block 0 = Some left_saved).
 { eapply Mem.load_unchanged_on; [exact Hframe| |exact Hleftload0]. intros; reflexivity. }
 assert (Hleftload : Mem.load left_chunk final left_block 0 = Some left_saved).
 { rewrite (Mem.load_store_other _ _ _ _ _ _ Hrightstore); [exact Hleftload1|].
   left; exact Hdistinct. }
 assert (Hrightload : Mem.load right_chunk final right_block 0 = Some right_saved).
 { rewrite (Mem.load_store_same _ _ _ _ _ _ Hrightstore), Hrightnorm. reflexivity. }
 exists final. split; [exact Hrightstore|]. split; [exact Hrightcapture|].
 split; [exact Hleftload|]. split; [exact Hrightload|]. split.
 - eapply local_capture_read; eauto.
 - split; [exact Hrightread|].
   inversion Hrightread as [env0 m0 expr0 trace0 final0 reduced value0 Hreduce Hsimple]; subst.
   eapply eval_expression_intro; [|exact Hsimple].
   eapply eval_comma; [exact Hleftcapture|constructor| |reflexivity].
   replace right_trace with (right_trace ** E0) by (unfold E0, Eapp; apply app_nil_r).
   eapply eval_comma; [exact Hrightcapture|constructor|exact Hreduce|reflexivity].
Qed.

Print Assumptions binary_capture_prefix.

(* Pure local reads can occur repeatedly in the guard without repeating either
   source operand.  This predicate supplies both phases of Cstrategy evaluation. *)
Definition pure_rvalue ge env m expr value :=
 eval_expr ge env m RV expr E0 m expr /\ eval_simple_rvalue ge env m expr value.

Lemma pure_literal : forall ge env m value ty,
 pure_rvalue ge env m (Eval value ty) value.
Proof. intros; split; constructor. Qed.

Lemma pure_local_read : forall ge env m temp block ty chunk value,
 PTree.get temp env = Some (block,ty) ->
 access_mode ty = By_value chunk -> type_is_volatile ty = false ->
 Mem.load chunk m block 0 = Some value ->
 pure_rvalue ge env m (Evalof (Evar temp ty) ty) value.
Proof.
 intros * Henv Hmode Hvolatile Hload. split.
 - apply eval_valof; [exact Hvolatile|constructor].
 - eapply esr_rvalof; [apply esl_var_local; exact Henv|reflexivity|exact Hvolatile|].
   eapply deref_loc_value; eauto.
Qed.

Lemma pure_binary : forall ge env m op lhs rhs ty lv rv result,
 pure_rvalue ge env m lhs lv -> pure_rvalue ge env m rhs rv ->
 sem_binary_operation ge op lv (typeof lhs) rv (typeof rhs) m = Some result ->
 pure_rvalue ge env m (Ebinop op lhs rhs ty) result.
Proof.
 intros * [Hl Hlv] [Hr Hrv] Hop; split.
 - eapply eval_binop with (t1:=E0) (t2:=E0); eauto.
 - eapply esr_binop; eauto.
Qed.

Lemma pure_cast : forall ge env m operand ty value result,
 pure_rvalue ge env m operand value ->
 sem_cast value (typeof operand) ty m = Some result ->
 pure_rvalue ge env m (Ecast operand ty) result.
Proof.
 intros * [He Hv] Hcast; split.
 - constructor; exact He.
 - eapply esr_cast; eauto.
Qed.

Lemma pure_condition_evaluates : forall ge env m guard yes no ty gv decision result,
 pure_rvalue ge env m guard gv ->
 bool_val gv (typeof guard) m = Some decision ->
 pure_rvalue ge env m (if decision then yes else no) result ->
 sem_cast result (typeof (if decision then yes else no)) ty m = Some result ->
 eval_expression ge env m (Econdition guard yes no ty) E0 m result.
Proof.
 intros * [Hg Hgv] Hbool [Hb Hbv] Hcast.
 eapply eval_expression_intro; [|constructor].
 eapply eval_condition with (t1:=E0) (t2:=E0); eauto.
Qed.

Lemma checked_shift32_on_pure_operands : forall ge env m op sign lhs rhs lv rv g expr g' i',
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 typeof lhs = Ctypes.Tint I32 sign noattr -> typeof rhs = Ctypes.Tint I32 sign noattr ->
 pure_rvalue ge env m lhs (Values.Vint lv) -> pure_rvalue ge env m rhs (Values.Vint rv) ->
 check_shift op (Econs lhs (Econs rhs Enil)) (Values.Vint Int.zero)
   (Ctypes.Tint I32 sign noattr) g = Res expr g' i' ->
 eval_expression ge env m expr E0 m (Values.Vint (guarded_shift32_result op sign lv rv)).
Proof.
 intros * Hop Hlty Hrty Hl Hr Hrun.
 unfold check_shift, SimplExpr.ret in Hrun; simpl in Hrun; inversion Hrun; subst expr.
 assert (Hg : pure_rvalue ge env m
   (Ebinop Olt (Ecast rhs (Ctypes.Tint I32 Unsigned noattr))
     (Eval (Values.Vint Int.iwordsize) (Ctypes.Tint I32 Unsigned noattr)) tint)
   (Val.of_bool (Int.ltu rv Int.iwordsize))).
 { eapply pure_binary.
   - eapply pure_cast; [exact Hr|]. rewrite Hrty; destruct sign; reflexivity.
   - apply pure_literal.
   - reflexivity. }
 unfold guarded_shift32_result.
 destruct (Int.ltu rv Int.iwordsize) eqn:Hvalid.
 - eapply pure_condition_evaluates with (decision:=true).
   + exact Hg.
   + reflexivity.
   + eapply pure_binary; [exact Hl|exact Hr|].
     rewrite Hlty,Hrty. destruct Hop as [Hop|Hop]; subst op; destruct sign; cbn; rewrite Hvalid; reflexivity.
   + destruct Hop as [Hop|Hop]; subst op; destruct sign; reflexivity.
 - eapply pure_condition_evaluates with (decision:=false).
   + exact Hg.
   + reflexivity.
   + apply pure_literal.
   + destruct sign; reflexivity.
Qed.

Definition divmod_operand_guard32 sign lhs rhs :=
 let ty := Ctypes.Tint I32 sign noattr in
 Ebinop Oor (Ebinop Oeq rhs (Eval (Values.Vint Int.zero) ty) tint)
  (match sign with
   | Signed => Ebinop Oand
      (Ebinop Oeq lhs (Eval (Values.Vint (Int.repr Int.min_signed)) ty) tint)
      (Ebinop Oeq rhs (Eval (Values.Vint Int.mone) ty) tint) tint
   | Unsigned => Eval (Values.Vint Int.zero) tint
   end) tint.

Lemma divmod_operand_guard32_evaluates : forall ge env m sign lhs rhs lv rv,
 typeof lhs = Ctypes.Tint I32 sign noattr -> typeof rhs = Ctypes.Tint I32 sign noattr ->
 pure_rvalue ge env m lhs (Values.Vint lv) -> pure_rvalue ge env m rhs (Values.Vint rv) ->
 pure_rvalue ge env m (divmod_operand_guard32 sign lhs rhs)
  (Val.of_bool (BeePL_sem.check_unsafe_op Odiv sign (BeePL_values.Vint lv) (BeePL_values.Vint rv))).
Proof.
 intros * Hlty Hrty Hl Hr.
 assert (E : forall operand value constant,
   typeof operand = Ctypes.Tint I32 sign noattr ->
   pure_rvalue ge env m operand (Values.Vint value) ->
   pure_rvalue ge env m (Ebinop Oeq operand
     (Eval (Values.Vint constant) (Ctypes.Tint I32 sign noattr)) tint)
     (Val.of_bool (Int.eq value constant))).
 { intros * Hty Hp. eapply pure_binary; [exact Hp|apply pure_literal|].
   rewrite Hty; destruct sign; reflexivity. }
 unfold divmod_operand_guard32. destruct sign.
 - assert (Hunsafe : BeePL_sem.check_unsafe_op Odiv Signed (BeePL_values.Vint lv) (BeePL_values.Vint rv) =
       orb (Int.eq rv Int.zero) (andb (Int.eq lv (Int.repr Int.min_signed)) (Int.eq rv Int.mone))).
   { unfold BeePL_sem.check_unsafe_op, BeePL_values.is_zero_val, BeePL_values.is_overflow_vals.
     destruct (Int.eq rv Int.zero), (Int.eq lv (Int.repr Int.min_signed)), (Int.eq rv Int.mone); reflexivity. }
   rewrite Hunsafe.
   eapply pure_binary; [exact (E rhs rv Int.zero Hrty Hr)| |apply canonical_boolean_or].
   eapply pure_binary; [exact (E lhs lv (Int.repr Int.min_signed) Hlty Hl)|exact (E rhs rv Int.mone Hrty Hr)|apply canonical_boolean_and].
 - assert (Hunsafe : BeePL_sem.check_unsafe_op Odiv Unsigned (BeePL_values.Vint lv) (BeePL_values.Vint rv) =
       orb (Int.eq rv Int.zero) false).
   { unfold BeePL_sem.check_unsafe_op, BeePL_values.is_zero_val. destruct (Int.eq rv Int.zero); reflexivity. }
   rewrite Hunsafe.
   eapply pure_binary with (rv:=Val.of_bool false); [exact (E rhs rv Int.zero Hrty Hr)|apply pure_literal|apply canonical_boolean_or].
Qed.

Lemma checked_divmod32_on_pure_operands : forall ge env m op sign lhs rhs lv rv g expr g' i',
 (op = Odiv \/ op = Omod) ->
 typeof lhs = Ctypes.Tint I32 sign noattr -> typeof rhs = Ctypes.Tint I32 sign noattr ->
 pure_rvalue ge env m lhs (Values.Vint lv) -> pure_rvalue ge env m rhs (Values.Vint rv) ->
 check_divmod op (Econs lhs (Econs rhs Enil)) (Values.Vint Int.zero)
   (Ctypes.Tint I32 sign noattr) g = Res expr g' i' ->
 eval_expression ge env m expr E0 m (Values.Vint (guarded_divmod32_result op sign lv rv)).
Proof.
 intros * Hop Hlty Hrty Hl Hr Hrun.
 assert (Hexpr : expr = Econdition (divmod_operand_guard32 sign lhs rhs)
   (Eval (Values.Vint Int.zero) (Ctypes.Tint I32 sign noattr))
   (Ebinop op lhs rhs (Ctypes.Tint I32 sign noattr)) (Ctypes.Tint I32 sign noattr)).
 { unfold check_divmod, SimplExpr.ret in Hrun. destruct sign; inversion Hrun; reflexivity. }
 subst expr.
 pose proof (divmod_operand_guard32_evaluates ge env m sign lhs rhs lv rv Hlty Hrty Hl Hr) as Hg.
 rewrite <- (divmod_unsafe_same op sign (BeePL_values.Vint lv) (BeePL_values.Vint rv) Hop) in Hg.
 unfold guarded_divmod32_result.
 destruct (BeePL_sem.check_unsafe_op op sign (BeePL_values.Vint lv) (BeePL_values.Vint rv)) eqn:Hunsafe.
 - eapply pure_condition_evaluates with (decision:=true).
   + exact Hg.
   + unfold divmod_operand_guard32; reflexivity.
   + apply pure_literal.
   + destruct sign; reflexivity.
 - eapply pure_condition_evaluates with (decision:=false).
   + exact Hg.
   + unfold divmod_operand_guard32; reflexivity.
   + eapply pure_binary; [exact Hl|exact Hr|]. rewrite Hlty,Hrty.
     apply safe_divmod32_computes; assumption.
   + destruct sign; reflexivity.
Qed.

Lemma checked_shift64_on_pure_operands : forall ge env m op sign lhs rhs lv rv g expr g' i',
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 typeof lhs = Ctypes.Tlong sign noattr -> typeof rhs = Ctypes.Tlong sign noattr ->
 pure_rvalue ge env m lhs (Values.Vlong lv) -> pure_rvalue ge env m rhs (Values.Vlong rv) ->
 check_shift op (Econs lhs (Econs rhs Enil)) (Values.Vlong Int64.zero)
   (Ctypes.Tlong sign noattr) g = Res expr g' i' ->
 eval_expression ge env m expr E0 m (Values.Vlong (guarded_shift64_result op sign lv rv)).
Proof.
 intros * Hop Hlty Hrty Hl Hr Hrun.
 unfold check_shift, SimplExpr.ret in Hrun; simpl in Hrun; inversion Hrun; subst expr.
 assert (Hg : pure_rvalue ge env m
   (Ebinop Olt (Ecast rhs (Ctypes.Tlong Unsigned noattr))
     (Eval (Values.Vlong Int64.iwordsize) (Ctypes.Tlong Unsigned noattr)) tint)
   (Val.of_bool (Int64.ltu rv Int64.iwordsize))).
 { eapply pure_binary.
   - eapply pure_cast; [exact Hr|]. rewrite Hrty; destruct sign; reflexivity.
   - apply pure_literal.
   - reflexivity. }
 unfold guarded_shift64_result.
 destruct (Int64.ltu rv Int64.iwordsize) eqn:Hvalid.
 - eapply pure_condition_evaluates with (decision:=true).
   + exact Hg.
   + reflexivity.
   + eapply pure_binary; [exact Hl|exact Hr|].
     rewrite Hlty,Hrty. destruct Hop as [Hop|Hop]; subst op; destruct sign; cbn; rewrite Hvalid; reflexivity.
   + destruct Hop as [Hop|Hop]; subst op; destruct sign; reflexivity.
 - eapply pure_condition_evaluates with (decision:=false).
   + exact Hg.
   + reflexivity.
   + apply pure_literal.
   + destruct sign; reflexivity.
Qed.

Definition divmod_operand_guard64 sign lhs rhs :=
 let ty := Ctypes.Tlong sign noattr in
 Ebinop Oor (Ebinop Oeq rhs (Eval (Values.Vlong Int64.zero) ty) tint)
  (match sign with
   | Signed => Ebinop Oand
      (Ebinop Oeq lhs (Eval (Values.Vlong (Int64.repr Int64.min_signed)) ty) tint)
      (Ebinop Oeq rhs (Eval (Values.Vlong Int64.mone) ty) tint) tint
   | Unsigned => Eval (Values.Vint Int.zero) tint
   end) tint.

Lemma divmod_operand_guard64_evaluates : forall ge env m sign lhs rhs lv rv,
 typeof lhs = Ctypes.Tlong sign noattr -> typeof rhs = Ctypes.Tlong sign noattr ->
 pure_rvalue ge env m lhs (Values.Vlong lv) -> pure_rvalue ge env m rhs (Values.Vlong rv) ->
 pure_rvalue ge env m (divmod_operand_guard64 sign lhs rhs)
  (Val.of_bool (BeePL_sem.check_unsafe_op Odiv sign (BeePL_values.Vint64 lv) (BeePL_values.Vint64 rv))).
Proof.
 intros * Hlty Hrty Hl Hr.
 assert (E : forall operand value constant,
   typeof operand = Ctypes.Tlong sign noattr ->
   pure_rvalue ge env m operand (Values.Vlong value) ->
   pure_rvalue ge env m (Ebinop Oeq operand
     (Eval (Values.Vlong constant) (Ctypes.Tlong sign noattr)) tint)
     (Val.of_bool (Int64.eq value constant))).
 { intros * Hty Hp. eapply pure_binary; [exact Hp|apply pure_literal|].
   rewrite Hty; destruct sign; reflexivity. }
 unfold divmod_operand_guard64. destruct sign.
 - assert (Hunsafe : BeePL_sem.check_unsafe_op Odiv Signed (BeePL_values.Vint64 lv) (BeePL_values.Vint64 rv) =
       orb (Int64.eq rv Int64.zero) (andb (Int64.eq lv (Int64.repr Int64.min_signed)) (Int64.eq rv Int64.mone))).
   { unfold BeePL_sem.check_unsafe_op, BeePL_values.is_zero_val, BeePL_values.is_overflow_vals.
     destruct (Int64.eq rv Int64.zero), (Int64.eq lv (Int64.repr Int64.min_signed)), (Int64.eq rv Int64.mone); reflexivity. }
   rewrite Hunsafe.
   eapply pure_binary; [exact (E rhs rv Int64.zero Hrty Hr)| |apply canonical_boolean_or].
   eapply pure_binary; [exact (E lhs lv (Int64.repr Int64.min_signed) Hlty Hl)|exact (E rhs rv Int64.mone Hrty Hr)|apply canonical_boolean_and].
 - assert (Hunsafe : BeePL_sem.check_unsafe_op Odiv Unsigned (BeePL_values.Vint64 lv) (BeePL_values.Vint64 rv) =
       orb (Int64.eq rv Int64.zero) false).
   { unfold BeePL_sem.check_unsafe_op, BeePL_values.is_zero_val. destruct (Int64.eq rv Int64.zero); reflexivity. }
   rewrite Hunsafe.
   eapply pure_binary with (rv:=Val.of_bool false); [exact (E rhs rv Int64.zero Hrty Hr)|apply pure_literal|apply canonical_boolean_or].
Qed.

Lemma checked_divmod64_on_pure_operands : forall ge env m op sign lhs rhs lv rv g expr g' i',
 (op = Odiv \/ op = Omod) ->
 typeof lhs = Ctypes.Tlong sign noattr -> typeof rhs = Ctypes.Tlong sign noattr ->
 pure_rvalue ge env m lhs (Values.Vlong lv) -> pure_rvalue ge env m rhs (Values.Vlong rv) ->
 check_divmod op (Econs lhs (Econs rhs Enil)) (Values.Vlong Int64.zero)
   (Ctypes.Tlong sign noattr) g = Res expr g' i' ->
 eval_expression ge env m expr E0 m (Values.Vlong (guarded_divmod64_result op sign lv rv)).
Proof.
 intros * Hop Hlty Hrty Hl Hr Hrun.
 assert (Hexpr : expr = Econdition (divmod_operand_guard64 sign lhs rhs)
   (Eval (Values.Vlong Int64.zero) (Ctypes.Tlong sign noattr))
   (Ebinop op lhs rhs (Ctypes.Tlong sign noattr)) (Ctypes.Tlong sign noattr)).
 { unfold check_divmod, SimplExpr.ret in Hrun. destruct sign; inversion Hrun; reflexivity. }
 subst expr.
 pose proof (divmod_operand_guard64_evaluates ge env m sign lhs rhs lv rv Hlty Hrty Hl Hr) as Hg.
 rewrite <- (divmod_unsafe_same op sign (BeePL_values.Vint64 lv) (BeePL_values.Vint64 rv) Hop) in Hg.
 unfold guarded_divmod64_result.
 destruct (BeePL_sem.check_unsafe_op op sign (BeePL_values.Vint64 lv) (BeePL_values.Vint64 rv)) eqn:Hunsafe.
 - eapply pure_condition_evaluates with (decision:=true).
   + exact Hg.
   + unfold divmod_operand_guard64; reflexivity.
   + apply pure_literal.
   + destruct sign; reflexivity.
 - eapply pure_condition_evaluates with (decision:=false).
   + exact Hg.
   + unfold divmod_operand_guard64; reflexivity.
   + eapply pure_binary; [exact Hl|exact Hr|]. rewrite Hlty,Hrty.
     apply safe_divmod64_computes; assumption.
   + destruct sign; reflexivity.
Qed.

Definition generated_guard op operands zero ty :=
 match op with
 | Odiv => check_div operands zero ty
 | Omod => check_mod operands zero ty
 | Oshl => check_shl operands zero ty
 | Oshr => check_shr operands zero ty
 | _ => SimplExpr.error (Errors.msg "COMPILER ERROR: Expected guarded binary operator")
 end.
Definition guarded_result32 op sign lhs rhs :=
 match op with
 | Oshl | Oshr => guarded_shift32_result op sign lhs rhs
 | _ => guarded_divmod32_result op sign lhs rhs
 end.
Definition guarded_result64 op sign lhs rhs :=
 match op with
 | Oshl | Oshr => guarded_shift64_result op sign lhs rhs
 | _ => guarded_divmod64_result op sign lhs rhs
 end.

Lemma generated_guard32_evaluates : forall ge env m op sign lhs rhs lv rv g expr g' i',
 typeof lhs = Ctypes.Tint I32 sign noattr -> typeof rhs = Ctypes.Tint I32 sign noattr ->
 pure_rvalue ge env m lhs (Values.Vint lv) -> pure_rvalue ge env m rhs (Values.Vint rv) ->
 generated_guard op (Econs lhs (Econs rhs Enil)) (Values.Vint Int.zero)
   (Ctypes.Tint I32 sign noattr) g = Res expr g' i' ->
 typeof expr = Ctypes.Tint I32 sign noattr /\
 eval_expression ge env m expr E0 m (Values.Vint (guarded_result32 op sign lv rv)).
Proof.
 intros * Hlty Hrty Hl Hr Hrun.
 destruct op; cbn [generated_guard SimplExpr.error] in Hrun; try discriminate;
 split.
 all: try (unfold check_div, check_mod, check_shl, check_shr, check_divmod, check_shift,
   SimplExpr.ret in Hrun; destruct sign; inversion Hrun; reflexivity).
 all: unfold guarded_result32.
 all: first [eapply checked_divmod32_on_pure_operands | eapply checked_shift32_on_pure_operands];
   [auto|exact Hlty|exact Hrty|exact Hl|exact Hr|exact Hrun].
Qed.

Lemma generated_guard64_evaluates : forall ge env m op sign lhs rhs lv rv g expr g' i',
 typeof lhs = Ctypes.Tlong sign noattr -> typeof rhs = Ctypes.Tlong sign noattr ->
 pure_rvalue ge env m lhs (Values.Vlong lv) -> pure_rvalue ge env m rhs (Values.Vlong rv) ->
 generated_guard op (Econs lhs (Econs rhs Enil)) (Values.Vlong Int64.zero)
   (Ctypes.Tlong sign noattr) g = Res expr g' i' ->
 typeof expr = Ctypes.Tlong sign noattr /\
 eval_expression ge env m expr E0 m (Values.Vlong (guarded_result64 op sign lv rv)).
Proof.
 intros * Hlty Hrty Hl Hr Hrun.
 destruct op; cbn [generated_guard SimplExpr.error] in Hrun; try discriminate;
 split.
 all: try (unfold check_div, check_mod, check_shl, check_shr, check_divmod, check_shift,
   SimplExpr.ret in Hrun; destruct sign; inversion Hrun; reflexivity).
 all: unfold guarded_result64.
 all: first [eapply checked_divmod64_on_pure_operands | eapply checked_shift64_on_pure_operands];
   [auto|exact Hlty|exact Hrty|exact Hl|exact Hr|exact Hrun].
Qed.

Lemma capture_sequence_evaluation : forall ge env initial left_memory final
 lhs rhs left_temp right_temp ty left_trace right_trace left_saved right_saved guard result,
 eval_expr ge env initial RV (Eassign (Evar left_temp ty) lhs ty)
   left_trace left_memory (Eval left_saved ty) ->
 eval_expr ge env left_memory RV (Eassign (Evar right_temp ty) rhs ty)
   right_trace final (Eval right_saved ty) ->
 typeof guard = ty -> eval_expression ge env final guard E0 final result ->
 eval_expression ge env initial
   (Ecomma (Eassign (Evar left_temp ty) lhs ty)
     (Ecomma (Eassign (Evar right_temp ty) rhs ty) guard ty) ty)
   (left_trace ** right_trace) final result.
Proof.
 intros * Hl Hr Hty Hguard.
 inversion Hguard as [env0 m0 e0 t0 m1 e1 v1 He Hv]; subst.
 eapply eval_expression_intro; [|exact Hv].
 eapply eval_comma with (v1:=left_saved); [exact Hl|apply esr_val| |reflexivity].
 replace right_trace with (right_trace ** E0) by (unfold E0,Eapp; apply app_nil_r).
 eapply eval_comma with (v1:=right_saved); [exact Hr|apply esr_val|exact He|reflexivity].
Qed.

Theorem guarded_binary32_captures_once : forall ge env initial lhs left_trace left_evaluated
    left_value left_temp left_block sign lv,
 let ty := Ctypes.Tint I32 sign noattr in
 eval_expression ge env initial lhs left_trace left_evaluated left_value ->
 PTree.get left_temp env = Some (left_block,ty) ->
 Cop.sem_cast left_value (typeof lhs) ty left_evaluated = Some (Values.Vint lv) ->
 Mem.valid_access left_evaluated Mint32 left_block 0 Writable ->
 exists left_memory,
 Mem.store Mint32 left_evaluated left_block 0 (Values.Vint lv) = Some left_memory /\
 forall rhs right_trace right_evaluated right_value right_temp right_block rv
    op generator guard generator' increase,
 eval_expression ge env left_memory rhs right_trace right_evaluated right_value ->
 Mem.unchanged_on (fun block _ => block = left_block) left_memory right_evaluated ->
 PTree.get right_temp env = Some (right_block,ty) -> left_block <> right_block ->
 Cop.sem_cast right_value (typeof rhs) ty right_evaluated = Some (Values.Vint rv) ->
 Mem.valid_access right_evaluated Mint32 right_block 0 Writable ->
 generated_guard op
   (Econs (Evalof (Evar left_temp ty) ty) (Econs (Evalof (Evar right_temp ty) ty) Enil))
   (Values.Vint Int.zero) ty generator = Res guard generator' increase ->
 exists final,
 Mem.store Mint32 right_evaluated right_block 0 (Values.Vint rv) = Some final /\
 Mem.load Mint32 final left_block 0 = Some (Values.Vint lv) /\
 Mem.load Mint32 final right_block 0 = Some (Values.Vint rv) /\
 eval_expression ge env initial
   (Ecomma (Eassign (Evar left_temp ty) lhs ty)
     (Ecomma (Eassign (Evar right_temp ty) rhs ty) guard ty) ty)
   (left_trace ** right_trace) final (Values.Vint (guarded_result32 op sign lv rv)).
Proof.
 intros ge env initial lhs left_trace left_evaluated left_value left_temp left_block sign lv
   ty Hleft Hleftenv Hleftcast Hleftaccess.
 assert (Hmode : access_mode ty = By_value Mint32) by (destruct sign; reflexivity).
 assert (Hvolatile : type_is_volatile ty = false) by reflexivity.
 destruct (binary_capture_prefix ge env initial lhs left_trace left_evaluated left_value
   left_temp left_block ty Mint32 (Values.Vint lv) Hleft Hleftenv Hmode Hvolatile
   Hleftcast Hleftaccess eq_refl) as [left_memory [Hstore [Hcapture Hnext]]].
 exists left_memory; split; [exact Hstore|].
 intros * Hright Hframe Hrightenv Hdistinct Hrightcast Hrightaccess Hrun.
 destruct (Hnext rhs right_trace right_evaluated right_value right_temp right_block ty Mint32
   (Values.Vint rv) Hright Hframe Hrightenv Hdistinct Hmode Hvolatile Hrightcast Hrightaccess eq_refl)
   as [final [Hstore2 [Hcapture2 [Hload1 [Hload2 Hrest]]]]].
 assert (Hp1 : pure_rvalue ge env final (Evalof (Evar left_temp ty) ty) (Values.Vint lv)).
 { eapply pure_local_read; eauto. }
 assert (Hp2 : pure_rvalue ge env final (Evalof (Evar right_temp ty) ty) (Values.Vint rv)).
 { eapply pure_local_read; eauto. }
 destruct (generated_guard32_evaluates ge env final op sign (Evalof (Evar left_temp ty) ty) (Evalof (Evar right_temp ty) ty) lv rv generator guard generator' increase
   eq_refl eq_refl Hp1 Hp2 Hrun) as [Hguardty Hguard].
 exists final; split; [exact Hstore2|]. split; [exact Hload1|]. split; [exact Hload2|].
 eapply capture_sequence_evaluation; eauto.
Qed.

Theorem guarded_binary64_captures_once : forall ge env initial lhs left_trace left_evaluated
    left_value left_temp left_block sign lv,
 let ty := Ctypes.Tlong sign noattr in
 eval_expression ge env initial lhs left_trace left_evaluated left_value ->
 PTree.get left_temp env = Some (left_block,ty) ->
 Cop.sem_cast left_value (typeof lhs) ty left_evaluated = Some (Values.Vlong lv) ->
 Mem.valid_access left_evaluated Mint64 left_block 0 Writable ->
 exists left_memory,
 Mem.store Mint64 left_evaluated left_block 0 (Values.Vlong lv) = Some left_memory /\
 forall rhs right_trace right_evaluated right_value right_temp right_block rv
    op generator guard generator' increase,
 eval_expression ge env left_memory rhs right_trace right_evaluated right_value ->
 Mem.unchanged_on (fun block _ => block = left_block) left_memory right_evaluated ->
 PTree.get right_temp env = Some (right_block,ty) -> left_block <> right_block ->
 Cop.sem_cast right_value (typeof rhs) ty right_evaluated = Some (Values.Vlong rv) ->
 Mem.valid_access right_evaluated Mint64 right_block 0 Writable ->
 generated_guard op
   (Econs (Evalof (Evar left_temp ty) ty) (Econs (Evalof (Evar right_temp ty) ty) Enil))
   (Values.Vlong Int64.zero) ty generator = Res guard generator' increase ->
 exists final,
 Mem.store Mint64 right_evaluated right_block 0 (Values.Vlong rv) = Some final /\
 Mem.load Mint64 final left_block 0 = Some (Values.Vlong lv) /\
 Mem.load Mint64 final right_block 0 = Some (Values.Vlong rv) /\
 eval_expression ge env initial
   (Ecomma (Eassign (Evar left_temp ty) lhs ty)
     (Ecomma (Eassign (Evar right_temp ty) rhs ty) guard ty) ty)
   (left_trace ** right_trace) final (Values.Vlong (guarded_result64 op sign lv rv)).
Proof.
 intros ge env initial lhs left_trace left_evaluated left_value left_temp left_block sign lv
   ty Hleft Hleftenv Hleftcast Hleftaccess.
 assert (Hmode : access_mode ty = By_value Mint64) by (destruct sign; reflexivity).
 assert (Hvolatile : type_is_volatile ty = false) by reflexivity.
 destruct (binary_capture_prefix ge env initial lhs left_trace left_evaluated left_value
   left_temp left_block ty Mint64 (Values.Vlong lv) Hleft Hleftenv Hmode Hvolatile
   Hleftcast Hleftaccess eq_refl) as [left_memory [Hstore [Hcapture Hnext]]].
 exists left_memory; split; [exact Hstore|].
 intros * Hright Hframe Hrightenv Hdistinct Hrightcast Hrightaccess Hrun.
 destruct (Hnext rhs right_trace right_evaluated right_value right_temp right_block ty Mint64
   (Values.Vlong rv) Hright Hframe Hrightenv Hdistinct Hmode Hvolatile Hrightcast Hrightaccess eq_refl)
   as [final [Hstore2 [Hcapture2 [Hload1 [Hload2 Hrest]]]]].
 assert (Hp1 : pure_rvalue ge env final (Evalof (Evar left_temp ty) ty) (Values.Vlong lv)).
 { eapply pure_local_read; eauto. }
 assert (Hp2 : pure_rvalue ge env final (Evalof (Evar right_temp ty) ty) (Values.Vlong rv)).
 { eapply pure_local_read; eauto. }
 destruct (generated_guard64_evaluates ge env final op sign (Evalof (Evar left_temp ty) ty) (Evalof (Evar right_temp ty) ty) lv rv generator guard generator' increase
   eq_refl eq_refl Hp1 Hp2 Hrun) as [Hguardty Hguard].
 exists final; split; [exact Hstore2|]. split; [exact Hload1|]. split; [exact Hload2|].
 eapply capture_sequence_evaluation; eauto.
Qed.

Print Assumptions guarded_binary32_captures_once.
Print Assumptions guarded_binary64_captures_once.

(* This is the executable helper's exact shape, rather than a separately
   invented capture expression.  The returned context records both slots. *)
Lemma guarded_binop_capture_shape : forall op source_lhs source_rhs lhs rhs ty ctx bctx
 g expression ctx' bctx' g' increase,
 guarded_binop op (source_lhs :: source_rhs :: nil) (Econs lhs (Econs rhs Enil))
   ty ctx bctx g = Res (expression,ctx',bctx') g' increase ->
 exists li lname ri rname zero guard guard_generator guard_increase zero_generator zero_increase,
 let lty := BeePL.typeof_expr source_lhs in
 let rty := BeePL.typeof_expr source_rhs in
 let clty := BeeTypes.transBeePL_type lty in
 let crty := BeeTypes.transBeePL_type rty in
 let result_ty := BeeTypes.transBeePL_type ty in
 expression = Ecomma (Eassign (Evar li clty) lhs clty)
   (Ecomma (Eassign (Evar ri crty) rhs crty) guard result_ty) result_ty /\
 ctx' = (ri,rty,rname) :: (li,lty,lname) :: ctx /\ bctx' = bctx /\
 return_czero result_ty zero_generator = Res zero guard_generator zero_increase /\
 generated_guard op
   (Econs (Evalof (Evar li clty) clty) (Econs (Evalof (Evar ri crty) crty) Enil))
   zero result_ty guard_generator = Res guard g' guard_increase.
Proof.
 intros * Hrun.
 unfold guarded_binop, SimplExpr.bind2, SimplExpr.bind, SimplExpr.ret, SimplExpr.error in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E := fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair : (_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst;
 unfold generated_guard;
 repeat eexists; eauto.
Qed.
Print Assumptions guarded_binop_capture_shape.

Definition guarded_capture32_contract op sign lhs rhs li ri expression : Prop :=
 forall ge env initial left_trace left_evaluated left_value left_block lv,
 let ty := Ctypes.Tint I32 sign noattr in
 eval_expression ge env initial lhs left_trace left_evaluated left_value ->
 PTree.get li env = Some (left_block,ty) ->
 Cop.sem_cast left_value (typeof lhs) ty left_evaluated = Some (Values.Vint lv) ->
 Mem.valid_access left_evaluated Mint32 left_block 0 Writable ->
 exists left_memory,
 Mem.store Mint32 left_evaluated left_block 0 (Values.Vint lv) = Some left_memory /\
 forall right_trace right_evaluated right_value right_block rv,
 eval_expression ge env left_memory rhs right_trace right_evaluated right_value ->
 Mem.unchanged_on (fun block _ => block = left_block) left_memory right_evaluated ->
 PTree.get ri env = Some (right_block,ty) -> left_block <> right_block ->
 Cop.sem_cast right_value (typeof rhs) ty right_evaluated = Some (Values.Vint rv) ->
 Mem.valid_access right_evaluated Mint32 right_block 0 Writable ->
 exists final,
 Mem.store Mint32 right_evaluated right_block 0 (Values.Vint rv) = Some final /\
 Mem.load Mint32 final left_block 0 = Some (Values.Vint lv) /\
 Mem.load Mint32 final right_block 0 = Some (Values.Vint rv) /\
 eval_expression ge env initial expression (left_trace ** right_trace) final
   (Values.Vint (guarded_result32 op sign lv rv)).

Theorem actual_guarded_binop32_evaluation : forall op source_lhs source_rhs lhs rhs ty sign ctx bctx
 g expression ctx' bctx' g' increase,
 BeeTypes.transBeePL_type (BeePL.typeof_expr source_lhs) = Ctypes.Tint I32 sign noattr ->
 BeeTypes.transBeePL_type (BeePL.typeof_expr source_rhs) = Ctypes.Tint I32 sign noattr ->
 BeeTypes.transBeePL_type ty = Ctypes.Tint I32 sign noattr ->
 guarded_binop op (source_lhs :: source_rhs :: nil) (Econs lhs (Econs rhs Enil))
   ty ctx bctx g = Res (expression,ctx',bctx') g' increase ->
 exists li lname ri rname,
 ctx' = (ri,BeePL.typeof_expr source_rhs,rname) :: (li,BeePL.typeof_expr source_lhs,lname) :: ctx /\
 bctx' = bctx /\ guarded_capture32_contract op sign lhs rhs li ri expression.
Proof.
 intros * Hlt Hrt Hty Hrun.
 destruct (guarded_binop_capture_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun)
   as [li [lname [ri [rname [zero [guard [gg [gi [zg [zi Hshape]]]]]]]]]].
 cbn beta iota zeta in Hshape.
 destruct Hshape as [Hexpression [Hctx [Hbc [Hzero Hguard]]]].
 rewrite Hlt,Hrt,Hty in Hexpression,Hguard.
 rewrite Hty in Hzero. unfold return_czero,SimplExpr.ret in Hzero.
 inversion Hzero; subst zero.
 exists li,lname,ri,rname; split; [exact Hctx|]. split; [exact Hbc|].
 unfold guarded_capture32_contract.
 intros ge env initial lt le lvalue lb lv Hleft Henv Hcast Haccess.
 destruct (guarded_binary32_captures_once ge env initial lhs lt le lvalue li lb sign lv
   Hleft Henv Hcast Haccess) as [lm [Hstore Hnext]].
 exists lm; split; [exact Hstore|].
 intros rt re rvalue rb rv Hright Hframe Hrenv Hdistinct Hrcast Hraccess.
 destruct (Hnext rhs rt re rvalue ri rb rv op gg guard g' gi
   Hright Hframe Hrenv Hdistinct Hrcast Hraccess Hguard)
   as [final [Hs [Hl [Hr He]]]].
 exists final; split; [exact Hs|]. split; [exact Hl|]. split; [exact Hr|].
 rewrite Hexpression; exact He.
Qed.

Definition guarded_capture64_contract op sign lhs rhs li ri expression : Prop :=
 forall ge env initial left_trace left_evaluated left_value left_block lv,
 let ty := Ctypes.Tlong sign noattr in
 eval_expression ge env initial lhs left_trace left_evaluated left_value ->
 PTree.get li env = Some (left_block,ty) ->
 Cop.sem_cast left_value (typeof lhs) ty left_evaluated = Some (Values.Vlong lv) ->
 Mem.valid_access left_evaluated Mint64 left_block 0 Writable ->
 exists left_memory,
 Mem.store Mint64 left_evaluated left_block 0 (Values.Vlong lv) = Some left_memory /\
 forall right_trace right_evaluated right_value right_block rv,
 eval_expression ge env left_memory rhs right_trace right_evaluated right_value ->
 Mem.unchanged_on (fun block _ => block = left_block) left_memory right_evaluated ->
 PTree.get ri env = Some (right_block,ty) -> left_block <> right_block ->
 Cop.sem_cast right_value (typeof rhs) ty right_evaluated = Some (Values.Vlong rv) ->
 Mem.valid_access right_evaluated Mint64 right_block 0 Writable ->
 exists final,
 Mem.store Mint64 right_evaluated right_block 0 (Values.Vlong rv) = Some final /\
 Mem.load Mint64 final left_block 0 = Some (Values.Vlong lv) /\
 Mem.load Mint64 final right_block 0 = Some (Values.Vlong rv) /\
 eval_expression ge env initial expression (left_trace ** right_trace) final
   (Values.Vlong (guarded_result64 op sign lv rv)).

Theorem actual_guarded_binop64_evaluation : forall op source_lhs source_rhs lhs rhs ty sign ctx bctx
 g expression ctx' bctx' g' increase,
 BeeTypes.transBeePL_type (BeePL.typeof_expr source_lhs) = Ctypes.Tlong sign noattr ->
 BeeTypes.transBeePL_type (BeePL.typeof_expr source_rhs) = Ctypes.Tlong sign noattr ->
 BeeTypes.transBeePL_type ty = Ctypes.Tlong sign noattr ->
 guarded_binop op (source_lhs :: source_rhs :: nil) (Econs lhs (Econs rhs Enil))
   ty ctx bctx g = Res (expression,ctx',bctx') g' increase ->
 exists li lname ri rname,
 ctx' = (ri,BeePL.typeof_expr source_rhs,rname) :: (li,BeePL.typeof_expr source_lhs,lname) :: ctx /\
 bctx' = bctx /\ guarded_capture64_contract op sign lhs rhs li ri expression.
Proof.
 intros * Hlt Hrt Hty Hrun.
 destruct (guarded_binop_capture_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun)
   as [li [lname [ri [rname [zero [guard [gg [gi [zg [zi Hshape]]]]]]]]]].
 cbn beta iota zeta in Hshape.
 destruct Hshape as [Hexpression [Hctx [Hbc [Hzero Hguard]]]].
 rewrite Hlt,Hrt,Hty in Hexpression,Hguard.
 rewrite Hty in Hzero. unfold return_czero,SimplExpr.ret in Hzero.
 inversion Hzero; subst zero.
 exists li,lname,ri,rname; split; [exact Hctx|]. split; [exact Hbc|].
 unfold guarded_capture64_contract.
 intros ge env initial lt le lvalue lb lv Hleft Henv Hcast Haccess.
 destruct (guarded_binary64_captures_once ge env initial lhs lt le lvalue li lb sign lv
   Hleft Henv Hcast Haccess) as [lm [Hstore Hnext]].
 exists lm; split; [exact Hstore|].
 intros rt re rvalue rb rv Hright Hframe Hrenv Hdistinct Hrcast Hraccess.
 destruct (Hnext rhs rt re rvalue ri rb rv op gg guard g' gi
   Hright Hframe Hrenv Hdistinct Hrcast Hraccess Hguard)
   as [final [Hs [Hl [Hr He]]]].
 exists final; split; [exact Hs|]. split; [exact Hl|]. split; [exact Hr|].
 rewrite Hexpression; exact He.
Qed.

Print Assumptions actual_guarded_binop32_evaluation.
Print Assumptions actual_guarded_binop64_evaluation.
