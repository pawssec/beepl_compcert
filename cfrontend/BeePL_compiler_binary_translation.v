(* The guard tests below evaluate actual generated Csyntax expressions.  They
   establish the unsafe-count policy for both integer widths; they do not yet
   claim a simulation of temporary allocation or effectful operand evaluation. *)
Require Import Coqlib Errors Integers Maps AST Memory Ctypes Csyntax Cop SimplExpr Cstrategy Csyntaxdefs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_Csyntax.

Lemma unsigned_shift_guard32 : forall ge env m count sign attr,
 Cstrategy.eval_simple_rvalue ge env m
   (Ebinop Cop.Olt
     (Ecast (Eval (Values.Vint count) (Ctypes.Tint I32 sign attr))
       (Ctypes.Tint I32 Unsigned noattr))
     (Eval (Values.Vint Int.iwordsize) (Ctypes.Tint I32 Unsigned noattr))
     tint)
   (Values.Val.of_bool (Int.ltu count Int.iwordsize)).
Proof.
 intros. eapply Cstrategy.esr_binop.
 - eapply Cstrategy.esr_cast. constructor. destruct sign; reflexivity.
 - constructor.
 - reflexivity.
Qed.

Lemma unsigned_shift_guard64 : forall ge env m count sign attr,
 Cstrategy.eval_simple_rvalue ge env m
   (Ebinop Cop.Olt
     (Ecast (Eval (Values.Vlong count) (Ctypes.Tlong sign attr))
       (Ctypes.Tlong Unsigned noattr))
     (Eval (Values.Vlong Int64.iwordsize) (Ctypes.Tlong Unsigned noattr))
     tint)
   (Values.Val.of_bool (Int64.ltu count Int64.iwordsize)).
Proof.
 intros. eapply Cstrategy.esr_binop.
 - eapply Cstrategy.esr_cast. constructor. destruct sign; reflexivity.
 - constructor.
 - reflexivity.
Qed.

Lemma generated_shift_guard32_matches_source : forall op sign count m,
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 Cop.bool_val (Values.Val.of_bool (Int.ltu count Int.iwordsize)) tint m =
 Some (negb (check_unsafe_op op sign (Vint Int.zero) (Vint count))).
Proof.
 intros op sign count m Hop; destruct Hop as [Hop|Hop]; subst op; simpl;
 destruct (Int.ltu count Int.iwordsize); reflexivity.
Qed.

Lemma generated_shift_guard64_matches_source : forall op sign count m,
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 Cop.bool_val (Values.Val.of_bool (Int64.ltu count Int64.iwordsize)) tint m =
 Some (negb (check_unsafe_op op sign (Vint64 Int64.zero) (Vint64 count))).
Proof.
 intros op sign count m Hop; destruct Hop as [Hop|Hop]; subst op; simpl;
 destruct (Int64.ltu count Int64.iwordsize); reflexivity.
Qed.

Print Assumptions unsigned_shift_guard32.
Print Assumptions unsigned_shift_guard64.
Print Assumptions generated_shift_guard32_matches_source.
Print Assumptions generated_shift_guard64_matches_source.

Definition guarded_shift32_result op sign value count :=
 if Int.ltu count Int.iwordsize then
   match op with
   | Cop.Oshl => Int.shl value count
   | _ => match sign with Signed => Int.shr value count | Unsigned => Int.shru value count end
   end
 else Int.zero.

Lemma evaluated_shift32_correct : forall ge env m op sign value count,
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 let ty := Ctypes.Tint I32 sign noattr in
 let uty := Ctypes.Tint I32 Unsigned noattr in
 Cstrategy.eval_expression ge env m
   (Econdition
     (Ebinop Cop.Olt (Ecast (Eval (Values.Vint count) ty) uty)
       (Eval (Values.Vint Int.iwordsize) uty) tint)
     (Ebinop op (Eval (Values.Vint value) ty) (Eval (Values.Vint count) ty) ty)
     (Eval (Values.Vint Int.zero) ty) ty)
   Events.E0 m (Values.Vint (guarded_shift32_result op sign value count)).
Proof.
 intros ge env m op sign value count Hop ty uty.
 unfold guarded_shift32_result.
 destruct (Int.ltu count Int.iwordsize) eqn:Hcount.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=true)
     (v1:=Values.Val.of_bool true)
     (v':=Values.Vint (match op with Cop.Oshl => Int.shl value count | _ => match sign with Signed => Int.shr value count | Unsigned => Int.shru value count end end)) (t1:=Events.E0) (t2:=Events.E0).
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); [apply Cstrategy.eval_cast|]; constructor.
   + rewrite <- Hcount. apply unsigned_shift_guard32.
   + reflexivity.
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); constructor.
   + eapply Cstrategy.esr_binop; [constructor|constructor|].
     destruct Hop as [Hop|Hop]; subst op; destruct sign; cbn; rewrite Hcount; reflexivity.
   + destruct Hop as [Hop|Hop]; subst op; destruct sign; reflexivity.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=false)
     (v1:=Values.Val.of_bool false) (t1:=Events.E0) (t2:=Events.E0).
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); [apply Cstrategy.eval_cast|]; constructor.
   + rewrite <- Hcount. apply unsigned_shift_guard32.
   + reflexivity.
   + constructor.
   + constructor.
   + destruct sign; reflexivity.
Qed.

Definition guarded_shift64_result op sign value count :=
 if Int64.ltu count Int64.iwordsize then
   match op with
   | Cop.Oshl => Int64.shl value count
   | _ => match sign with Signed => Int64.shr value count | Unsigned => Int64.shru value count end
   end
 else Int64.zero.

Lemma evaluated_shift64_correct : forall ge env m op sign value count,
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 let ty := Ctypes.Tlong sign noattr in
 let uty := Ctypes.Tlong Unsigned noattr in
 Cstrategy.eval_expression ge env m
   (Econdition
     (Ebinop Cop.Olt (Ecast (Eval (Values.Vlong count) ty) uty)
       (Eval (Values.Vlong Int64.iwordsize) uty) tint)
     (Ebinop op (Eval (Values.Vlong value) ty) (Eval (Values.Vlong count) ty) ty)
     (Eval (Values.Vlong Int64.zero) ty) ty)
   Events.E0 m (Values.Vlong (guarded_shift64_result op sign value count)).
Proof.
 intros ge env m op sign value count Hop ty uty.
 unfold guarded_shift64_result.
 destruct (Int64.ltu count Int64.iwordsize) eqn:Hcount.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=true)
     (v1:=Values.Val.of_bool true)
     (v':=Values.Vlong (match op with Cop.Oshl => Int64.shl value count | _ => match sign with Signed => Int64.shr value count | Unsigned => Int64.shru value count end end)) (t1:=Events.E0) (t2:=Events.E0).
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); [apply Cstrategy.eval_cast|]; constructor.
   + rewrite <- Hcount. apply unsigned_shift_guard64.
   + reflexivity.
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); constructor.
   + eapply Cstrategy.esr_binop; [constructor|constructor|].
     destruct Hop as [Hop|Hop]; subst op; destruct sign; cbn; rewrite Hcount; reflexivity.
   + destruct Hop as [Hop|Hop]; subst op; destruct sign; reflexivity.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=false)
     (v1:=Values.Val.of_bool false) (t1:=Events.E0) (t2:=Events.E0).
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); [apply Cstrategy.eval_cast|]; constructor.
   + rewrite <- Hcount. apply unsigned_shift_guard64.
   + reflexivity.
   + constructor.
   + constructor.
   + destruct sign; reflexivity.
Qed.

Print Assumptions evaluated_shift32_correct.
Print Assumptions evaluated_shift64_correct.

Lemma canonical_boolean_and : forall ge m x y,
 Cop.sem_binary_operation ge Cop.Oand (Values.Val.of_bool x) tint
   (Values.Val.of_bool y) tint m = Some (Values.Val.of_bool (andb x y)).
Proof. intros; destruct x, y; reflexivity. Qed.
Lemma canonical_boolean_or : forall ge m x y,
 Cop.sem_binary_operation ge Cop.Oor (Values.Val.of_bool x) tint
   (Values.Val.of_bool y) tint m = Some (Values.Val.of_bool (orb x y)).
Proof. intros; destruct x, y; reflexivity. Qed.

Definition divmod_guard32 sign lhs rhs :=
 let ty := Ctypes.Tint I32 sign noattr in
 Ebinop Cop.Oor
   (Ebinop Cop.Oeq (Eval (Values.Vint rhs) ty) (Eval (Values.Vint Int.zero) ty) tint)
   (match sign with
    | Signed => Ebinop Cop.Oand
       (Ebinop Cop.Oeq (Eval (Values.Vint lhs) ty)
         (Eval (Values.Vint (Int.repr Int.min_signed)) ty) tint)
       (Ebinop Cop.Oeq (Eval (Values.Vint rhs) ty) (Eval (Values.Vint Int.mone) ty) tint) tint
    | Unsigned => Eval (Values.Vint Int.zero) tint
    end) tint.

Lemma divmod_guard32_matches_source : forall ge env m sign lhs rhs,
 Cstrategy.eval_simple_rvalue ge env m (divmod_guard32 sign lhs rhs)
   (Values.Val.of_bool (check_unsafe_op Cop.Odiv sign (Vint lhs) (Vint rhs))).
Proof.
 intros. unfold divmod_guard32.
 assert (E: forall x y s,
   Cstrategy.eval_simple_rvalue ge env m
    (Ebinop Cop.Oeq (Eval (Values.Vint x) (Ctypes.Tint I32 s noattr))
     (Eval (Values.Vint y) (Ctypes.Tint I32 s noattr)) tint)
    (Values.Val.of_bool (Int.eq x y))).
 { intros. eapply Cstrategy.esr_binop; [constructor|constructor|]. destruct s; reflexivity. }
 destruct sign.
 - assert (Hunsafe : check_unsafe_op Cop.Odiv Signed (Vint lhs) (Vint rhs) =
       orb (Int.eq rhs Int.zero) (andb (Int.eq lhs (Int.repr Int.min_signed)) (Int.eq rhs Int.mone))).
   { unfold check_unsafe_op, is_zero_val, is_overflow_vals.
     destruct (Int.eq rhs Int.zero), (Int.eq lhs (Int.repr Int.min_signed)), (Int.eq rhs Int.mone); reflexivity. }
   rewrite Hunsafe.
   eapply Cstrategy.esr_binop; [apply E| |apply canonical_boolean_or].
   eapply Cstrategy.esr_binop; [apply E|apply E|apply canonical_boolean_and].
 - assert (Hunsafe : check_unsafe_op Cop.Odiv Unsigned (Vint lhs) (Vint rhs) = orb (Int.eq rhs Int.zero) false).
   { unfold check_unsafe_op, is_zero_val. destruct (Int.eq rhs Int.zero); reflexivity. }
   rewrite Hunsafe.
   eapply Cstrategy.esr_binop with (v1:=Values.Val.of_bool (Int.eq rhs Int.zero)) (v2:=Values.Val.of_bool false); [apply E|constructor|apply canonical_boolean_or].
Qed.

Lemma actual_check_shift32_correct : forall ge env m op sign value count
    g ce g' i',
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 check_shift op
   (Econs (Eval (Values.Vint value) (Ctypes.Tint I32 sign noattr))
     (Econs (Eval (Values.Vint count) (Ctypes.Tint I32 sign noattr)) Enil))
   (Values.Vint Int.zero) (Ctypes.Tint I32 sign noattr) g = Res ce g' i' ->
 Cstrategy.eval_expression ge env m ce Events.E0 m
   (Values.Vint (guarded_shift32_result op sign value count)).
Proof.
 intros ge env m op sign value count g ce g' i' Hop Hrun.
 unfold check_shift, SimplExpr.ret in Hrun; simpl in Hrun.
 inversion Hrun; subst ce. apply evaluated_shift32_correct. exact Hop.
Qed.

Lemma actual_check_shift64_correct : forall ge env m op sign value count
    g ce g' i',
 (op = Cop.Oshl \/ op = Cop.Oshr) ->
 check_shift op
   (Econs (Eval (Values.Vlong value) (Ctypes.Tlong sign noattr))
     (Econs (Eval (Values.Vlong count) (Ctypes.Tlong sign noattr)) Enil))
   (Values.Vlong Int64.zero) (Ctypes.Tlong sign noattr) g = Res ce g' i' ->
 Cstrategy.eval_expression ge env m ce Events.E0 m
   (Values.Vlong (guarded_shift64_result op sign value count)).
Proof.
 intros ge env m op sign value count g ce g' i' Hop Hrun.
 unfold check_shift, SimplExpr.ret in Hrun; simpl in Hrun.
 inversion Hrun; subst ce. apply evaluated_shift64_correct. exact Hop.
Qed.

Print Assumptions actual_check_shift32_correct.
Print Assumptions actual_check_shift64_correct.
Print Assumptions divmod_guard32_matches_source.

Definition divmod_guard64 sign lhs rhs :=
 let ty := Ctypes.Tlong sign noattr in
 Ebinop Cop.Oor
   (Ebinop Cop.Oeq (Eval (Values.Vlong rhs) ty) (Eval (Values.Vlong Int64.zero) ty) tint)
   (match sign with
    | Signed => Ebinop Cop.Oand
       (Ebinop Cop.Oeq (Eval (Values.Vlong lhs) ty)
         (Eval (Values.Vlong (Int64.repr Int64.min_signed)) ty) tint)
       (Ebinop Cop.Oeq (Eval (Values.Vlong rhs) ty) (Eval (Values.Vlong Int64.mone) ty) tint) tint
    | Unsigned => Eval (Values.Vint Int.zero) tint
    end) tint.

Lemma divmod_guard64_matches_source : forall ge env m sign lhs rhs,
 Cstrategy.eval_simple_rvalue ge env m (divmod_guard64 sign lhs rhs)
   (Values.Val.of_bool (check_unsafe_op Cop.Odiv sign (Vint64 lhs) (Vint64 rhs))).
Proof.
 intros. unfold divmod_guard64.
 assert (E: forall x y s,
   Cstrategy.eval_simple_rvalue ge env m
    (Ebinop Cop.Oeq (Eval (Values.Vlong x) (Ctypes.Tlong s noattr))
     (Eval (Values.Vlong y) (Ctypes.Tlong s noattr)) tint)
    (Values.Val.of_bool (Int64.eq x y))).
 { intros. eapply Cstrategy.esr_binop; [constructor|constructor|]. destruct s; reflexivity. }
 destruct sign.
 - assert (Hunsafe : check_unsafe_op Cop.Odiv Signed (Vint64 lhs) (Vint64 rhs) =
       orb (Int64.eq rhs Int64.zero) (andb (Int64.eq lhs (Int64.repr Int64.min_signed)) (Int64.eq rhs Int64.mone))).
   { unfold check_unsafe_op, is_zero_val, is_overflow_vals.
     destruct (Int64.eq rhs Int64.zero), (Int64.eq lhs (Int64.repr Int64.min_signed)), (Int64.eq rhs Int64.mone); reflexivity. }
   rewrite Hunsafe.
   eapply Cstrategy.esr_binop; [apply E| |apply canonical_boolean_or].
   eapply Cstrategy.esr_binop; [apply E|apply E|apply canonical_boolean_and].
 - assert (Hunsafe : check_unsafe_op Cop.Odiv Unsigned (Vint64 lhs) (Vint64 rhs) = orb (Int64.eq rhs Int64.zero) false).
   { unfold check_unsafe_op, is_zero_val. destruct (Int64.eq rhs Int64.zero); reflexivity. }
   rewrite Hunsafe.
   eapply Cstrategy.esr_binop with (v1:=Values.Val.of_bool (Int64.eq rhs Int64.zero)) (v2:=Values.Val.of_bool false); [apply E|constructor|apply canonical_boolean_or].
Qed.


Print Assumptions divmod_guard64_matches_source.

Definition divmod32_value op sign lhs rhs :=
 match op, sign with
 | Cop.Odiv, Signed => Int.divs lhs rhs
 | Cop.Odiv, Unsigned => Int.divu lhs rhs
 | _, Signed => Int.mods lhs rhs
 | _, Unsigned => Int.modu lhs rhs
 end.
Definition guarded_divmod32_result op sign lhs rhs :=
 if check_unsafe_op op sign (Vint lhs) (Vint rhs)
 then Int.zero else divmod32_value op sign lhs rhs.

Lemma divmod_unsafe_same : forall op sign lhs rhs,
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 check_unsafe_op op sign lhs rhs = check_unsafe_op Cop.Odiv sign lhs rhs.
Proof. intros op sign lhs rhs [H|H]; subst op; reflexivity. Qed.

Lemma safe_divmod32_computes : forall ge m op sign lhs rhs,
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 check_unsafe_op op sign (Vint lhs) (Vint rhs) = false ->
 Cop.sem_binary_operation ge op (Values.Vint lhs) (Ctypes.Tint I32 sign noattr)
  (Values.Vint rhs) (Ctypes.Tint I32 sign noattr) m =
 Some (Values.Vint (divmod32_value op sign lhs rhs)).
Proof.
 intros ge m op sign lhs rhs [Hop|Hop] Hsafe; subst op; destruct sign;
 unfold Cop.sem_binary_operation, Cop.sem_div, Cop.sem_mod, Cop.sem_binarith, Cop.sem_cast;
 cbn; destruct Archi.ptr64; cbn; unfold check_unsafe_op, is_zero_val, is_overflow_vals in Hsafe;
 cbn in Hsafe;
 destruct (Int.eq rhs Int.zero), (Int.eq lhs (Int.repr (-2147483648))), (Int.eq rhs Int.mone);
 simpl in Hsafe |- *; try discriminate; reflexivity.
Qed.

Lemma evaluated_divmod32_correct : forall ge env m op sign lhs rhs,
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 let ty := Ctypes.Tint I32 sign noattr in
 Cstrategy.eval_expression ge env m
  (Econdition (divmod_guard32 sign lhs rhs) (Eval (Values.Vint Int.zero) ty)
    (Ebinop op (Eval (Values.Vint lhs) ty) (Eval (Values.Vint rhs) ty) ty) ty)
  Events.E0 m (Values.Vint (guarded_divmod32_result op sign lhs rhs)).
Proof.
 intros ge env m op sign lhs rhs Hop ty.
 assert (Hguard : Cstrategy.eval_expr ge env m Csem.RV (divmod_guard32 sign lhs rhs)
   Events.E0 m (divmod_guard32 sign lhs rhs)).
 { unfold divmod_guard32. destruct sign;
   repeat first [apply Cstrategy.eval_val | eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0)]. }
 pose proof (divmod_guard32_matches_source ge env m sign lhs rhs) as Hvalue.
 rewrite <- (divmod_unsafe_same op sign (Vint lhs) (Vint rhs) Hop) in Hvalue.
 unfold guarded_divmod32_result.
 destruct (check_unsafe_op op sign (Vint lhs) (Vint rhs)) eqn:Hunsafe.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=true) (v1:=Values.Val.of_bool true)
      (v':=Values.Vint Int.zero) (t1:=Events.E0) (t2:=Events.E0).
   + exact Hguard.
   + exact Hvalue.
   + reflexivity.
   + constructor.
   + constructor.
   + destruct sign; reflexivity.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=false) (v1:=Values.Val.of_bool false)
      (v':=Values.Vint (divmod32_value op sign lhs rhs)) (t1:=Events.E0) (t2:=Events.E0).
   + exact Hguard.
   + exact Hvalue.
   + reflexivity.
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); constructor.
   + eapply Cstrategy.esr_binop; [constructor|constructor|].
     apply safe_divmod32_computes; assumption.
   + destruct sign; reflexivity.
Qed.

Definition divmod64_value op sign lhs rhs :=
 match op, sign with
 | Cop.Odiv, Signed => Int64.divs lhs rhs
 | Cop.Odiv, Unsigned => Int64.divu lhs rhs
 | _, Signed => Int64.mods lhs rhs
 | _, Unsigned => Int64.modu lhs rhs
 end.
Definition guarded_divmod64_result op sign lhs rhs :=
 if check_unsafe_op op sign (Vint64 lhs) (Vint64 rhs)
 then Int64.zero else divmod64_value op sign lhs rhs.

Lemma safe_divmod64_computes : forall ge m op sign lhs rhs,
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 check_unsafe_op op sign (Vint64 lhs) (Vint64 rhs) = false ->
 Cop.sem_binary_operation ge op (Values.Vlong lhs) (Ctypes.Tlong sign noattr)
  (Values.Vlong rhs) (Ctypes.Tlong sign noattr) m =
 Some (Values.Vlong (divmod64_value op sign lhs rhs)).
Proof.
 intros ge m op sign lhs rhs [Hop|Hop] Hsafe; subst op; destruct sign;
 unfold Cop.sem_binary_operation, Cop.sem_div, Cop.sem_mod, Cop.sem_binarith, Cop.sem_cast;
 cbn; destruct Archi.ptr64; cbn; unfold check_unsafe_op, is_zero_val, is_overflow_vals in Hsafe;
 cbn in Hsafe;
 destruct (Int64.eq rhs Int64.zero), (Int64.eq lhs (Int64.repr (-9223372036854775808))), (Int64.eq rhs Int64.mone);
 simpl in Hsafe |- *; try discriminate; reflexivity.
Qed.

Lemma evaluated_divmod64_correct : forall ge env m op sign lhs rhs,
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 let ty := Ctypes.Tlong sign noattr in
 Cstrategy.eval_expression ge env m
  (Econdition (divmod_guard64 sign lhs rhs) (Eval (Values.Vlong Int64.zero) ty)
    (Ebinop op (Eval (Values.Vlong lhs) ty) (Eval (Values.Vlong rhs) ty) ty) ty)
  Events.E0 m (Values.Vlong (guarded_divmod64_result op sign lhs rhs)).
Proof.
 intros ge env m op sign lhs rhs Hop ty.
 assert (Hguard : Cstrategy.eval_expr ge env m Csem.RV (divmod_guard64 sign lhs rhs)
   Events.E0 m (divmod_guard64 sign lhs rhs)).
 { unfold divmod_guard64. destruct sign;
   repeat first [apply Cstrategy.eval_val | eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0)]. }
 pose proof (divmod_guard64_matches_source ge env m sign lhs rhs) as Hvalue.
 rewrite <- (divmod_unsafe_same op sign (Vint64 lhs) (Vint64 rhs) Hop) in Hvalue.
 unfold guarded_divmod64_result.
 destruct (check_unsafe_op op sign (Vint64 lhs) (Vint64 rhs)) eqn:Hunsafe.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=true) (v1:=Values.Val.of_bool true)
      (v':=Values.Vlong Int64.zero) (t1:=Events.E0) (t2:=Events.E0).
   + exact Hguard.
   + exact Hvalue.
   + reflexivity.
   + constructor.
   + constructor.
   + destruct sign; reflexivity.
 - eapply Cstrategy.eval_expression_intro; [|constructor].
   eapply Cstrategy.eval_condition with (b:=false) (v1:=Values.Val.of_bool false)
      (v':=Values.Vlong (divmod64_value op sign lhs rhs)) (t1:=Events.E0) (t2:=Events.E0).
   + exact Hguard.
   + exact Hvalue.
   + reflexivity.
   + eapply Cstrategy.eval_binop with (t1:=Events.E0) (t2:=Events.E0); constructor.
   + eapply Cstrategy.esr_binop; [constructor|constructor|].
     apply safe_divmod64_computes; assumption.
   + destruct sign; reflexivity.
Qed.

Lemma actual_check_divmod32_correct : forall ge env m op sign lhs rhs g ce g' i',
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 check_divmod op
   (Econs (Eval (Values.Vint lhs) (Ctypes.Tint I32 sign noattr))
     (Econs (Eval (Values.Vint rhs) (Ctypes.Tint I32 sign noattr)) Enil))
   (Values.Vint Int.zero) (Ctypes.Tint I32 sign noattr) g = Res ce g' i' ->
 Cstrategy.eval_expression ge env m ce Events.E0 m
   (Values.Vint (guarded_divmod32_result op sign lhs rhs)).
Proof.
 intros ge env m op sign lhs rhs g ce g' i' Hop Hrun.
 unfold check_divmod, SimplExpr.ret in Hrun.
 destruct sign; simpl in Hrun; inversion Hrun; subst ce.
 - exact (evaluated_divmod32_correct ge env m op Signed lhs rhs Hop).
 - exact (evaluated_divmod32_correct ge env m op Unsigned lhs rhs Hop).
Qed.

Lemma actual_check_divmod64_correct : forall ge env m op sign lhs rhs g ce g' i',
 (op = Cop.Odiv \/ op = Cop.Omod) ->
 check_divmod op
   (Econs (Eval (Values.Vlong lhs) (Ctypes.Tlong sign noattr))
     (Econs (Eval (Values.Vlong rhs) (Ctypes.Tlong sign noattr)) Enil))
   (Values.Vlong Int64.zero) (Ctypes.Tlong sign noattr) g = Res ce g' i' ->
 Cstrategy.eval_expression ge env m ce Events.E0 m
   (Values.Vlong (guarded_divmod64_result op sign lhs rhs)).
Proof.
 intros ge env m op sign lhs rhs g ce g' i' Hop Hrun.
 unfold check_divmod, SimplExpr.ret in Hrun.
 destruct sign; simpl in Hrun; inversion Hrun; subst ce.
 - exact (evaluated_divmod64_correct ge env m op Signed lhs rhs Hop).
 - exact (evaluated_divmod64_correct ge env m op Unsigned lhs rhs Hop).
Qed.

Print Assumptions actual_check_divmod32_correct.
Print Assumptions actual_check_divmod64_correct.
