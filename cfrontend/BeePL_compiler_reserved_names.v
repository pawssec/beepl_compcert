(* Checked reservation and complete function-entry local allocation. *)
(* Reserved source identifiers cannot be introduced as generated local storage.
   Compiler-context metadata is unchanged by expression/statement visitors. *)
Require Import List String ZArith Lia Coqlib Integers AST Maps Memory Csem SimplExpr.
Require Import BeeTypes BeePL BeePL_Csyntax BeePL_compiler_context_growth.
Import ListNotations.
Definition reserved_growth (reserved : list ident) (before after : compilation_context) :=
 forall id, In id reserved -> In id(map unzip_ident after) -> In id(map unzip_ident before).
Lemma reserved_growth_refl : forall r c, reserved_growth r c c.
Proof. unfold reserved_growth; auto. Qed.
Lemma reserved_growth_trans : forall r a b c,
 reserved_growth r a b -> reserved_growth r b c -> reserved_growth r a c.
Proof. unfold reserved_growth; firstorder. Qed.
Lemma reserved_growth_fresh : forall r c id ty tag,
 ~In id r -> reserved_growth r c ((id,ty,tag)::c).
Proof. unfold reserved_growth; intros r c id ty tag Hnot x Hx [E|Hin]; [subst; contradiction|exact Hin]. Qed.
Lemma reserved_exclusion_right : forall (used reserved : list ident) id,
 ~In id(used ++ reserved) -> ~In id reserved.
Proof. intros used reserved id H Hin; apply H,in_or_app; auto. Qed.
Lemma fresh_compiler_binding_reserved : forall source ty ctx bc g binding ctx' bc' g' ip,
 fresh_compiler_binding source ty ctx bc g=Res(binding,ctx',bc')g' ip ->
 reserved_identifiers bc'=reserved_identifiers bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Proof.
 intros * Hrun.
 unfold fresh_compiler_binding,SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E:=fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair:(_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; split; try reflexivity; try apply reserved_growth_refl.
 all: apply reserved_growth_fresh;
 match goal with E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?gf ?pi |- _ =>
 exact (reserved_exclusion_right used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) end.
Qed.

Lemma compiler_destination_reserved : forall selected ty ctx bc g id ctx' g' ip,
 compiler_destination selected ty ctx bc g=Res(id,ctx')g' ip ->
 reserved_growth(reserved_identifiers bc)ctx ctx'.
Proof.
 intros * Hrun. unfold compiler_destination,SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
   let rec descend t := lazymatch t with
   | context[match ?inner with _ => _ end] => descend inner
   | _ => let E:=fresh "Epart" in destruct t eqn:E
   end in descend scr;
   repeat match goal with pair:(_ * _)%type |- _ => destruct pair end;
   cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; try apply reserved_growth_refl.
 all: apply reserved_growth_fresh;
 match goal with E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?gf ?pi |- _ =>
 exact (reserved_exclusion_right used reserved id (actual_fresh_identifier _ _ _ _ _ _ _ E)) end.
Qed.

Lemma fresh_compiler_fields_reserved : forall fields ctx bc g bindings ctx' bc' g' ip,
 fresh_compiler_fields fields ctx bc g=Res(bindings,ctx',bc')g' ip ->
 reserved_identifiers bc'=reserved_identifiers bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Proof.
 induction fields as [|[field ty] fields IH]; intros * Hrun;
 cbn [fresh_compiler_fields] in Hrun;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in Hrun.
 - inversion Hrun; split; [reflexivity|apply reserved_growth_refl].
 - destruct (fresh_compiler_binding field ty ctx bc g) as [msg|[[binding mid] scope] gm pm] eqn:Hbinding;
   cbn [fst snd] in Hrun; try discriminate.
   destruct (fresh_compiler_fields fields mid scope gm) as [msg|[[rest final] finalscope] gf pf] eqn:Hfields;
   cbn [fst snd] in Hrun; try discriminate.
   destruct binding; inversion Hrun; subst;
   destruct (fresh_compiler_binding_reserved _ _ _ _ _ _ _ _ _ _ Hbinding) as [Rbinding Gbinding];
   destruct (IH _ _ _ _ _ _ _ _ Hfields) as [Rfields Gfields]; rewrite Rbinding in Gfields; split.
   all: first [congruence | eapply reserved_growth_trans; eassumption].
Qed.

Ltac normalize_reserved := repeat match goal with
 | H:reserved_identifiers ?a=reserved_identifiers ?b |- _ =>
   first [constr_eq a b; clear H | progress rewrite H in *; clear H]
 end.

Lemma guarded_binop_reserved_growth : forall op es ces ty ctx bc g ce ctx' bc' g' ip,
 guarded_binop op es ces ty ctx bc g=Res(ce,ctx',bc')g' ip ->
 bc'=bc /\ reserved_growth (reserved_identifiers bc) ctx ctx'.
Proof.
 intros op es ces ty ctx bc g ce ctx' bc' g' ip Hrun.
 unfold guarded_binop, SimplExpr.bind2, SimplExpr.bind, SimplExpr.ret, SimplExpr.error in Hrun.
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
     let rec descend t := lazymatch t with
       | context[match ?inner with _ => _ end] => descend inner
       | _ => let E := fresh "Epart" in destruct t eqn:E
       end in descend scr;
     repeat match goal with p : (_ * _)%type |- _ => destruct p end;
     cbn beta iota zeta in Hrun; try discriminate
 end;
 inversion Hrun; subst; split; try reflexivity.
 all: repeat match goal with
 | E : fresh_ident (seq.cat ?used ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof |- _ =>
 let HF := fresh "HF" in
 pose proof(reserved_exclusion_right used reserved id(actual_fresh_identifier _ _ _ _ _ _ _ E)) as HF; clear E
 end.
 all: match goal with |- reserved_growth _ _ (_ :: ?tail) => eapply reserved_growth_trans with (b:=tail) end; apply reserved_growth_fresh; assumption.
Qed.

Definition expression_reserved_safe (e : BeePL.expr) :=
 forall ctx bc g ce ctx' bc' g' proof,
 transBeePL_expr_expr e ctx bc g=Res(ce,ctx',bc')g' proof ->
 bc'=bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Lemma list_reserved_safe : forall es,
 (forall e,In e es -> expression_reserved_safe e) ->
 forall ctx bc g ces ctx' bc' g' proof,
 transBeePL_expr_exprs transBeePL_expr_expr es ctx bc g=Res(ces,ctx',bc')g' proof ->
 bc'=bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Proof.
 intros es; induction es as [|e rest IH]; intros Hall ctx bc g ces ctx' bc' g' proof H;
 cbn [transBeePL_expr_exprs] in H;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in H; cbn in H.
 - inversion H; subst; split; [reflexivity|apply reserved_growth_refl].
 - destruct(transBeePL_expr_expr e ctx bc g) as [msg|[[ce mid] bmid] gm im] eqn:E; cbn in H; try discriminate.
   destruct(transBeePL_expr_exprs transBeePL_expr_expr rest mid bmid gm)
   as [msg|[[cs final] bfinal] gf ip] eqn:F; cbn in H; try discriminate.
   inversion H; subst.
   destruct(Hall e (or_introl eq_refl) _ _ _ _ _ _ _ _ E) as [Eb Gb]; subst bmid.
   destruct(IH (fun child Hin=>Hall child (or_intror Hin)) _ _ _ _ _ _ _ _ F) as [Eb' Gf]; subst bc'.
   split; [reflexivity|eapply reserved_growth_trans; eassumption].
Qed.
Ltac reserved_chain := first [assumption|apply reserved_growth_refl|
 match goal with G:reserved_growth ?r ?mid ?last |- reserved_growth ?r ?first ?last =>
 eapply reserved_growth_trans with (b:=mid); [clear G; reserved_chain|exact G] end|
 match goal with |-reserved_growth ?r ?first ((?id,?ty,?tag)::?tail) =>
 eapply reserved_growth_trans with (b:=tail); [reserved_chain|apply reserved_growth_fresh; assumption] end].
Ltac reserved_collect := repeat match goal with
 | E:fresh_compiler_binding ?source ?ty ?ctx ?bc ?g=Res(?binding,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gbinding" in let R:=fresh "Rbinding" in
   destruct(fresh_compiler_binding_reserved _ _ _ _ _ _ _ _ _ _ E) as [R G]; clear E
 | E:compiler_destination ?selected ?ty ?ctx ?bc ?g=Res(?id,?ctx')?g' ?ip |- _ =>
   let G:=fresh "Gdestination" in pose proof(compiler_destination_reserved _ _ _ _ _ _ _ _ _ E) as G; clear E
 | E:fresh_compiler_fields ?fields ?ctx ?bc ?g=Res(?bindings,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gfields" in let R:=fresh "Rfields" in
   destruct(fresh_compiler_fields_reserved _ _ _ _ _ _ _ _ _ E) as [R G]; clear E

 | E : guarded_binop ?op ?es ?ces ?ty ?ctx ?bc ?g=Res(?ce,?ctx',?bc')?g' ?ip |- _ =>
     let G := fresh "Rguard" in let EQ := fresh "EQguard" in
     destruct(guarded_binop_reserved_growth _ _ _ _ _ _ _ _ _ _ _ _ E) as [EQ G]; clear E; subst
 | IH:expression_reserved_safe ?e,
 E:transBeePL_expr_expr ?e ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
 let EQ:=fresh "EQctx" in let G:=fresh "Rchild" in
 destruct(IH _ _ _ _ _ _ _ _ E) as [EQ G]; clear IH; subst
 | IH:forall child,In child ?es -> expression_reserved_safe child,
 E:transBeePL_expr_exprs transBeePL_expr_expr ?es ?ctx ?bc ?g=Res(?ces,?ctx',?bc') ?g' ?ip |- _ =>
 let EQ:=fresh "EQctx" in let G:=fresh "Rlist" in
 destruct(list_reserved_safe es IH _ _ _ _ _ _ _ _ E) as [EQ G]; clear IH; subst
 end.
Theorem expression_translation_reserved_safe : forall e,expression_reserved_safe e.
Proof.
 intros e; induction e using expr_ind_rec;
 unfold expression_reserved_safe at 1; intros ctx bc g ce ctx' bc' g' ip Hrun;
 cbn [transBeePL_expr_expr] in Hrun;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret,SimplExpr.error in Hrun;
 cbn beta iota zeta in Hrun;
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
 let rec descend t := lazymatch t with
 |context[match ?inner with _=>_ end]=>descend inner
 | _=>let E:=fresh "Epart" in destruct t eqn:E end in descend scr;
 repeat match goal with p:(_ * _)%type|-_=>destruct p end;
 cbn beta iota zeta in *; try discriminate
 end;
 try(inversion Hrun; subst; clear Hrun; reserved_collect);
 try solve[split; [reflexivity|reserved_chain]].
all: reserved_collect.
all: repeat match goal with
 | E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof|-_=>
 let Hfresh:=fresh "Hfresh" in
 pose proof(reserved_exclusion_right used reserved id(actual_fresh_identifier _ _ _ _ _ _ _ E)) as Hfresh; clear E
 end.
all: repeat match goal with
 | IH:forall child,In child ?es -> expression_reserved_safe child,
 E:transBeePL_expr_expr ?child ?ctx ?bc ?g=Res(?ce,?ctx',?bc')?g' ?ip|-_=>
 let Hin:=fresh "Hin" in assert(Hin:In child es) by(simpl;tauto);
 let EQ:=fresh "EQctx" in let G:=fresh "Rbranch" in
 destruct(IH child Hin _ _ _ _ _ _ _ _ E) as[EQ G]; clear E; subst
 end.
all: cbv beta iota zeta delta [fst snd] in *.
all: normalize_reserved.
all: try solve[split;[reflexivity|reserved_chain]].
Qed.

Lemma expression_list_reserved_safe : forall es ctx bc g ces ctx' bc' g' proof,
 transBeePL_expr_exprs transBeePL_expr_expr es ctx bc g=Res(ces,ctx',bc')g' proof ->
 bc'=bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Proof. intros; eapply list_reserved_safe; [intros; apply expression_translation_reserved_safe|eassumption]. Qed.
Definition statement_reserved_safe (e : BeePL.expr) :=
 forall env ctx bc g cs ctx' bc' g' proof,
 transBeePL_expr_st env e ctx bc g=Res(cs,ctx',bc')g' proof ->
 bc'=bc /\ reserved_growth(reserved_identifiers bc)ctx ctx'.
Ltac statement_reserved_collect := repeat match goal with
 | E:fresh_compiler_binding ?source ?ty ?ctx ?bc ?g=Res(?binding,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gbinding" in let R:=fresh "Rbinding" in
   destruct(fresh_compiler_binding_reserved _ _ _ _ _ _ _ _ _ _ E) as [R G]; clear E
 | E:compiler_destination ?selected ?ty ?ctx ?bc ?g=Res(?id,?ctx')?g' ?ip |- _ =>
   let G:=fresh "Gdestination" in pose proof(compiler_destination_reserved _ _ _ _ _ _ _ _ _ E) as G; clear E
 | E:fresh_compiler_fields ?fields ?ctx ?bc ?g=Res(?bindings,?ctx',?bc')?g' ?ip |- _ =>
   let G:=fresh "Gfields" in let R:=fresh "Rfields" in
   destruct(fresh_compiler_fields_reserved _ _ _ _ _ _ _ _ _ E) as [R G]; clear E

 | E : guarded_binop ?op ?es ?ces ?ty ?ctx ?bc ?g=Res(?ce,?ctx',?bc')?g' ?ip |- _ =>
     let G := fresh "Rguard" in let EQ := fresh "EQguard" in
     destruct(guarded_binop_reserved_growth _ _ _ _ _ _ _ _ _ _ _ _ E) as [EQ G]; clear E; subst
 | IH:statement_reserved_safe ?e,
 E:transBeePL_expr_st ?env ?e ?ctx ?bc ?g=Res(?cs,?ctx',?bc') ?g' ?ip |- _ =>
 let EQ:=fresh "EQctx" in let G:=fresh "Rchild" in
 destruct(IH _ _ _ _ _ _ _ _ _ E) as [EQ G]; clear IH; subst
 | E:transBeePL_expr_expr ?e ?ctx ?bc ?g=Res(?ce,?ctx',?bc') ?g' ?ip |- _ =>
 let EQ:=fresh "EQctx" in let G:=fresh "Rexpr" in
 destruct(expression_translation_reserved_safe e _ _ _ _ _ _ _ _ E) as [EQ G]; clear E; subst
 | E:transBeePL_expr_exprs transBeePL_expr_expr ?es ?ctx ?bc ?g=Res(?ces,?ctx',?bc') ?g' ?ip |- _ =>
 let EQ:=fresh "EQctx" in let G:=fresh "Rlist" in
 destruct(expression_list_reserved_safe _ _ _ _ _ _ _ _ _ E) as [EQ G]; clear E; subst
 end.
Theorem statement_translation_reserved_safe : forall e,statement_reserved_safe e.
Proof.
 intros e; induction e using expr_ind_rec;
 unfold statement_reserved_safe at 1; intros env ctx bc g ce ctx' bc' g' ip Hrun;
 cbn [transBeePL_expr_st] in Hrun;
 unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret,SimplExpr.error in Hrun;
 cbn beta iota zeta in Hrun;
 repeat match type of Hrun with
 | context[match ?scr with _ => _ end] =>
 let rec descend t := lazymatch t with
 |context[match ?inner with _=>_ end]=>descend inner
 | _=>let E:=fresh "Epart" in destruct t eqn:E end in descend scr;
 repeat match goal with p:(_ * _)%type|-_=>destruct p end;
 cbn beta iota zeta in *; try discriminate
 end;
 try(inversion Hrun; subst; clear Hrun; statement_reserved_collect);
 try solve[split; [reflexivity|reserved_chain]].
all: statement_reserved_collect.
all: repeat match goal with
 | E:fresh_ident (?used ++ ?reserved) ?fuel ?g=Res(?id,?tag)?g' ?proof|-_=>
 let Hfresh:=fresh "Hfresh" in
 pose proof(reserved_exclusion_right used reserved id(actual_fresh_identifier _ _ _ _ _ _ _ E)) as Hfresh; clear E
 end.
all: repeat match goal with
 | IH:forall child,In child ?es -> statement_reserved_safe child,
 E:transBeePL_expr_st ?env ?child ?ctx ?bc ?g=Res(?ce,?ctx',?bc')?g' ?ip|-_=>
 let Hin:=fresh "Hin" in assert(Hin:In child es) by(simpl;tauto);
 let EQ:=fresh "EQctx" in let G:=fresh "Rbranch" in
 destruct(IH child Hin _ _ _ _ _ _ _ _ _ E) as[EQ G]; clear E; subst
 end.
all: cbv beta iota zeta delta [fst snd] in *.
all: normalize_reserved.
all: try solve[split;[reflexivity|reserved_chain]].
Qed.

Print Assumptions expression_translation_reserved_safe.
Print Assumptions statement_translation_reserved_safe.

Require Import BeePL_Wrapper_Pass BeePL_compiler_structure BeePL_compiler_local_allocation BeePL_compiler_statement_growth.
Lemma source_args_zip : forall (args:list(ident * BeeTypes.type)),
 seq.zip(seq.unzip1 args)(seq.unzip2 args)=args.
Proof. intros args; induction args as [|[id ty] rest IH]; simpl; congruence. Qed.
Lemma translated_args_identifiers : forall (args:list(ident * BeeTypes.type)),
 map fst(seq.zip(seq.unzip1 args)(transBeePL_types transBeePL_type(seq.unzip2 args)))=map fst args.
Proof. intros args; induction args as [|[id ty] rest IH]; simpl; congruence. Qed.
Lemma wrapped_parameter_identifiers : forall args params,
 transform_ctx_ebpf_ctx args=Errors.OK params -> map fst params=map fst args.
Proof.
 intros args params H; unfold transform_ctx_ebpf_ctx in H.
 repeat match type of H with context[match ?scr with _=>_ end] =>
 let E:=fresh "Ewrap" in destruct scr eqn:E; cbn in H; try discriminate end;
 inversion H; subst; reflexivity.
Qed.
Theorem translated_parameter_identifiers : forall env bf names bc cf names' bc',
 transBeePL_function_function env bf names bc=Errors.OK(cf,names',bc') ->
 map fst(Csyntax.fn_params cf)=map fst(BeePL.fn_args bf).
Proof.
 intros env bf names bc cf names' bc' H.
 destruct(function_translation_signature _ _ _ _ _ _ _ H) as [_ [_ [Hnative Hbpf]]].
 destruct(is_ebpf bf) eqn:E.
 - specialize(Hbpf eq_refl). rewrite source_args_zip in Hbpf.
   eapply wrapped_parameter_identifiers; exact Hbpf.
 - rewrite(Hnative eq_refl). apply translated_args_identifiers.
Qed.
Lemma nodup_suffix : forall (a b:list ident), NoDup(a++b) -> NoDup b.
Proof. intros a; induction a; intros b H; simpl in H; [exact H|]. inversion H; eauto. Qed.
Lemma nodup_prefix_transport : forall (prefix before after:list ident),
 NoDup(prefix++before) -> NoDup after ->
 (forall id,In id prefix -> In id after -> In id before) -> NoDup(prefix++after).
Proof.
 intros prefix; induction prefix as [|x rest IH]; intros before after H Hafter Horigin; simpl in *; [exact Hafter|].
 inversion H; subst. constructor.
 - intro Hin. apply in_app_iff in Hin. apply H2,in_or_app.
   destruct Hin as [Hin|Hin]; [left;exact Hin|right;apply Horigin;auto].
 - eapply IH; [eassumption|exact Hafter|]. intros; apply Horigin; auto.
Qed.

Theorem translated_function_entry_names_distinct : forall env bf names bc cf names' bc',
 transBeePL_function_function env bf names bc=Errors.OK(cf,names',bc') ->
 NoDup(map fst(BeePL.fn_args bf)) ->
 NoDup(map fst(Csyntax.fn_params cf) ++ map fst(Csyntax.fn_vars cf)).
Proof.
 intros env bf names bc cf names' bc' Hcompile Hsource.
 destruct(function_translation_body_context _ _ _ _ _ _ _ Hcompile)
 as [initial [g0 [i0 [ctx [g1 [i1 [Hinitial [Hbody Hlocals]]]]]]]].
 pose proof(initial_compiler_context_identifiers _ _ _ _ _ _ Hinitial) as Hids.
 destruct(statement_translation_reserved_safe _ _ _ _ _ _ _ _ _ _ Hbody) as [Hbc Hreserved].
 pose proof(translated_function_locals_distinct _ _ _ _ _ _ _ Hcompile) as HlocalsDistinct.
 rewrite(translated_parameter_identifiers _ _ _ _ _ _ _ Hcompile).
 eapply nodup_prefix_transport with (before:=[]);
 [rewrite app_nil_r; exact Hsource|exact HlocalsDistinct|].
 intros id Hparam Hlocal. simpl in Hids. rewrite <-Hids.
 apply (Hreserved id).
 - unfold reserve_function_context; simpl. apply in_or_app; right.
   apply in_or_app; left; exact Hparam.
 - rewrite Hlocals in Hlocal.
   change (In id(map fst(compiled_context_locals ctx))) in Hlocal.
   rewrite compiled_context_locals_map,map_map in Hlocal; exact Hlocal.
Qed.
Print Assumptions translated_function_entry_names_distinct.

Corollary translated_function_entry_allocation : forall env bf names bc cf names' bc',
 transBeePL_function_function env bf names bc=Errors.OK(cf,names',bc') ->
 NoDup(map fst(BeePL.fn_args bf)) ->
 forall ge e m, exists e' m',
 Csem.alloc_variables ge e m (Csyntax.fn_params cf ++ Csyntax.fn_vars cf) e' m' /\
 (forall id ty, In(id,ty)(Csyntax.fn_params cf ++ Csyntax.fn_vars cf) -> exists b,
 PTree.get id e'=Some(b,ty) /\ Memory.Mem.valid_block m' b /\
 (forall ofs k, (0<=ofs<Ctypes.sizeof ge ty)%Z -> Memory.Mem.perm m' b ofs k Freeable)).
Proof.
 intros env bf names bc cf names' bc' Hcompile Hsource ge e m.
 destruct(c_local_allocation_exists ge (Csyntax.fn_params cf ++ Csyntax.fn_vars cf) e m)
 as [e' [m' Halloc]]. exists e',m'; split; [exact Halloc|].
 intros id ty Hin. eapply c_local_allocation_declared; [exact Halloc| |exact Hin].
 rewrite map_app. eapply translated_function_entry_names_distinct; eauto.
Qed.
Print Assumptions translated_function_entry_allocation.
