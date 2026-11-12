(* Authentic code aliases and initialized data slots share one callee map. *)
Require Import List Bool Coqlib Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_function_parameters BeePL_callable_locations BeePL_callable_variables BeePL_packet_bindings.
Require Import BeePL_call_state BeePL_scalar_call_layout BeePL_soundness_variables BeePL_parameter_allocations BeePL_allocation_proofs.
Require Import BeePL_general_call_preparation BeePL_parameter_storage_check BeePL_initialized_runtime.
Import ListNotations.

Definition general_argument_values ge Gamma Sigma L (params:list(ident*type)) values :=
  Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
    value_locations L v(snd param)) params values.

Theorem general_function_parameter_partition : forall ge Gamma Sigma L params values,
  (forall b args effects result variadic,L b Ptrofs.zero(Ftype args effects result variadic) ->
    internal_code_locations ge b Ptrofs.zero(Ftype args effects result variadic)) ->
  general_argument_values ge Gamma Sigma L params values ->
  exists codes data data_values,function_parameter_partition ge params values codes data data_values /\
    general_argument_values ge Gamma Sigma L data data_values.
Proof.
  intros ge Gamma Sigma L params values Hcode Hvalues;induction Hvalues as [|[id ty] v params values Hhead Htail IH].
  - exists empty_vmap,[],[];split;constructor.
  - destruct IH as [codes [data [data_values [Hpartition Hdata]]]].
    destruct Hhead as [Htyped Hlocated];simpl in Htyped,Hlocated.
    destruct(is_funtype ty) eqn:Hfun.
    + destruct ty;try discriminate Hfun.
      destruct(typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Htyped) as [Hnil [Hannotation [block Hv]]]. subst v.
      destruct(Hcode block _ _ _ _ Hlocated) as [Hz [args [effects [result [variadic [fn [Hsig [Hfind Htype]]]]]]]].
      inversion Hsig;subst;eexists;exists data,data_values;split;[eapply function_partition_code;eauto|exact Hdata].
    + exists codes,((id,ty)::data),(v::data_values);split.
      * apply function_partition_data;assumption.
      * constructor;[split;assumption|exact Hdata].
Qed.

Lemma general_typed_located_arguments : forall ge Gamma Sigma L params es ef,
  type_exprs ge.(genv_cenv) Gamma Sigma es ef(seq.unzip2 params) ->
  Forall(fun e=>exists v annotation,e=Val v annotation) es ->all_expr_locations(runtime_locations L) es ->
  general_argument_values ge Gamma Sigma L params(extract_values_exprs es).
Proof.
  intros ge Gamma Sigma L params;induction params as [|[id ty] params IH];intros es ef Htyped Hvalues Hlocated.
  - inversion Htyped;subst;constructor.
  - inversion Htyped;subst;inversion Hvalues as [|head tail Hhead Htail];subst.
    destruct Hhead as [v [annotation Heq]];subst;simpl in Hlocated;destruct Hlocated as [Hheadloc Htailloc].
    match goal with Hvalue:type_expr _ _ _ (Val v annotation) _ ty|-_=>
      pose proof(type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;simpl in Hannotation;subst annotation;
      pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hef end.
    subst;constructor;[split;[eassumption|exact Hheadloc]|eapply IH;eauto].
Qed.

Lemma partition_without_functions : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  ~has_function_parameter params ->codes=empty_vmap /\data=params /\data_values=values.
Proof.
  intros ge params values codes data data_values Hpartition;induction Hpartition;intros Hnone;auto.
  - exfalso;apply Hnone;do 5 eexists;left;reflexivity.
  - destruct IHHpartition as [Hcodes [Hdata Hvalues]].
    + intros [name [args [effects [result [variadic Hin]]]]];apply Hnone.
      exists name,args,effects,result,variadic;right;exact Hin.
    + subst;auto.
Qed.

Theorem general_callee_packet_bindings : forall ge Sigma Sigma' globals oldcells oldobjects oldpackets
    cells objects packets params values codes data data_values m callee allocated,
  function_parameter_partition ge params values codes data data_values ->NoDup(map fst params) ->
  packet_variable_layout globals Sigma ge empty_vmap oldcells oldobjects oldpackets ->
  alloc_variables ge Sigma codes m data callee allocated Sigma' ->
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk,oldcells b ofs ty chunk ->cells b ofs ty chunk) ->
  (forall b ofs ty,oldobjects b ofs ty ->objects b ofs ty) ->
  (forall b ofs,oldpackets b ofs ->packets b ofs) ->
  (forall id ty,In(id,ty)data ->packet_variable_binding ge Sigma' callee cells objects packets id ty) ->
  packet_variable_layout(bind_vars globals params) Sigma' ge callee cells objects packets.
Proof.
  intros ge Sigma Sigma' globals oldcells oldobjects oldpackets cells objects packets params values codes data data_values m callee allocated
    Hpartition Hnames Hglobals Ha Hext Hcells Hobjects Hpackets Hdata x ty Hlookup.
  destruct(bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - destruct(function_partition_parameter_origin _ _ _ _ _ _ Hpartition Hnames _ _ Hin) as [Hmember|[b [Hget Hcode]]].
    + apply Hdata;exact Hmember.
    + constructor;eapply callable_variable_local_code;[|exact Hcode].
      rewrite(alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Ha x).
      * exact Hget.
      * eapply function_partition_code_not_data;eauto.
  - assert(HmissingData:~In x(map fst data)).
    { intro Hin;apply Hmissing;apply in_map_iff in Hin as [[name t] [Heq Hin]];simpl in Heq;subst name.
      apply in_map_iff;exists(x,t);split;[reflexivity|eapply function_partition_data_in;eauto]. }
    assert(Habsent:callee ! x=None).
    { rewrite(alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Ha x HmissingData).
      eapply function_partition_code_missing;eauto. }
    destruct(Hglobals _ _ Hglobal) as [Hcall|b Hloc Hkind Hobject|b Hloc Hbytes Hpacket].
    2:{ eapply packet_variable_aggregate;[|exact Hkind|apply Hobjects;exact Hobject].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]];[rewrite PTree.gempty in Hlocal;discriminate|right;auto]. }
    2:{ eapply packet_variable_bytes;[|exact Hbytes|apply Hpackets;exact Hpacket].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]];[rewrite PTree.gempty in Hlocal;discriminate|right;auto]. }
    constructor;destruct Hcall as [b Hlocation Hbinding Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
    + eapply callable_variable_data with(b:=b);[| |exact Hnonfun].
      * destruct Hlocation as [Hlocal|[Hnone Hsymbol]];[rewrite PTree.gempty in Hlocal;discriminate|right;auto].
      * eapply heap_variable_binding_extend;[exact Hext|exact Hcells|exact Hbinding].
    + eapply callable_variable_code;eauto.
    + rewrite PTree.gempty in Hlocal;discriminate.
Qed.
