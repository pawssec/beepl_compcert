(* Actual source members determine offsets and storage kinds. No uniqueness
   assumption on initializer field names is needed. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas.
Require Import BeePL_substitution_proofs BeePL_runtime_locations BeePL_array_proofs.
Require Import BeePL_coherent_fields BeePL_program_member_types BeePL_structure_storage_typing.
Require Import BeePL_structure_initializer_slots BeePL_scalar_structure_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Record evaluated_field_slot := {
 field_slot_name : ident;
 field_slot_offset : Z;
 field_slot_type : type;
 field_slot_value : value
}.
Definition field_slot_expression slot := Val slot.(field_slot_value) slot.(field_slot_type).
Definition evaluated_field_valid p Gamma Sigma L sid attr co slot : Prop :=
 type_expr p.(prog_comp_env) Gamma Sigma (field_slot_expression slot) nil slot.(field_slot_type) /\
 value_locations L slot.(field_slot_value) slot.(field_slot_type) /\
 source_member_type slot.(field_slot_name) co.(co_members)=OK slot.(field_slot_type) /\
 field_offset(bcomposite_composite_env p.(prog_comp_env)) slot.(field_slot_name)
 (bmembers_cmembers co.(co_members))=OK(slot.(field_slot_offset),Full) /\
 0<=slot.(field_slot_offset) /\
 slot.(field_slot_offset)+sizeof_type p.(prog_comp_env) slot.(field_slot_type)<=sizeof_type p.(prog_comp_env)(Stype sid attr) /\
 bcomplete_type p.(prog_comp_env) slot.(field_slot_type)=true /\
 ((exists chunk,access_mode_type slot.(field_slot_type)=By_value(transl_bchunk_cchunk chunk)) \/
 is_aggregate_type slot.(field_slot_type)=true \/ slot.(field_slot_type)=Bytes).

Lemma plan_evaluated_fields : forall es ids ts p Gamma Sigma L sid attr co ef,
 type_exprs p.(prog_comp_env) Gamma Sigma es ef ts ->
 Forall(fun e=>exists v ty,e=Val v ty /\ value_locations L v ty) es ->
 source_member_types ids co.(co_members)=OK ts ->
 PTree.get sid p.(prog_comp_env)=Some co ->
 exists slots,
 map field_slot_name slots=ids /\ map field_slot_expression slots=es /\
 map field_slot_type slots=ts /\ Forall(evaluated_field_valid p Gamma Sigma L sid attr co) slots.
Proof.
 induction es as [|e es IH]; intros ids ts p Gamma Sigma L sid attr co ef Htyped Hlocated Hmembers Hco.
 - inversion Htyped; subst. destruct ids as [|id ids]; [exists []; repeat split; constructor|].
   simpl in Hmembers. unfold Errors.bind in Hmembers.
   destruct(source_member_type id(co_members co)); try discriminate.
   destruct(source_member_types ids(co_members co)); discriminate.
 - inversion Htyped; subst. inversion Hlocated as [|head tail Hhead Htail]; subst head tail.
   destruct Hhead as [v [ty [He Hlocation]]]; subst e.
   match goal with Ht:type_expr _ _ _ (Val v ty) _ _ |- _ =>
    pose proof(typed_value_annotation _ _ _ _ _ _ _ Ht) as Hannotation;
    pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Ht) as Heffect
   end; subst.
   destruct ids as [|id ids]; [discriminate Hmembers|].
   simpl in Hmembers. unfold Errors.bind in Hmembers.
   destruct(source_member_type id(co_members co)) eqn:Hmember; try discriminate.
   destruct(source_member_types ids(co_members co)) eqn:Hrest; try discriminate.
   inversion Hmembers; subst.
   match goal with Hargs:type_exprs _ _ _ es _ _ |- _ =>
    destruct(IH ids ts0 p Gamma Sigma L sid attr co efs Hargs Htail Hrest Hco) as [slots [Hnames [Hexprs [Htypes Hvalid]]]]
   end.
   destruct(program_field_layout p sid attr co id t Hco Hmember) as [offset [Hoffset [Hlo [Hsize Hbound]]]].
   pose proof(program_source_member_complete p sid co id t Hco Hmember) as Hcomplete.
   exists({|field_slot_name:=id;field_slot_offset:=offset;field_slot_type:=t;field_slot_value:=v|}::slots).
   split; [change (id::map field_slot_name slots=id::ids); congruence|].
   split; [change (Val v t::map field_slot_expression slots=Val v t::es); congruence|].
   split; [change (t::map field_slot_type slots=t::ts0); congruence|].
   constructor; [|exact Hvalid]. unfold evaluated_field_valid,field_slot_expression; cbn.
   split; [assumption|]. split; [exact Hlocation|]. split; [exact Hmember|].
   split; [exact Hoffset|]. split; [exact Hlo|]. split; [exact Hbound|].
   split; [exact Hcomplete|]. exact (complete_field_runtime_kind p.(prog_comp_env) t Hcomplete).
Qed.

Theorem typed_structure_field_plan : forall p Gamma Sigma L sid attr ids es result ef,
 type_expr p.(prog_comp_env) Gamma Sigma(Sinit sid ids es result) ef result ->
 structure_result_type sid attr result ->
 Forall(fun e=>exists v ty,e=Val v ty /\ value_locations L v ty) es ->
 exists co slots,
 PTree.get sid p.(prog_comp_env)=Some co /\
 map field_slot_name slots=ids /\ map field_slot_expression slots=es /\
 Forall(evaluated_field_valid p Gamma Sigma L sid attr co) slots.
Proof.
 intros * Htyped Hshape Hlocated. inversion Htyped; subst.
 match goal with Hargs:type_exprs _ _ _ es _ _, Hco:PTree.get id _=Some ?co,
 Hmembers:source_member_types ?names _=OK _ |- _ =>
 destruct(plan_evaluated_fields es names _ p Gamma Sigma L id attr co _ Hargs Hlocated Hmembers Hco)
 as [slots [Hnames [Hexprs [Htypes Hvalid]]]];
 exists co,slots; repeat split; assumption
 end.
Qed.

Lemma scalarize_evaluated_field_plan : forall p Gamma Sigma L sid attr co fields,
 Forall(evaluated_field_valid p Gamma Sigma L sid attr co) fields ->
 Forall(fun field=>is_aggregate_type(field_slot_type field)=false /\ field_slot_type field<>Bytes) fields ->
 exists slots,
 map scalar_field_name slots=map field_slot_name fields /\
 map scalar_slot_expression slots=map field_slot_expression fields /\
 (forall slot,In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) /\
 (forall slot,In slot slots -> field_offset(bcomposite_composite_env p.(prog_comp_env))(scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)).
Proof.
 intros p Gamma Sigma L sid attr co fields Hvalid Hscalar.
 induction fields as [|field fields IH].
 - exists []; repeat split; intros; contradiction.
 - inversion Hvalid as [|head tail Hhead Htail]; subst head tail.
   inversion Hscalar as [|head tail [Haggregate Hbytes] HscalarTail]; subst head tail.
   destruct(IH Htail HscalarTail) as [slots [Hnames [Hexprs [Hmodes Hoffsets]]]].
   destruct Hhead as [Htyped [Hlocated [Hmember [Hoffset [Hlo [Hbound [Hcomplete Hkind]]]]]]].
   destruct Hkind as [[chunk Hmode]|[Hkind|Hkind]]; [|congruence|contradiction].
   set(slot:={|scalar_field_name:=field_slot_name field;scalar_field_offset:=field_slot_offset field;
    scalar_field_type:=field_slot_type field;scalar_field_chunk:=chunk;scalar_field_value:=field_slot_value field|}).
   exists(slot::slots). split; [simpl; unfold slot; cbn; congruence|].
   split; [change(field_slot_expression field::map scalar_slot_expression slots=field_slot_expression field::map field_slot_expression fields); congruence|].
   split; intros other [Heq|Hin]; [subst other; exact Hmode|apply Hmodes; exact Hin|subst other; exact Hoffset|apply Hoffsets; exact Hin].
Qed.

Print Assumptions typed_structure_field_plan.
Print Assumptions scalarize_evaluated_field_plan.
