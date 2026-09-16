theory Factor_Development_Cases
  imports Factor_Development_Admission Factor_Workflow_Cases
begin

definition development_formed_condition :: "native_development_condition" where
  "development_formed_condition=\<lparr>condition_source=finite_guard_source True,condition_source_use=None,
    condition_source_root=[0],condition_goals=[Existing_Admission (None,[1])]\<rparr>"

definition development_scope_pattern :: "bool \<Rightarrow> local_address finite_term_pattern" where
  "development_scope_pattern nonempty=Finite_Pattern_Pair (Finite_Variable [0])
    (Finite_Pattern_Pair (if nonempty then Finite_Pattern_Pair (Finite_Variable [1]) (Finite_Variable [2])
      else Finite_Pattern_Payload []) (Finite_Pattern_Pair (Finite_Variable [3]) (Finite_Pattern_Payload [])))"

definition development_scope_condition :: "bool \<Rightarrow> native_development_condition" where
  "development_scope_condition nonempty=(let E=finite_guard_source True; P=finite_guard_source_program True;
    e=(Some [],[]); pattern=development_scope_pattern nonempty;
    rule=\<lparr>finite_schema_conclusion=Finite_Pattern_Pair pattern pattern,
      finite_schema_premises={||},finite_schema_materials={||}\<rparr>;
    Q=finite_add_view_definition P e (Finite_Variable []) {|([],rule)|} in
    case finite_install_source_entry E None [0] Q e of None \<Rightarrow>
      development_formed_condition\<lparr>condition_source_root:=[255]\<rparr>
    | Some (d,F,u) \<Rightarrow> \<lparr>condition_source=F,condition_source_use=u,condition_source_root=[],
        condition_goals=[Existing_Admission d]\<rparr>)"

definition development_generated_question :: "bool \<Rightarrow> nat \<Rightarrow> native_development_question" where
  "development_generated_question b copies=(let S=(case workflow_generating_stage b copies of None \<Rightarrow>
    (workflow_guard_stage True Workflow_Input)\<lparr>workflow_source_root:=[255]\<rparr> | Some S \<Rightarrow> S) in
    \<lparr>development_source=workflow_source S,development_source_use=workflow_source_use S,
      development_source_root=workflow_source_root S,development_generator_entry=workflow_entry S,
      development_problem=Finite_Payload [],development_conditions=[development_formed_condition],
      development_scope_criticism=development_scope_condition True,development_selected_facets=[]\<rparr>)"

definition development_case_inputs :: "native_development_question list" where
  "development_case_inputs=(let Q=development_generated_question True 1;
    equality=development_formed_condition\<lparr>condition_source:=finite_guard_source False\<rparr>;
    missing=(development_scope_criticism Q)\<lparr>condition_source_root:=[255]\<rparr>;
    nested=development_formed_condition\<lparr>condition_goals:=[Paired_Admission
      (Existing_Admission (None,[1])) (Collected_Admission (Existing_Admission (None,[1])))]\<rparr> in
    [Q,development_generated_question True 2,Q\<lparr>development_conditions:=[equality]\<rparr>,
      development_generated_question False 1,Q\<lparr>development_scope_criticism:=missing\<rparr>,
      Q\<lparr>development_scope_criticism:=development_scope_condition False\<rparr>,
      Q\<lparr>development_problem:=Finite_Payload [256]\<rparr>,
      Q\<lparr>development_conditions:=[nested,development_formed_condition],development_selected_facets:=[0]\<rparr>])"

definition development_case_at where
  "development_case_at w=(if w<length development_case_inputs then development_case_inputs!w
    else development_generated_question True 1)"

definition development_remove_certificates :: "native_condition_execution \<Rightarrow> native_condition_execution" where
  "development_remove_certificates execution=(case execution of (S,P,D,A,T,ys) \<Rightarrow> (S,P,D,A,{||},ys))"

definition development_producer_from ::
    "nat \<Rightarrow> native_development_question \<Rightarrow> native_development_report \<Rightarrow> finite_factor_term list option \<Rightarrow> native_development_report\<times>finite_factor_term list option" where
  "development_producer_from m Q report decision=(
    if m=1 then (report\<lparr>development_scope_review:=None\<rparr>,decision)
    else if m=2 then (report\<lparr>development_observed_conditions:=map_option
      (map (map_option development_remove_certificates)) (development_observed_conditions report)\<rparr>,decision)
    else if m=3 then (report\<lparr>development_generation:=map_option (\<lambda>(P,D,A,rows). (P,D,A,drop 1 rows))
      (development_generation report)\<rparr>,decision)
    else if m=4 then (report\<lparr>development_compiled_conditions:=None\<rparr>,decision)
    else if m=5 then (report\<lparr>development_comparison:=None\<rparr>,decision)
    else if m=6 then (report\<lparr>development_revision:=None\<rparr>,decision)
    else if m=7 then (let other=Q\<lparr>development_problem:=Finite_Pair (development_problem Q) (development_problem Q)\<rparr>;
      altered=construct_native_development other in (altered,native_development_admission other altered))
    else if m=8 then (report,map_option (take 1) decision)
    else if m=9 then (let other=Q\<lparr>development_scope_criticism:=development_formed_condition\<rparr>;
      altered=construct_native_development other in (altered,native_development_admission other altered))
    else (report,decision))"

definition development_producer where
  "development_producer m Q=(let report=construct_native_development Q in
    development_producer_from m Q report (native_development_admission Q report))"

text \<open>
  The scope critic is an actual installed native clause. Its pattern inspects
  the whole candidate-list field of the complete review input, distinguishing
  a nonempty family from the empty family. The contrasting critic requires an
  empty family. Native execution, not a supplied outcome, decides each request.
  Other sources include equality, whole formed-term admission and nested goals.
  Producers remove complete operations or certificates, lose a generated row,
  change the original question, discard duplicate answers or replace the
  original native scope critic. Every complete subject is retained.
\<close>

end
