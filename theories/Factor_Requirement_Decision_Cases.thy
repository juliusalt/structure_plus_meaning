theory Factor_Requirement_Decision_Cases
  imports Factor_Finite_Requirement_Decisions Factor_Native_Requirement_Family_Cases
    Factor_Finite_Proof_Inspection Factor_Finite_Source_Preservation
begin

type_synonym requirement_decision_result =
  "(local_address option definition_site\<times>local_address option finite_artifact_environment\<times>
    local_address option\<times>local_address option finite_native_system\<times>
    (local_address option definition_site\<times>finite_factor_term) fset\<times>
    (local_address option definition_site\<times>finite_factor_term) fset\<times>
    ((local_address option definition_site\<times>finite_factor_term)\<times>
      (local_address,local_address,local_address) finite_schema_proof) fset\<times>
    finite_factor_term fset) option"

definition requirement_decision_indices :: "nat list" where
  "requirement_decision_indices=[0,2,7,8,10,12,15,22,32,62,72,82]"

definition requirement_decision_reference where
  "requirement_decision_reference X=(case X of (E,u,r,gs,Xs) \<Rightarrow>
    finite_native_requirement_term_observation E u r gs Xs)"

theorem requirement_decision_reference_exact:
  "requirement_decision_reference (E,u,r,gs,Xs)=Some (P,Ys) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)) \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P Xs)=Some A) \<and>
    fset Ys={t\<in>fset Xs. admission_requirements_hold
      (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
  by (simp only: requirement_decision_reference_def case_prod_conv
    finite_native_requirement_term_observation_semantics)

definition requirement_decision_base :: "native_requirement_problem\<Rightarrow>requirement_decision_result" where
  "requirement_decision_base X=(case X of (E,u,r,gs,Xs) \<Rightarrow> finite_requirement_decision E u r gs Xs)"

definition requirement_decision_mutation :: "nat\<Rightarrow>requirement_decision_result\<Rightarrow>requirement_decision_result" where
  "requirement_decision_mutation m result=(if m=5 then None else map_option
    (\<lambda>(d,F,v,Q,D,A,T,Ys). (d,
      (if m=4 then F\<lparr>finite_environment_artifacts:=
        ffilter (\<lambda>(u,R). u\<noteq>Some [255]) (finite_environment_artifacts F)\<rparr> else F),v,
      (if m=6 then Q\<lparr>finite_system_clauses:={||}\<rparr> else Q),
      (if m=7 then {||} else D),(if m=8 then {||} else A),
      (if m=9 then {||} else if m=10 then
        fimage (\<lambda>(q,p). (q,case p of Schema_Proof c V B \<Rightarrow> Schema_Proof [255] V B)) T else T),
      (if m=11 then {||} else Ys))) result)"

definition requirement_decision_method :: "nat\<Rightarrow>native_requirement_problem\<Rightarrow>requirement_decision_result" where
  "requirement_decision_method m X=(case X of (E,u,r,gs,Xs) \<Rightarrow>
    requirement_decision_mutation m (finite_requirement_decision E u r
      (native_requirement_variant (if m<4 then m else 0) gs) Xs))"

lemma requirement_decision_mutation_original [simp]:
  "requirement_decision_mutation 0 result=result"
  by (cases result) (auto simp: requirement_decision_mutation_def split: prod.splits)

lemma requirement_decision_method_original:
  "requirement_decision_method 0 X=requirement_decision_base X"
  by (auto simp: requirement_decision_method_def requirement_decision_mutation_def
    requirement_decision_base_def option.map_id split: prod.splits option.splits)

definition requirement_decision_evaluation_report where
  "requirement_decision_evaluation_report P D=(finite_system_formed P,finite_program_head_covered P D,
    finite_program_demand_closed P D,finite_program_applications P D,finite_program_rule_table P D,
    finite_program_evaluation P D)"

definition requirement_decision_original_report where
  "requirement_decision_original_report X=(case X of (E,u,r,gs,Xs) \<Rightarrow>
    let source=finite_native_source E u r; D=map_option (\<lambda>P. finite_program_term_demand P Xs) source in
    (source,map_option (finite_admission_requirements_supported gs) source,D,
      map_option (\<lambda>P. requirement_decision_evaluation_report P (finite_program_term_demand P Xs)) source))"

definition requirement_decision_context where
  "requirement_decision_context w=map_option (\<lambda>X. (X,(requirement_decision_reference X,
    requirement_decision_original_report X),map (\<lambda>m. (m,requirement_decision_method m X)) [0,1,2,3]))
      (native_requirement_problem w)"

text \<open>
  The original requirement families and actual environments precede every
  candidate operation. Their original term observation supplies an independent
  reference. Three operations omit or duplicate actual requirements before
  construction. Later mutations alter full returned artifacts, claimed program,
  demand, answer, proof family or admitted terms. The empty family, conflicting
  requirements, unsupported entries and an unrelated original artifact remain
  actual source cases. No branch supplies a claimed satisfaction value.
\<close>

end
