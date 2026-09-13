theory Factor_Native_Requirement_Assessment
  imports Factor_Native_Requirement_Family_Cases Factor_Finite_Requirement_Term_Comparison Factor_Native_Admission_Assessment
begin

definition native_requirement_ready :: "native_requirement_problem\<Rightarrow>bool" where
  "native_requirement_ready X=(case X of (E,u,r,gs,T) \<Rightarrow>
    (case finite_native_source E u r of None \<Rightarrow> False
    | Some P \<Rightarrow> finite_admission_requirements_supported gs P))"

definition native_requirement_ready_condition :: "native_requirement_problem\<Rightarrow>bool" where
  "native_requirement_ready_condition X=(case X of (E,u,r,gs,T) \<Rightarrow>
    \<exists>P. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)))"

lemma native_requirement_ready_exact:
  "native_requirement_ready X=native_requirement_ready_condition X"
  by (auto simp: native_requirement_ready_def native_requirement_ready_condition_def
    finite_native_source_correct[symmetric] finite_admission_requirements_supported_correct
    split: prod.splits option.splits)

definition native_requirement_preservation_observation ::
    "native_requirement_problem\<Rightarrow>finite_native_entry_result\<Rightarrow>bool" where
  "native_requirement_preservation_observation X result=(case X of (E,u,r,gs,T) \<Rightarrow>
    finite_source_preservation_observation E u r result)"

definition native_requirement_preservation_condition ::
    "native_requirement_problem\<Rightarrow>finite_native_entry_result\<Rightarrow>bool" where
  "native_requirement_preservation_condition X result=(case X of (E,u,r,gs,T) \<Rightarrow>
    finite_source_preservation_condition E u r result)"

lemma native_requirement_preservation_exact:
  "native_requirement_preservation_observation X result=native_requirement_preservation_condition X result"
  by (simp add: native_requirement_preservation_observation_def native_requirement_preservation_condition_def
    finite_source_preservation_exact split: prod.splits)

definition native_requirement_term_observation :: "native_requirement_problem\<Rightarrow>finite_native_entry_result\<Rightarrow>
    (finite_factor_term fset\<times>finite_factor_term fset) option" where
  "native_requirement_term_observation X result=(case X of (E,u,r,gs,T) \<Rightarrow>
    (case result of None \<Rightarrow> None | Some (d,F,v) \<Rightarrow>
      finite_native_requirement_term_comparison E u r gs F v d T))"

definition native_requirement_term_condition ::
    "nat\<Rightarrow>native_requirement_problem\<Rightarrow>finite_native_entry_result\<Rightarrow>bool" where
  "native_requirement_term_condition f X result=(case X of (E,u,r,gs,T) \<Rightarrow>
    (case result of None \<Rightarrow> False | Some (d,F,v) \<Rightarrow>
      finite_native_requirement_term_comparison_condition f E u r gs F v d T))"

lemma native_requirement_term_exact:
  "(case native_requirement_term_observation X result of None \<Rightarrow> False
    | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))=
      native_requirement_term_condition f X result"
  by (simp add: native_requirement_term_observation_def native_requirement_term_condition_def
    finite_native_requirement_term_comparison_exact[symmetric] finite_native_requirement_term_comparison_holds_def
    split: prod.splits option.splits)

definition native_requirement_assessment where
  "native_requirement_assessment X result=(native_requirement_ready X,native_requirement_term_observation X result,
    native_requirement_preservation_observation X result,result=None)"

definition native_requirement_condition where
  "native_requirement_condition f method X=(if f=3 then
    (\<not>native_requirement_ready_condition X \<longrightarrow> method X=None)
    else if f<3 then (native_requirement_ready_condition X \<longrightarrow>
      (if f=2 then native_requirement_preservation_condition X (method X)
        else native_requirement_term_condition f X (method X))) else False)"

theorem native_requirement_assessment_exact:
  "native_admission_inspect (native_requirement_assessment X (method X)) f=
    native_requirement_condition f method X"
  by (simp only: native_admission_inspect_def native_requirement_assessment_def prod.case
    native_requirement_condition_def native_requirement_ready_exact native_requirement_preservation_exact
    native_requirement_term_exact)

export_code native_requirement_assessment checking SML

end
