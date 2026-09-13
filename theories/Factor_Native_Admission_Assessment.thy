theory Factor_Native_Admission_Assessment
  imports Factor_Native_Admission_Cases Factor_Finite_Goal_Term_Comparison
    Factor_Finite_Source_Preservation
begin

type_synonym native_admission_result = "finite_native_entry_result"

type_synonym native_admission_assessment =
  "bool\<times>(finite_factor_term fset\<times>finite_factor_term fset) option\<times>bool\<times>bool"

definition native_admission_ready :: "native_admission_problem\<Rightarrow>bool" where
  "native_admission_ready X=(case X of (E,u,r,g,T) \<Rightarrow>
    (case finite_native_source E u r of None \<Rightarrow> False
    | Some P \<Rightarrow> finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P))"

definition native_admission_ready_condition :: "native_admission_problem\<Rightarrow>bool" where
  "native_admission_ready_condition X=(case X of (E,u,r,g,T) \<Rightarrow>
    \<exists>P. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P))"

lemma native_admission_ready_exact:
  "native_admission_ready X=native_admission_ready_condition X"
  by (auto simp: native_admission_ready_def native_admission_ready_condition_def
    finite_native_source_correct[symmetric] less_eq_fset.rep_eq
    finite_system_definitions_correct
    split: prod.splits option.splits)

definition native_admission_preservation_observation ::
    "native_admission_problem\<Rightarrow>native_admission_result\<Rightarrow>bool" where
  "native_admission_preservation_observation X result=(case X of (E,u,r,g,T) \<Rightarrow>
    finite_source_preservation_observation E u r result)"

definition native_admission_preservation_condition ::
    "native_admission_problem\<Rightarrow>native_admission_result\<Rightarrow>bool" where
  "native_admission_preservation_condition X result=(case X of (E,u,r,g,T) \<Rightarrow>
    finite_source_preservation_condition E u r result)"

lemma native_admission_preservation_exact:
  "native_admission_preservation_observation X result=native_admission_preservation_condition X result"
  by (simp add: native_admission_preservation_observation_def native_admission_preservation_condition_def
    finite_source_preservation_exact split: prod.splits)

definition native_admission_term_observation :: "native_admission_problem\<Rightarrow>native_admission_result\<Rightarrow>
    (finite_factor_term fset\<times>finite_factor_term fset) option" where
  "native_admission_term_observation X result=(case X of (E,u,r,g,T) \<Rightarrow>
    (case result of None \<Rightarrow> None | Some (d,F,v) \<Rightarrow>
      finite_native_goal_term_comparison E u r g F v [] (Existing_Admission d) T))"

definition native_admission_term_condition ::
    "nat\<Rightarrow>native_admission_problem\<Rightarrow>native_admission_result\<Rightarrow>bool" where
  "native_admission_term_condition f X result=(case X of (E,u,r,g,T) \<Rightarrow>
    (case result of None \<Rightarrow> False | Some (d,F,v) \<Rightarrow>
      \<exists>P Q. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
        admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
        (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
        native_package_at (decode_finite_environment F) v [] (decode_finite_system Q) \<and>
        d\<in>system_definitions (decode_finite_system Q) \<and>
        (\<exists>B. finite_program_evaluation Q (finite_program_term_demand Q T)=Some B) \<and>
        (\<forall>t\<in>fset T. if f=0 then
          (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q) \<longrightarrow>
            admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
          else admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
            \<longrightarrow> (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q))))"

definition native_admission_assessment where
  "native_admission_assessment X result=(native_admission_ready X,
    native_admission_term_observation X result,
    native_admission_preservation_observation X result,result=None)"

definition native_admission_inspect :: "native_admission_assessment\<Rightarrow>nat\<Rightarrow>bool" where
  "native_admission_inspect A (f::nat)=(case A of (ready,terms,preserved,rejected) \<Rightarrow>
    if f=3 then (\<not>ready \<longrightarrow> rejected)
    else if f<3 then (ready \<longrightarrow>
      (if f=2 then preserved else case terms of None \<Rightarrow> False | Some (extra,missing) \<Rightarrow>
        (if f=0 then extra={||} else missing={||}))) else False)"

definition native_admission_condition where
  "native_admission_condition f method X=(if f=3 then
    (\<not>native_admission_ready_condition X \<longrightarrow> method X=None)
    else if f<3 then (native_admission_ready_condition X \<longrightarrow>
      (if f=2 then native_admission_preservation_condition X (method X)
        else native_admission_term_condition f X (method X))) else False)"

lemma native_admission_term_condition_comparison:
  "native_admission_term_condition f X result=(case X of (E,u,r,g,T) \<Rightarrow>
    (case result of None \<Rightarrow> False | Some (d,F,v) \<Rightarrow>
      finite_native_goal_term_comparison_condition f E u r g F v [] (Existing_Admission d) T))"
  by (simp add: native_admission_term_condition_def finite_native_goal_term_comparison_condition_def
    split: prod.splits option.splits)

lemma native_admission_term_exact:
  "(case native_admission_term_observation X result of None \<Rightarrow> False
    | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))=
      native_admission_term_condition f X result"
  by (simp add: native_admission_term_observation_def native_admission_term_condition_comparison
    finite_native_goal_term_comparison_exact[symmetric] finite_native_goal_term_comparison_holds_def
    split: prod.splits option.splits)

theorem native_admission_assessment_exact:
  "native_admission_inspect (native_admission_assessment X (method X)) f=
    native_admission_condition f method X"
  by (simp only: native_admission_inspect_def native_admission_assessment_def prod.case
    native_admission_condition_def native_admission_ready_exact native_admission_preservation_exact
    native_admission_term_exact)

export_code native_admission_assessment native_admission_inspect checking SML

text \<open>
  The independently stated conditions concern the original goal's positive
  meaning, a usable evaluation of both actual programs, the returned definition,
  all retained artifacts and outgoing bindings, and refusal of unsupported
  requests. The computed term observation returns every extra and missing
  tested term. Failure to observe either program returns no term comparison.
  The exact assessment equation relates every inspection to these conditions.
\<close>

end
