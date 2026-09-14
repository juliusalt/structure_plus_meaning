theory Factor_Native_Requirement_Report_Assessment
  imports Factor_Native_Requirement_Assessment Finite_Optional_Report_Observations
begin

lemma finite_existing_admission_test_function:
  "finite_admission_goal_test A (Existing_Admission d)=(\<lambda>t. (d,t) |\<in>| A)"
  by (rule ext) simp

definition native_requirement_report_observation where
  "native_requirement_report_observation source=(case source of (P,supported,D,evaluated,terms) \<Rightarrow>
    optional_report_observation supported evaluated terms)"

lemma native_requirement_report_observation_exact:
  "native_requirement_report_observation (native_requirement_source_report (E,u,r,gs,T))=
    finite_native_requirement_term_observation E u r gs T"
  by (cases "finite_native_source E u r")
    (simp_all add: native_requirement_report_observation_def native_requirement_source_report_def
      optional_report_observation_map finite_native_requirement_term_observation_def
      finite_native_term_observation_def Let_def)

definition native_requirement_target_observation where
  "native_requirement_target_observation target=(case target of None \<Rightarrow> None
    | Some (d,F,v,source,D,evaluated,terms,old) \<Rightarrow>
      optional_report_observation (case source of None \<Rightarrow> False
        | Some P \<Rightarrow> d |\<in>| finite_system_definitions P) evaluated terms)"

lemma native_requirement_target_observation_exact:
  "native_requirement_target_observation (native_requirement_target_report (E,u,r,gs,T) result)=
    (case result of None \<Rightarrow> None | Some (d,F,v) \<Rightarrow>
      finite_native_goal_term_observation F v [] (Existing_Admission d) T)"
  by (cases result)
    (auto simp: native_requirement_target_observation_def native_requirement_target_report_def
      native_entry_target_report_def optional_report_observation_map
      finite_native_goal_term_observation_def finite_native_term_observation_def
      finite_existing_admission_test_function Let_def split: prod.splits option.splits)

definition native_requirement_report_preservation where
  "native_requirement_report_preservation X source target=(case X of (E,u,r,gs,T) \<Rightarrow>
    case source of (original,supported,D,evaluated,terms) \<Rightarrow>
    case target of None \<Rightarrow> False
    | Some (d,F,v,Q,M,result,values,old) \<Rightarrow>
      finite_environment_formed F \<and> finite_environment_included E F \<and>
      finite_environment_agrees_on E F (finite_environment_uses E) \<and>
      original\<noteq>None \<and> old=original)"

lemma native_requirement_report_preservation_exact:
  "native_requirement_report_preservation X (native_requirement_source_report X)
      (native_requirement_target_report X result)=native_requirement_preservation_observation X result"
  by (cases X; cases result)
    (auto simp: native_requirement_report_preservation_def native_requirement_source_report_def
      native_requirement_target_report_def native_entry_target_report_def
      native_requirement_preservation_observation_def finite_source_preservation_observation_def
      Let_def split: prod.splits option.splits)

definition native_requirement_assessment_from_reports where
  "native_requirement_assessment_from_reports X source result target=(
    fst (snd source),
    (case result of None \<Rightarrow> None | Some unused \<Rightarrow>
      finite_term_observation_comparison (native_requirement_report_observation source)
        (native_requirement_target_observation target)),
    native_requirement_report_preservation X source target,result=None)"

lemma native_requirement_report_ready_exact:
  "fst (snd (native_requirement_source_report X))=native_requirement_ready X"
  by (cases X) (simp add: native_requirement_source_report_def native_requirement_ready_def Let_def)

theorem native_requirement_assessment_from_reports_exact:
  "native_requirement_assessment_from_reports X (native_requirement_source_report X) result
      (native_requirement_target_report X result)=native_requirement_assessment X result"
  by (cases X; cases result)
    (simp_all add: native_requirement_assessment_from_reports_def native_requirement_assessment_def
      native_requirement_report_preservation_exact native_requirement_report_observation_exact
      native_requirement_target_observation_exact native_requirement_term_observation_def
      finite_native_requirement_term_comparison_def native_requirement_report_ready_exact
      Let_def split: prod.splits)

text \<open>
  The original observations are recovered from complete actual reports. Support,
  source unavailability, target unavailability, complete term differences and
  original-source preservation keep their existing meanings on every input.
  No evaluation result is supplied independently and no failed field is dropped.
\<close>

end
