theory Finite_Assessed_Observation_Readings
  imports Finite_Assessment_Reports
begin

definition read_assessed_observation :: "(nat\<times>nat\<times>nat) list\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool" where
  "read_assessed_observation rows c w f=((f,c,w)\<in>set rows)"

lemma read_assessed_observation_exact:
  assumes "c\<in>set cs" "f\<in>set fs" "w\<in>set ws"
  shows "read_assessed_observation (fst (assessed_subject_investigation cs fs ws assess inspect)) c w f=
    inspect (assess c w) f"
  using assms by (simp add: read_assessed_observation_def assessed_subject_investigation_def
      Let_def assessed_subject_observations_member)

theorem context_assessment_observation_at_cell:
  assumes subject: "(w,C,cells)\<in>set (context_assessment_table cs ws context assess)"
    and cell: "(c,A)\<in>set cells" and facet: "f\<in>set fs"
  shows "read_assessed_observation (fst (context_assessment_investigation cs fs ws
      (context_assessment_table cs ws context assess) inspect)) c w f=inspect A f"
proof -
  have fields: "w\<in>set ws" "C=context w" "cells=map (\<lambda>c. (c,assess c C)) cs"
    using subject by (auto simp: context_assessment_table_def Let_def)
  have method: "c\<in>set cs" and result: "A=assess c (context w)"
    using cell by (auto simp: fields)
  show ?thesis by (simp only: context_assessment_investigation_exact
      read_assessed_observation_exact[OF method facet fields(1)] result)
qed

text \<open>This lookup reads observations already derived by the actual
  assessment and inspection. Its complete cell equation requires the actual
  constructed table, actual cell membership and the declared facet. It grants
  no condition satisfaction to an arbitrary supplied observation table.\<close>

end
