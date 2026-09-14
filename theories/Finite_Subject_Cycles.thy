theory Finite_Subject_Cycles
  imports Finite_Assessment_Reports Finite_Investigation_Readiness
begin

definition subject_cycle_basis_ready where
  "subject_cycle_basis_ready cs fs ws observe selected=(let
    rows=subject_investigation_observations cs fs ws observe;
    relation=subject_investigation_relation cs fs ws observe
    in set selected\<subseteq>set fs \<and> investigation_revised_ready cs fs selected rows relation)"

definition subject_cycle_admissible where
  "subject_cycle_admissible cs fs ws candidate condition problem critical selected c \<longleftrightarrow>
    c\<in>set cs \<and> (\<forall>f\<in>set fs. \<forall>w\<in>set ws. condition f (candidate c) (problem w)) \<and>
    critical \<and> subject_cycle_basis_ready cs fs ws
      (\<lambda>c w f. condition f (candidate c) (problem w)) selected"

definition subject_cycle_admissions where
  "subject_cycle_admissions cs fs ws candidate observe critical selected=
    (if critical \<and> subject_cycle_basis_ready cs fs ws observe selected then
      map (\<lambda>c. (c,candidate c)) (subject_investigation_adequate cs fs ws observe) else [])"

context finite_subject_investigation
begin

theorem subject_cycle_admissions_exact:
  "(c,C)\<in>set (subject_cycle_admissions cs fs ws candidate observe critical selected) \<longleftrightarrow>
    C=candidate c \<and> subject_cycle_admissible cs fs ws candidate condition problem critical selected c"
  by (auto simp: subject_cycle_admissions_def subject_cycle_admissible_def
    subject_investigation_adequate_def observation_equation[abs_def] split: if_splits)

theorem subject_cycle_admission_conditions:
  assumes admitted: "(c,C)\<in>set (subject_cycle_admissions cs fs ws candidate observe critical selected)"
    and facet: "(f,F) |\<in>| conditions" and workload: "(w,W) |\<in>| problems"
  shows "F C W"
  using admitted facet workload
  by (auto simp: subject_cycle_admissions_exact subject_cycle_admissible_def
    finite_function_graph_member fset_of_list.rep_eq)

theorem failed_criticism_prevents_subject_admission:
  "\<not>critical \<Longrightarrow> subject_cycle_admissions cs fs ws candidate observe critical selected=[]"
  by (simp only: subject_cycle_admissions_def simp_thms if_False)

end

definition context_subject_cycle where
  "context_subject_cycle cs fs ws candidate context assess inspect criticise critic_accept selected=(let
    table=context_assessment_table cs ws context assess;
    criticism=criticise table;
    result=context_assessment_investigation cs fs ws table inspect;
    cycle=investigation_cycle_report cs fs (fst result) (fst (snd result)) selected;
    followed=snd (snd (snd (snd cycle)));
    allowed=(set selected\<subseteq>set fs \<and> fst followed \<and> fst (snd followed)=[] \<and> critic_accept criticism)
    in (table,criticism,result,cycle,
      if allowed then map (\<lambda>c. (c,candidate c)) (snd (snd (snd result))) else []))"

theorem context_subject_cycle_table:
  "fst (context_subject_cycle cs fs ws candidate context assess inspect criticise critic_accept selected)=
    context_assessment_table cs ws context assess"
  by (simp only: context_subject_cycle_def Let_def fst_conv)

theorem context_subject_cycle_criticism:
  "fst (snd (context_subject_cycle cs fs ws candidate context assess inspect criticise critic_accept selected))=
    criticise (context_assessment_table cs ws context assess)"
  by (simp only: context_subject_cycle_def Let_def fst_conv snd_conv)

theorem context_subject_cycle_admissions:
  "snd (snd (snd (snd (context_subject_cycle cs fs ws candidate context assess inspect criticise critic_accept selected))))=
    subject_cycle_admissions cs fs ws candidate (\<lambda>c w f. inspect (assess c (context w)) f)
      (critic_accept (criticise (context_assessment_table cs ws context assess))) selected"
proof -
  let ?observe="\<lambda>c w f. inspect (assess c (context w)) f"
  have rows: "set (assessed_subject_observations cs fs ws (\<lambda>c w. assess c (context w)) inspect)=
    set (subject_investigation_observations cs fs ws ?observe)"
    by (rule assessed_subject_observations_equation)
  have ready: "investigation_revised_ready cs fs selected
      (assessed_subject_observations cs fs ws (\<lambda>c w. assess c (context w)) inspect)
      (subject_investigation_relation cs fs ws ?observe)=
    investigation_revised_ready cs fs selected (subject_investigation_observations cs fs ws ?observe)
      (subject_investigation_relation cs fs ws ?observe)"
    by (rule investigation_revised_ready_cong[OF rows refl])
  show ?thesis
    using ready
    by (auto simp only: context_subject_cycle_def context_assessment_investigation_exact
      assessed_subject_investigation_equation subject_cycle_admissions_def subject_cycle_basis_ready_def
      investigation_cycle_report_def investigation_revised_ready_def investigation_ready_def
      Let_def fst_conv snd_conv split: if_splits)
qed


theorem context_subject_cycle_indices_exact:
  assumes observed: "\<And>c w f. inspect (assess c (context w)) f=condition f (candidate c) (problem w)"
  shows "c\<in>set (map fst (snd (snd (snd (snd
      (context_subject_cycle cs fs ws candidate context assess inspect criticise critic_accept selected)))))) \<longleftrightarrow>
    subject_cycle_admissible cs fs ws candidate condition problem
      (critic_accept (criticise (context_assessment_table cs ws context assess))) selected c"
proof -
  have actual: "finite_subject_investigation candidate condition problem
    (\<lambda>c w f. inspect (assess c (context w)) f)"
    by (unfold_locales) (rule observed)
  show ?thesis
    by (simp only: context_subject_cycle_admissions set_map image_iff Bex_def split_paired_Ex fst_conv
      Finite_Subject_Cycles.finite_subject_investigation.subject_cycle_admissions_exact[OF actual]; blast)
qed

text \<open>
  The original scopes and actual operations construct every context and cell.
  Criticism receives that entire constructed table, including all actual
  subjects, results and assessments. Admission requires every represented
  condition, accepted criticism, an available original selection and a formed
  followed comparison with no residual. All qualifying original candidates
  remain available; comparison selection alone cannot confer admission.

  Each use must establish the actual observation equation and the independent
  condition computed by its criticism. Native presentations of the complete
  cycle, adequate coverage of the development workflow, historical permission,
  candidate-language completeness and the complete cost account remain separate
  obligations. This conditional construction does not establish those premises.
\<close>

end
