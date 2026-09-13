theory Finite_Assessed_Investigation
  imports Finite_Subject_Investigation
begin

section \<open>Share each actual assessment across all conditions and comparisons\<close>

definition assessed_subject_observations :: "nat list\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>
    (nat\<Rightarrow>nat\<Rightarrow>'a)\<Rightarrow>('a\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>(nat\<times>nat\<times>nat) list" where
  "assessed_subject_observations cs fs ws assess inspect=concat (map (\<lambda>c.
    concat (map (\<lambda>w. let A=assess c w in
      map (\<lambda>f. (f,c,w)) (filter (inspect A) fs)) ws)) cs)"

lemma assessed_subject_observations_member:
  "(f,c,w)\<in>set (assessed_subject_observations cs fs ws assess inspect) \<longleftrightarrow>
    c\<in>set cs \<and> f\<in>set fs \<and> w\<in>set ws \<and> inspect (assess c w) f"
  by (auto simp: assessed_subject_observations_def Let_def)

lemma assessed_subject_observations_equation:
  "set (assessed_subject_observations cs fs ws assess inspect)=
    set (subject_investigation_observations cs fs ws (\<lambda>c w f. inspect (assess c w) f))"
  by (auto simp only: set_eq_iff split_paired_All assessed_subject_observations_member
    subject_investigation_observations_def indexed_predicate_rows_member)

definition subject_investigation_adequate :: "nat list\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>
    (nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>nat list" where
  "subject_investigation_adequate cs fs ws observe=filter (\<lambda>c.
    \<forall>w\<in>set ws. \<forall>f\<in>set fs. observe c w f) cs"

definition assessed_subject_investigation where
  "assessed_subject_investigation cs fs ws assess inspect=(let
    rows=assessed_subject_observations cs fs ws assess inspect;
    observed=(\<lambda>c w f. (f,c,w)\<in>set rows)
    in (rows,subject_investigation_relation cs fs ws observed,
      subject_investigation_selected cs fs ws observed,
      subject_investigation_adequate cs fs ws observed))"

lemma assessed_subject_investigation_equation:
  "assessed_subject_investigation cs fs ws assess inspect=
    (assessed_subject_observations cs fs ws assess inspect,
      subject_investigation_relation cs fs ws (\<lambda>c w f. inspect (assess c w) f),
      subject_investigation_selected cs fs ws (\<lambda>c w f. inspect (assess c w) f),
      subject_investigation_adequate cs fs ws (\<lambda>c w f. inspect (assess c w) f))"
  by (auto simp: assessed_subject_investigation_def Let_def
    subject_investigation_relation_def subject_investigation_selected_def
    subject_investigation_adequate_def assessed_subject_observations_member
    investigation_pairs_exact intro!: filter_cong)

context finite_subject_investigation
begin

theorem adequacy_at_subject:
  assumes subject: "(c,C) |\<in>| candidates"
  shows "c\<in>set (subject_investigation_adequate cs fs ws observe) \<longleftrightarrow>
    (\<forall>(f,F)\<in>fset conditions. \<forall>(w,W)\<in>fset problems. F C W)"
proof -
  have fields: "c\<in>set cs \<and> C=candidate c"
    using subject by (simp only: finite_function_graph_member fset_of_list.rep_eq; blast)
  show ?thesis using fields
    by (simp only: subject_investigation_adequate_def set_filter mem_Collect_eq
      finite_function_graph_all fset_of_list.rep_eq observation_equation; blast)
qed

theorem adequacy_implies_selection:
  assumes "c\<in>set (subject_investigation_adequate cs fs ws observe)"
  shows "c\<in>set (subject_investigation_selected cs fs ws observe)"
  using assms by (auto simp: subject_investigation_adequate_def subject_investigation_selected_def
    subject_investigation_relation_def investigation_pairs_exact)

end

definition investigation_cycle_report where
  "investigation_cycle_report cs fs rows relation selected=(let
    initial=investigation_basis cs fs selected rows relation;
    repairs=investigation_repairs cs fs selected rows relation;
    revision=investigation_revision cs fs selected rows relation;
    revised=fst (snd (snd (snd revision)))
    in (selected,initial,repairs,revision,investigation_basis cs fs revised rows relation))"

lemma investigation_cycle_initial:
  "fst (snd (investigation_cycle_report cs fs rows relation selected))=
    investigation_basis cs fs selected rows relation"
  by (simp only: investigation_cycle_report_def Let_def fst_conv snd_conv)

lemma investigation_cycle_followed:
  "snd (snd (snd (snd (investigation_cycle_report cs fs rows relation selected))))=
    investigation_basis cs fs
      (fst (snd (snd (snd (investigation_revision cs fs selected rows relation))))) rows relation"
  by (simp only: investigation_cycle_report_def Let_def fst_conv snd_conv)

text \<open>
  The assessment operation runs once for each candidate and problem. Its result
  supplies every condition inspection, and the resulting observations supply
  all comparisons. The equations preserve the complete subject investigation.
  Adequacy additionally requires every represented condition at every problem;
  a comparison winner can still be inadequate when every candidate fails.
\<close>

end
