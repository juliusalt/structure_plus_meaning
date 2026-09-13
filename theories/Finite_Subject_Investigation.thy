theory Finite_Subject_Investigation
  imports Finite_Observation_Contracts
begin

section \<open>One finite investigation construction for actual subject conditions\<close>

definition subject_investigation_observations :: "nat list\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>
    (nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>(nat\<times>nat\<times>nat) list" where
  "subject_investigation_observations cs fs ws observe=concat (map (\<lambda>f.
    concat (map (\<lambda>c. map (\<lambda>w. (f,c,w)) (filter (\<lambda>w. observe c w f) ws)) cs)) fs)"

definition subject_investigation_relation :: "nat list\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>
    (nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>(nat\<times>nat) list" where
  "subject_investigation_relation cs fs ws observe=filter (\<lambda>(c,d).
    \<forall>w\<in>set ws. \<forall>f\<in>set fs. observe c w f \<longrightarrow> observe d w f) (investigation_pairs cs)"

definition subject_investigation_selected :: "nat list\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>
    (nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>nat list" where
  "subject_investigation_selected cs fs ws observe=filter (\<lambda>d.
    \<forall>c\<in>set cs. (c,d)\<in>set (subject_investigation_relation cs fs ws observe)) cs"

definition finite_subject_comparison where
  "finite_subject_comparison conditions problems candidate other \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset conditions. \<forall>(w,problem)\<in>fset problems.
      condition candidate problem \<longrightarrow> condition other problem)"

locale finite_subject_investigation =
  fixes cs fs ws :: "nat list"
    and candidate :: "nat\<Rightarrow>'c" and condition :: "nat\<Rightarrow>'c\<Rightarrow>'w\<Rightarrow>bool"
    and problem :: "nat\<Rightarrow>'w" and observe :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool"
  assumes observation_equation: "\<And>c w f. observe c w f=condition f (candidate c) (problem w)"
begin

abbreviation candidates where "candidates \<equiv> fimage (\<lambda>c. (c,candidate c)) (fset_of_list cs)"
abbreviation conditions where "conditions \<equiv> fimage (\<lambda>f. (f,condition f)) (fset_of_list fs)"
abbreviation problems where "problems \<equiv> fimage (\<lambda>w. (w,problem w)) (fset_of_list ws)"

lemma maps_formed:
  "finite_observation_subjects_formed candidates conditions problems"
  by (rule finite_observation_function_graphs_formed)

lemma observations_derived:
  "fset_of_list (subject_investigation_observations cs fs ws observe)=
    finite_derived_observations candidates conditions problems (\<lambda>condition candidate problem. condition candidate problem)"
  by (rule finite_table_derived_from_function_graphs)
    (simp only: fset_of_list.rep_eq subject_investigation_observations_def indexed_predicate_rows_member
      observation_equation; blast)

theorem observation_at_subject:
  assumes "(c,C) |\<in>| candidates" "(f,F) |\<in>| conditions" "(w,W) |\<in>| problems"
  shows "(f,c,w)\<in>set (subject_investigation_observations cs fs ws observe) \<longleftrightarrow> F C W"
  using finite_derived_observation_at_subject[OF maps_formed assms,
    where P="\<lambda>condition candidate problem. condition candidate problem"]
  by (simp only: observations_derived[symmetric] fset_of_list.rep_eq)

lemma comparison_equation:
  "finite_subject_comparison conditions problems (candidate c) (candidate d) \<longleftrightarrow>
    (\<forall>w\<in>set ws. \<forall>f\<in>set fs. observe c w f \<longrightarrow> observe d w f)"
  by (simp only: finite_subject_comparison_def finite_function_graph_all fset_of_list.rep_eq observation_equation; blast)

theorem comparison_at_subject:
  assumes first: "(c,C) |\<in>| candidates" and second: "(d,D) |\<in>| candidates"
  shows "(c,d)\<in>set (subject_investigation_relation cs fs ws observe) \<longleftrightarrow>
    finite_subject_comparison conditions problems C D"
proof -
  have fields: "c\<in>set cs \<and> C=candidate c \<and> d\<in>set cs \<and> D=candidate d"
    using first second by (simp only: finite_function_graph_member fset_of_list.rep_eq; blast)
  show ?thesis by (simp only: subject_investigation_relation_def indexed_relation_rows_member;
    use fields comparison_equation in blast)
qed

theorem selection_at_subject:
  assumes subject: "(c,C) |\<in>| candidates"
  shows "c\<in>set (subject_investigation_selected cs fs ws observe) \<longleftrightarrow>
    (\<forall>(d,D)\<in>fset candidates. finite_subject_comparison conditions problems D C)"
proof -
  have fields: "c\<in>set cs \<and> C=candidate c"
    using subject by (simp only: finite_function_graph_member fset_of_list.rep_eq; blast)
  have member: "c\<in>set cs" and same: "C=candidate c" using fields by blast+
  show ?thesis
    by (simp only: subject_investigation_selected_def set_filter mem_Collect_eq
      finite_function_graph_all fset_of_list.rep_eq same;
      auto simp: subject_investigation_relation_def indexed_relation_rows_member investigation_pairs_exact comparison_equation member)

qed

end

text \<open>
  Each use supplies actual candidates, independently stated conditions and
  problems, together with an exact equation for its executable observation.
  The shared construction derives the complete subject maps, observations,
  comparison relation and selection. Selection retains all represented
  candidates that preserve every other candidate's satisfied condition at
  every represented problem. The equation remains a prerequisite of each use;
  this construction supplies no observation about an unaccounted operation.
\<close>

end
