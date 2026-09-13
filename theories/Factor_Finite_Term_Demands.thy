theory Factor_Finite_Term_Demands
  imports Factor_Finite_Admission_Goal_Evaluation Factor_Finite_Term_Components
begin

definition finite_program_term_demand where
  "finite_program_term_demand P T=ffUnion (fimage (\<lambda>d.
    fimage (\<lambda>t. (d,t)) (ffUnion (fimage finite_term_components T))) (finite_system_definitions P))"

lemma finite_program_term_demand_component:
  assumes "d |\<in>| finite_system_definitions P" "t |\<in>| T"
    "x |\<in>| finite_term_components t"
  shows "(d,x) |\<in>| finite_program_term_demand P T"
proof -
  let ?V="ffUnion (fimage finite_term_components T)"
  have selected: "finite_term_components t |\<in>| fimage finite_term_components T"
    by (rule fimageI[OF assms(2)])
  have contained: "x |\<in>| ?V"
    using selected assms(3)
    by (simp only: ffUnion_membership; blast)
  have call: "(d,x) |\<in>| fimage (\<lambda>x. (d,x)) ?V"
    by (rule fimageI[OF contained])
  have family: "fimage (\<lambda>x. (d,x)) ?V |\<in>|
      fimage (\<lambda>e. fimage (\<lambda>x. (e,x)) ?V) (finite_system_definitions P)"
    by (rule fimageI[OF assms(1)])
  show ?thesis using family call
    by (simp only: finite_program_term_demand_def ffUnion_membership; blast)
qed

lemma finite_program_term_demand_root:
  assumes "d |\<in>| finite_system_definitions P" "t |\<in>| T"
  shows "(d,t) |\<in>| finite_program_term_demand P T"
  by (rule finite_program_term_demand_component[OF assms finite_term_components_self])

lemma finite_sequence_component_inclusion:
  assumes "x\<in>set xs"
  shows "finite_term_components x |\<subseteq>| finite_term_components (finite_data_sequence xs)"
  using assms by (induction xs) (auto simp: less_eq_fset.rep_eq)

theorem finite_admission_goal_demand_components:
  assumes "(d,x) |\<in>| finite_admission_goal_demand g t"
  shows "d\<in>admission_goal_sites g \<and> x |\<in>| finite_term_components t"
  using assms
proof (induction g arbitrary: t)
  case (Existing_Admission a)
  then show ?case by auto
next
  case (Paired_Admission g h)
  then show ?case by (cases t) auto
next
  case (Collected_Admission g)
  obtain xs where sequence: "finite_data_sequence_elements t=Some xs"
    using Collected_Admission.prems by (cases "finite_data_sequence_elements t") auto
  obtain y where element: "y\<in>set xs" "(d,x) |\<in>| finite_admission_goal_demand g y"
    using Collected_Admission.prems by (auto simp: sequence fset_of_list.rep_eq)
  have child: "d\<in>admission_goal_sites g \<and> x |\<in>| finite_term_components y"
    by (rule Collected_Admission.IH[OF element(2)])
  have shape: "t=finite_data_sequence xs"
    using sequence by (simp only: finite_data_sequence_elements_exact)
  have included: "finite_term_components y |\<subseteq>| finite_term_components t"
    by (simp only: shape; rule finite_sequence_component_inclusion[OF element(1)])
  show ?case using child included by auto
qed

theorem finite_program_goal_demand_included:
  assumes supported: "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    and tested: "t |\<in>| T"
  shows "finite_admission_goal_demand g t |\<subseteq>| finite_program_term_demand P T"
  unfolding less_eq_fset.rep_eq
proof
  fix q assume demand: "q\<in>fset (finite_admission_goal_demand g t)"
  obtain d x where shape: "q=(d,x)" by (cases q)
  have parts: "d\<in>admission_goal_sites g \<and> x |\<in>| finite_term_components t"
    by (rule finite_admission_goal_demand_components) (use demand shape in simp)
  have site: "d |\<in>| finite_system_definitions P"
    using supported parts by (auto simp: less_eq_fset.rep_eq)
  show "q\<in>fset (finite_program_term_demand P T)"
    unfolding shape
    by (rule finite_program_term_demand_component[OF site tested]) (use parts in blast)
qed

theorem finite_native_goal_terms_exact:
  assumes evaluated: "finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A)"
    and supported: "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  shows "fset (ffilter (finite_admission_goal_test A g) T)=
    {t\<in>fset T. admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
proof -
  have each: "finite_admission_goal_test A g t \<longleftrightarrow>
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
    if tested: "t |\<in>| T" for t
  proof (rule finite_admission_goal_observation_exact)
    fix d x assume demand: "(d,x) |\<in>| finite_admission_goal_demand g t"
    have included: "(d,x) |\<in>| finite_program_term_demand P T"
      using finite_program_goal_demand_included[OF supported tested] demand by auto
    show "(d,x) |\<in>| A \<longleftrightarrow> (d,decode_finite_term x)\<in>positive_meaning (decode_finite_system P)"
      by (rule finite_native_program_evaluation_call[OF evaluated included])
  qed
  show ?thesis using each by auto
qed

end
