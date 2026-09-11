theory Factor_Investigation_Input_Development
  imports Factor_Investigation_Input_Contracts Factor_Admission_Plan_Contracts
begin

section \<open>The original input requirement supplies a construction goal\<close>

definition investigation_input_goal :: admission_goal where
  "investigation_input_goal=Paired_Admission (Existing_Admission 311)
    (Collected_Admission (Paired_Admission (Existing_Admission 2) (Existing_Admission 2)))"

lemma investigation_input_goal_supported:
  "admission_goal_sites investigation_input_goal\<subseteq>system_definitions investigation_input_base_system"
  using investigation_input_base_roots by (auto simp: investigation_input_goal_def)

lemma investigation_input_goal_exact:
  "admission_goal_holds (positive_meaning investigation_input_base_system) investigation_input_goal t
    \<longleftrightarrow> (\<exists>z. investigation_input_presents z t)"
proof -
  have same: "(e,x)\<in>positive_meaning investigation_input_system \<longleftrightarrow>
      (e,x)\<in>positive_meaning investigation_input_base_system"
    if "e\<in>{2,311}" for e x
    using investigation_input_group.old_meaning[of e x] investigation_input_base_roots that
    by (simp only: investigation_input_system_def; blast)
  have scope_same: "(311,x)\<in>positive_meaning investigation_input_system \<longleftrightarrow>
      (311,x)\<in>positive_meaning investigation_input_base_system" for x
    by (rule same) simp
  have data_same: "(2,x)\<in>positive_meaning investigation_input_system \<longleftrightarrow>
      (2,x)\<in>positive_meaning investigation_input_base_system" for x
    by (rule same) simp
  have goal: "admission_goal_holds (positive_meaning investigation_input_base_system) investigation_input_goal t
      \<longleftrightarrow> (338,t)\<in>positive_meaning investigation_input_system"
    by (simp only: investigation_input_goal_def admission_goal_holds.simps
      investigation_input_fields.exact investigation_input_pairs.exact investigation_input_pair.exact
      data_same scope_same; simp)
  show ?thesis using goal investigation_input_exact by blast
qed

lemma investigation_input_generated_plan:
  "admission_plan investigation_input_goal n=(Suc (Suc n),Suc (Suc (Suc n)),
    [Pair_Admission_Instruction n 2 2,List_Admission_Instruction (Suc n) n,
      Pair_Admission_Instruction (Suc (Suc n)) 311 (Suc n)])"
  by (simp add: investigation_input_goal_def)

definition generated_investigation_input_system where
  "generated_investigation_input_system n=install_admission_plan investigation_input_base_system
    (snd (snd (admission_plan investigation_input_goal n)))"

theorem generated_investigation_input_contract:
  assumes source: "admission_source investigation_input_base_system n"
  shows "schema_system_formed (generated_investigation_input_system n)"
    "systems_agree_on investigation_input_base_system (generated_investigation_input_system n)
      (system_definitions investigation_input_base_system)"
    "(Suc (Suc n),t)\<in>positive_meaning (generated_investigation_input_system n)
      \<longleftrightarrow> (\<exists>z. investigation_input_presents z t)"
  using admission_plan_installed[OF source investigation_input_goal_supported
      investigation_input_generated_plan[of n]]
  by (auto simp only: generated_investigation_input_system_def investigation_input_generated_plan
    fst_conv snd_conv admission_source_def admission_extension_def investigation_input_goal_exact)

lemma investigation_input_original_plan:
  "admission_plan investigation_input_goal 336=(338,339,
    [Pair_Admission_Instruction 336 2 2,List_Admission_Instruction 337 336,
      Pair_Admission_Instruction 338 311 337])"
  by (simp only: investigation_input_generated_plan; simp)

lemma investigation_input_original_installation:
  "generated_investigation_input_system 336=investigation_input_system"
  by (simp add: generated_investigation_input_system_def investigation_input_original_plan
    investigation_input_system_def investigation_input_group_system_def system_union_def
    add_view_definition_def admitted_data_pair_schema list_profile_clauses_def;
    auto simp: fun_eq_iff)

export_code admission_plan investigation_input_goal checking SML

text \<open>
  The goal retains the original scope predicate and the independently admitted
  complete relation. The earlier component contracts establish its exactness
  for the unchanged input subject. Planning receives this goal and a starting
  counter, and computes every constructor, callee, and allocated entry. Its
  output is not a supplied candidate list. Installation at the earlier counter
  reproduces the actual complete-input program; every fresh counter has the
  same all-term contract. Source freshness remains an explicit prerequisite.
\<close>

end
