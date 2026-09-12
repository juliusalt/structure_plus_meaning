theory Factor_Portable_Table_Development
  imports Factor_Requirement_Plan_Realization Finite_Portable_Table_Guard
begin

section \<open>The actual two table requirements determine the generated guard\<close>

definition portable_table_goals :: "admission_goal list" where
  "portable_table_goals=[Existing_Admission 2,Existing_Admission 353]"

lemma portable_table_goal_support:
  "\<forall>g\<in>set portable_table_goals.
    admission_goal_sites g\<subseteq>system_definitions keyed_table_comparison_system"
  using keyed_table_data_supported by (auto simp: portable_table_goals_def)

lemma portable_table_admission_source:
  "admission_source keyed_table_comparison_system 354"
  using keyed_table_base_subdomain by (auto simp: admission_source_def)

lemma portable_table_source_exact:
  "admission_source keyed_table_comparison_system n \<longleftrightarrow> 354\<le>n"
proof
  assume source: "admission_source keyed_table_comparison_system n"
  have "353<n" using source by (auto simp: admission_source_def)
  then show "354\<le>n" by simp
next
  assume "354\<le>n"
  then show "admission_source keyed_table_comparison_system n"
    by (rule admission_source_weaken[OF portable_table_admission_source])
qed

lemma portable_table_sequence:
  "admission_sequence portable_table_goals n=([2,353],n,[])"
  by (simp add: portable_table_goals_def)

definition generated_portable_table_system where
  "generated_portable_table_system n=required_admission_system keyed_table_comparison_system [2,353] n []"

lemma generated_portable_table_original:
  "generated_portable_table_system 360=portable_table_system"
  by (simp add: generated_portable_table_system_def required_admission_system_def
    requirement_sockets_def portable_table_system_def portable_table_requirements_def)

lemma generated_portable_table_contract:
  assumes bound: "354\<le>n"
  shows "admission_source (generated_portable_table_system n) (Suc n)"
    "admission_extension keyed_table_comparison_system (generated_portable_table_system n)"
    "(n,t)\<in>positive_meaning (generated_portable_table_system n) \<longleftrightarrow>
      (360,t)\<in>positive_meaning portable_table_system"
proof -
  have source: "admission_source keyed_table_comparison_system n"
    by (rule admission_source_weaken[OF portable_table_admission_source bound])
  have native: "(361,admission_plan_argument (data_list_term (map admission_goal_value portable_table_goals))
      (admission_counter n) (data_list_term (map admission_counter [2,353])) (admission_counter n)
      (data_list_term (map admission_instruction_value [])))\<in>positive_meaning admission_sequence_system"
    by (simp only: admission_sequence_at_values portable_table_sequence)
  show "admission_source (generated_portable_table_system n) (Suc n)"
    "admission_extension keyed_table_comparison_system (generated_portable_table_system n)"
    using native_required_admission_installed(1,2)[OF native source portable_table_goal_support]
    by (simp_all only: generated_portable_table_system_def)
  have gate: "(n,t)\<in>positive_meaning (generated_portable_table_system n) \<longleftrightarrow>
      term_formed t \<and> (2,t)\<in>positive_meaning keyed_table_comparison_system \<and>
      (353,t)\<in>positive_meaning keyed_table_comparison_system"
    using native_required_admission_installed(3)[OF native source portable_table_goal_support, of t]
    by (simp add: generated_portable_table_system_def portable_table_goals_def)
  show "(n,t)\<in>positive_meaning (generated_portable_table_system n) \<longleftrightarrow>
      (360,t)\<in>positive_meaning portable_table_system"
    by (simp only: gate portable_table_system_def portable_table_installation.guarded_meaning
      ; simp add: portable_table_requirements_def)
qed

definition portable_requirement_execution where
  "portable_requirement_execution n xs ys=
    (if n<354 then None else Some (admission_sequence portable_table_goals n,
      (n,Pair_Term (pair_list_term (decoded_keyed_rows xs)) (pair_list_term (decoded_keyed_rows ys)))
        \<in>positive_meaning (generated_portable_table_system n)))"

lemma portable_requirement_execution_code [code]:
  "portable_requirement_execution n xs ys=
    (if n<354 then None else Some (admission_sequence portable_table_goals n,
      finite_portable_table_comparison xs ys))"
proof (cases "n<354")
  case True
  then show ?thesis by (simp add: portable_requirement_execution_def)
next
  case False
  have bound: "354\<le>n" using False by simp
  show ?thesis by (simp only: portable_requirement_execution_def
    generated_portable_table_contract(3)[OF bound] finite_portable_table_comparison_correct)
qed

export_code admission_sequence portable_table_goals portable_requirement_execution checking SML

text \<open>
  The independently defined subject is the complete pair of keyed tables.
  Its two conditions are actual table equality with unique keys and actual
  self-contained value admission. Existing predicate contracts identify those
  conditions before the native planner constructs their shared-subject guard.

  Execution reports the computed plan and that generated program's judgment
  on the complete supplied tables. Counters below the established source bound
  fail this execution interface. This bounded use does not yet compute the
  observations or authorize the transitions required by the whole development
  workflow; table descriptions supply no additional semantic authority.
\<close>

end
