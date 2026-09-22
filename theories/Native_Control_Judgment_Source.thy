theory Native_Control_Judgment_Source
  imports Native_Control_Judgment_Scope
begin

definition filtered_judgment_source where
  "filtered_judgment_source present subjects condition=
    finite_ground_source (filtered_judgment_rows present subjects condition)"

theorem filtered_judgment_source_total:
  assumes formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
  shows "\<exists>d F u. filtered_judgment_source present subjects condition=Some (d,F,u)"
proof -
  have rows: "list_all finite_term_formed (filtered_judgment_rows present subjects condition)"
    using formed by (auto simp: filtered_judgment_rows_def list_all_iff)
  show ?thesis unfolding filtered_judgment_source_def
    using finite_ground_source_total[of "filtered_judgment_rows present subjects condition"] rows by blast
qed

theorem filtered_judgment_source_program:
  assumes formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and source: "filtered_judgment_source present subjects condition=Some (d,F,u)"
  obtains P where "native_package_at (decode_finite_environment F) u [] P"
    "\<And>t. (d,t)\<in>positive_meaning P \<longleftrightarrow>
      ((Some [],[]),t)\<in>positive_meaning
        (decode_finite_system (filtered_judgment_program present subjects condition))"
proof -
  have rows: "list_all finite_term_formed (filtered_judgment_rows present subjects condition)"
    using formed by (auto simp: filtered_judgment_rows_def list_all_iff)
  obtain P where package: "native_package_at (decode_finite_environment F) u [] P"
    and reading: "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow>
      t\<in>decode_finite_term ` set (filtered_judgment_rows present subjects condition)"
    by (rule finite_ground_source_meaning[OF source[unfolded filtered_judgment_source_def]]) blast
  show thesis by (rule that[OF package])
    (simp only: reading filtered_judgment_program_def finite_ground_program_meaning[OF rows])
qed

theorem filtered_judgment_source_meaning:
  assumes injective: "inj present"
    and formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and source: "filtered_judgment_source present subjects condition=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] P"
  shows "(d,decode_finite_term (present x))\<in>positive_meaning P \<longleftrightarrow>
    x\<in>set subjects \<and> condition x"
proof (rule filtered_judgment_source_program[OF formed source])
  fix Q
  assume installed: "native_package_at (decode_finite_environment F) u [] Q"
    and meaning: "\<And>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow>
      ((Some [],[]),t)\<in>positive_meaning
        (decode_finite_system (filtered_judgment_program present subjects condition))"
  have same: "P=Q" by (rule native_package_unique[OF package installed])
  show ?thesis by (simp only: same meaning filtered_judgment_meaning[OF injective formed])
qed

definition judgment_bridge_source where
  "judgment_bridge_source b=filtered_judgment_source syntax_judgment_data
    syntax_judgment_cases (judgment_bridge_result b)"

theorem judgment_bridge_source_total:
  "\<exists>d F u. judgment_bridge_source b=Some (d,F,u)"
  unfolding judgment_bridge_source_def by (rule filtered_judgment_source_total) simp

theorem admitted_judgment_source_meaning:
  assumes question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates b)\<in>set accepted"
    and member: "b\<in>set judgment_bridge_candidates"
    and source: "judgment_bridge_source b=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] P"
  shows "(d,decode_finite_term (syntax_judgment_data (C,syntax_proposition m)))\<in>positive_meaning P
    \<longleftrightarrow> C=syntax_checked_rooted_context \<and> syntax_join_refinement m"
proof -
  have formed: "\<And>x. x\<in>set syntax_judgment_cases \<Longrightarrow> finite_term_formed (syntax_judgment_data x)" by simp
  have base: "(d,decode_finite_term (syntax_judgment_data s))\<in>positive_meaning P \<longleftrightarrow>
      s\<in>set syntax_judgment_cases \<and> judgment_bridge_result b s" for s
    by (rule filtered_judgment_source_meaning[OF syntax_judgment_data_injective formed
      source[unfolded judgment_bridge_source_def] package])
  have condition: "judgment_bridge_condition b syntax_judgment_cases"
    by (rule judgment_bridge_admission[OF question admission selected member])
  have truth: "(d,decode_finite_term (syntax_judgment_data s))\<in>positive_meaning P \<longleftrightarrow>
      syntax_judgment_truth s" for s
    using base[of s] condition syntax_truth_has_case[of s]
    by (auto simp: judgment_bridge_condition_def)
  show ?thesis by (simp only: truth syntax_judgment_at_proposition)
qed

text \<open>The installed-source receiver reuses the direct program's local
  semantic contract through the existing source-construction theorem. Its
  original package reading is mandatory; an unrelated accepting package cannot
  substitute. Construction of a policy cause and owner authority remain separate.\<close>

definition judgment_bridge_install where
  "judgment_bridge_install report=map_option (map (\<lambda>(i,A). (i,
    case A of None \<Rightarrow> None | Some accepted \<Rightarrow>
      judgment_bridge_source (judgment_bridge_candidates!i)))) (judgment_bridge_receive report)"

theorem judgment_bridge_install_fields:
  assumes result: "judgment_bridge_install report=Some rows"
    and row: "(i,Some (d,F,u))\<in>set rows"
  obtains Q accepted where "judgment_bridge_question ()=Some Q"
    "native_development_admission Q report=Some accepted"
    "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates (judgment_bridge_candidates!i))\<in>set accepted"
    "judgment_bridge_source (judgment_bridge_candidates!i)=Some (d,F,u)"
proof -
  obtain receives A where receive: "judgment_bridge_receive report=Some receives"
    and member: "(i,Some A)\<in>set receives"
    and source: "judgment_bridge_source (judgment_bridge_candidates!i)=Some (d,F,u)"
    using result row by (auto simp: judgment_bridge_install_def split: option.splits)
  obtain Q accepted where "judgment_bridge_question ()=Some Q"
    "native_development_admission Q report=Some accepted" "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates (judgment_bridge_candidates!i))\<in>set accepted"
    by (rule judgment_bridge_receive_fields[OF receive member]) blast
  then show thesis using source that by blast
qed

corollary judgment_bridge_installed_truth:
  assumes result: "judgment_bridge_install report=Some rows"
    and row: "(i,Some (d,F,u))\<in>set rows"
    and package: "native_package_at (decode_finite_environment F) u [] P"
  shows "(d,decode_finite_term (syntax_judgment_data (C,syntax_proposition m)))\<in>positive_meaning P
    \<longleftrightarrow> C=syntax_checked_rooted_context \<and> syntax_join_refinement m"
proof (rule judgment_bridge_install_fields[OF result row])
  fix Q accepted
  assume question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and inside: "i<length judgment_bridge_candidates"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates
      (judgment_bridge_candidates!i))\<in>set accepted"
    and source: "judgment_bridge_source (judgment_bridge_candidates!i)=Some (d,F,u)"
  show ?thesis
    by (rule admitted_judgment_source_meaning[OF question admission selected nth_mem[OF inside] source package])
qed

definition judgment_bridge_install_summary where
  "judgment_bridge_install_summary result=map_option (map (\<lambda>(i,S). (i,S\<noteq>None))) result"

definition judgment_bridge_install_value where
  "judgment_bridge_install_value=finite_pair_presentation judgment_bridge_value
    (finite_option_presentation (finite_sequence_presentation
      (finite_pair_presentation isabelle_position_data (finite_option_presentation
        (finite_pair_presentation finite_site_data
          (finite_pair_presentation finite_environment_presentation finite_use_data))))))"

lemma judgment_bridge_install_value_injective: "inj judgment_bridge_install_value"
  unfolding judgment_bridge_install_value_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective judgment_bridge_value_injective
    isabelle_position_data_injective finite_site_data_injective
    finite_environment_presentation_injective finite_use_data_injective)

export_code judgment_steering_questions judgment_bridge_question judgment_bridge_value
  judgment_bridge_install judgment_bridge_install_summary judgment_bridge_install_value
  context_execution_summary native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Judgment file_prefix "native_control_judgment"

end
