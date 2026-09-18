theory Native_Control_Literal_Boundary
  imports Native_Control_Judgment_Source Factor_Finite_Required_Causes
begin

lemma judgment_bridge_refuses_literal_target:
  "((Some [],[]),Target_Term (Whole_Artifact R))\<notin>
    positive_meaning (decode_finite_system (judgment_bridge_program b))"
proof -
  have formed: "list_all finite_term_formed (filtered_judgment_rows syntax_judgment_data
      syntax_judgment_cases (judgment_bridge_result b))"
    by (auto simp: filtered_judgment_rows_def list_all_iff)
  show ?thesis
    unfolding judgment_bridge_program_def filtered_judgment_program_def
    by (simp only: finite_ground_program_meaning[OF formed];
      auto simp: filtered_judgment_rows_def syntax_judgment_data_def finite_pair_presentation_def
      split: prod.splits)
qed

theorem judgment_source_refuses_literal_target:
  assumes source: "judgment_bridge_source b=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] P"
  shows "(d,Target_Term (Whole_Artifact R))\<notin>positive_meaning P"
proof -
  have formed: "\<And>x. x\<in>set syntax_judgment_cases \<Longrightarrow> finite_term_formed (syntax_judgment_data x)" by simp
  obtain Q where installed: "native_package_at (decode_finite_environment F) u [] Q"
    and meaning: "\<And>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow>
      ((Some [],[]),t)\<in>positive_meaning (decode_finite_system (judgment_bridge_program b))"
    using filtered_judgment_source_program[OF formed source[unfolded judgment_bridge_source_def]]
    by (simp only: judgment_bridge_program_def; blast)
  have same: "P=Q" by (rule native_package_unique[OF package installed])
  show ?thesis by (simp only: same meaning judgment_bridge_refuses_literal_target not_False_eq_True)
qed

theorem direct_body_entry_cannot_certify_literal_cause:
  assumes source: "judgment_bridge_source b=Some (d,F,u)"
    and original: "finite_native_source F u []=Some P"
  shows "\<not>finite_required_cause F u [] [Existing_Admission d] E gu gr G H root R"
proof -
  have package: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    using original by (simp only: finite_native_source_correct)
  have refused: "\<not>admission_goal_holds (positive_meaning (decode_finite_system P)) (Existing_Admission d)
      (Target_Term (Whole_Artifact (decode_finite_object R)))"
    using judgment_source_refuses_literal_target[OF source package] by simp
  show ?thesis by (rule finite_required_cause_failed_requirement[OF original _ refused]) simp
qed

text \<open>This is an obstruction under the current contracts, not a new
  authorization or a weaker policy. The current source judges a context and
  proposition body; a certified cause judges a whole literal artifact. A
  complete-body quotation adapter with its original program premises must
  connect these subjects before the body entry can serve that role.\<close>

end
