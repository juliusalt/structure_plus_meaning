theory Native_Control_Finite_Guard
  imports Native_Control_Artifact_Source Native_Control_Closed_Installation
    Native_Control_Artifact_Reused_Execution
begin

section \<open>The existing exact representation is applied to the original guard\<close>

definition finite_quoted_judgment where
  "finite_quoted_judgment xs=finite_system_of (quoted_judgment_rows.artifact_system xs)"

context quoted_judgment_rows
begin

lemma finite_guard_exact:
  "decode_finite_system (finite_quoted_judgment xs)=artifact_system"
  unfolding finite_quoted_judgment_def by (rule decode_finite_system_of[OF artifact_formed])

lemma finite_guard_formed: "finite_system_formed (finite_quoted_judgment xs)"
  by (simp only: finite_system_formed_correct finite_guard_exact artifact_formed)

lemma finite_guard_entry:
  "369 |\<in>| finite_system_definitions (finite_quoted_judgment xs)"
  by (simp only: finite_system_definitions_correct finite_guard_exact artifact_entry)

lemma finite_body_not_guard:
  "finite_system_of body_system\<noteq>finite_quoted_judgment xs"
proof
  assume same: "finite_system_of body_system=finite_quoted_judgment xs"
  have programs: "body_system=artifact_system"
    using arg_cong[OF same, of decode_finite_system]
    by (simp only: decode_finite_system_of[OF body_formed] finite_guard_exact)
  have "369\<in>system_definitions body_system" by (simp only: programs artifact_entry)
  then show False by simp
qed

lemma finite_empty_not_guard:
  "empty_installation_program\<noteq>finite_quoted_judgment xs"
  using finite_guard_entry by auto

end

section \<open>Exact target selection has actual finite program subjects\<close>

datatype guard_representation = Complete_Guard_Target | Body_Only_Target | Empty_Target

fun guard_target where
  "guard_target Complete_Guard_Target xs=finite_quoted_judgment xs"
| "guard_target Body_Only_Target xs=finite_system_of (quoted_judgment_rows.body_system xs)"
| "guard_target Empty_Target xs=empty_installation_program"

definition guard_representation_condition where
  "guard_representation_condition m xs \<longleftrightarrow> list_all finite_term_formed xs \<and>
    decode_finite_system (guard_target m xs)=quoted_judgment_rows.artifact_system xs"

definition guard_representation_observation where
  "guard_representation_observation m xs=(list_all finite_term_formed xs \<and>
    guard_target m xs=finite_quoted_judgment xs)"

lemma guard_representation_observation_exact:
  "guard_representation_observation m xs=guard_representation_condition m xs"
proof (cases "list_all finite_term_formed xs")
  case True
  then interpret rows: quoted_judgment_rows xs by unfold_locales
  show ?thesis using True
    by (simp only: guard_representation_observation_def guard_representation_condition_def
      rows.finite_guard_exact[symmetric] decode_finite_system_injective)
next
  case False
  then show ?thesis by (simp add: guard_representation_observation_def guard_representation_condition_def)
qed

declare guard_representation_observation_def[code del]

lemma guard_representation_observation_code [code]:
  "guard_representation_observation m xs=(list_all finite_term_formed xs \<and> m=Complete_Guard_Target)"
proof (cases "list_all finite_term_formed xs")
  case True
  then interpret rows: quoted_judgment_rows xs by unfold_locales
  show ?thesis using True
    by (cases m) (simp_all add: guard_representation_observation_def rows.finite_body_not_guard
      rows.finite_empty_not_guard)
next
  case False
  then show ?thesis by (simp add: guard_representation_observation_def)
qed

definition guard_representation_candidates where
  "guard_representation_candidates=[Body_Only_Target,Empty_Target,Complete_Guard_Target]"

definition guard_representation_question where
  "guard_representation_question xs=filtered_development_question guard_representation_candidates
    (\<lambda>m. guard_representation_observation m xs)"

theorem guard_representation_admission:
  assumes question: "guard_representation_question xs=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  shows "i<length guard_representation_candidates \<and>
    guard_representation_condition (guard_representation_candidates!i) xs"
  using filtered_development_admission[OF question[unfolded guard_representation_question_def] admitted selected]
  by (simp only: guard_representation_observation_exact)

definition checked_judgment_rows where
  "checked_judgment_rows=filtered_judgment_rows syntax_judgment_data syntax_judgment_cases syntax_judgment_check"

lemma checked_judgment_rows_formed: "list_all finite_term_formed checked_judgment_rows"
  by (simp add: checked_judgment_rows_def filtered_judgment_rows_def list_all_iff)

context admitted_judgment_artifacts
begin

lemma original_rows:
  "filtered_judgment_rows syntax_judgment_data syntax_judgment_cases (judgment_bridge_result bridge)=
    checked_judgment_rows"
proof -
  have pointwise: "judgment_bridge_result bridge s=syntax_judgment_check s"
    if "s\<in>set syntax_judgment_cases" for s
    using body_condition that
    by (simp only: judgment_bridge_condition_def syntax_judgment_check_exact; blast)
  have filtered: "filter (judgment_bridge_result bridge) syntax_judgment_cases=
      filter syntax_judgment_check syntax_judgment_cases"
    by (rule filter_cong[OF refl]) (use pointwise in blast)
  show ?thesis by (simp only: filtered_judgment_rows_def checked_judgment_rows_def filtered)
qed

lemma finite_original_guard:
  "decode_finite_system (finite_quoted_judgment checked_judgment_rows)=receiver.artifact.artifact_system"
  using receiver.artifact.finite_guard_exact by (simp only: original_rows)

end

definition guard_representation_execution_question where
  "guard_representation_execution_question ignored=guard_representation_question checked_judgment_rows"

export_code guard_representation_execution_question judgment_artifact_execution_question
  judgment_bridge_question judgment_steering_questions judgment_artifact_value
  context_execution_summary native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Guard file_prefix "native_control_guard"

text \<open>The comparison concerns exact finite representations of the original
  complete guard. Its observation is equality of actual targets; the execution
  equation is derived from complete decoding and the missing guard entry in
  each rejected target. Formation is computed on the actual checked judgment
  rows. Selection does not establish executable code for arbitrary abstract
  programs, installation, certified causes, or a governing owner policy.\<close>

end
