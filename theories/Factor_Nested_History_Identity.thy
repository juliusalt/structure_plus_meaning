theory Factor_Nested_History_Identity
  imports Factor_Constructed_History_Investigation Nested_Artifact_Value_Identity
    Finite_Prepared_Reader_Inspections Structural_Word_Lists
begin

definition nested_required_history_rows where
  "nested_required_history_rows q=(nested_environment_rows (required_history_source q),
    required_history_source_use q,required_history_source_root q,required_history_goals q,
    required_history_entry q,nested_environment_rows (required_history_policy q),
    required_history_policy_use q,nested_environment_rows (required_history_material q),
    map nested_generation_member (required_history_members q),finite_required_history_state.more q)"

lemma nested_required_history_rows_injective:
  "nested_required_history_rows q=nested_required_history_rows p \<longleftrightarrow> q=p"
  by (cases q; cases p)
    (simp add: nested_required_history_rows_def nested_environment_rows_injective
      structural_map_injective[OF nested_generation_member_injective])

definition nested_history_value where
  "nested_history_value result=(case result of (n,q,I) \<Rightarrow>
    (n,nested_required_history_rows q,fimage nested_generation_member I))"

lemma nested_history_value_injective:
  "nested_history_value x=nested_history_value y \<longleftrightarrow> x=y"
proof -
  have injective: "inj nested_generation_member"
    by (auto simp: inj_def nested_generation_member_injective)
  show ?thesis by (cases x; cases y)
    (auto simp: nested_history_value_def nested_required_history_rows_injective
      fset_image_equality[OF injective] split: prod.splits)
qed

definition nested_history_row where
  "nested_history_row row=(fst row,map_option (map_option nested_history_value) (snd row))"

lemma nested_history_row_injective:
  "nested_history_row x=nested_history_row y \<longleftrightarrow> x=y"
  by (cases x; cases y)
    (simp add: nested_history_row_def optional_identity_map_injective[
      OF optional_identity_map_injective[OF nested_history_value_injective]])

declare digit_history_inspect_def[code del]
declare digit_history_question_inspect_def[code del]

lemma digit_history_inspect_nested_code [code]:
  "digit_history_inspect report=prepared_reader_inspection nested_history_row report"
  by (simp only: prepared_reader_inspection_exact[OF nested_history_row_injective]
      digit_history_inspect_def)

lemma digit_history_question_inspect_nested_code [code]:
  "digit_history_question_inspect (covered,report)=
    (if covered then digit_history_inspect report else (\<lambda>f. False))"
  by (rule ext) (simp add: digit_history_question_inspect_def)

text \<open>All original history fields are retained, including the ordered
  ledger and its separate unordered cache relation. Every generation is mapped
  recursively and every artifact retains all counted occurrences. Original
  unavailable-input and refused-result positions remain distinct. No history
  formation, reachability or admission is inferred from the identity map.\<close>

end
