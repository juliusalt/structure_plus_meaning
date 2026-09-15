theory Factor_Nested_Replay_Identity
  imports Factor_Prepared_Replay_Inspections Nested_Artifact_Value_Identity
begin

definition nested_replay_value where
  "nested_replay_value result=map_option (\<lambda>((n,E),u,G,J,C).
    (n,nested_environment_rows E,u,nested_generation_rows G,
      nested_environment_rows J,finite_artifact_rows C)) result"

lemma nested_replay_value_injective:
  "nested_replay_value x=nested_replay_value y \<longleftrightarrow> x=y"
  by (cases x; cases y)
    (auto simp: nested_replay_value_def nested_environment_rows_injective
      nested_generation_rows_injective finite_artifact_rows_injective split: prod.splits)

definition nested_replay_row where
  "nested_replay_row row=(fst row,map_option (fimage nested_replay_value) (snd row))"

lemma nested_replay_row_injective:
  "nested_replay_row x=nested_replay_row y \<longleftrightarrow> x=y"
proof -
  have injective: "inj nested_replay_value" by (auto simp: inj_def nested_replay_value_injective)
  show ?thesis by (cases x; cases y)
    (simp add: nested_replay_row_def optional_identity_map_injective[where encode="fimage nested_replay_value",
      OF fset_image_equality[OF injective]])
qed

declare digit_replay_inspect_prepared_code[code del]
declare digit_replay_family_inspect_prepared_code[code del]

lemma digit_replay_inspect_nested_code [code]:
  "digit_replay_inspect (result,reference,causes)=
    prepared_reader_inspection nested_replay_value (result,reference)"
  by (rule ext) (simp add: prepared_reader_inspection_exact[OF nested_replay_value_injective]
      digit_replay_inspect_def)

lemma digit_replay_family_inspect_nested_code [code]:
  "digit_replay_family_inspect (result,reference,covered,causes)=
    (if covered then prepared_reader_inspection nested_replay_row (result,reference) else (\<lambda>f. False))"
  by (rule ext) (simp add: prepared_reader_inspection_exact[OF nested_replay_row_injective]
      digit_replay_family_inspect_def)

text \<open>The complete original replay results supply each comparison.
  Every optional level, certificate, allocation head and complete nested
  environment and generation remains part of identity. The original coverage
  guard and both reader conditions are unchanged.\<close>

end
