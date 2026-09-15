theory Factor_Prepared_Replay_Inspections
  imports Factor_Structural_Replay_Identity Finite_Prepared_Reader_Inspections
begin

declare digit_replay_inspect_structural_code[code del]
declare digit_replay_family_inspect_structural_code[code del]

lemma digit_replay_inspect_prepared_code [code]:
  "digit_replay_inspect (result,reference,causes)=
    prepared_reader_inspection structural_replay_value_code (result,reference)"
  by (rule ext) (simp add: prepared_reader_inspection_exact[OF structural_replay_value_code_injective]
      digit_replay_inspect_def)

lemma digit_replay_family_inspect_prepared_code [code]:
  "digit_replay_family_inspect (result,reference,covered,causes)=
    (if covered then prepared_reader_inspection structural_replay_row (result,reference) else (\<lambda>f. False))"
  by (rule ext) (simp add: prepared_reader_inspection_exact[OF structural_replay_row_injective]
      digit_replay_family_inspect_def)

text \<open>The existing injective complete-value maps prepare an inspection
  function before its facet arguments are supplied. Context lookup also selects
  the optional inspection function before the facet traversal. The complete
  original observation list, all facet values and all reports remain equal.\<close>

end
