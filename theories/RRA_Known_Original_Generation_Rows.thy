theory RRA_Known_Original_Generation_Rows
  imports RRA_Known_Generation_Rows
begin

definition finite_construct_known_original_generation where
  "finite_construct_known_original_generation E l p c rows=(if generation_record_targets_ready l p c rows then
    map_option (finite_generation_record_body E l p c rows)
      (keyed_option_map (finite_anchor_artifact E) (map fst rows)) else None)"

theorem finite_construct_known_original_generation_exact:
  assumes formed: "finite_environment_formed E"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G E (fst d) (snd d)) rows"
  shows "finite_construct_known_original_generation E l p c rows=finite_construct_generation_record E l p c rows"
  by (simp only: finite_construct_known_original_generation_def finite_construct_generation_record_def
      finite_generation_ready_known_rows[OF formed rows])

text \<open>The original allocator instantiates the same known-predecessor
  readiness equation as the digit allocator. Its original anchors, material
  extension, selected use and complete generation body are unchanged.\<close>

end
