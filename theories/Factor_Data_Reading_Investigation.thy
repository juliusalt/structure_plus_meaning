theory Factor_Data_Reading_Investigation
  imports Factor_Data_Reading_Methods
begin

definition data_reading_quality where
  "data_reading_quality source m w f=data_reading_inspect
    (data_reading_assessment m (data_reading_context (data_reading_case source w))) f"

theorem data_reading_quality_exact:
  "data_reading_quality source m w f=data_reading_condition f (data_reading_method m) (data_reading_case source w)"
  by (simp only: data_reading_quality_def data_reading_assessment_exact)

interpretation data_reading: finite_subject_investigation "[0,1,2,3,4,5,6]" "[0,1]" ws
    data_reading_method data_reading_condition "data_reading_case source" "data_reading_quality source" for ws source
  by (unfold_locales) (rule data_reading_quality_exact)

definition data_reading_investigation where
  "data_reading_investigation source ws selected=investigation_basis [0,1,2,3,4,5,6] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6] [0,1] ws (data_reading_quality source))
    (subject_investigation_relation [0,1,2,3,4,5,6] [0,1] ws (data_reading_quality source))"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm data_reading_investigation_def},
   equation = @{thm data_reading.observations_derived},
   formation = @{thm data_reading.maps_formed},
   observation = @{thm data_reading.observation_at_subject},
   comparison = @{thm data_reading.comparison_at_subject}}\<close>

definition data_reading_packet where
  "data_reading_packet source ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6] ws
      (data_reading_context \<circ> data_reading_case source) data_reading_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6] [0,1] ws table data_reading_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1]
      (fst compared) (fst (snd compared))) selections))"

theorem data_reading_packet_comparison:
  "fst (snd (data_reading_packet source ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6] [0,1] ws (\<lambda>m w. data_reading_assessment m (data_reading_context (data_reading_case source w)))
      data_reading_inspect"
  by (simp only: data_reading_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact comp_apply)

definition data_reading_indices :: "nat list" where
  "data_reading_indices=[0,1,2,3,4,5,6,7,8,9,10,11]"

end
