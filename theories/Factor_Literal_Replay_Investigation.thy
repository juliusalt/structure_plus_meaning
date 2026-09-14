theory Factor_Literal_Replay_Investigation
  imports Factor_Literal_Replay_Assessment Factor_Literal_Replay_Alternatives
begin

definition literal_replay_context_from where
  "literal_replay_context_from seed w=(seed,w,literal_replay_covered seed,
    fimage (\<lambda>(c,X). (c,map_option (\<lambda>x. (x,literal_replay_report x)) X))
      (literal_replay_family seed w))"

definition literal_replay_cell where
  "literal_replay_cell m context=(case context of (seed,w,covered,rows) \<Rightarrow>
    (covered,fimage (\<lambda>(c,X). (c,map_option (\<lambda>(x,report).
      (x,report,literal_replay_decide 0 report,literal_replay_decide m report)) X)) rows))"

lemma literal_replay_cell_exact:
  "literal_replay_cell m (literal_replay_context_from seed w)=literal_replay_family_assessment m (seed,w)"
  by (simp add: literal_replay_cell_def literal_replay_context_from_def literal_replay_family_assessment_def
    literal_replay_row_assessment_def[abs_def] fimage_fimage comp_def case_prod_unfold Let_def option.map_comp)

definition literal_replay_problem where
  "literal_replay_problem w=(literal_replay_seed,w)"

definition literal_replay_quality where
  "literal_replay_quality m w f=literal_replay_family_inspect
    (literal_replay_cell m (literal_replay_context_from literal_replay_seed w)) f"

theorem literal_replay_quality_exact:
  "literal_replay_quality m w f=literal_replay_family_condition f (literal_replay_method m) (literal_replay_problem w)"
  by (simp only: literal_replay_quality_def literal_replay_cell_exact
    literal_replay_family_assessment_exact literal_replay_problem_def)

interpretation literal_replay: finite_subject_investigation "[0,1,2,3,4,5,6]" "[0,1]" ws
    literal_replay_method literal_replay_family_condition literal_replay_problem literal_replay_quality for ws
  by (unfold_locales) (rule literal_replay_quality_exact)

definition literal_replay_investigation where
  "literal_replay_investigation ws selected=investigation_basis [0,1,2,3,4,5,6] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6] [0,1] ws literal_replay_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6] [0,1] ws literal_replay_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm literal_replay_investigation_def},
   equation = @{thm literal_replay.observations_derived},
   formation = @{thm literal_replay.maps_formed},
   observation = @{thm literal_replay.observation_at_subject},
   comparison = @{thm literal_replay.comparison_at_subject}}\<close>

definition literal_replay_packet where
  "literal_replay_packet ws selections=(let seed=literal_replay_seed;
    table=context_assessment_table [0,1,2,3,4,5,6] ws (literal_replay_context_from seed) literal_replay_cell;
    compared=context_assessment_investigation [0,1,2,3,4,5,6] [0,1] ws table literal_replay_family_inspect
    in (seed,table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1]
      (fst compared) (fst (snd compared))) selections))"

theorem literal_replay_packet_comparison:
  "fst (snd (snd (literal_replay_packet ws selections)))=assessed_subject_investigation
    [0,1,2,3,4,5,6] [0,1] ws (\<lambda>m w. literal_replay_cell m
      (literal_replay_context_from literal_replay_seed w)) literal_replay_family_inspect"
  by (simp only: literal_replay_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

definition literal_replay_indices :: "nat list" where
  "literal_replay_indices=[0,1,2,3,4,5,6]"

export_code literal_replay_packet checking SML

end
