theory RRA_Generation_Record_Investigation
  imports RRA_Generation_Record_Permutations Finite_Assessment_Reports
begin

definition generation_record_original_report where
  "generation_record_original_report X=(case X of (E,l,p,c,rows) \<Rightarrow>
    (finite_environment_formed E,finite_target_formed l,finite_target_formed p,
      finite_target_formed c,distinct (map snd rows),
      map (\<lambda>(d,G). ((d,G),finite_check_generation G E (fst d) (snd d))) rows))"

definition generation_record_context where
  "generation_record_context w=(let X=generation_record_case w in
    (X,generation_record_reference X,generation_record_original_report X,
      map (\<lambda>k. (k,generation_record_variant k X)) [0,1,3,4,5,6]))"

definition generation_record_prepared where
  "generation_record_prepared (m::nat) X bases=generation_record_mutation m X
    (case map_of bases (if m=1 \<or> (3\<le>m \<and> m\<le>6) then m else 0) of
      None \<Rightarrow> None | Some result \<Rightarrow> result)"

lemma generation_record_prepared_exact:
  "generation_record_prepared m X (map (\<lambda>k. (k,generation_record_variant k X)) [0,1,3,4,5,6])=
    generation_record_method m X"
proof -
  let ?k="if m=1 \<or> (3\<le>m \<and> m\<le>6) then m else 0"
  have key: "?k\<in>set [0,1,3,4,5,6]" by (auto; arith)
  have encoded: "generation_record_variant ?k X=generation_record_variant m X"
    by (auto simp: generation_record_variant_def split: prod.splits; arith)
  show ?thesis by (simp only: generation_record_prepared_def mapped_function_lookup key
    if_True option.case encoded generation_record_method_def)
qed

definition generation_record_cell where
  "generation_record_cell m context=(case context of (X,ready,original,bases) \<Rightarrow>
    let result=generation_record_prepared m X bases
    in (X,result,(ready,result\<noteq>None,generation_record_result_assessment X result)))"

lemma generation_record_cell_exact:
  "generation_record_cell m (generation_record_context w)=(generation_record_case w,
    generation_record_method m (generation_record_case w),
    generation_record_assessment (generation_record_case w) (generation_record_method m (generation_record_case w)))"
  by (simp only: generation_record_cell_def generation_record_context_def Let_def case_prod_conv
    generation_record_prepared_exact generation_record_assessment_def)

definition generation_record_cell_inspect where
  "generation_record_cell_inspect cell f=(case cell of (X,result,assessment) \<Rightarrow>
    generation_record_inspect assessment f)"

definition generation_record_quality where
  "generation_record_quality m w f=generation_record_cell_inspect
    (generation_record_cell m (generation_record_context w)) f"

theorem generation_record_quality_exact:
  "generation_record_quality m w f=generation_record_condition f (generation_record_method m) (generation_record_case w)"
  by (simp only: generation_record_quality_def generation_record_cell_exact
    generation_record_cell_inspect_def case_prod_conv generation_record_assessment_exact)

interpretation generation_record: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12]"
    "[0,1,2,3,4,5,6,7,8]" ws generation_record_method generation_record_condition
    generation_record_case generation_record_quality for ws
  by (unfold_locales) (rule generation_record_quality_exact)

definition generation_record_investigation where
  "generation_record_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12]
    [0,1,2,3,4,5,6,7,8] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1,2,3,4,5,6,7,8] ws generation_record_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1,2,3,4,5,6,7,8] ws generation_record_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm generation_record_investigation_def},
   equation = @{thm generation_record.observations_derived},
   formation = @{thm generation_record.maps_formed},
   observation = @{thm generation_record.observation_at_subject},
   comparison = @{thm generation_record.comparison_at_subject}}\<close>

definition generation_record_packet where
  "generation_record_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12] ws generation_record_context generation_record_cell;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1,2,3,4,5,6,7,8] ws
      table generation_record_cell_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1,2,3,4,5,6,7,8]
      (fst compared) (fst (snd compared))) selections))"

theorem generation_record_packet_comparison:
  "fst (snd (generation_record_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1,2,3,4,5,6,7,8] ws
    (\<lambda>m w. generation_record_cell m (generation_record_context w)) generation_record_cell_inspect"
  by (simp only: generation_record_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

definition generation_record_indices :: "nat list" where
  "generation_record_indices=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]"

end
