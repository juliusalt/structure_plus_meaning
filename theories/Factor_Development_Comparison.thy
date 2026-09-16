theory Factor_Development_Comparison
  imports Factor_Development_Cases Factor_Finite_Requirement_Term_Observations
begin

definition development_condition_reference ::
    "native_development_condition \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow> finite_factor_term list option" where
  "development_condition_reference C input ys=map_option (\<lambda>(P,A).
    filter (\<lambda>y. Finite_Pair input y |\<in>| A) ys)
    (finite_native_requirement_term_observation (condition_source C) (condition_source_use C)
      (condition_source_root C) (condition_goals C) (fset_of_list (map (Finite_Pair input) ys)))"

definition development_reference ::
    "native_development_question \<Rightarrow> finite_factor_term list option" where
  "development_reference Q=(case finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q) of None \<Rightarrow> None
    | Some G \<Rightarrow> (let ys=development_generated_values Q G;
        results=map (\<lambda>C. development_condition_reference C (development_problem Q) ys) (development_conditions Q);
        input=development_review_values Q ys results in
      if development_conditions Q=[] \<or> condition_goals (development_scope_criticism Q)=[] \<or>
        list_ex (\<lambda>x. x=None) results then None
      else (case development_condition_reference (development_scope_criticism Q) input [input] of
        None \<Rightarrow> None | Some reviewed \<Rightarrow> if reviewed=[input]
          then Some (filter (\<lambda>y. list_all (\<lambda>r. y\<in>set (case_option [] id r)) results) ys) else None)))"

definition development_producer_assessment where
  "development_producer_assessment Q original reference actual=(let result=snd actual;
    values=case_option [] id result; expected=case_option [] id reference in
    (set values\<subseteq>set expected,set expected\<subseteq>set values,result=reference,
      result=native_development_admission Q (fst actual),fst actual=original))"

definition development_producer_inspect :: "bool\<times>bool\<times>bool\<times>bool\<times>bool \<Rightarrow> nat \<Rightarrow> bool" where
  "development_producer_inspect A f=(case A of (sound,complete,ordered,admitted,whole) \<Rightarrow>
    if f=0 then sound else if f=1 then complete else if f=2 then ordered else if f=3 then admitted
    else if f=4 then whole else False)"

definition development_producer_condition where
  "development_producer_condition f method Q=development_producer_inspect
    (development_producer_assessment Q (construct_native_development Q) (development_reference Q) (method Q)) f"

definition development_producer_quality where
  "development_producer_quality m w f=development_producer_condition f (development_producer m) (development_case_at w)"

interpretation development_producer: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]" "[0,1,2,3,4]" ws
    development_producer development_producer_condition development_case_at development_producer_quality for ws
  by (unfold_locales) (simp only: development_producer_quality_def)

definition development_producer_investigation where
  "development_producer_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws development_producer_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws development_producer_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm development_producer_investigation_def},
   equation = @{thm development_producer.observations_derived},
   formation = @{thm development_producer.maps_formed},
   observation = @{thm development_producer.observation_at_subject},
   comparison = @{thm development_producer.comparison_at_subject}}\<close>

definition development_producer_context where
  "development_producer_context w=(let Q=development_case_at w in (Q,construct_native_development Q,development_reference Q))"

definition development_producer_cell where
  "development_producer_cell m context=(case context of (Q,original,reference) \<Rightarrow>
    let actual=development_producer_from m Q original (native_development_admission Q original)
    in (actual,development_producer_assessment Q original reference actual))"

lemma development_producer_cell_exact:
  "development_producer_cell m (development_producer_context w)=
    (development_producer m (development_case_at w),
      development_producer_assessment (development_case_at w) (construct_native_development (development_case_at w))
        (development_reference (development_case_at w)) (development_producer m (development_case_at w)))"
  by (simp only: development_producer_cell_def development_producer_context_def development_producer_def
    Let_def case_prod_conv)

definition development_producer_packet where
  "development_producer_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws
      development_producer_context development_producer_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws table
      (\<lambda>(actual,assessment). development_producer_inspect assessment)
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4]
      (fst comparison) (fst (snd comparison))) selections))"

text \<open>
  The reference observes the original uncompiled native goals directly; it
  does not consume proposed criterion certificates or satisfaction flags.
  Complete evidence and declared decisions are separate conditions. The full
  report comparison retains every original operation and diagnostic, including
  a legitimate refusal. These finite subject equations authorize exactly this
  comparison; wider problem or candidate coverage remains explicit.
\<close>

end
