theory Native_Control_Seed_Subject
  imports Isabelle_Entity_Export Development_Problems Isabelle_Acceptance
    Native_Execution_Refinements Factor_Shared_Replay_Construction
begin

section \<open>The seeded development state of the paused refinement candidates\<close>

text \<open>
  The roots are the constants whose code equations the three measured and paused
  refinement candidates would change: replay values compared without nested row keys,
  an artifact index built once per complete data walk, and formation carried through
  guarded reading entries. Only the roots are expanded; every development constant they
  mention stands on the frontier of this state and is extended when work demands it.
  Identifying these constants from the candidates is a residual choice generated outside
  the native process; it gains no authority from this definition.
\<close>

local_setup \<open>Isabelle_Entity_Export.define \<^binding>\<open>development_seed\<close>
  [("_replay_roots", [\<^term>\<open>digit_replay_inspect\<close>, \<^term>\<open>digit_replay_family_inspect\<close>]),
   ("_walk_roots", [\<^term>\<open>finite_complete_data_readings_prepared\<close>]),
   ("_formation_roots", [\<^term>\<open>finite_native_definition_readings\<close>, \<^term>\<open>finite_family_readings\<close>,
     \<^term>\<open>finite_call_readings\<close>, \<^term>\<open>finite_pattern_record_readings\<close>,
     \<^term>\<open>finite_pattern_vector_readings\<close>, \<^term>\<open>finite_native_schema_readings\<close>,
     \<^term>\<open>finite_scoped_pattern_readings\<close>])]\<close>

declare development_seed_context_def [code] development_seed_roots_def [code]
  development_seed_replay_roots_def [code] development_seed_walk_roots_def [code]
  development_seed_formation_roots_def [code]

definition development_seed_state :: isabelle_rooted_context where
  "development_seed_state=(development_seed_roots,development_seed_context)"

section \<open>The seed is assessed and accepted natively\<close>

text \<open>
  The demanded entities are those of the state itself together with one constant declared
  at a position the table does not hold. A demand is derived from the state it is made
  against, so every control demands its own entities rather than another state's.
\<close>

definition development_seed_absent_entity :: "isabelle_context \<Rightarrow> isabelle_entity" where
  "development_seed_absent_entity C=Isabelle_Development_Constant
    (Isabelle_Constant (length (fst C)) (Isabelle_Type_Application (length (fst C)) []))"

definition development_seed_demands :: "isabelle_context \<Rightarrow> isabelle_entity list" where
  "development_seed_demands C=snd C@[development_seed_absent_entity C]"

type_synonym development_seed_report =
  "isabelle_term fset\<times>isabelle_context\<times>isabelle_context_assessment\<times>isabelle_acceptance_assessment"

definition development_seed_report :: "isabelle_rooted_context \<Rightarrow> development_seed_report" where
  "development_seed_report S=(fset_of_list (fst S),snd S,
    isabelle_context_assessment (fst S) (snd S),
    isabelle_demand_acceptance (snd (snd S)) (development_seed_demands (snd S)))"

definition development_seed_report_data :: "development_seed_report \<Rightarrow> finite_factor_term" where
  "development_seed_report_data=finite_pair_presentation isabelle_terms_data
    (finite_pair_presentation isabelle_context_data
      (finite_pair_presentation isabelle_context_assessment_data isabelle_acceptance_assessment_data))"

lemma development_seed_report_data_injective [intro]: "inj development_seed_report_data"
  unfolding development_seed_report_data_def
  by (intro finite_pair_presentation_injective isabelle_collections_injective(3)
    isabelle_context_data_injective isabelle_context_assessment_data_injective
    isabelle_acceptance_assessment_data_injective)

definition development_seed_report_value :: "isabelle_rooted_context \<Rightarrow> finite_factor_term" where
  "development_seed_report_value S=development_seed_report_data (development_seed_report S)"


end
