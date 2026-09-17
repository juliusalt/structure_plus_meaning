theory Development_Seed
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

definition development_seed_report_value :: "isabelle_rooted_context \<Rightarrow> finite_factor_term" where
  "development_seed_report_value S=development_seed_report_data (development_seed_report S)"

section \<open>The problems the seeded state carries\<close>

text \<open>
  Each measured refinement candidate is one problem whose subject is the constants its
  answer would change, decomposed into one leaf problem per constant. The premise slot of a
  leaf is the constant it concerns, so distinct constants occupy distinct slots and no list
  order enters. Grouping the roots into candidates and decomposing a candidate into leaves
  are choices generated outside the native process: the candidates are retained as residuals
  and every seeded problem carries generated authority. No seeded problem carries owner
  authority, because the owner has authorized none; the report shows that absence.
\<close>

definition development_seed_candidate_roots :: "isabelle_term list list" where
  "development_seed_candidate_roots=[development_seed_replay_roots,development_seed_walk_roots,
    development_seed_formation_roots]"

definition development_seed_candidate :: "isabelle_term list \<Rightarrow> development_problem" where
  "development_seed_candidate roots=Development_Problem
    (fset_of_list (List.map_filter isabelle_head_constant roots)) Development_Refinement
    Development_Residual Development_Generated"

definition development_seed_leaf :: "nat \<Rightarrow> development_problem" where
  "development_seed_leaf c=Development_Problem {|c|} Development_Refinement
    Development_Demand Development_Generated"

definition development_seed_leaves :: "isabelle_term list \<Rightarrow> development_problem list" where
  "development_seed_leaves roots=map development_seed_leaf (List.map_filter isabelle_head_constant roots)"

definition development_seed_problems :: "development_problem list" where
  "development_seed_problems=map development_seed_candidate development_seed_candidate_roots@
    concat (map development_seed_leaves development_seed_candidate_roots)"

definition development_seed_dependencies :: development_dependencies where
  "development_seed_dependencies=fset_of_list (map (\<lambda>roots. (development_seed_candidate roots,
     fset_of_list (map (\<lambda>c. (c,development_seed_leaf c)) (List.map_filter isabelle_head_constant roots))))
     development_seed_candidate_roots)"

type_synonym development_seed_problem_report = "development_problem list\<times>development_problem_assessment"

definition development_seed_problem_report_value ::
    "development_problem fset \<Rightarrow> development_seed_problem_report" where
  "development_seed_problem_report_value answered=(development_seed_problems,
    development_problem_assessment development_seed_context development_seed_dependencies answered
      development_seed_problems)"

definition development_seed_problem_report_data ::
    "development_seed_problem_report \<Rightarrow> finite_factor_term" where
  "development_seed_problem_report_data=finite_pair_presentation development_problems_data
    development_problem_assessment_data"

definition development_seed_problem_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_problem_value answered=
    development_seed_problem_report_data (development_seed_problem_report_value answered)"

text \<open>
  With nothing answered only the leaves are ready: a candidate waits for every constant of
  its subject. Answering the leaves of one candidate makes exactly that candidate ready and
  removes its answered leaves, which is the readiness computation on its actual dependencies.
\<close>

definition development_seed_unanswered :: "development_problem fset" where
  "development_seed_unanswered={||}"

definition development_seed_replay_answered :: "development_problem fset" where
  "development_seed_replay_answered=fset_of_list (development_seed_leaves development_seed_replay_roots)"

section \<open>Controls remove a declaration or add unreached and malformed entities\<close>

definition development_seed_missing_declaration :: isabelle_rooted_context where
  "development_seed_missing_declaration=(development_seed_roots,(fst development_seed_context,
    filter (\<lambda>e. isabelle_declared_constant e\<noteq>isabelle_head_constant (hd development_seed_roots))
      (snd development_seed_context)))"

definition development_seed_extra_entities :: isabelle_rooted_context where
  "development_seed_extra_entities=(development_seed_roots,(fst development_seed_context,
    snd development_seed_context@[development_seed_absent_entity development_seed_context,
      Isabelle_Code_Equation (Isabelle_Bound 0)]))"

section \<open>Controls move every position, and separately change a name the reading uses\<close>

text \<open>
  Reversing the table moves every name of the state to another position. The assessment
  of the reversed state must be the image of the original assessment under the same
  correspondence: nothing the state computes depends on a position or on table order.

  Replacing the name of HOL equality in the table is not a renaming. No position moves,
  yet the state can no longer read the left side of a code equation, so those entities
  lose their subjects. The control exposes exactly which fixed base names the reading
  depends on.
\<close>

definition development_seed_renamed :: isabelle_rooted_context where
  "development_seed_renamed=isabelle_rooted_rename
    (isabelle_reversal (length (fst development_seed_context)))
    (rev (fst development_seed_context)) development_seed_state"

theorem development_seed_renamed_assessment:
  "isabelle_context_assessment (fst development_seed_renamed) (snd development_seed_renamed)=
    isabelle_assessment_rename (isabelle_reversal (length (fst development_seed_context)))
      (isabelle_context_assessment development_seed_roots development_seed_context)"
proof -
  have corr: "isabelle_table_correspondence (isabelle_reversal (length (fst development_seed_context)))
      (fst (snd development_seed_state)) (rev (fst development_seed_context))"
    by (simp only: development_seed_state_def snd_conv isabelle_reversal_correspondence)
  show ?thesis
    unfolding development_seed_renamed_def
    using isabelle_renamed_rooted_assessment[OF corr] by (simp only: development_seed_state_def fst_conv snd_conv)
qed

definition development_seed_moved_equality :: isabelle_rooted_context where
  "development_seed_moved_equality=(development_seed_roots,
    (map (\<lambda>s. if s=STR ''HOL.eq'' then STR ''HOL.eq.moved'' else s) (fst development_seed_context),
     snd development_seed_context))"

text \<open>
  The complete seed is expected to mention only declared constants, to hold no malformed
  entity, to reach every entity from its roots and to accept exactly its own entities;
  its frontier states the development constants it does not expand. Removing the first
  root's declaration exposes an undeclared constant and refuses it. Adding a declaration
  of a constant no entity mentions and an equation without a head exposes unreached and
  malformed entities, while acceptance still follows exactly the supplied entities. The
  reversed state reports the image of the original observations, and the moved equality
  name reports the readings the state loses with it.
\<close>

end
