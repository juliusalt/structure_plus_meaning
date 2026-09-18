theory Development_Seed
  imports Native_Control_Seed_Subject Development_Refinement_Contracts
begin

section \<open>The problems the seeded state carries\<close>

text \<open>
  The seeded state is the subject defined in the checked context; this theory adds the
  problems it carries and reads them from that one state rather than defining it again.

  Each root constant is one refinement problem whose subject is that constant and whose
  contract is the code equation the state states for it. The scope of a constant and the
  demand a refinement makes of that scope are both read from the state's own entities, so no
  author supplies the term an answer must establish, and a constant the state states no
  single demanded statement for yields no problem and is retained instead.

  Every seeded problem records the residual origin of its subject: identifying these
  constants from the measured candidates is a choice generated outside the native process,
  and the problems rest on it. No seeded problem carries owner authority, because the owner
  has authorized none; the report shows that absence.
\<close>

definition development_seed_root_constants :: "nat list" where
  "development_seed_root_constants=remdups (List.map_filter isabelle_head_constant development_seed_roots)"

definition development_seed_problem :: "nat \<Rightarrow> development_problem option" where
  "development_seed_problem c=development_refinement_problem development_seed_context
    Development_Residual Development_Generated c"

definition development_seed_problems :: "development_problem list" where
  "development_seed_problems=development_refinement_problems development_seed_context
    Development_Residual Development_Generated development_seed_root_constants"

definition development_seed_unstated :: "nat fset" where
  "development_seed_unstated=development_refinement_unstated development_seed_context
    development_seed_root_constants"

definition development_seed_dependencies :: development_dependencies where
  "development_seed_dependencies=development_refinement_dependencies development_seed_context
    Development_Residual Development_Generated development_seed_root_constants"

text \<open>
  A problem depends on the problems of the other root constants its own demanded statement
  mentions. That relation is read from the actual statements, so it replaces the grouping of
  roots into measured candidates as the state's dependency structure. Readiness is then the
  existing computation on those actual dependencies.

  What that reading finds is reported, not assumed: on this state the demanded statements
  mention no other root, so every premise set is empty and the ten problems are independent.
  The grouping asserted dependencies the state's own statements do not supply. The remaining
  variation of readiness is therefore the answered set, and the control answers every problem.
\<close>

definition development_seed_unanswered :: "development_problem fset" where
  "development_seed_unanswered={||}"

definition development_seed_answered :: "development_problem fset" where
  "development_seed_answered=fset_of_list development_seed_problems"

section \<open>A grouping of several constants states no single refinement\<close>

text \<open>
  The three measured candidates group the roots. A problem's contract is one term its answer
  must establish, and the state's entity language states each code equation separately: the
  equations of these roots are Pure equalities, so no entity and no term of the state states
  the refinement of several constants at once. A grouping of more than one constant therefore
  has no contract, and the state retains it as an obstruction rather than joining the
  statements of its constants or choosing one of them by position.
\<close>

definition development_seed_candidate_roots :: "isabelle_term list list" where
  "development_seed_candidate_roots=[development_seed_replay_roots,development_seed_walk_roots,
    development_seed_formation_roots]"

definition development_seed_ungrouped :: "isabelle_term list list" where
  "development_seed_ungrouped=filter
    (\<lambda>roots. list_singleton_option (List.map_filter isabelle_head_constant roots)=None)
    development_seed_candidate_roots"

theorem development_seed_ungrouped_exact:
  "roots\<in>set development_seed_ungrouped \<longleftrightarrow> roots\<in>set development_seed_candidate_roots \<and>
    list_singleton_option (List.map_filter isabelle_head_constant roots)=None"
  by (simp only: development_seed_ungrouped_def set_filter mem_Collect_eq)

corollary development_seed_grouped_constant:
  assumes grouping: "roots\<in>set development_seed_candidate_roots"
    and stateable: "roots\<notin>set development_seed_ungrouped"
  obtains c where "set (List.map_filter isabelle_head_constant roots)={c}"
proof -
  have "list_singleton_option (List.map_filter isabelle_head_constant roots)\<noteq>None"
    using grouping stateable by (simp only: development_seed_ungrouped_exact) simp
  then obtain c where found: "list_singleton_option
      (List.map_filter isabelle_head_constant roots)=Some c" by auto
  have "set (List.map_filter isabelle_head_constant roots)={c}"
    using found by (simp only: list_singleton_option_some)
  then show thesis by (rule that)
qed

section \<open>The report presents the problems, the retained absences and the assessment\<close>

type_synonym development_seed_problem_report = "development_problem list\<times>nat fset\<times>
  isabelle_term list list\<times>development_problem_assessment"

definition development_seed_problem_report_value ::
    "development_problem fset \<Rightarrow> development_seed_problem_report" where
  "development_seed_problem_report_value answered=(development_seed_problems,
    development_seed_unstated,development_seed_ungrouped,
    development_problem_assessment development_seed_context development_seed_dependencies answered
      development_seed_problems)"

definition development_seed_problem_report_data ::
    "development_seed_problem_report \<Rightarrow> finite_factor_term" where
  "development_seed_problem_report_data=finite_pair_presentation development_problems_data
    (finite_pair_presentation isabelle_positions_data
      (finite_pair_presentation (finite_sequence_presentation
        (finite_sequence_presentation isabelle_term_data)) development_problem_assessment_data))"

lemma development_seed_problem_report_data_injective [intro]:
  "inj development_seed_problem_report_data"
  unfolding development_seed_problem_report_data_def
  by (intro finite_pair_presentation_injective development_problems_data_injective
    isabelle_collections_injective(2) finite_sequence_presentation_injective
    isabelle_term_data_injective development_problem_assessment_data_injective)

definition development_seed_problem_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_problem_value answered=
    development_seed_problem_report_data (development_seed_problem_report_value answered)"

section \<open>Controls remove every root declaration or add unreached and malformed entities\<close>

text \<open>
  Removing the declarations of the state's own root constants exposes them as undeclared and
  refuses the state; the control names no position of the entity list, so the defect it
  exposes does not depend on one. Adding a declaration of a constant no entity mentions and
  an equation without a head exposes unknown positions, unreached and malformed entities,
  while acceptance still follows exactly the supplied entities.
\<close>

definition development_seed_missing_declaration :: isabelle_rooted_context where
  "development_seed_missing_declaration=(development_seed_roots,(fst development_seed_context,
    filter (\<lambda>e. list_all (\<lambda>c. isabelle_declared_constant e\<noteq>Some c) development_seed_root_constants)
      (snd development_seed_context)))"

definition development_seed_extra_entities :: isabelle_rooted_context where
  "development_seed_extra_entities=(development_seed_roots,(fst development_seed_context,
    snd development_seed_context@[development_seed_absent_entity development_seed_context,
      Isabelle_Code_Equation (Isabelle_Bound 0)]))"

section \<open>Controls move every position, and separately each name the reader recognizes\<close>

text \<open>
  Reversing the table moves every name of the state to another position. The assessment
  of the reversed state must be the image of the original assessment under the same
  correspondence: nothing the state computes depends on a position or on table order.

  Replacing a name the equation reader recognizes is not a renaming. No position moves, yet
  every entity stated as an equality under that name can no longer be read: it loses its
  subject and, declaring nothing either, is malformed. The controls are derived from the
  reader itself, one for each equality name it recognizes, so the report shows exactly which
  of these fixed base names the state's readings depend on and which they do not; no name is
  chosen for the state.
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

definition development_seed_name_moved :: "String.literal \<Rightarrow> isabelle_rooted_context" where
  "development_seed_name_moved n=(development_seed_roots,
    (map (\<lambda>s. if s=n then s+STR ''.moved'' else s) (fst development_seed_context),
     snd development_seed_context))"

definition development_seed_moved_equalities :: "isabelle_rooted_context list" where
  "development_seed_moved_equalities=map development_seed_name_moved isabelle_equality_names"

definition development_seed_reports_data :: "development_seed_report list \<Rightarrow> finite_factor_term" where
  "development_seed_reports_data=finite_sequence_presentation development_seed_report_data"

lemma development_seed_reports_data_injective [intro]: "inj development_seed_reports_data"
  unfolding development_seed_reports_data_def
  by (intro finite_sequence_presentation_injective development_seed_report_data_injective)

definition development_seed_reports_value :: "isabelle_rooted_context list \<Rightarrow> finite_factor_term" where
  "development_seed_reports_value Ss=development_seed_reports_data (map development_seed_report Ss)"

text \<open>
  The complete seed is expected to mention only declared constants, to hold no malformed
  entity, to reach every entity from its roots and to accept exactly its own entities;
  its frontier states the development constants it does not expand. The problem report adds
  the refinement problems its roots demand, the roots whose refinement it cannot state, the
  groupings it cannot state as one problem, and the readiness computed from the dependencies
  its own statements supply. Whether these roots are adequate to the measured candidates,
  and every extension of the frontier, remain open.
\<close>

end
