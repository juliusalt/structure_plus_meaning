theory Native_Control_Judgment_Review
  imports Native_Control_Filtered_Judgment Native_Control_Syntax_Statements
begin

section \<open>Independently varied context, roots and actual proposition\<close>

definition syntax_changed_name_context :: isabelle_rooted_context where
  "syntax_changed_name_context=(syntax_statement_roots,
    (STR ''unissued-name''#fst syntax_statement_context,snd syntax_statement_context))"

definition syntax_changed_root_context :: isabelle_rooted_context where
  "syntax_changed_root_context=([],syntax_statement_context)"

definition syntax_judgment_cases :: "syntax_judgment_subject list" where
  "syntax_judgment_cases=concat (map (\<lambda>C. map (\<lambda>m. (C,syntax_proposition m)) union_candidates)
    [syntax_checked_rooted_context,syntax_changed_name_context,syntax_changed_root_context,
      (development_seed_roots,development_seed_context)])"

lemma syntax_truth_has_case:
  "syntax_judgment_truth s \<Longrightarrow> s\<in>set syntax_judgment_cases"
proof -
  assume truth: "syntax_judgment_truth s"
  obtain m where subject: "s=(syntax_checked_rooted_context,syntax_proposition m)"
    using truth by (auto simp: syntax_judgment_truth_def prod_eq_iff)
  have "m\<in>set union_candidates" by (cases m) (simp_all add: union_candidates_def)
  then show ?thesis by (simp add: syntax_judgment_cases_def subject)
qed

datatype judgment_bridge = Context_Only | Proposition_Only | Context_And_Proposition

fun judgment_bridge_result :: "judgment_bridge \<Rightarrow> syntax_judgment_subject \<Rightarrow> bool" where
  "judgment_bridge_result Context_Only s=(fst s=syntax_checked_rooted_context)"
| "judgment_bridge_result Proposition_Only s=(snd s\<in>set syntax_checked_propositions)"
| "judgment_bridge_result Context_And_Proposition s=syntax_judgment_check s"

definition judgment_bridge_condition where
  "judgment_bridge_condition b cases \<longleftrightarrow>
    (\<forall>s\<in>set cases. judgment_bridge_result b s=syntax_judgment_truth s)"

definition judgment_bridge_observation where
  "judgment_bridge_observation b cases=list_all
    (\<lambda>s. judgment_bridge_result b s=syntax_judgment_truth s) cases"

lemma judgment_bridge_observation_exact:
  "judgment_bridge_observation b cases=judgment_bridge_condition b cases"
  by (simp only: judgment_bridge_observation_def judgment_bridge_condition_def list_all_iff)

lemma complete_judgment_bridge:
  "judgment_bridge_condition Context_And_Proposition cases"
  by (simp add: judgment_bridge_condition_def syntax_judgment_check_exact)

definition judgment_bridge_candidates where
  "judgment_bridge_candidates=[Context_Only,Proposition_Only,Context_And_Proposition]"

definition judgment_bridge_question where
  "judgment_bridge_question ignored=keyed_development_question
    (first_occurrence_key judgment_bridge_candidates) judgment_bridge_candidates
    (\<lambda>b. judgment_bridge_observation b syntax_judgment_cases)"

theorem judgment_bridge_admission:
  assumes question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates b)\<in>set accepted"
    and member: "b\<in>set judgment_bridge_candidates"
  shows "judgment_bridge_condition b syntax_judgment_cases"
proof -
  have "judgment_bridge_observation b syntax_judgment_cases"
    by (rule keyed_faceted_admission_at[OF first_occurrence_key_inj_on
      question[unfolded judgment_bridge_question_def keyed_development_question_def]
      admission selected member]) simp
  then show ?thesis by (simp only: judgment_bridge_observation_exact)
qed

section \<open>The receiving program and its local meaning are fixed by those subjects\<close>

definition judgment_bridge_program where
  "judgment_bridge_program b=filtered_judgment_program syntax_judgment_data
    syntax_judgment_cases (judgment_bridge_result b)"

definition judgment_bridge_call :: "syntax_judgment_subject \<Rightarrow>
    local_address option definition_site\<times>finite_factor_term" where
  "judgment_bridge_call s=((Some [],[]),syntax_judgment_data s)"

theorem judgment_bridge_program_meaning:
  assumes condition: "judgment_bridge_condition b syntax_judgment_cases"
  shows "decode_finite_call_term (judgment_bridge_call s)\<in>
    positive_meaning (decode_finite_system (judgment_bridge_program b))
    \<longleftrightarrow> syntax_judgment_truth s"
proof -
  have base: "((Some [],[]),decode_finite_term (syntax_judgment_data s))\<in>
      positive_meaning (decode_finite_system (judgment_bridge_program b))
    \<longleftrightarrow> s\<in>set syntax_judgment_cases \<and> judgment_bridge_result b s"
    unfolding judgment_bridge_program_def
    by (rule filtered_judgment_meaning[OF syntax_judgment_data_injective]) simp
  show ?thesis
    using base condition syntax_truth_has_case[of s]
    by (auto simp: judgment_bridge_call_def judgment_bridge_condition_def)
qed

theorem admitted_bridge_native_meaning:
  assumes question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates b)\<in>set accepted"
    and member: "b\<in>set judgment_bridge_candidates"
  shows "decode_finite_call_term (judgment_bridge_call (C,syntax_proposition m))\<in>
    positive_meaning (decode_finite_system (judgment_bridge_program b))
    \<longleftrightarrow> C=syntax_checked_rooted_context \<and> syntax_join_refinement m"
  using judgment_bridge_admission[OF question admission selected member]
    judgment_bridge_program_meaning[of b "(C,syntax_proposition m)"]
  by (simp only: syntax_judgment_at_proposition; blast)

theorem admitted_bridge_known_calls:
  assumes question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates b)\<in>set accepted"
    and member: "b\<in>set judgment_bridge_candidates"
    and established: "X\<subseteq>{s. syntax_judgment_truth s}"
  shows "(decode_finite_call_term o judgment_bridge_call) ` X\<subseteq>
    positive_meaning (decode_finite_system (judgment_bridge_program b))"
  using judgment_bridge_program_meaning[OF judgment_bridge_admission[OF question admission selected member]]
    established by auto

definition judgment_bridge_demands where
  "judgment_bridge_demands=fset_of_list (map judgment_bridge_call syntax_judgment_cases)"

definition judgment_bridge_evaluation where
  "judgment_bridge_evaluation b=finite_program_evaluation (judgment_bridge_program b) judgment_bridge_demands"

definition judgment_bridge_evaluation_summary where
  "judgment_bridge_evaluation_summary result=map_option (\<lambda>A.
    map (\<lambda>s. judgment_bridge_call s |\<in>| A) syntax_judgment_cases) result"

definition judgment_bridge_receive where
  "judgment_bridge_receive report=(case judgment_bridge_question () of None \<Rightarrow> None
    | Some Q \<Rightarrow> (case native_development_admission Q report of None \<Rightarrow> None
      | Some accepted \<Rightarrow> Some (map (\<lambda>i. (i,
          judgment_bridge_evaluation (judgment_bridge_candidates!i)))
        (filter (\<lambda>i. finite_path (first_occurrence_key judgment_bridge_candidates
            (judgment_bridge_candidates!i))\<in>set accepted)
          [0..<length judgment_bridge_candidates]))))"

theorem judgment_bridge_receive_fields:
  assumes result: "judgment_bridge_receive report=Some rows"
    and row: "(i,Some A)\<in>set rows"
  obtains Q accepted where "judgment_bridge_question ()=Some Q"
    "native_development_admission Q report=Some accepted"
    "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates (judgment_bridge_candidates!i))\<in>set accepted"
    "judgment_bridge_evaluation (judgment_bridge_candidates!i)=Some A"
  using result row by (auto simp: judgment_bridge_receive_def split: option.splits)

theorem judgment_bridge_receive_truth:
  assumes result: "judgment_bridge_receive report=Some rows"
    and row: "(i,Some A)\<in>set rows"
    and scope: "s\<in>set syntax_judgment_cases"
  shows "judgment_bridge_call s |\<in>| A \<longleftrightarrow> syntax_judgment_truth s"
proof (rule judgment_bridge_receive_fields[OF result row])
  fix Q accepted
  assume question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and inside: "i<length judgment_bridge_candidates"
    and selected: "finite_path (first_occurrence_key judgment_bridge_candidates
      (judgment_bridge_candidates!i))\<in>set accepted"
    and evaluated: "judgment_bridge_evaluation (judgment_bridge_candidates!i)=Some A"
  have meaning: "decode_finite_call_term (judgment_bridge_call s)\<in>
      positive_meaning (decode_finite_system (judgment_bridge_program (judgment_bridge_candidates!i)))
      \<longleftrightarrow> syntax_judgment_truth s"
    by (rule judgment_bridge_program_meaning[OF judgment_bridge_admission[OF question admission selected
      nth_mem[OF inside]]])
  have demand: "judgment_bridge_call s |\<in>| judgment_bridge_demands"
    using scope by (auto simp: judgment_bridge_demands_def fset_of_list_elem)
  show ?thesis
    using finite_program_evaluation_exact(2)[OF evaluated[unfolded judgment_bridge_evaluation_def]] demand meaning
    by auto
qed

theorem judgment_bridge_receive_known:
  assumes result: "judgment_bridge_receive report=Some rows"
    and row: "(i,Some A)\<in>set rows"
  shows "decode_finite_call_term ` fset A\<subseteq>
    positive_meaning (decode_finite_system (judgment_bridge_program (judgment_bridge_candidates!i)))"
proof (rule judgment_bridge_receive_fields[OF result row])
  fix Q accepted
  assume "judgment_bridge_question ()=Some Q"
    "native_development_admission Q report=Some accepted"
    "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates (judgment_bridge_candidates!i))\<in>set accepted"
    and evaluated: "judgment_bridge_evaluation (judgment_bridge_candidates!i)=Some A"
  show ?thesis using finite_program_evaluation_exact(2)[OF evaluated[unfolded judgment_bridge_evaluation_def]] by auto
qed

definition judgment_bridge_receive_summary where
  "judgment_bridge_receive_summary result=map_option (map
    (\<lambda>(i,A). (i,judgment_bridge_evaluation_summary A))) result"

definition judgment_bridge_value where
  "judgment_bridge_value run=finite_pair_presentation
    (finite_sequence_presentation syntax_judgment_data)
    (finite_steered_development_value finite_development_question_value)
    (syntax_judgment_cases,run)"

lemma judgment_bridge_value_injective: "inj judgment_bridge_value"
proof -
  have complete: "inj (finite_pair_presentation
      (finite_sequence_presentation syntax_judgment_data)
      (finite_steered_development_value finite_development_question_value))"
    by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
      syntax_judgment_data_injective finite_development_values_injective finite_development_question_value_injective)
  show ?thesis unfolding judgment_bridge_value_def by (rule injI; drule injD[OF complete]; simp)
qed

definition judgment_bridge_receiving_value where
  "judgment_bridge_receiving_value=finite_pair_presentation judgment_bridge_value
    (finite_option_presentation (finite_sequence_presentation
      (finite_pair_presentation isabelle_position_data
        (finite_option_presentation (finite_collection_presentation finite_call_value)))))"

lemma judgment_bridge_receiving_value_injective: "inj judgment_bridge_receiving_value"
  unfolding judgment_bridge_receiving_value_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective finite_collection_presentation_injective
    judgment_bridge_value_injective isabelle_position_data_injective finite_call_value_injective)

text \<open>The receiving native program is an actual computed ground program.
  The local theorem connects every recognized complete subject to its original
  whole-constructor refinement, including context and proposition refusals.
  Admission of a bridge is distinct from policy adoption, execution selection by
  cost, arbitrary HOL interpretation and the genesis handoff. The complete
  source package and proof graph premises of further receivers remain required.\<close>

export_code judgment_bridge_question judgment_bridge_value judgment_bridge_evaluation
  judgment_bridge_receive judgment_bridge_receive_summary judgment_bridge_receiving_value
  judgment_bridge_evaluation_summary judgment_bridge_candidates judgment_bridge_observation
  syntax_judgment_cases syntax_judgment_truth syntax_proposition syntax_checked_rooted_context
  context_execution_summary native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Judgment file_prefix "native_control_judgment"

end
