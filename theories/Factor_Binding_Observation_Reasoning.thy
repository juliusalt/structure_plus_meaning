theory Factor_Binding_Observation_Reasoning
  imports Factor_Binding_Observation_Execution Factor_Learned_Execution_Soundness Factor_Clause_Rule_Application
begin

section \<open>The native report clause becomes another applicable learned rule\<close>

lemma binding_observation_rule_sound:
  assumes rule: "schema_rule_instance binding_observation_pair_schema (positive_meaning binding_observation_program) t"
  shows "(347,t)\<in>positive_meaning binding_observation_program"
  by (rule positive_variable_clause_rule[OF binding_observation_program_formed _ _ rule, where c=0 and a=0])
    (auto simp: binding_observation_clauses_def)

definition finite_binding_observation_schema :: "(nat,nat,nat) finite_factor_schema" where
  "finite_binding_observation_schema=\<lparr>
    finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))),
    finite_schema_premises=fset_of_list
      [(0,345,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
       (1,346,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)))],
    finite_schema_materials={||}\<rparr>"

lemma finite_binding_observation_schema_exact:
  "decode_finite_schema finite_binding_observation_schema=binding_observation_pair_schema"
  by (simp add: finite_binding_observation_schema_def binding_observation_pair_schema_def paired_context_results_schema_def
    decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def; auto)

definition binding_observation_reasoning_library ::
  "(nat\<times>(nat,nat,nat) finite_factor_schema\<times>(nat\<times>nat\<times>nat finite_term_pattern) list) list" where
  "binding_observation_reasoning_library=[(347,finite_binding_observation_schema,
    [(0,345,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
     (1,346,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)))])]"

lemma binding_observation_library_member_sound:
  assumes member: "(d,S,ps)\<in>set binding_observation_reasoning_library"
    and rule: "schema_rule_instance (decode_finite_schema S) (positive_meaning binding_observation_program) t"
  shows "(d,t)\<in>positive_meaning binding_observation_program"
  using member rule by (auto simp: binding_observation_reasoning_library_def
    finite_binding_observation_schema_exact intro: binding_observation_rule_sound)

definition binding_observation_calls where
  "binding_observation_calls sources=concat (map (\<lambda>(u,bs). finite_binding_observation_frontier u bs) sources)"

lemma binding_observation_calls_sound:
  "decode_finite_call_term ` set (binding_observation_calls sources)\<subseteq>positive_meaning binding_observation_program"
  using finite_binding_observation_frontier_sound
  by (auto simp: binding_observation_calls_def decode_finite_call_term_def split: prod.splits)

theorem binding_observation_known_closure_sound:
  "decode_finite_call_term ` finite_inference_result
      (finite_generated_schema_rules (if enabled then binding_observation_reasoning_library else [])
        (binding_observation_calls sources)) (fset_of_list (binding_observation_calls sources))
    \<subseteq>positive_meaning binding_observation_program"
proof (rule finite_learned_closure_sound)
  fix d S ps t
  assume member: "(d,S,ps)\<in>set (if enabled then binding_observation_reasoning_library else [])"
    and rule: "schema_rule_instance (decode_finite_schema S) (positive_meaning binding_observation_program) t"
  have actual: "(d,S,ps)\<in>set binding_observation_reasoning_library" using member by (cases enabled) auto
  show "(d,t)\<in>positive_meaning binding_observation_program"
    by (rule binding_observation_library_member_sound[OF actual rule])
next
  show "decode_finite_call_term ` fset (fset_of_list (binding_observation_calls sources))
      \<subseteq>positive_meaning binding_observation_program"
    using binding_observation_calls_sound[of sources] by (simp only: fset_of_list.rep_eq)
qed

definition binding_observation_sources_formed where
  "binding_observation_sources_formed sources \<longleftrightarrow>
    (\<forall>(u,bs)\<in>set sources. finite_term_formed u \<and> list_all finite_term_formed bs)"

definition binding_observation_investigation where
  "binding_observation_investigation enabled sources goals=
    (let C=binding_observation_calls sources;
      result=natural_learned_investigation (if enabled then binding_observation_reasoning_library else [])
        C (fset_of_list C) goals
     in (fst result \<and> binding_observation_sources_formed sources,snd result))"

text \<open>
  The source rows determine the two traversal results. Only actual successful
  native computations enter the known frontier. The report schema then joins
  them at the same context and complete input, using the unchanged generation
  and inference engine. Removing the learned rule leaves those same established
  premises available while removing the generated report construction.

  The input gate checks every original source term, including unused sources.
  A formed row whose owner or paired-value shape is wrong produces no traversal
  result and supplies no known premise. Closure soundness follows from the
  actual computed premises and the shared clause-application theorem.
\<close>

end
