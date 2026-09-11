theory Factor_Finite_Inference_Premises
  imports Factor_Finite_Inference_Example Factor_Inference_Reader_Investigation
begin

section \<open>The complete initial calls concern the actual supplied sources\<close>

definition finite_literal_source_calls :: "octets \<Rightarrow> (nat\<times>factor_term) list" where
  "finite_literal_source_calls p = (let
    e=finite_environment_term (finite_literal_extension p);
    f=finite_environment_term (finite_literal_sources p);
    a=source_root_argument e (use_data_term None) (Payload_Term [0]);
    d=Pair_Term (use_data_term None) (Payload_Term [1]);
    c=Payload_Term [7];
    r=Pair_Term f (Pair_Term (use_data_term None) (Payload_Term [3]));
    q=Pair_Term f (Pair_Term (use_data_term None) (Payload_Term [8]));
    empty=Payload_Term [];
    ri=data_list_term (map Payload_Term [[3]]);
    inst=pattern_instantiation_argument f (use_data_term None) empty empty (Payload_Term [3])
      empty empty ri empty
    in [(94,term_quotation_argument e (use_data_term (Some [])) (Payload_Term [])
          (data_list_term [Pair_Term (use_data_term None) c,empty,empty])
          (data_list_term (map Payload_Term finite_literal_node_interior))
          (data_list_term (map Payload_Term [[6]]))),
        (294,Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term r q)),
        (126,Pair_Term q (ground_schema_report (Payload_Term p))),
        (125,reference_bindings_value empty empty empty),
        (61,inst),(61,inst),
        (345,context_relation_argument (use_data_term None) empty empty),
        (346,context_relation_argument (use_data_term None) empty empty)])"

theorem finite_literal_source_calls_sound:
  "set (finite_literal_source_calls [])\<subseteq>positive_meaning inference_specialization_system"
proof -
  let ?e="finite_environment_term (finite_literal_extension [])"
  let ?f="finite_environment_term (finite_literal_sources [])"
  let ?empty="Payload_Term []"
  let ?a="source_root_argument ?e (use_data_term None) (Payload_Term [0])"
  let ?d="Pair_Term (use_data_term None) (Payload_Term [1])"
  let ?c="Payload_Term [7]"
  let ?r="Pair_Term ?f (Pair_Term (use_data_term None) (Payload_Term [3]))"
  let ?q="Pair_Term ?f (Pair_Term (use_data_term None) (Payload_Term [8]))"
  let ?z="ground_schema_report (Payload_Term [])"
  let ?ri="data_list_term (map Payload_Term [[3]])"
  have node: "(94,term_quotation_argument ?e (use_data_term (Some [])) (Payload_Term [])
      (data_list_term [Pair_Term (use_data_term None) ?c,?empty,?empty])
      (data_list_term (map Payload_Term finite_literal_node_interior))
      (data_list_term (map Payload_Term [[6]])))\<in>positive_meaning proof_node_reading_system"
    using proof_node_reading_inference[OF finite_literal_presentations(2),
      where u="Some []" and r="[]" and c="(None,[7])" and bs="[]" and ds="[]"
        and Is=finite_literal_node_interior and Ks="[[6]]"] finite_literal_native_node
    by (simp add: finite_literal_node_interior_def site_data_term_def)
  obtain report where report_shape: "?z=Pair_Term ?empty report"
    by (auto simp: ground_schema_report_def)
  have binding: "(349,specialization_binding_argument ?a (use_data_term None) (Payload_Term [1]) ?c
      ?f (use_data_term None) (Payload_Term [3]) ?q ?empty report ?empty ?ri ?empty)
      \<in>positive_meaning specialization_binding_system"
    using specialization_binding_on_sources[OF finite_literal_presentations(2)
      finite_literal_presentations(1) finite_literal_presentations(1),
      where pu=None and pr="[0]" and du=None and dr="[1]" and c="[7]" and v=None
        and r="[3]" and w=None and t="[8]" and Is="[[3]]" and Ks="[]"
        and b="?empty" and report=report and bs="?empty"] finite_literal_binding
    by (simp add: report_shape)
  have report_call: "(342,specialization_report_value ?a ?d ?c ?r ?q ?z)
      \<in>positive_meaning specialization_report_system"
    using binding by (simp only: report_shape specialization_binding_at_arguments; blast)
  have reported:
    "(294,Pair_Term (Pair_Term ?a (Pair_Term ?d ?c)) (Pair_Term ?r ?q))
      \<in>positive_meaning clause_specialization_reading_system"
    "(126,Pair_Term ?q ?z)\<in>positive_meaning schema_reading_system"
    using report_call by (auto simp only: specialization_report_at_arguments
      specialization_report_reference_meaning)
  have rec: "pattern_record_at (example_literal_environment []) None {} [3] [] {[3]} {}"
    by (rule empty_binder_pattern_record[OF finite_literal_environments_formed(1)
      finite_literal_artifact_at finite_literal_binder])
  have record_calls:
    "(125,reference_bindings_value ?empty ?empty ?empty)\<in>positive_meaning reference_bindings_system"
    "(61,pattern_instantiation_argument ?f (use_data_term None) ?empty ?empty
      (Payload_Term [3]) ?empty ?empty ?ri ?empty)\<in>positive_meaning record_instantiation_system"
    using binding_record_source_calls[OF finite_literal_presentations(1), where v=None
      and r="[3]" and Bs="[]" and As="[]" and s=Pattern_Variable and Is="[[3]]" and Ks="[]"] rec
    by (auto simp: substitution_row_patterns_def)
  have lists:
    "(345,context_relation_argument (use_data_term None) ?empty ?empty)\<in>positive_meaning binding_observation_program"
    "(346,context_relation_argument (use_data_term None) ?empty ?empty)\<in>positive_meaning binding_observation_program"
    using binding_observation_first_list.lists[of "use_data_term None" "[]" "[]"]
      binding_observation_second_list.lists[of "use_data_term None" "[]" "[]"]
    by (simp_all add: octets_formed_def)
  show ?thesis using node reported record_calls lists
    by (auto simp: finite_literal_source_calls_def Let_def inference_specialization_readers
      inference_reader_source_meanings inference_reader_observation_meaning)
qed

section \<open>Finite execution receives those same data calls\<close>

lemma finite_literal_source_calls_data:
  assumes "(d,t)\<in>set (finite_literal_source_calls p)"
  shows "self_contained_term t"
  using assms by (auto simp: finite_literal_source_calls_def Let_def ground_schema_report_def
    data_list_term_self_contained)

definition finite_literal_inference_known :: "octets \<Rightarrow> (nat\<times>finite_factor_term) list" where
  "finite_literal_inference_known p =
    map (\<lambda>(d,t). (d,the (finite_self_contained_term t))) (finite_literal_source_calls p)"

lemma decode_finite_literal_inference_known:
  "map decode_finite_call_term (finite_literal_inference_known p)=finite_literal_source_calls p"
  unfolding finite_literal_inference_known_def map_map
proof (rule map_idI)
  fix q assume member: "q\<in>set (finite_literal_source_calls p)"
  obtain d t where shape: "q=(d,t)" by (cases q)
  have data: "self_contained_term t"
    using finite_literal_source_calls_data member by (simp only: shape; blast)
  show "(decode_finite_call_term \<circ> (\<lambda>(d,t). (d,the (finite_self_contained_term t)))) q=q"
    by (simp add: shape decode_finite_self_contained_term[OF data])
qed

theorem finite_literal_inference_known_sound:
  "image decode_finite_call_term (set (finite_literal_inference_known []))
    \<subseteq>positive_meaning inference_specialization_system"
  using finite_literal_source_calls_sound
  by (simp only: set_map[symmetric] decode_finite_literal_inference_known)

lemma finite_literal_known_entries:
  "map fst (finite_literal_inference_known p)=[94,294,126,125,61,61,345,346]"
  by (simp add: finite_literal_inference_known_def finite_literal_source_calls_def Let_def)

export_code finite_literal_inference_value finite_literal_inference_known
  Finite_Payload Finite_Pair Finite_Target Finite_Whole nat_of_integer integer_of_nat
  in SML module_name Finite_Literal_Inference_Premises file_prefix finite_literal_inference_premises

text \<open>
  The two reference instantiations coincide for an empty scope, but both
  premise occurrences remain in the supplied list. Every initial call is
  proved in the same program as the compiled construction library. The final
  inference-specialization entry is absent from this initial evidence.
\<close>

end
