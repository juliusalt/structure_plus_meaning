theory Factor_Ground_Inference_Premises
  imports Factor_Inference_Reader_Investigation Factor_Executable_Environment_Values
    Factor_Specialization_Binding_Contracts
begin

section \<open>Complete source calls for an empty replacement scope\<close>

definition ground_inference_source_calls where
  "ground_inference_source_calls e pu pr nu nr du dr c f v r g w t z ds Is Ks RIs RKs = (let
    a=source_root_argument e (use_data_term pu) (Payload_Term pr);
    d=Pair_Term (use_data_term du) (Payload_Term dr);
    q=Pair_Term g (Pair_Term (use_data_term w) (Payload_Term t));
    rr=Pair_Term f (Pair_Term (use_data_term v) (Payload_Term r));
    empty=Payload_Term [];
    inst=pattern_instantiation_argument f (use_data_term v) empty empty (Payload_Term r)
      empty empty (data_list_term (map Payload_Term RIs)) (data_list_term (map Payload_Term RKs))
    in [(94,term_quotation_argument e (use_data_term nu) (Payload_Term nr)
          (data_list_term [Pair_Term (use_data_term du) (Payload_Term c),empty,discharge_rows_term ds])
          (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks))),
        (294,Pair_Term (Pair_Term a (Pair_Term d (Payload_Term c))) (Pair_Term rr q)),
        (126,Pair_Term q z),(125,reference_bindings_value empty empty empty),
        (61,inst),(61,inst),
        (345,context_relation_argument (use_data_term du) empty empty),
        (346,context_relation_argument (use_data_term du) empty empty)])"

theorem ground_inference_source_calls_sound:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents H g"
    and node: "native_proof_node_at E nu nr (Schema_Inference (du,c) {||}) (set ds) (set Is) (set Ks)"
    and binding: "specialization_binding_at E pu pr (du,dr) c F v r H w t
      (Pair_Term (Payload_Term []) report) (positioned_binding_rows_term []) RIs RKs"
    and raw_record: "pattern_record_at F v {} r [] (set RIs) (set RKs)"
    and orders: "distinct ds" "distinct Is" "distinct Ks" "distinct RIs" "distinct RKs"
  shows "set (ground_inference_source_calls e pu pr nu nr du dr c f v r g w t
      (Pair_Term (Payload_Term []) report) ds Is Ks RIs RKs)
    \<subseteq>positive_meaning inference_specialization_system"
proof -
  let ?empty="Payload_Term []"
  let ?a="source_root_argument e (use_data_term pu) (Payload_Term pr)"
  let ?d="Pair_Term (use_data_term du) (Payload_Term dr)"
  let ?c="Payload_Term c"
  let ?rr="Pair_Term f (Pair_Term (use_data_term v) (Payload_Term r))"
  let ?q="Pair_Term g (Pair_Term (use_data_term w) (Payload_Term t))"
  let ?z="Pair_Term ?empty report"
  let ?ri="data_list_term (map Payload_Term RIs)"
  let ?rk="data_list_term (map Payload_Term RKs)"
  have node_call: "(94,term_quotation_argument e (use_data_term nu) (Payload_Term nr)
      (data_list_term [Pair_Term (use_data_term du) ?c,?empty,discharge_rows_term ds])
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning proof_node_reading_system"
    using proof_node_reading_inference[OF sources(1), where u=nu and r=nr and c="(du,c)"
      and bs="[]" and ds=ds and Is=Is and Ks=Ks] node orders
    by (simp add: site_data_term_def)
  have binding_call: "(349,specialization_binding_argument ?a (use_data_term du) (Payload_Term dr) ?c
      f (use_data_term v) (Payload_Term r) ?q ?empty report ?empty ?ri ?rk)
      \<in>positive_meaning specialization_binding_system"
    using specialization_binding_on_sources[OF sources, where pu=pu and pr=pr and du=du and dr=dr
      and c=c and v=v and r=r and w=w and t=t and Is=RIs and Ks=RKs
      and b="?empty" and report=report and bs="?empty"] binding by simp
  have report_call: "(342,specialization_report_value ?a ?d ?c ?rr ?q ?z)
      \<in>positive_meaning specialization_report_system"
    using binding_call by (simp only: specialization_binding_at_arguments; blast)
  have reported:
    "(294,Pair_Term (Pair_Term ?a (Pair_Term ?d ?c)) (Pair_Term ?rr ?q))
      \<in>positive_meaning clause_specialization_reading_system"
    "(126,Pair_Term ?q ?z)\<in>positive_meaning schema_reading_system"
    using report_call by (auto simp only: specialization_report_at_arguments specialization_report_reference_meaning)
  have record_calls:
    "(125,reference_bindings_value ?empty ?empty ?empty)\<in>positive_meaning reference_bindings_system"
    "(61,pattern_instantiation_argument f (use_data_term v) ?empty ?empty (Payload_Term r)
      ?empty ?empty ?ri ?rk)\<in>positive_meaning record_instantiation_system"
    using binding_record_source_calls[OF sources(2), where v=v and r=r and Bs="[]" and As="[]"
      and s=Pattern_Variable and Is=RIs and Ks=RKs] raw_record orders
    by (auto simp: substitution_row_patterns_def)
  have owner: "term_formed (use_data_term du)"
    using binding by (auto simp: specialization_binding_at_def)
  have lists:
    "(345,context_relation_argument (use_data_term du) ?empty ?empty)\<in>positive_meaning binding_observation_program"
    "(346,context_relation_argument (use_data_term du) ?empty ?empty)\<in>positive_meaning binding_observation_program"
    using binding_observation_first_list.lists[of "use_data_term du" "[]" "[]"]
      binding_observation_second_list.lists[of "use_data_term du" "[]" "[]"] owner by simp_all
  show ?thesis using node_call reported record_calls lists
    by (auto simp: ground_inference_source_calls_def Let_def inference_specialization_readers
      inference_reader_source_meanings inference_reader_observation_meaning)
qed

lemma ground_inference_source_calls_data:
  assumes "self_contained_term e" "self_contained_term f" "self_contained_term g" "self_contained_term z"
    "(d,t)\<in>set (ground_inference_source_calls e pu pr nu nr du dr c f v r g w q z ds Is Ks RIs RKs)"
  shows "self_contained_term t"
  using assms by (auto simp: ground_inference_source_calls_def Let_def data_list_term_self_contained)

definition finite_data_call_values :: "(nat\<times>factor_term) list\<Rightarrow>(nat\<times>finite_factor_term) list" where
  "finite_data_call_values qs=map (\<lambda>(d,t). (d,the (finite_self_contained_term t))) qs"

lemma decode_finite_data_call_values:
  assumes data: "\<And>d t. (d,t)\<in>set qs \<Longrightarrow> self_contained_term t"
  shows "map decode_finite_call_term (finite_data_call_values qs)=qs"
  unfolding finite_data_call_values_def map_map
proof (rule map_idI)
  fix q assume member: "q\<in>set qs"
  obtain d t where shape: "q=(d,t)" by (cases q)
  have contained: "self_contained_term t" using data member by (simp only: shape; blast)
  show "(decode_finite_call_term \<circ> (\<lambda>(d,t). (d,the (finite_self_contained_term t)))) q=q"
    by (simp add: shape decode_finite_self_contained_term[OF contained])
qed

text \<open>
  The reusable source construction keeps all discharge occurrences and all
  four support lists. Its replacement binder and record are explicitly empty;
  no restriction to an empty child relation is imposed. The two instantiation
  calls retain their distinct occurrences even when their values coincide.
\<close>

end
