theory Factor_Finite_Proof_Nodes
  imports Factor_Finite_Proof_Tables Factor_Finite_Graph_Metadata Factor_Proof_Node_Code
begin

definition finite_citation_block :: "'u definition_site\<Rightarrow>'u finite_syntax_block" where
  "finite_citation_block d=(finite_external_occurrence_syntax (snd d),{||},{|([4],d)|})"

lemma finite_citation_block_fields [simp]:
  "decode_finite_object (finite_block_artifact (finite_citation_block d))=external_occurrence_syntax (snd d)"
  "map_relation_values decode_finite_object (fset (finite_block_literals (finite_citation_block d)))={}"
  "fset (finite_block_callees (finite_citation_block d))={([4],d)}"
  by (simp_all add: finite_citation_block_def map_relation_values_def)

definition finite_inference_node_block where
  "finite_inference_node_block c B T=finite_record_block [finite_citation_block c,B,T]"

definition finite_assertion_node_block :: "'u finite_syntax_block" where
  "finite_assertion_node_block=finite_record_block []"

locale finite_inference_node_construction =
  fixes c :: "local_address option definition_site"
    and V :: "(local_address option definition_site\<times>finite_factor_term) fset"
    and D :: "(local_address option definition_site\<times>local_address option definition_site) fset"
  assumes address: "octets_formed (snd c)"
    and bindings: "finite_binding_table_ready V"
    and discharges: "finite_discharge_table_ready D"
begin

sublocale binding: finite_binding_table_construction V
  by (rule finite_binding_table_construction.intro[OF bindings])
sublocale discharge: finite_discharge_table_construction D
  by (rule finite_discharge_table_construction.intro[OF discharges])

sublocale native: inference_node_syntax_construction c "decode_finite_binding_set V" "fset D"
    "decode_finite_object (finite_block_artifact binding.block)"
    "decode_finite_object (finite_block_artifact discharge.block)"
    "map_relation_values decode_finite_object (fset (finite_block_literals binding.block))"
    "map_relation_values decode_finite_object (fset (finite_block_literals discharge.block))"
    "fset (finite_block_callees binding.block)" "fset (finite_block_callees discharge.block)"
    "fset (finite_block_interior binding.block)" "fset (finite_block_slots binding.block)"
    "fset (finite_block_interior discharge.block)" "fset (finite_block_slots discharge.block)"
  by (rule inference_node_syntax_construction.intro[OF address])
    (use binding.properties discharge.properties binding.recovers discharge.recovers in
      \<open>simp_all only: decode_finite_binding_set_values; blast+\<close>)+

abbreviation block where "block \<equiv> finite_inference_node_block c binding.block discharge.block"

lemma fields:
  "decode_finite_object (finite_block_artifact block)=native.assembled.framed"
  "map_relation_values decode_finite_object (fset (finite_block_literals block))=native.assembled.literals"
  "fset (finite_block_callees block)=native.assembled.callees"
  by (simp_all add: finite_inference_node_block_def finite_record_block_fields)

lemma boundaries:
  "fset (finite_block_slots block)=native.assembled.slots"
  "fset (finite_block_interior block)=native.assembled.interior"
  using finite_block_boundary[where B=block and I="native.assembled.interior" and K="native.assembled.slots"]
  by (simp_all only: fields native.assembled.carrier native.assembled.boundary native.assembled.reference_domain)

theorem code:
  "proof_node_code_for (decode_finite_graph_node (Finite_Inference c V)) (fset D)
    (decode_finite_object (finite_block_artifact block))
    (map_relation_values decode_finite_object (fset (finite_block_literals block)))
    (fset (finite_block_callees block)) (fset (finite_block_interior block)) (fset (finite_block_slots block))"
  using native.assembled.frame.record_formed native.assembled.frame.record_counts
    native.assembled.frame.record_root native.assembled.reference_table native.assembled.carrier
    native.assembled.boundary native.assembled.reference_domain native.deps native.recover
  by (simp only: proof_node_code_for_def fields boundaries decode_finite_graph_node.simps
    proof_node_reference_sites.simps; blast)

end

lemma finite_assertion_node_block_fields:
  "decode_finite_object (finite_block_artifact finite_assertion_node_block)=assertion_node_syntax"
  "map_relation_values decode_finite_object (fset (finite_block_literals finite_assertion_node_block))={}"
  "fset (finite_block_callees finite_assertion_node_block)={}"
  by (simp_all add: finite_assertion_node_block_def finite_record_block_fields
    assertion_node_syntax_def family_ports_def)

lemma finite_assertion_node_block_boundaries:
  "fset (finite_block_slots finite_assertion_node_block)={}"
  "fset (finite_block_interior finite_assertion_node_block)={[]}"
  using finite_block_boundary[where B=finite_assertion_node_block and I="{[]}" and K="{}"]
  by (simp_all add: finite_assertion_node_block_fields assertion_node_syntax_properties(3))

lemma finite_assertion_node_block_code:
  "proof_node_code_for Schema_Assertion {} (decode_finite_object (finite_block_artifact finite_assertion_node_block))
    (map_relation_values decode_finite_object (fset (finite_block_literals finite_assertion_node_block)))
    (fset (finite_block_callees finite_assertion_node_block))
    (fset (finite_block_interior finite_assertion_node_block)) (fset (finite_block_slots finite_assertion_node_block))"
  using assertion_node_syntax_properties
  by (auto simp: proof_node_code_for_def finite_assertion_node_block_fields finite_assertion_node_block_boundaries)

definition finite_proof_node_ready where
  "finite_proof_node_ready E N D=(finite_environment_formed E \<and> finite_graph_node_inputs_at E D N \<and>
    finite_relation_functional D \<and> fBall D (\<lambda>(s,n). octets_formed (snd n)))"

definition finite_compile_proof_node where
  "finite_compile_proof_node E N D=(if finite_proof_node_ready E N D then
    (case N of Finite_Assertion \<Rightarrow> Some finite_assertion_node_block
    | Finite_Inference c V \<Rightarrow>
      (case finite_compile_binding_table V of None \<Rightarrow> None | Some B \<Rightarrow>
        map_option (finite_inference_node_block c B) (finite_compile_discharge_table D))) else None)"

lemma finite_proof_node_ready_exact:
  "finite_proof_node_ready E N D=(environment_formed (decode_finite_environment E) \<and>
    graph_node_inputs_at (decode_finite_environment E) (fset D) (decode_finite_graph_node N) \<and>
    single_valued (fset D) \<and> (\<forall>s n. (s,n)\<in>fset D \<longrightarrow> octets_formed (snd n)))"
  by (auto simp: finite_proof_node_ready_def finite_environment_formed_correct
    finite_graph_node_inputs_at_exact finite_relation_functional_correct)

lemma finite_proof_node_ready_tables:
  assumes ready: "finite_proof_node_ready E (Finite_Inference c V) D"
  shows "octets_formed (snd c)" "finite_binding_table_ready V" "finite_discharge_table_ready D"
proof -
  have ef: "environment_formed (decode_finite_environment E)"
    and clause: "c\<in>environment_positions (decode_finite_environment E)"
    and binding: "finite_relation_functional V"
    and terms: "\<forall>(a,t)\<in>fset V. a\<in>environment_positions (decode_finite_environment E) \<and> finite_term_formed t"
    and sockets: "rel_dom (fset D)\<subseteq>environment_positions (decode_finite_environment E)"
    and functional: "finite_relation_functional D"
    and targets: "\<forall>(s,n)\<in>fset D. octets_formed (snd n)"
    using ready by (auto simp: finite_proof_node_ready_def finite_environment_formed_correct
      finite_environment_positions_correct rel_dom_image less_eq_fset.rep_eq)
  show "octets_formed (snd c)" by (rule environment_position_address[OF ef clause])
  show "finite_binding_table_ready V"
    using binding terms environment_position_address[OF ef]
    by (auto simp: finite_binding_table_ready_def)
  show "finite_discharge_table_ready D"
    using functional sockets targets environment_position_address[OF ef]
    by (auto simp: finite_discharge_table_ready_def rel_dom_def)
qed

theorem finite_compile_proof_node_domain:
  "(\<exists>B. finite_compile_proof_node E N D=Some B) \<longleftrightarrow> finite_proof_node_ready E N D"
proof (cases "finite_proof_node_ready E N D")
  case False
  then show ?thesis by (simp add: finite_compile_proof_node_def)
next
  case True
  show ?thesis
  proof (cases N)
    case Finite_Assertion
    then show ?thesis using True
      by (simp only: finite_compile_proof_node_def if_True finite_schema_graph_node.simps option.simps; blast)
  next
    case (Finite_Inference c V)
    have tables: "finite_binding_table_ready V" "finite_discharge_table_ready D"
      using finite_proof_node_ready_tables[OF True[unfolded Finite_Inference]] by blast+
    obtain B T where compiled: "finite_compile_binding_table V=Some B" "finite_compile_discharge_table D=Some T"
      using tables by (simp only: finite_compile_binding_table_domain[symmetric]
        finite_compile_discharge_table_domain[symmetric]; blast)
    have available: "finite_proof_node_ready E (Finite_Inference c V) D"
      using True by (simp only: Finite_Inference)
    have result: "finite_compile_proof_node E N D=Some (finite_inference_node_block c B T)"
      by (simp add: finite_compile_proof_node_def Finite_Inference available compiled)
    show ?thesis using result True by blast
  qed
qed

theorem finite_compile_proof_node_correct:
  assumes compiled: "finite_compile_proof_node E N D=Some B"
  shows "finite_proof_node_ready E N D"
    "proof_node_code_for (decode_finite_graph_node N) (fset D)
      (decode_finite_object (finite_block_artifact B))
      (map_relation_values decode_finite_object (fset (finite_block_literals B)))
      (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
proof -
  show ready: "finite_proof_node_ready E N D"
    using compiled finite_compile_proof_node_domain[of E N D] by blast
  show "proof_node_code_for (decode_finite_graph_node N) (fset D)
      (decode_finite_object (finite_block_artifact B))
      (map_relation_values decode_finite_object (fset (finite_block_literals B)))
      (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
  proof (cases N)
    case Finite_Assertion
    have empty: "D={||}" using ready Finite_Assertion by (simp add: finite_proof_node_ready_def)
    have block: "B=finite_assertion_node_block"
      using compiled ready[unfolded Finite_Assertion]
      by (simp add: finite_compile_proof_node_def Finite_Assertion)
    show ?thesis by (simp only: block Finite_Assertion decode_finite_graph_node.simps empty bot_fset.rep_eq;
      rule finite_assertion_node_block_code)
  next
    case (Finite_Inference c V)
    interpret construction: finite_inference_node_construction c V D
      by (rule finite_inference_node_construction.intro[OF finite_proof_node_ready_tables[OF ready[unfolded Finite_Inference]]])
    have block: "B=construction.block"
      using compiled ready[unfolded Finite_Inference]
      by (simp add: finite_compile_proof_node_def Finite_Inference
        finite_compile_binding_table_def finite_compile_discharge_table_def construction.bindings construction.discharges)
    show ?thesis by (simp only: block Finite_Inference; rule construction.code)
  qed
qed

export_code finite_compile_proof_node checking SML

text \<open>
  The compiler receives the actual source environment, original node metadata
  and complete indexed proof-target relation. Its successful output satisfies
  the original proof-node code contract, including every literal, reference
  and carrier position. The input contract checks source positions and formed
  terms. Unsupported inputs return no code. Node construction does not select
  a derivation or establish that its proof targets prove the required premises.
\<close>

end
