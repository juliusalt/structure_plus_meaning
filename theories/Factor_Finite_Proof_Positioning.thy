theory Factor_Finite_Proof_Positioning
  imports Factor_Finite_Graph_Positioning Factor_Finite_Proof_Flattening
begin

definition finite_schema_proof_owner ::
    "(local_address,local_address,'u definition_site,local_address) finite_instantiated_proof_node\<Rightarrow>'u" where
  "finite_schema_proof_owner n=fst (fst (snd n))"

definition finite_source_proof_graph :: "'u finite_native_system\<Rightarrow>
    (local_address,local_address,'u definition_site,local_address) finite_instantiated_proof_node\<Rightarrow>
    ('u definition_site,'u definition_site,'u definition_site,
      (local_address,local_address,'u definition_site,local_address) finite_instantiated_proof_node) finite_derivation_graph" where
  "finite_source_proof_graph P root=finite_positioned_graph finite_schema_proof_owner (finite_schema_proof_graph P root)"

lemma finite_source_proof_graph_nodes:
  "finite_graph_nodes (finite_source_proof_graph P (p,d,t))=finite_schema_proof_positions P p d t"
  by (simp only: finite_source_proof_graph_def finite_positioned_graph_nodes finite_schema_proof_graph_nodes)

theorem finite_source_proof_graph_reading:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_reading (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_source_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t)
    (graph_map (fset (finite_schema_proof_positions P p d t)) (snd\<circ>decode_finite_instantiated_node))"
proof -
  let ?G = "finite_schema_proof_graph P (p,d,t)"
  let ?D = decode_finite_instantiated_node
  let ?N = "fset (finite_schema_proof_positions P p d t)"
  let ?J = "graph_map ?N (snd\<circ>?D)"
  have sound: "(d,decode_finite_term t)\<in>positive_meaning (decode_finite_system P)"
    by (rule schema_proof_sound) (use checked in \<open>simp only: finite_checks_schema_proof_exact\<close>)
  have formed: "finite_system_formed P"
    by (simp only: finite_system_formed_correct; rule positive_meaning_has_formed_system[OF sound])
  have read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph ?G) (p,d,t) d (decode_finite_term t) ?J"
    by (rule finite_schema_proof_graph_reading[OF checked])
  have owners: "finite_schema_proof_owner n=fst (fst (rel_value ?J n))"
    if inside: "n |\<in>| finite_graph_nodes ?G" for n
  proof -
    have member: "n\<in>?N" using inside by (simp only: finite_schema_proof_graph_nodes)
    have claim_value: "rel_value ?J n=snd (?D n)"
      using rel_value_graph_map[OF member, of "snd\<circ>?D"] by (simp only: comp_apply)
    show ?thesis unfolding claim_value
      by (cases n) (simp add: finite_schema_proof_owner_def decode_finite_instantiated_node_pair)
  qed
  show ?thesis unfolding finite_source_proof_graph_def
    by (rule finite_positioned_graph_reading[where owner=finite_schema_proof_owner, OF formed read owners])
qed

lemma finite_source_proof_graph_assumptions:
  "schema_graph_assumptions (decode_finite_graph (finite_source_proof_graph P root)) J={}"
  by (simp only: finite_source_proof_graph_def finite_positioned_graph_correct
    positioned_schema_graph_assumptions finite_schema_proof_graph_assumptions)

theorem finite_source_proof_graph_derives:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_derives (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_source_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t) {}"
  unfolding schema_graph_derives_def
  by (rule exI[of _ "graph_map (fset (finite_schema_proof_positions P p d t)) (snd\<circ>decode_finite_instantiated_node)"])
    (simp only: finite_source_proof_graph_reading[OF checked] finite_source_proof_graph_assumptions simp_thms)

export_code finite_source_proof_graph checking SML

text \<open>
  Every node's full required call determines its owning definition use.
  The complete finite claim assignment is the exact transported original
  proof-graph reading, so ownership is derived from the actual certificate.
  Clause, binder and premise metadata is positioned under that use while every
  original node, call, term, edge endpoint and shared occurrence is retained.
  A checked certificate supplies the same closed derivation in the positioned
  view of its original program. Native allocation and replay remain separate.
\<close>

end
