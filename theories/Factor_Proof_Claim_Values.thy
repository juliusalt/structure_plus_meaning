theory Factor_Proof_Claim_Values
  imports Factor_Keyed_Row_Join Factor_Positioned_Instances Functional_Relation_Lists
begin

section \<open>One faithful row shape serves node claims and positioned premises\<close>

abbreviation encoded_positioned_calls where
  "encoded_positioned_calls xs \<equiv>
    map (\<lambda>(n,d,t). (definition_site_value n,call_instance_value d t)) xs"

abbreviation positioned_call_rows_term where
  "positioned_call_rows_term xs \<equiv> pair_list_term (encoded_positioned_calls xs)"

lemma positioned_call_rows_cons:
  "positioned_call_rows_term ((n,d,t)#xs)=
    Pair_Term (Pair_Term (definition_site_value n) (call_instance_value d t)) (positioned_call_rows_term xs)"
  by simp

lemma call_instance_pair_injective: "inj (\<lambda>(d,t). call_instance_value d t)"
  by (rule injI) (auto simp: call_instance_value_injective split: prod.splits)

lemma positioned_call_rows_term_injective:
  "positioned_call_rows_term xs=positioned_call_rows_term ys \<longleftrightarrow> xs=ys"
  using keyed_rows_term_injective[OF definition_site_value_injective call_instance_pair_injective, of xs ys]
  by (simp only: case_prod_unfold)

lemma positioned_calls_key_order:
  "distinct (map fst (encoded_positioned_calls xs)) \<longleftrightarrow> distinct (map fst xs)"
proof -
  have mapped: "map fst (encoded_positioned_calls xs)=map definition_site_value (map fst xs)"
    by (simp add: comp_def case_prod_unfold)
  have injective: "inj_on definition_site_value (set (map fst xs))"
    by (rule inj_on_subset[OF definition_site_value_injective subset_UNIV])
  show ?thesis using injective by (simp only: mapped distinct_map; blast)
qed

lemma positioned_calls_fibre:
  assumes keys: "distinct (map fst xs)"
  shows "key_values (definition_site_value n) (encoded_positioned_calls xs)=[call_instance_value d t]
    \<longleftrightarrow> (n,d,t)\<in>set xs"
proof
  assume fibre: "key_values (definition_site_value n) (encoded_positioned_calls xs)=[call_instance_value d t]"
  have member: "(definition_site_value n,call_instance_value d t)\<in>set (encoded_positioned_calls xs)"
    using fibre key_values_set[of "definition_site_value n" "encoded_positioned_calls xs"] by auto
  show "(n,d,t)\<in>set xs"
    using member by (auto simp: definition_site_value_eq call_instance_value_injective)
next
  assume row: "(n,d,t)\<in>set xs"
  have mapped: "key_values (definition_site_value n) (encoded_positioned_calls xs)=
      map (\<lambda>(e,x). call_instance_value e x) (key_values n xs)"
    using key_values_map[OF definition_site_value_injective, where k=n
      and g="\<lambda>(e,x). call_instance_value e x" and xs=xs]
    by (simp only: case_prod_unfold)
  show "key_values (definition_site_value n) (encoded_positioned_calls xs)=[call_instance_value d t]"
    by (simp only: mapped key_values_unique_key[OF keys row] list.map case_prod_conv)
qed

lemma qualify_binding_rows:
  "qualified_rows_term (use_data_term u) (map (\<lambda>(a,t). (Payload_Term a,t)) xs)=
    positioned_binding_rows_term (map (\<lambda>(a,t). ((u,a),t)) xs)"
  by (simp add: comp_def case_prod_unfold site_data_term_def)

lemma qualify_call_rows:
  "qualified_rows_term (use_data_term u) (map (\<lambda>(s,d,t). (Payload_Term s,call_instance_value d t)) qs)=
    positioned_call_rows_term (map (\<lambda>(s,q). ((u,s),q)) qs)"
  by (simp add: comp_def case_prod_unfold site_data_term_def)

lemma local_call_rows_encoding:
  "call_instance_rows_term qs=pair_list_term (map (\<lambda>(s,d,t). (Payload_Term s,call_instance_value d t)) qs)"
  by (simp add: comp_def case_prod_unfold)

section \<open>Each supplied claim checks against all of its actual child fibres\<close>

definition proof_claim_at where
  "proof_claim_at P G js n d t \<longleftrightarrow>
    ((n,Schema_Assertion)\<in>fset (graph_inferences G) \<and> schema_call_formed P d t \<and>
      schema_graph_premises G n={}) \<or>
    (\<exists>c V Q. (n,Schema_Inference c V)\<in>fset (graph_inferences G) \<and>
      admitted_schema_instance P d c (fset V) t Q \<and>
      rel_dom (schema_graph_premises G n)=rel_dom Q \<and>
      (\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
        key_values (definition_site_value m) js=
          [call_instance_value (fst (rel_value Q s)) (snd (rel_value Q s))]))"

definition proof_claim_values where
  "proof_claim_values P G js xs hs \<longleftrightarrow>
    (\<forall>n d t. (n,d,t)\<in>set xs \<longrightarrow> proof_claim_at P G js n d t) \<and>
    hs=filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs"

lemma proof_claim_values_nil [simp]:
  "proof_claim_values P G js [] hs \<longleftrightarrow> hs=[]"
  by (simp add: proof_claim_values_def)

lemma proof_claim_values_cons:
  "proof_claim_values P G js ((n,d,t)#xs) hs \<longleftrightarrow>
    proof_claim_at P G js n d t \<and>
    (\<exists>ts. proof_claim_values P G js xs ts \<and>
      hs=(if (n,Schema_Assertion)\<in>fset (graph_inferences G) then (n,d,t)#ts else ts))"
  by (cases n; cases d) (auto simp: proof_claim_values_def)

lemma proof_claim_at_node_call:
  assumes "proof_claim_at P G js n d t"
  shows "n\<in>schema_graph_nodes G" "schema_call_formed P d t"
  using assms by (auto simp: proof_claim_at_def schema_graph_nodes_def rel_dom_def admitted_schema_instance_def)

lemma proof_claim_values_entry:
  assumes "proof_claim_values P G js xs hs" "(n,d,t)\<in>set xs"
  shows "proof_claim_at P G js n d t"
  using assms unfolding proof_claim_values_def by blast

lemma proof_claim_values_boundary:
  assumes "proof_claim_values P G js xs hs"
  shows "set hs=schema_graph_assumptions G (set xs)"
  using assms by (auto simp: proof_claim_values_def schema_graph_assumptions_def)

lemma proof_claim_at_table:
  assumes formed: "schema_graph_formed G root" and keys: "distinct (map fst xs)"
    and claim: "(n,d,t)\<in>set xs" and node: "(n,A)\<in>fset (graph_inferences G)"
  shows "proof_claim_at P G (encoded_positioned_calls xs) n d t \<longleftrightarrow>
    checks_schema_graph_node P G (set xs) n A"
proof -
  have jsv: "single_valued (set xs)" using keys by (simp only: distinct_keys_iff; blast)
  have row_value: "rel_value (set xs) n=(d,t)" by (rule rel_value_eq[OF jsv claim])
  have nsv: "single_valued (fset (graph_inferences G))" using formed by (simp add: schema_graph_formed_def)
  have same: "(n,B)\<in>fset (graph_inferences G) \<longleftrightarrow> B=A" for B
    using node single_valued_outputs[OF nsv node] by blast
  show ?thesis
  proof (cases A)
    case Schema_Assertion
    show ?thesis
      by (simp only: Schema_Assertion proof_claim_at_def same inference_node.distinct inference_node.inject
        checks_schema_graph_node.simps row_value fst_conv snd_conv; blast)
  next
    case (Schema_Inference c V)
    show ?thesis
      by (simp only: Schema_Inference proof_claim_at_def same inference_node.distinct inference_node.inject
        checks_schema_graph_node.simps row_value fst_conv snd_conv positioned_calls_fibre[OF keys] prod.collapse; blast)
  qed
qed

lemma proof_claim_at_child:
  assumes keys: "distinct (map fst xs)" and at: "proof_claim_at P G (encoded_positioned_calls xs) n d t"
    and edge: "(m,n)\<in>schema_graph_edges G"
  shows "m\<in>rel_dom (set xs)"
proof -
  obtain s where premise: "(s,m)\<in>schema_graph_premises G n"
    using edge by (auto simp: schema_graph_edges_def schema_graph_premises_def)
  obtain Q where fibre: "key_values (definition_site_value m) (encoded_positioned_calls xs)=
      [call_instance_value (fst (rel_value Q s)) (snd (rel_value Q s))]"
    using at premise by (auto simp: proof_claim_at_def; blast)
  have row: "(m,rel_value Q s)\<in>set xs"
    using fibre by (simp only: positioned_calls_fibre[OF keys] prod.collapse)
  show ?thesis by (rule rel_domI[OF row])
qed

lemma proof_claim_values_domain:
  assumes formed: "schema_graph_formed G root" and keys: "distinct (map fst xs)"
    and checked: "proof_claim_values P G (encoded_positioned_calls xs) xs hs"
    and root: "(root,d,t)\<in>set xs"
  shows "rel_dom (set xs)=schema_graph_nodes G"
proof -
  have lower: "rel_dom (set xs)\<subseteq>schema_graph_nodes G"
    using proof_claim_at_node_call(1)[OF proof_claim_values_entry[OF checked]]
    by (auto simp: rel_dom_def)
  have start: "root\<in>rel_dom (set xs)" by (rule rel_domI[OF root])
  have closed: "m\<in>rel_dom (set xs)" if "n\<in>rel_dom (set xs)" "(m,n)\<in>schema_graph_edges G" for m n
  proof -
    have key: "n\<in>rel_dom (set xs)" by (rule that(1))
    have exists: "\<exists>q. (n,q)\<in>set xs" using key by (simp only: rel_dom_def mem_Collect_eq)
    obtain q where entry: "(n,q)\<in>set xs" using exists by blast
    obtain e x where q: "q=(e,x)" by (cases q)
    have row: "(n,e,x)\<in>set xs" using entry q by simp
    show ?thesis by (rule proof_claim_at_child[OF keys proof_claim_values_entry[OF checked row] that(2)])
  qed
  have closure: "{n. (n,root)\<in>(schema_graph_edges G)\<^sup>*}\<subseteq>rel_dom (set xs)"
    by (rule root_predecessors_least[OF start]) (use closed in blast)
  have upper: "schema_graph_nodes G\<subseteq>rel_dom (set xs)"
    using formed closure unfolding schema_graph_formed_def by blast
  show ?thesis using lower upper by blast
qed

theorem proof_claim_values_to_reading:
  assumes formed: "schema_graph_formed G root" and keys: "distinct (map fst xs)"
    and checked: "proof_claim_values P G (encoded_positioned_calls xs) xs hs"
    and root: "(root,d,t)\<in>set xs"
  shows "schema_graph_reading P G root d t (set xs)"
    "set hs=schema_graph_assumptions G (set xs)"
proof -
  have domain: "rel_dom (set xs)=schema_graph_nodes G"
    by (rule proof_claim_values_domain[OF formed keys checked root])
  have jsv: "single_valued (set xs)" using keys by (simp only: distinct_keys_iff; blast)
  have each: "checks_schema_graph_node P G (set xs) n A"
    if node: "(n,A)\<in>fset (graph_inferences G)" for n A
  proof -
    have member: "n\<in>rel_dom (set xs)" using node domain by (auto simp: schema_graph_nodes_def rel_dom_def)
    have exists: "\<exists>q. (n,q)\<in>set xs" using member by (simp only: rel_dom_def mem_Collect_eq)
    obtain q where entry: "(n,q)\<in>set xs" using exists by blast
    obtain e x where q: "q=(e,x)" by (cases q)
    have row: "(n,e,x)\<in>set xs" using entry q by simp
    show ?thesis using proof_claim_values_entry[OF checked row] proof_claim_at_table[OF formed keys row node] by blast
  qed
  show "schema_graph_reading P G root d t (set xs)"
    using formed jsv domain root each by (simp add: schema_graph_reading_def)
  show "set hs=schema_graph_assumptions G (set xs)" by (rule proof_claim_values_boundary[OF checked])
qed

theorem reading_to_proof_claim_values:
  assumes read: "schema_graph_reading P G root d t (set xs)" and keys: "distinct (map fst xs)"
  shows "proof_claim_values P G (encoded_positioned_calls xs) xs
    (filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs)"
proof -
  have formed: "schema_graph_formed G root" and domain: "rel_dom (set xs)=schema_graph_nodes G"
    using read by (auto simp: schema_graph_reading_def)
  have every: "proof_claim_at P G (encoded_positioned_calls xs) n e x" if row: "(n,e,x)\<in>set xs" for n e x
  proof -
    have member: "n\<in>schema_graph_nodes G" using rel_domI[OF row] domain by simp
    obtain A where node: "(n,A)\<in>fset (graph_inferences G)"
      using member by (auto simp: schema_graph_nodes_def rel_dom_def)
    have checked: "checks_schema_graph_node P G (set xs) n A"
      using read node unfolding schema_graph_reading_def by blast
    show ?thesis using proof_claim_at_table[OF formed keys row node] checked by blast
  qed
  show ?thesis using every by (simp add: proof_claim_values_def)
qed

theorem schema_graph_claim_order:
  assumes read: "schema_graph_reading P G root d t J" and order: "distinct hs"
    and boundary: "set hs=schema_graph_assumptions G J"
  obtains xs where "set xs=J" "distinct (map fst xs)"
    "filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs=hs"
proof -
  have finite: "finite J" by (rule schema_graph_reading_finite[OF read])
  have exact: "set hs={z\<in>J. (fst z,Schema_Assertion)\<in>fset (graph_inferences G)}"
    using boundary by (auto simp: schema_graph_assumptions_def)
  have jsv: "single_valued J" using read by (simp add: schema_graph_reading_def)
  obtain xs where rows: "set xs=J" "distinct (map fst xs)"
    "filter (\<lambda>z. (fst z,Schema_Assertion)\<in>fset (graph_inferences G)) xs=hs"
    by (rule functional_filter_order[OF finite jsv order exact]) (rule that; assumption)
  show thesis by (rule that[OF rows(1,2)]) (use rows(3) in \<open>simp add: case_prod_unfold\<close>)
qed

section \<open>Native readings form every actual claim value\<close>

lemma native_claim_context_formed:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G"
  shows "term_formed e" "term_formed (use_data_term pu)" "octets_formed pr"
    "term_formed (definition_site_value root)"
proof -
  have program: "(80,source_root_argument e (use_data_term pu) (Payload_Term pr))\<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source package])
  have graph_call: "(97,source_root_argument e (use_data_term (fst root)) (Payload_Term (snd root)))
      \<in>positive_meaning proof_graph_admission_system"
    by (rule proof_graph_admission_complete[OF source]) (use graph in simp)
  show "term_formed e" "term_formed (use_data_term pu)" "octets_formed pr"
    "term_formed (definition_site_value root)"
    using schema_call_formed_target[OF positive_meaning_formed[OF program]]
      schema_call_formed_target[OF positive_meaning_formed[OF graph_call]] by auto
qed

lemma native_claim_rows_formed:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G"
    and checked: "proof_claim_values (positioned_program P) G js xs hs"
  shows "formed_key_rows (encoded_positioned_calls xs)"
    "term_formed (positioned_call_rows_term xs)" "term_formed (positioned_call_rows_term hs)"
proof -
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have ef: "environment_formed E" by (rule native_schema_graph_environment[OF graph])
  have every: "term_formed (definition_site_value n) \<and> term_formed (call_instance_value d t)"
    if row: "(n,d,t)\<in>set xs" for n d t
  proof -
    have at: "proof_claim_at (positioned_program P) G js n d t" by (rule proof_claim_values_entry[OF checked row])
    have inside: "n\<in>schema_graph_nodes G" and call: "schema_call_formed (positioned_program P) d t"
      using proof_claim_at_node_call[OF at] by blast+
    have position: "n\<in>environment_positions E" using native_schema_graph_positions[OF graph] inside by blast
    have key: "term_formed (definition_site_value n)" by (rule environment_position_value_formed[OF ef position])
    have original: "schema_call_formed P d t" using call by (simp only: positioned_program_calls[OF pf])
    have ordinary: "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) t))\<in>positive_meaning program_call_admission_system"
      by (rule program_call_admission_complete[OF source package original])
    have row_value: "term_formed (call_instance_value d t)"
      using schema_call_formed_target[OF positive_meaning_formed[OF ordinary]] by (auto simp: call_instance_value_def)
    show ?thesis using key row_value by blast
  qed
  have formed: "formed_key_rows (encoded_positioned_calls xs)"
    using every by (auto simp: case_prod_unfold)
  show "formed_key_rows (encoded_positioned_calls xs)" by (rule formed)
  show "term_formed (positioned_call_rows_term xs)" by (rule pair_list_term_formed[OF formed])
  have subset: "set hs\<subseteq>set xs" using checked by (auto simp: proof_claim_values_def)
  have output_formed: "formed_key_rows (encoded_positioned_calls hs)"
    using every subset by (auto simp: case_prod_unfold)
  show "term_formed (positioned_call_rows_term hs)" by (rule pair_list_term_formed[OF output_formed])
qed

text \<open>
  The temporary claim table is separate from native proof metadata. Each row
  supplies one node's call; all premise fibres refer to the same complete
  table. A root row and closure under every actual premise force its domain
  to be exactly the admitted graph's reachable nodes.

  Assertions select their exact rows from the chosen enumeration. Every
  distinct enumeration of the identified assumption boundary extends to
  a complete claim-table enumeration. Equal calls at different assertion
  sites remain distinct rows, and arbitrary formed call values are retained.
\<close>

end
