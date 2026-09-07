theory Factor_Proof_Graph_Admission
  imports Factor_Proof_Bound_Checking
begin

section \<open>A root belongs to a complete acyclic native graph\<close>

abbreviation proof_graph_admission_result :: "factor_term \<Rightarrow> bool" where
  "proof_graph_admission_result z \<equiv> \<exists>E e u r G.
    z=source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents E e \<and> native_schema_graph_at E (u,r) G"

definition proof_graph_admission_schema :: "(nat,nat,nat) factor_schema" where
  "proof_graph_admission_schema=data_rule (source_root_pattern data_x data_y data_z)
    {(0,96,proof_bound_pattern data_x data_w (Pattern_Variable 4)),
     (1,28,Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (data_list_pattern [Pattern_Variable 5]))),
     (2,21,Pattern_Variable 4)}"

definition proof_graph_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_graph_admission_system=add_view_definition proof_bound_checking_system 97 data_x {(0,proof_graph_admission_schema)}"

lemma proof_graph_admission_system_formed [simp]: "schema_system_formed proof_graph_admission_system"
  unfolding proof_graph_admission_system_def
  by (rule add_recursive_definition_formed[OF proof_bound_checking_system_formed])
    (auto simp: proof_graph_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_graph_admission_definitions [simp]:
  "system_definitions proof_graph_admission_system=insert 97 (system_definitions proof_bound_checking_system)"
  by (simp add: proof_graph_admission_system_def)

lemma proof_graph_admission_call:
  "schema_call_formed proof_graph_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_graph_admission_system \<and> term_formed t"
  using added_variable_calls[OF proof_bound_checking_system_formed
    proof_graph_admission_system_formed[unfolded proof_graph_admission_system_def] proof_bound_checking_call]
  by (simp only: proof_graph_admission_system_def[symmetric])

lemma proof_graph_admission_old_meaning:
  assumes "d\<in>system_definitions proof_bound_checking_system"
  shows "(d,t)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_bound_checking_system"
  using added_definition_preserves_old(2)[OF proof_bound_checking_system_formed
    proof_graph_admission_system_formed[unfolded proof_graph_admission_system_def], of d t] assms
  by (auto simp: proof_graph_admission_system_def)

lemma proof_graph_admission_clause [simp]:
  "((97,c),S)\<in>system_clauses proof_graph_admission_system \<longleftrightarrow> (c,S)\<in>{(0,proof_graph_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_bound_checking_system \<Longrightarrow> d\<in>system_definitions proof_bound_checking_system" for d c S
    using proof_bound_checking_system_formed unfolding schema_system_formed_def by blast
  have absent: "((97,c),S)\<notin>system_clauses proof_bound_checking_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_graph_admission_system_def)
qed

lemma proof_graph_admission_node_meaning:
  assumes "d\<in>system_definitions proof_node_reading_system"
  shows "(d,t)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system"
  using proof_graph_admission_old_meaning[of d t] proof_bound_checking_node_meaning[OF assms, of t] assms by auto

lemma proof_graph_admission_components:
  "(96,t)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> (96,t)\<in>positive_meaning proof_bound_checking_system"
  "(28,t)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  "(21,t)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  using proof_graph_admission_old_meaning[of 96 t]
    proof_graph_admission_old_meaning[of 28 t] proof_bound_checking_old_meaning[of 28 t] proof_link_checking_fibre_meaning[of 28 t]
    proof_graph_admission_old_meaning[of 21 t] proof_bound_checking_old_meaning[of 21 t] proof_link_checking_keyed_meaning[of 21 t] by auto

lemma proof_graph_admission_step:
  assumes bound: "(96,proof_bound_argument e b h)\<in>positive_meaning proof_bound_checking_system"
    and root: "(28,key_fibre_argument (Pair_Term u r) b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
    and origins: "(21,h)\<in>positive_meaning keyed_list_system"
  shows "(97,source_root_argument e u r)\<in>positive_meaning proof_graph_admission_system"
proof -
  have formed: "term_formed e" "term_formed b" "term_formed h" "term_formed u" "term_formed r" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF bound]]
      schema_call_formed_target[OF positive_meaning_formed[OF root]] by auto
  let ?f="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then b else if n=4 then h else v"
  have result: "(97,evaluate_pattern ?f (schema_conclusion proof_graph_admission_schema))\<in>positive_meaning proof_graph_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: proof_graph_admission_schema_def schema_variables_def
        proof_graph_admission_call proof_graph_admission_components\<close>)
  show ?thesis using result by (simp add: proof_graph_admission_schema_def)
qed

theorem proof_graph_admission_sound:
  assumes holds: "(97,z)\<in>positive_meaning proof_graph_admission_system"
  shows "proof_graph_admission_result z"
proof -
  have consequence: "(97,z)\<in>schema_consequences proof_graph_admission_system (positive_meaning proof_graph_admission_system)"
    using holds positive_meaning_unfold[of proof_graph_admission_system] by blast
  obtain c S h where clause: "((97,c),S)\<in>system_clauses proof_graph_admission_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning proof_graph_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=proof_graph_admission_schema" using clause by simp
  have bound: "(96,proof_bound_argument (h 0) (h 3) (h 4))\<in>positive_meaning proof_bound_checking_system"
    and root: "(28,key_fibre_argument (Pair_Term (h 1) (h 2)) (h 3) (data_list_term [h 5]))\<in>positive_meaning key_fibre_system"
    and origins: "(21,h 4)\<in>positive_meaning keyed_list_system"
    using support by (auto simp: schema proof_graph_admission_schema_def proof_graph_admission_components)
  obtain rs where lookup: "h 3=pair_list_term rs" "key_values (Pair_Term (h 1) (h 2)) rs=[h 5]"
    by (rule key_fibre_singleton_rows[OF root]) (rule that; assumption)
  have nonempty: "h 3\<noteq>Payload_Term []"
  proof
    assume empty: "h 3=Payload_Term []"
    have nil_rows: "rs=[]" using lookup(1) empty by (cases rs) auto
    show False using lookup(2) by (simp add: nil_rows)
  qed
  obtain E bs hs where source: "environment_value_presents E (h 0)" and fields: "h 3=proof_bound_term bs" "h 4=pair_list_term hs"
    and checked: "proof_bound_values E bs hs"
    using bound nonempty by (simp only: proof_bound_checking_exact factor_term.inject) blast
  have same: "rs=map (\<lambda>(n,t). (definition_site_value n,t)) bs"
    using lookup(1) fields(1) by (simp only: pair_list_term_injective id_apply)
  have member: "(Pair_Term (h 1) (h 2),h 5)\<in>set rs"
    using lookup(2) key_values_set[of "Pair_Term (h 1) (h 2)" rs] by auto
  obtain n where row: "(n,h 5)\<in>set bs" and site: "Pair_Term (h 1) (h 2)=definition_site_value n"
    using member same by auto
  have root_member: "n\<in>set (map fst bs)" using row by force
  have keys: "(21,pair_list_term hs)\<in>positive_meaning keyed_list_system" using origins fields(2) by simp
  obtain G where graph: "native_schema_graph_at E n G"
    using checked root_member keys native_graph_value_bound[of E n] by blast
  have inputs: "h 1=use_data_term (fst n)" "h 2=Payload_Term (snd n)"
    using site by (simp_all add: site_data_term_def)
  show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ "fst n"],
      rule exI[of _ "snd n"], rule exI[of _ G])
    (use conclusion source graph inputs in \<open>simp add: schema proof_graph_admission_schema_def\<close>)
qed

theorem proof_graph_admission_complete:
  assumes source: "environment_value_presents E e" and graph: "native_schema_graph_at E (u,r) G"
  shows "(97,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning proof_graph_admission_system"
proof -
  obtain bs hs where bound: "proof_bound_values E bs hs" and root: "(u,r)\<in>set (map fst bs)"
    and origins: "(21,pair_list_term hs)\<in>positive_meaning keyed_list_system"
    using graph native_graph_value_bound[of E "(u,r)"] by blast
  have checked: "(96,proof_bound_argument e (proof_bound_term bs) (pair_list_term hs))\<in>positive_meaning proof_bound_checking_system"
    by (rule proof_bound_checking_complete[OF source bound])
  obtain t where row: "((u,r),t)\<in>set bs" using root by auto
  have rows: "native_value_rows E bs" by (rule proof_bound_values_reads[OF bound])
  obtain N D I K where presented: "proof_node_value_presents N D t" and raw: "native_proof_node_at E u r N D I K"
    using rows row by auto
  have site: "term_formed (definition_site_value (u,r))"
    using native_proof_node_value_formed(1)[of E "(u,r)" N D I K t] raw presented by simp
  have fibre: "key_values (u,r) bs=[t]" by (rule key_values_unique_key[OF proof_bound_values_keys[OF bound] row])
  have lookup: "(28,key_fibre_argument (definition_site_value (u,r)) (proof_bound_term bs) (data_list_term [t]))
    \<in>positive_meaning key_fibre_system"
    by (simp only: key_fibre_lists key_values_map[OF definition_site_value_injective] map_ident id_def)
      (use site native_value_rows_formed(1)[OF rows] fibre in simp)
  show ?thesis by (rule proof_graph_admission_step[OF checked _ origins])
    (use lookup in \<open>simp add: site_data_term_def\<close>)
qed

theorem proof_graph_admission_exact:
  "(97,z)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow> proof_graph_admission_result z"
  using proof_graph_admission_sound proof_graph_admission_complete by blast

corollary proof_graph_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(97,source_root_argument e u r)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow>
    (\<exists>v a G. u=use_data_term v \<and> r=Payload_Term a \<and> native_schema_graph_at E (v,a) G)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: proof_graph_admission_exact factor_term.inject) (use unique source in blast)
qed

corollary proof_graph_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(97,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning proof_graph_admission_system
    \<longleftrightarrow> (\<exists>G. native_schema_graph_at E (u,r) G)"
  by (simp only: proof_graph_admission_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary proof_graph_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(97,source_root_argument e u r)\<in>positive_meaning proof_graph_admission_system \<longleftrightarrow>
    (97,source_root_argument f u r)\<in>positive_meaning proof_graph_admission_system"
  by (simp only: proof_graph_admission_at_source[OF assms(1)] proof_graph_admission_at_source[OF assms(2)])

corollary proof_graph_admission_unique_graph:
  assumes source: "environment_value_presents E e"
    and accepted: "(97,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning proof_graph_admission_system"
  shows "\<exists>!G. native_schema_graph_at E (u,r) G"
  using accepted native_schema_graph_unique by (simp only: proof_graph_admission_on_values[OF source]) blast

corollary proof_graph_admission_assertion:
  assumes source: "environment_value_presents E e"
    and raw: "native_proof_node_at E u r Schema_Assertion {} I K"
  shows "(97,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning proof_graph_admission_system"
proof -
  have bound: "native_node_bound E [(u,r)]" using raw by (auto simp: rel_ran_def)
  have uses: "native_assertion_origins E {(u,r)}={}"
    using native_assertion_origins_at_node[of E "(u,r)" Schema_Assertion "{}" I K] raw
    by (auto simp: native_assertion_origins_def dest: native_proof_node_unique)
  have witness: "\<exists>ns. native_node_bound E ns \<and> (u,r)\<in>set ns \<and>
    single_valued (native_assertion_origins E (set ns))"
    by (rule exI[of _ "[(u,r)]"]) (use bound uses in \<open>simp add: single_valued_def\<close>)
  have exists: "\<exists>G. native_schema_graph_at E (u,r) G"
    using witness by (simp only: native_graph_finite_bound)
  show ?thesis using exists by (simp only: proof_graph_admission_on_values[OF source])
qed

text \<open>
  One ordinary clause hides the checked finite bound, requires actual root
  membership through the complete key collector, and checks unique assertion
  keys. Acceptance is exactly existence of the existing native graph. Its
  complete node and discharge projection is unique and equals the actual
  root closure. No choice of bound may replace that projection. This admits
  graph structure alone; root claims, clause instances, and assumption truth
  remain the independent derivation boundary.
\<close>

end
