theory Factor_Generation_Citation_Roots
  imports Factor_Generation_Dependency_Clauses
begin

section \<open>The complete generation layout determines its citation roots\<close>

lemma generation_citation_root_valuation:
  "(170,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>predecessor. \<exists>h::nat\<Rightarrow>factor_term.
      (\<forall>i\<in>schema_variables (generation_citation_root_schema predecessor). term_formed (h i)) \<and>
      t=rooted_rows_argument (h 0) (h 1) (h 2) \<and>
      (147,generation_syntax_argument (h 0) (h 1) (h 3) (h 4) (h 5) (h 6))\<in>positive_meaning generation_source_system \<and>
      (5,Pair_Term (if predecessor then Pair_Term (h 7) (h 2) else h 2)
        (Pair_Term (if predecessor then h 4 else data_list_term [h 3,h 5,h 6]) (h 8)))
        \<in>positive_meaning bag_comparison_system)"
proof -
  have ordinary: "schema_material_premises S={}"
    if "((170,c),S)\<in>system_clauses generation_retention_system" for c S
    using that by (auto simp: generation_citation_root_schema_def)
  have valuation: "(170,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>c S h. ((170,c),S)\<in>system_clauses generation_retention_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      t=evaluate_pattern h (schema_conclusion S) \<and>
      schema_call_formed generation_retention_system 170 t \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning generation_retention_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  show ?thesis
  proof
    assume "(170,t)\<in>positive_meaning generation_retention_system"
    then obtain c S h where clause: "((170,c),S)\<in>system_clauses generation_retention_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and shape: "t=evaluate_pattern h (schema_conclusion S)"
      and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning generation_retention_system"
      by (simp only: valuation) blast
    have alternatives: "S=generation_citation_root_schema False \<or> S=generation_citation_root_schema True"
      using clause by auto
    have result: "\<exists>predecessor. \<exists>f::nat\<Rightarrow>factor_term.
      (\<forall>i\<in>schema_variables (generation_citation_root_schema predecessor). term_formed (f i)) \<and>
      t=rooted_rows_argument (f 0) (f 1) (f 2) \<and>
      (147,generation_syntax_argument (f 0) (f 1) (f 3) (f 4) (f 5) (f 6))\<in>positive_meaning generation_source_system \<and>
      (5,Pair_Term (if predecessor then Pair_Term (f 7) (f 2) else f 2)
        (Pair_Term (if predecessor then f 4 else data_list_term [f 3,f 5,f 6]) (f 8)))
        \<in>positive_meaning bag_comparison_system"
      if schema: "S=generation_citation_root_schema choice" for choice
    proof -
      have formed: "\<forall>i\<in>schema_variables (generation_citation_root_schema choice). term_formed (h i)"
        using assignment by (simp only: schema)
      have encoded: "t=rooted_rows_argument (h 0) (h 1) (h 2)"
        using shape by (simp add: schema generation_citation_root_schema_def)
      have syntax_read: "(147,generation_syntax_argument (h 0) (h 1) (h 3) (h 4) (h 5) (h 6))
          \<in>positive_meaning generation_source_system"
        using support by (cases choice)
          (auto simp: schema generation_citation_root_schema_def generation_retention_components)
      have selected: "(5,Pair_Term (if choice then Pair_Term (h 7) (h 2) else h 2)
          (Pair_Term (if choice then h 4 else data_list_term [h 3,h 5,h 6]) (h 8)))
          \<in>positive_meaning bag_comparison_system"
        using support by (cases choice)
          (auto simp: schema generation_citation_root_schema_def generation_retention_components)
      show ?thesis by (rule exI[of _ choice], rule exI[of _ h])
        (use formed encoded syntax_read selected in blast)
    qed
    show "\<exists>predecessor. \<exists>h::nat\<Rightarrow>factor_term.
      (\<forall>i\<in>schema_variables (generation_citation_root_schema predecessor). term_formed (h i)) \<and>
      t=rooted_rows_argument (h 0) (h 1) (h 2) \<and>
      (147,generation_syntax_argument (h 0) (h 1) (h 3) (h 4) (h 5) (h 6))\<in>positive_meaning generation_source_system \<and>
      (5,Pair_Term (if predecessor then Pair_Term (h 7) (h 2) else h 2)
        (Pair_Term (if predecessor then h 4 else data_list_term [h 3,h 5,h 6]) (h 8)))
        \<in>positive_meaning bag_comparison_system"
      using alternatives result by blast
  next
    assume "\<exists>predecessor. \<exists>h::nat\<Rightarrow>factor_term.
      (\<forall>i\<in>schema_variables (generation_citation_root_schema predecessor). term_formed (h i)) \<and>
      t=rooted_rows_argument (h 0) (h 1) (h 2) \<and>
      (147,generation_syntax_argument (h 0) (h 1) (h 3) (h 4) (h 5) (h 6))\<in>positive_meaning generation_source_system \<and>
      (5,Pair_Term (if predecessor then Pair_Term (h 7) (h 2) else h 2)
        (Pair_Term (if predecessor then h 4 else data_list_term [h 3,h 5,h 6]) (h 8)))
        \<in>positive_meaning bag_comparison_system"
    then obtain choice h where assignment: "\<forall>i\<in>schema_variables (generation_citation_root_schema choice). term_formed (h i)"
      and shape: "t=rooted_rows_argument (h 0) (h 1) (h 2)"
      and syntax_read: "(147,generation_syntax_argument (h 0) (h 1) (h 3) (h 4) (h 5) (h 6))
        \<in>positive_meaning generation_source_system"
      and selected: "(5,Pair_Term (if choice then Pair_Term (h 7) (h 2) else h 2)
        (Pair_Term (if choice then h 4 else data_list_term [h 3,h 5,h 6]) (h 8)))
        \<in>positive_meaning bag_comparison_system" by blast
    have clause: "((if choice then 1 else 0),generation_citation_root_schema choice)
        \<in>generation_retention_group_clauses 170"
      by (cases choice) (simp_all add: generation_retention_group_clauses_def)
    have support: "\<forall>s d p. (s,d,p)\<in>schema_premises (generation_citation_root_schema choice) \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning generation_retention_system"
      using syntax_read selected by (cases choice)
        (auto simp: generation_citation_root_schema_def generation_retention_components)
    have admitted: "(170,evaluate_pattern h (schema_conclusion (generation_citation_root_schema choice)))
        \<in>positive_meaning generation_retention_system"
      by (rule generation_retention_rule[OF _ clause assignment support]) simp
    show "(170,t)\<in>positive_meaning generation_retention_system"
      using admitted by (simp add: shape generation_citation_root_schema_def)
  qed
qed

lemma generation_citation_root_step:
  assumes syntax_read: "(147,generation_syntax_argument a r l rows pay cause)\<in>positive_meaning generation_source_system"
    and selected: "(5,Pair_Term (if predecessor then Pair_Term s q else q)
      (Pair_Term (if predecessor then rows else data_list_term [l,pay,cause]) rest))\<in>positive_meaning bag_comparison_system"
  shows "(170,rooted_rows_argument a r q)\<in>positive_meaning generation_retention_system"
proof -
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then r else if i=2 then q else if i=3 then l
    else if i=4 then rows else if i=5 then pay else if i=6 then cause else if i=7 then s else rest"
  have formed: "\<forall>i\<in>schema_variables (generation_citation_root_schema predecessor). term_formed (?h i)"
    using schema_call_formed_target[OF positive_meaning_formed[OF syntax_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]]
    by (cases predecessor) (auto simp: generation_citation_root_schema_def schema_variables_def)
  show ?thesis by (simp only: generation_citation_root_valuation, rule exI[of _ predecessor], rule exI[of _ ?h])
    (use formed syntax_read selected in auto)
qed

lemma generation_citation_root_fields:
  "(170,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>a r q l rows pay cause. t=rooted_rows_argument a r q \<and>
      (147,generation_syntax_argument a r l rows pay cause)\<in>positive_meaning generation_source_system \<and>
      (selected_data_member q (data_list_term [l,pay,cause]) \<or>
        (\<exists>s. selected_data_member (Pair_Term s q) rows)))"
proof
  assume "(170,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>a r q l rows pay cause. t=rooted_rows_argument a r q \<and>
      (147,generation_syntax_argument a r l rows pay cause)\<in>positive_meaning generation_source_system \<and>
      (selected_data_member q (data_list_term [l,pay,cause]) \<or> (\<exists>s. selected_data_member (Pair_Term s q) rows))"
    by (simp only: generation_citation_root_valuation) (auto split: if_splits; blast)
next
  assume "\<exists>a r q l rows pay cause. t=rooted_rows_argument a r q \<and>
      (147,generation_syntax_argument a r l rows pay cause)\<in>positive_meaning generation_source_system \<and>
      (selected_data_member q (data_list_term [l,pay,cause]) \<or> (\<exists>s. selected_data_member (Pair_Term s q) rows))"
  then show "(170,t)\<in>positive_meaning generation_retention_system"
    using generation_citation_root_step[of _ _ _ _ _ _ False] generation_citation_root_step[of _ _ _ _ _ _ True]
    by auto
qed

abbreviation generation_citation_root_result :: "factor_term \<Rightarrow> bool" where
  "generation_citation_root_result t \<equiv> \<exists>R a r k.
    t=rooted_rows_argument a (Payload_Term r) (Payload_Term k) \<and>
    artifact_value_presents R a \<and> k\<in>generation_citation_roots R r"

theorem generation_citation_root_sound:
  assumes holds: "(170,t)\<in>positive_meaning generation_retention_system"
  shows "generation_citation_root_result t"
proof -
  obtain a root q l rows pay cause where fields: "t=rooted_rows_argument a root q"
    "(147,generation_syntax_argument a root l rows pay cause)\<in>positive_meaning generation_source_system"
    "selected_data_member q (data_list_term [l,pay,cause]) \<or> (\<exists>s. selected_data_member (Pair_Term s q) rows)"
    using holds by (simp only: generation_citation_root_fields) blast
  obtain R r lr ms payr cr where syntax_read: "artifact_value_presents R a" "root=Payload_Term r"
    "l=Payload_Term lr" "rows=data_list_term (map address_pair_data ms)"
    "pay=Payload_Term payr" "cause=Payload_Term cr" "generation_syntax_at R r lr (set ms) payr cr"
    using fields(2) by (auto simp: generation_syntax_exact)
  obtain k where selected: "q=Payload_Term k" "k\<in>{lr,payr,cr}\<union>rel_ran (set ms)"
    using fields(3) syntax_read(3-6)
    by (auto simp: selected_data_member_exact data_list_term_injective address_pair_data_def rel_ran_def
      simp del: data_list_term.simps; blast)
  have request: "k\<in>generation_citation_roots R r"
    using selected(2) by (simp only: generation_roots_from_syntax(1)[OF syntax_read(7)])
  show ?thesis using fields(1) syntax_read(1,2) selected(1) request by blast
qed

theorem generation_citation_root_complete:
  assumes source: "artifact_value_presents R a" and member: "k\<in>generation_citation_roots R r"
  shows "(170,rooted_rows_argument a (Payload_Term r) (Payload_Term k))\<in>positive_meaning generation_retention_system"
proof -
  obtain l M pay cause where syntax_read: "generation_syntax_at R r l M pay cause"
    and selected: "k\<in>{l,pay,cause}\<union>rel_ran M"
    using member by (auto simp: generation_citation_roots_def)
  obtain pr where family: "family_at R pr M" using syntax_read by (auto simp: generation_syntax_at_def)
  obtain ms where rows: "distinct ms" "set ms=M" using finite_distinct_list[OF family_socket_graph_finite[OF family]] by blast
  have layout: "generation_syntax_at R r l (set ms) pay cause" using syntax_read by (simp only: rows(2))
  have read: "(147,generation_syntax_argument a (Payload_Term r) (Payload_Term l)
      (data_list_term (map address_pair_data ms)) (Payload_Term pay) (Payload_Term cause))\<in>positive_meaning generation_source_system"
    using rows(1) layout by (simp only: generation_syntax_on_rows[OF source]; blast)
  have formed: "term_formed (Payload_Term l)" "term_formed (Payload_Term pay)" "term_formed (Payload_Term cause)"
    "term_formed (data_list_term (map address_pair_data ms))"
    using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  have selection: "selected_data_member (Payload_Term k) (data_list_term [Payload_Term l,Payload_Term pay,Payload_Term cause]) \<or>
      (\<exists>s. selected_data_member (Pair_Term s (Payload_Term k)) (data_list_term (map address_pair_data ms)))"
  proof (cases "k\<in>{l,pay,cause}")
    case True
    have data: "data_elements [Payload_Term l,Payload_Term pay,Payload_Term cause]"
      using formed(1-3) by simp
    have member: "Payload_Term k\<in>set [Payload_Term l,Payload_Term pay,Payload_Term cause]"
      using True by auto
    have chosen: "selected_data_member (Payload_Term k)
        (data_list_term [Payload_Term l,Payload_Term pay,Payload_Term cause])"
      by (simp only: selected_data_member_exact,
          rule exI[of _ "[Payload_Term l,Payload_Term pay,Payload_Term cause]"])
        (use data member in blast)
    show ?thesis by (rule disjI1[OF chosen])
  next
    case False
    obtain s where pair: "(s,k)\<in>set ms" using selected False rows(2) by (auto simp: rel_ran_def)
    have data: "data_elements (map address_pair_data ms)"
      using formed(4) by (auto simp: data_list_term_formed address_pair_data_def)
    have mapped: "address_pair_data (s,k)\<in>image address_pair_data (set ms)" by (rule imageI[OF pair])
    have member: "Pair_Term (Payload_Term s) (Payload_Term k)\<in>set (map address_pair_data ms)"
      using mapped by (simp add: address_pair_data_def)
    have chosen: "selected_data_member (Pair_Term (Payload_Term s) (Payload_Term k))
        (data_list_term (map address_pair_data ms))"
      by (simp only: selected_data_member_exact, rule exI[of _ "map address_pair_data ms"])
        (use data member in blast)
    show ?thesis using chosen by blast
  qed
  show ?thesis using read selection by (simp only: generation_citation_root_fields) blast
qed

theorem generation_citation_root_exact:
  "(170,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_citation_root_result t"
  using generation_citation_root_sound generation_citation_root_complete by blast

corollary generation_citation_root_at_source:
  assumes source: "artifact_value_presents R a"
  shows "(170,rooted_rows_argument a (Payload_Term r) q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>k. q=Payload_Term k \<and> k\<in>generation_citation_roots R r)"
proof
  assume holds: "(170,rooted_rows_argument a (Payload_Term r) q)\<in>positive_meaning generation_retention_system"
  obtain S b v k where shape: "rooted_rows_argument a (Payload_Term r) q=
      rooted_rows_argument b (Payload_Term v) (Payload_Term k)"
    and presented: "artifact_value_presents S b"
    and member: "k\<in>generation_citation_roots S v"
    using generation_citation_root_sound[OF holds] by blast
  have fields: "b=a" "v=r" "q=Payload_Term k" using shape by auto
  have actual: "artifact_value_presents S a" using presented by (simp only: fields(1))
  have same: "S=R" by (rule artifact_value_presents_unique[OF actual source])
  show "\<exists>k. q=Payload_Term k \<and> k\<in>generation_citation_roots R r"
    using fields(3) member by (simp only: same fields(2)) blast
next
  assume "\<exists>k. q=Payload_Term k \<and> k\<in>generation_citation_roots R r"
  then obtain k where shape: "q=Payload_Term k" and member: "k\<in>generation_citation_roots R r" by blast
  show "(170,rooted_rows_argument a (Payload_Term r) q)\<in>positive_meaning generation_retention_system"
    by (simp only: shape) (rule generation_citation_root_complete[OF source member])
qed

text \<open>
  Citation-root recognition depends on the complete record and predecessor
  family layout. It requires neither successful recursive generation reading
  nor interpretation of the selected citation. The two clauses distinguish
  the three direct fields from predecessor endpoints while admitting every
  endpoint in both parts of the same actual layout.
\<close>

end
