theory Factor_Root_Family_Reading
  imports Factor_Located_List
begin

section \<open>Complete lists recover the actual root family\<close>

lemma native_root_family_from_list:
  assumes formed: "environment_formed E" and source: "artifact_at E u R"
    and family: "family_at R r (set xs)" and separate: "distinct xs"
    and reading: "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
  shows "native_root_family_at E u r (set (zip (map fst xs) ds))"
    and "rel_ran (set (zip (map fst xs) ds))=set ds"
proof -
  let ?Q="set (zip (map fst xs) ds)"
  have len: "length xs=length ds" using list_all2_lengthD[OF reading] by simp
  have keys: "distinct (map fst xs)" using separate family by (simp add: distinct_keys_iff family_at_def)
  have functional: "single_valued ?Q" by (rule single_valued_zip[OF keys])
  have domain: "rel_dom ?Q=rel_dom (set xs)"
    using zip_domain[of "map fst xs" ds] len by (simp add: rel_dom_image)
  have children: "\<forall>s a. (s,a)\<in>set xs \<longrightarrow>
    (\<exists>d. (s,d)\<in>?Q \<and> located_at E u a (fst d) (snd d))"
  proof (intro allI impI)
    fix s a assume member: "(s,a)\<in>set xs"
    obtain i where index: "i<length xs" "xs!i=(s,a)" using member by (auto simp: in_set_conv_nth)
    have paired: "(s,ds!i)\<in>?Q"
      by (simp only: in_set_zip; rule exI[of _ i]) (use index len in auto)
    have loc: "located_at E u a (fst (ds!i)) (snd (ds!i))"
      using list_all2_nthD[OF reading, of i] index by simp
    show "\<exists>d. (s,d)\<in>?Q \<and> located_at E u a (fst d) (snd d)" using paired loc by blast
  qed
  show "native_root_family_at E u r ?Q"
    unfolding native_root_family_at_def
    by (intro conjI formed exI[of _ R] exI[of _ "set xs"])
      (use source family functional domain children in auto)
  show "rel_ran ?Q=set ds" by (rule zip_range) (simp add: len)
qed

lemma native_root_family_list:
  assumes raw: "native_root_family_at E u r Q"
  shows "\<exists>R xs ds. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
    list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds \<and> rel_ran Q=set ds"
proof -
  obtain R M where formed: "environment_formed E" and source: "artifact_at E u R"
    and family: "family_at R r M"
    and children: "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>d. (s,d)\<in>Q \<and> located_at E u a (fst d) (snd d))"
    using raw by (auto simp: native_root_family_at_def)
  obtain xs where rows: "set xs=M" "distinct xs"
    using finite_distinct_list[OF family_socket_graph_finite[OF family]] by blast
  have covered: "\<forall>a\<in>set (map snd xs). \<exists>d. located_at E u a (fst d) (snd d)"
    using children rows(1) by force
  obtain ds where backwards: "list_all2 (\<lambda>d a. located_at E u a (fst d) (snd d)) ds (map snd xs)"
    using iffD1[OF list_all2_exists_left covered] by blast
  have reading: "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    using backwards by (auto simp: list_all2_conv_all_nth)
  have actual: "family_at R r (set xs)" using family rows(1) by simp
  have recovered: "native_root_family_at E u r (set (zip (map fst xs) ds))"
    by (rule native_root_family_from_list(1)[OF formed source actual rows(2) reading])
  have same: "Q=set (zip (map fst xs) ds)" by (rule native_root_family_unique[OF raw recovered])
  have range: "rel_ran Q=set ds"
    using native_root_family_from_list(2)[OF formed source actual rows(2) reading] same by simp
  show ?thesis by (rule exI[of _ R], rule exI[of _ xs], rule exI[of _ ds])
    (use source rows actual reading range in blast)
qed

section \<open>One actual family supplies every reference occurrence\<close>

abbreviation root_family_reading_result :: "factor_term \<Rightarrow> bool" where
  "root_family_reading_result z \<equiv> \<exists>E e u r R xs ds.
    z=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)) \<and>
    environment_value_presents E e \<and> artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
    list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"

definition root_family_reading_schema :: "(nat,nat,nat) factor_schema" where
  "root_family_reading_schema=data_rule (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (1,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z) (Pattern_Variable 5)),
     (2,59,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)),
     (3,78,Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 7)),
     (4,51,Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 6)),
     (5,59,Pattern_Pair (Pattern_Variable 7) data_w)}"

definition root_family_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "root_family_reading_system=add_view_definition located_list_system 79 data_x {(0,root_family_reading_schema)}"

lemma root_family_reading_system_formed [simp]: "schema_system_formed root_family_reading_system"
  unfolding root_family_reading_system_def
  by (rule add_recursive_definition_formed[OF located_list_system_formed])
    (auto simp: root_family_reading_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma root_family_reading_definitions [simp]:
  "system_definitions root_family_reading_system=insert 79 (system_definitions located_list_system)"
  by (simp add: root_family_reading_system_def)

lemma root_family_reading_call:
  "schema_call_formed root_family_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions root_family_reading_system \<and> term_formed t"
  using added_variable_calls[OF located_list_system_formed
    root_family_reading_system_formed[unfolded root_family_reading_system_def] located_list_call]
  by (simp only: root_family_reading_system_def[symmetric])

lemma root_family_reading_old_meaning:
  assumes "d\<in>system_definitions located_list_system"
  shows "(d,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning located_list_system"
  using added_definition_preserves_old(2)[OF located_list_system_formed
    root_family_reading_system_formed[unfolded root_family_reading_system_def], of d t] assms
  by (auto simp: root_family_reading_system_def)

lemma root_family_reading_clause [simp]:
  "((79,c),S)\<in>system_clauses root_family_reading_system \<longleftrightarrow> (c,S)\<in>{(0,root_family_reading_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses located_list_system \<Longrightarrow>
    d\<in>system_definitions located_list_system" for d c S
    using located_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((79,c),S)\<notin>system_clauses located_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: root_family_reading_system_def)
qed

lemma root_family_reading_previous_meaning:
  assumes "d\<in>system_definitions package_closure_admission_system"
  shows "(d,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_closure_admission_system"
  using root_family_reading_old_meaning[of d t] located_list_old_meaning[OF assms, of t] assms by auto

lemma root_family_reading_components:
  "(37,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(32,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(59,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(78,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (78,t)\<in>positive_meaning located_list_system"
  "(51,t)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  using root_family_reading_previous_meaning[of 37 t] package_closure_admission_old_meaning[of 37 t]
    definition_callee_list_old_meaning[of 37 t] definition_callee_inclusion_components(2)[of t]
    root_family_reading_previous_meaning[of 32 t] package_closure_admission_old_meaning[of 32 t]
    definition_callee_list_old_meaning[of 32 t] definition_callee_inclusion_components(4)[of t]
    root_family_reading_previous_meaning[of 59 t] package_closure_admission_old_meaning[of 59 t]
    definition_callee_list_old_meaning[of 59 t] definition_callee_inclusion_components(5)[of t]
    root_family_reading_old_meaning[of 78 t]
    root_family_reading_previous_meaning[of 51 t] package_closure_admission_old_meaning[of 51 t]
    definition_callee_list_old_meaning[of 51 t] definition_callee_inclusion_old_meaning[of 51 t]
    schema_callee_list_old_meaning[of 51 t] schema_callee_inclusion_components(3)[of t] by auto

lemma root_family_reading_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and family: "(32,rooted_rows_argument a r rows)\<in>positive_meaning family_admission_system"
    and roots: "(59,Pair_Term rows refs)\<in>positive_meaning row_values_system"
    and locations: "(78,Pair_Term (Pair_Term e u) pairs)\<in>positive_meaning located_list_system"
    and keys: "(51,Pair_Term pairs refs)\<in>positive_meaning row_keys_system"
    and sites: "(59,Pair_Term pairs ds)\<in>positive_meaning row_values_system"
  shows "(79,citation_observation_argument e u r ds)\<in>positive_meaning root_family_reading_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed ds"
    "term_formed a" "term_formed rows" "term_formed refs" "term_formed pairs"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF family]]
      schema_call_formed_target[OF positive_meaning_formed[OF keys]]
      schema_call_formed_target[OF positive_meaning_formed[OF sites]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then ds
    else if n=4 then a else if n=5 then rows else if n=6 then refs else pairs"
  have result: "(79,evaluate_pattern ?h (schema_conclusion root_family_reading_schema))
      \<in>positive_meaning root_family_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: root_family_reading_schema_def schema_variables_def
        root_family_reading_call root_family_reading_components\<close>)
  show ?thesis using result by (simp add: root_family_reading_schema_def)
qed

theorem root_family_reading_sound:
  assumes holds: "(79,z)\<in>positive_meaning root_family_reading_system"
  shows "root_family_reading_result z"
proof -
  have consequence: "(79,z)\<in>schema_consequences root_family_reading_system (positive_meaning root_family_reading_system)"
    using holds positive_meaning_unfold[of root_family_reading_system] by blast
  obtain n S h where clause: "((79,n),S)\<in>system_clauses root_family_reading_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning root_family_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=root_family_reading_schema" using clause by simp
  have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
    "(32,rooted_rows_argument (h 4) (h 2) (h 5))\<in>positive_meaning family_admission_system"
    "(59,Pair_Term (h 5) (h 6))\<in>positive_meaning row_values_system"
    "(78,Pair_Term (Pair_Term (h 0) (h 1)) (h 7))\<in>positive_meaning located_list_system"
    "(51,Pair_Term (h 7) (h 6))\<in>positive_meaning row_keys_system"
    "(59,Pair_Term (h 7) (h 3))\<in>positive_meaning row_values_system"
    using support by (auto simp: schema root_family_reading_schema_def root_family_reading_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 4)"
    using calls(1) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r xs where family: "h 2=Payload_Term r" "h 5=data_list_term (map address_pair_data xs)"
    "distinct xs" "family_at R r (set xs)"
    using calls(2) by (simp only: family_admission_at_source[OF source(4)]) blast
  have roots: "h 6=data_list_term (map Payload_Term (map snd xs))"
    using calls(3) by (simp only: family(2) address_row_values)
  obtain zs where pairs: "h 7=pair_list_term zs" "h 6=data_list_term (map fst zs)"
    using calls(5) by (auto simp: row_keys_exact)
  have locations: "\<forall>(a,d)\<in>set zs. \<exists>b v c. a=Payload_Term b \<and> d=site_data_term v c \<and> located_at E u b v c"
    using calls(4) by (simp only: source(2) pairs(1) located_list_on_rows[OF source(1)])
  let ?f="\<lambda>(a,d). (Payload_Term a,definition_site_value d)"
  let ?P="\<lambda>(a,d). located_at E u a (fst d) (snd d)"
  have typed: "\<forall>z\<in>set zs. \<exists>x. z=?f x \<and> ?P x"
  proof (intro ballI)
    fix z assume member: "z\<in>set zs"
    obtain a d where shape: "z=(a,d)" by (cases z)
    obtain b v c where parts: "a=Payload_Term b" "d=site_data_term v c" "located_at E u b v c"
      using locations member shape by blast
    show "\<exists>x. z=?f x \<and> ?P x"
      by (rule exI[of _ "(b,(v,c))"]) (use shape parts in simp)
  qed
  obtain ss where decoded: "zs=map ?f ss" "\<forall>x\<in>set ss. ?P x"
    using iffD1[OF list_range_restricted_witnesses typed] by blast
  have encoded_keys: "map Payload_Term (map fst ss)=map Payload_Term (map snd xs)"
    using pairs(2) roots by (simp add: decoded(1) data_list_term_injective comp_def split_def)
  have keys: "map fst ss=map snd xs"
    using encoded_keys by (simp only: injective_mapped_lists[OF payload_term_inj])
  have projection: "h 3=data_list_term (map snd zs)"
    using calls(6) by (simp only: pairs(1) row_values_at_rows)
  have sites: "h 3=data_list_term (map (\<lambda>d. definition_site_value d) (map snd ss))"
    using projection by (simp add: decoded(1) comp_def split_def)
  have located: "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map fst ss) (map snd ss)"
    using decoded(2) by (auto simp: list_all2_iff zip_map_fst_snd)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
      rule exI[of _ R], rule exI[of _ xs], rule exI[of _ "map snd ss"])
      (use source family sites located keys conclusion in \<open>simp add: schema root_family_reading_schema_def\<close>)
qed

theorem root_family_reading_complete:
  assumes source: "environment_value_presents E e" and artifact: "artifact_at E u R"
    and separate: "distinct xs" and family: "family_at R r (set xs)"
    and reading: "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
  shows "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
    (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef artifact by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  let ?rows="data_list_term (map address_pair_data xs)"
  let ?roots="data_list_term (map Payload_Term (map snd xs))"
  let ?ss="zip (map snd xs) ds"
  let ?pairs="pair_list_term (map (\<lambda>(b,d). (Payload_Term b,definition_site_value d)) ?ss)"
  let ?sites="data_list_term (map (\<lambda>d. definition_site_value d) ds)"
  have len: "length (map snd xs)=length ds" by (rule list_all2_lengthD[OF reading])
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using source artifact presented by (auto simp: artifact_lookup_exact)
  have fam: "(32,rooted_rows_argument a (Payload_Term r) ?rows)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_rows[OF presented]) (use separate family in blast)
  have rows_formed: "term_formed ?rows"
    using schema_call_formed_target[OF positive_meaning_formed[OF fam]] by auto
  have roots: "(59,Pair_Term ?rows ?roots)\<in>positive_meaning row_values_system"
    by (simp only: address_row_values) (use rows_formed in blast)
  have locations: "(78,Pair_Term (Pair_Term e (use_data_term u)) ?pairs)\<in>positive_meaning located_list_system"
    by (simp only: located_list_at_rows[OF source]) (use reading in \<open>simp add: list_all2_iff\<close>)
  have pairs_formed: "term_formed ?pairs"
    using schema_call_formed_target[OF positive_meaning_formed[OF locations]] by auto
  have keys: "(51,Pair_Term ?pairs ?roots)\<in>positive_meaning row_keys_system"
  proof -
    have projection: "map fst (map (\<lambda>(b,d). (Payload_Term b,definition_site_value d)) ?ss)
      =map Payload_Term (map fst ?ss)" by (simp add: comp_def split_def)
    show ?thesis by (simp only: row_keys_at_rows projection map_fst_zip[OF len])
      (use pairs_formed in simp)
  qed
  have sites: "(59,Pair_Term ?pairs ?sites)\<in>positive_meaning row_values_system"
  proof -
    have projection: "map snd (map (\<lambda>(b,d). (Payload_Term b,definition_site_value d)) ?ss)
      =map (\<lambda>d. definition_site_value d) (map snd ?ss)" by (simp add: comp_def split_def)
    show ?thesis by (simp only: row_values_at_rows projection map_snd_zip[OF len])
      (use pairs_formed in simp)
  qed
  show ?thesis by (rule root_family_reading_step[OF lookup fam roots locations keys sites])
qed

theorem root_family_reading_exact:
  "(79,z)\<in>positive_meaning root_family_reading_system \<longleftrightarrow> root_family_reading_result z"
proof
  show "(79,z)\<in>positive_meaning root_family_reading_system \<Longrightarrow> root_family_reading_result z"
    by (rule root_family_reading_sound)
next
  assume "root_family_reading_result z"
  then obtain E e u r R xs ds where parts:
    "z=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
    "environment_value_presents E e" "artifact_at E u R" "distinct xs" "family_at R r (set xs)"
    "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds" by auto
  show "(79,z)\<in>positive_meaning root_family_reading_system"
    using root_family_reading_complete[OF parts(2-6)] by (simp only: parts(1))
qed

corollary root_family_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(79,citation_observation_argument e u r w)\<in>positive_meaning root_family_reading_system \<longleftrightarrow>
    (\<exists>v b R xs ds. u=use_data_term v \<and> r=Payload_Term b \<and>
      w=data_list_term (map (\<lambda>d. definition_site_value d) ds) \<and> artifact_at E v R \<and>
      distinct xs \<and> family_at R b (set xs) \<and>
      list_all2 (\<lambda>a d. located_at E v a (fst d) (snd d)) (map snd xs) ds)"
proof
  assume holds: "(79,citation_observation_argument e u r w)\<in>positive_meaning root_family_reading_system"
  obtain F v b R xs ds where parts: "environment_value_presents F e" "u=use_data_term v" "r=Payload_Term b"
    "w=data_list_term (map (\<lambda>d. definition_site_value d) ds)" "artifact_at F v R" "distinct xs"
    "family_at R b (set xs)" "list_all2 (\<lambda>a d. located_at F v a (fst d) (snd d)) (map snd xs) ds"
    using holds by (simp only: root_family_reading_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>v b R xs ds. u=use_data_term v \<and> r=Payload_Term b \<and>
    w=data_list_term (map (\<lambda>d. definition_site_value d) ds) \<and> artifact_at E v R \<and>
    distinct xs \<and> family_at R b (set xs) \<and>
    list_all2 (\<lambda>a d. located_at E v a (fst d) (snd d)) (map snd xs) ds"
    using parts same by blast
next
  assume "\<exists>v b R xs ds. u=use_data_term v \<and> r=Payload_Term b \<and>
    w=data_list_term (map (\<lambda>d. definition_site_value d) ds) \<and> artifact_at E v R \<and>
    distinct xs \<and> family_at R b (set xs) \<and>
    list_all2 (\<lambda>a d. located_at E v a (fst d) (snd d)) (map snd xs) ds"
  then obtain v b R xs ds where parts: "u=use_data_term v" "r=Payload_Term b"
    "w=data_list_term (map (\<lambda>d. definition_site_value d) ds)" "artifact_at E v R" "distinct xs"
    "family_at R b (set xs)" "list_all2 (\<lambda>a d. located_at E v a (fst d) (snd d)) (map snd xs) ds" by blast
  show "(79,citation_observation_argument e u r w)\<in>positive_meaning root_family_reading_system"
    using root_family_reading_complete[OF source parts(4-7)] by (simp only: parts(1-3))
qed

corollary root_family_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system
    \<longleftrightarrow> (\<exists>R xs. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
      list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds)"
  by (simp only: root_family_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
    factor_term.inject data_list_term_injective injective_mapped_lists[OF definition_site_value_injective]) blast

corollary root_family_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(79,citation_observation_argument e u r w)\<in>positive_meaning root_family_reading_system \<longleftrightarrow>
    (79,citation_observation_argument f u r w)\<in>positive_meaning root_family_reading_system"
  by (simp only: root_family_reading_at_source[OF assms(1)] root_family_reading_at_source[OF assms(2)])

corollary root_family_reading_recovers:
  assumes source: "environment_value_presents E e"
    and holds: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
  shows "\<exists>Q. native_root_family_at E u r Q \<and> rel_ran Q=set ds"
proof -
  obtain R xs where parts: "artifact_at E u R" "distinct xs" "family_at R r (set xs)"
    "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    using holds by (simp only: root_family_reading_on_values[OF source]) blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  show ?thesis using native_root_family_from_list[OF ef parts(1,3,2,4)] by blast
qed

corollary root_family_reading_total:
  assumes source: "environment_value_presents E e" and raw: "native_root_family_at E u r Q"
  shows "\<exists>ds. (79,citation_observation_argument e (use_data_term u) (Payload_Term r)
    (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system \<and> rel_ran Q=set ds"
  using native_root_family_list[OF raw] root_family_reading_complete[OF source] by blast

corollary root_family_reading_range_unique:
  assumes source: "environment_value_presents E e"
    and first: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
    and second: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) es)))\<in>positive_meaning root_family_reading_system"
  shows "set ds=set es"
  using root_family_reading_recovers[OF source first] root_family_reading_recovers[OF source second]
    native_root_family_unique by metis

corollary root_family_reading_length:
  assumes source: "environment_value_presents E e" and artifact: "artifact_at E u R" and family: "family_at R r M"
    and holds: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
  shows "length ds=card M"
proof -
  obtain A xs where parts: "artifact_at E u A" "distinct xs" "family_at A r (set xs)"
    "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    using holds by (simp only: root_family_reading_on_values[OF source]) blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have same: "A=R" by (rule environment_artifact_unique[OF ef parts(1) artifact])
  have actual: "family_at R r (set xs)" using parts(3) same by simp
  have graph: "set xs=M" by (rule family_at_unique[OF actual family])
  show ?thesis using list_all2_lengthD[OF parts(4)] distinct_card[OF parts(2)] graph by simp
qed

corollary root_family_reading_empty:
  assumes source: "environment_value_presents E e"
  shows "(79,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term []))
      \<in>positive_meaning root_family_reading_system \<longleftrightarrow> (\<exists>R. artifact_at E u R \<and> family_at R r {})"
  using root_family_reading_on_values[OF source, of u r "[]"] by simp

text \<open>
  The actual artifact and complete root-family graph are read before projecting
  their reference endpoints. One complete list pairs every endpoint with its
  located destination. Existing key and value projections constrain both sides
  of this same list; no row can be omitted or added.

  Every distinct enumeration of the actual family and its corresponding
  destination list is admitted. The output has one entry per socket, including
  repeated destinations at distinct sockets. Its length and recovered root set
  are determined by the actual family. Equality of output sets alone is not the
  reader's completeness contract: occurrence counts are preserved.

  The proof reconstructs the uniquely determined raw root family from these
  complete lists. The native clause needs no stored root-family encoding,
  arbitrary environmental position scan, or new mapping primitive. Even an
  empty family retains the actual artifact and family-root checks.
\<close>

end
