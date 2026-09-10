theory Factor_Headed_Material
  imports Factor_Key_Fibres
begin

section \<open>Complete data at one actual carrier occurrence\<close>

definition headed_material_presents ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "headed_material_presents R r e b f \<longleftrightarrow>
    exact_formed R \<and> r\<in>rra_carrier (object_structure R) \<and>
    (\<exists>E B F. e=data_list_term (map address_pair_data E) \<and>
      b=data_list_term (map Payload_Term B) \<and> f=data_list_term (map Payload_Term F) \<and>
      distinct E \<and> set E=headed_incidence (object_structure R) r \<and>
      count_list B=(\<lambda>v. bag_count (object_data R) (r,v)) \<and>
      distinct F \<and> set F={v. (r,v)\<in>functional_bindings (object_data R)})"

lemma payload_term_inj: "inj Payload_Term"
  by (rule injI) simp

lemma distinct_source_mset:
  assumes "distinct xs"
  shows "mset xs=mset ys \<longleftrightarrow> distinct ys \<and> set ys=set xs"
  using assms mset_eq_imp_distinct_iff[of xs ys] mset_eq_setD[of xs ys]
    set_eq_iff_mset_eq_distinct[of xs ys] by auto

lemma headed_material_lists:
  "headed_material_presents R r (data_list_term (map address_pair_data E))
      (data_list_term (map Payload_Term B)) (data_list_term (map Payload_Term F))
    \<longleftrightarrow>
    exact_formed R \<and> r\<in>rra_carrier (object_structure R) \<and>
    distinct E \<and> set E=headed_incidence (object_structure R) r \<and>
    count_list B=(\<lambda>v. bag_count (object_data R) (r,v)) \<and>
    distinct F \<and> set F={v. (r,v)\<in>functional_bindings (object_data R)}"
  by (simp add: headed_material_presents_def data_list_term_injective
    injective_mapped_lists[OF address_pair_data_injective] injective_mapped_lists[OF payload_term_inj])

lemma headed_material_enumeration:
  assumes enumeration: "artifact_enumeration R A E B F"
  shows "headed_material_presents R r e b f \<longleftrightarrow>
    r\<in>rra_carrier (object_structure R) \<and>
    (\<exists>es bs fs. e=data_list_term (map address_pair_data es) \<and>
      b=data_list_term (map Payload_Term bs) \<and> f=data_list_term (map Payload_Term fs) \<and>
      mset (key_values r E)=mset es \<and> mset (key_values r B)=mset bs \<and>
      mset (key_values r F)=mset fs)"
proof -
  have formed: "exact_formed R" and edges: "set E=rra_incidence (object_structure R)"
    and counts: "count_list B=bag_count (object_data R)"
    and bindings: "set F=functional_bindings (object_data R)"
    using artifact_enumeration_material[OF enumeration] by auto
  have distinct: "distinct (key_values r E)" "distinct (key_values r F)"
    using enumeration key_values_distinct by (auto simp: artifact_enumeration_def)
  have heads: "set (key_values r E)=headed_incidence (object_structure R) r"
    using edges by (auto simp: key_values_set headed_incidence_def)
  have local_counts: "count_list (key_values r B)=(\<lambda>v. bag_count (object_data R) (r,v))"
    by (rule ext) (simp add: key_values_count counts)
  have local_bindings: "set (key_values r F)={v. (r,v)\<in>functional_bindings (object_data R)}"
    by (simp add: key_values_set bindings)
  have count_eq: "mset (key_values r B)=mset bs \<longleftrightarrow>
    count_list bs=(\<lambda>v. bag_count (object_data R) (r,v))" for bs
    using local_counts by (auto simp: multiset_eq_iff count_mset fun_eq_iff)
  show ?thesis
    by (simp only: headed_material_presents_def formed simp_thms
      distinct_source_mset[OF distinct(1)] distinct_source_mset[OF distinct(2)]
      heads local_bindings count_eq conj_assoc)
qed

lemma headed_material_empty_data:
  "headed_material_presents R r (data_list_term (map address_pair_data E)) (data_list_term []) (data_list_term [])
    \<longleftrightarrow> exact_formed R \<and> r\<in>rra_carrier (object_structure R) \<and>
      distinct E \<and> headed_incidence (object_structure R) r=set E \<and>
      restrict_basis {r} (object_data R)=empty_basis"
  using headed_material_lists[of R r E "[]" "[]"]
  by (auto simp: empty_restriction_iff fun_eq_iff)

lemma headed_material_payload_leaf:
  "headed_material_presents R r (data_list_term []) (data_list_term []) (data_list_term [Payload_Term v])
    \<longleftrightarrow> exact_formed R \<and> payload_leaf_at R r v"
proof -
  have counts: "count_list ([]::octets list)=(\<lambda>w. bag_count (object_data R) (r,w)) \<longleftrightarrow>
    (\<forall>w. bag_count (object_data R) (r,w)=0)"
    by (auto simp: fun_eq_iff)
  have bindings: "{v}={w. (r,w)\<in>functional_bindings (object_data R)} \<longleftrightarrow>
    (\<forall>w. (r,w)\<in>functional_bindings (object_data R) \<longleftrightarrow> w=v)"
    by auto
  have shape: "headed_material_presents R r (data_list_term []) (data_list_term []) (data_list_term [Payload_Term v])
    \<longleftrightarrow> exact_formed R \<and> r\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) r={} \<and> payload_at R r v"
    using headed_material_lists[of R r "[]" "[]" "[v]", simplified]
    by (simp only: counts bindings payload_at_characterization data_list_term.simps eq_commute)
  show ?thesis using shape payload_leaf_carrier[of R r v]
    by (auto simp: payload_leaf_at_def exact_formed_def)
qed

section \<open>One ordinary clause joins admission, collection, and comparison\<close>

abbreviation headed_material_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "headed_material_argument a r e b f \<equiv> Pair_Term a (Pair_Term r (Pair_Term e (Pair_Term b f)))"

definition headed_material_schema :: "(nat,nat,nat) factor_schema" where
  "headed_material_schema=data_rule
    (Pattern_Pair
      (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1)
        (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))
      (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 5)
        (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))))
    {(0,11,Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1)
        (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))),
     (1,5,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 11))),
     (2,28,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 8))),
     (3,28,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 9))),
     (4,28,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 10))),
     (5,6,Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 5)),
     (6,6,Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 6)),
     (7,6,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 7))}"

definition headed_material_system :: "(nat,nat,nat,nat) schema_system" where
  "headed_material_system=add_view_definition key_fibre_system 29 data_x {(0,headed_material_schema)}"

interpretation headed_material_view: positive_view key_fibre_system 29 data_x "{(0,headed_material_schema)}"
  by (rule positive_view.intro)
    (auto simp: headed_material_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def)

lemma headed_material_system_formed [simp]: "schema_system_formed headed_material_system"
  using headed_material_view.formed by (simp only: headed_material_system_def)

lemma headed_material_definitions [simp]:
  "system_definitions headed_material_system=insert 29 (system_definitions key_fibre_system)"
  by (simp add: headed_material_system_def)

lemma headed_material_call:
  "schema_call_formed headed_material_system d t \<longleftrightarrow>
    d\<in>system_definitions headed_material_system \<and> term_formed t"
  using added_variable_calls[OF key_fibre_system_formed
    headed_material_system_formed[unfolded headed_material_system_def] key_fibre_call]
  by (simp only: headed_material_system_def[symmetric])

theorem headed_material_old_meaning:
  assumes "d\<in>system_definitions key_fibre_system"
  shows "(d,t)\<in>positive_meaning headed_material_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning key_fibre_system"
  using headed_material_view.old_meaning[OF assms, of t] by (simp only: headed_material_system_def)

lemma headed_material_clause [simp]:
  "((29,c),S)\<in>system_clauses headed_material_system \<longleftrightarrow> c=0 \<and> S=headed_material_schema"
  using headed_material_view.no_old_clause[of c S] by (auto simp: headed_material_system_def)

lemma headed_material_components:
  "(11,t)\<in>positive_meaning headed_material_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
  "(5,t)\<in>positive_meaning headed_material_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(6,t)\<in>positive_meaning headed_material_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(28,t)\<in>positive_meaning headed_material_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  using headed_material_old_meaning[of 11 t] key_fibre_old_meaning[of 11 t]
    environment_identity_old_meaning[of 11 t] environment_comparison_artifact_meaning[of 11 t]
    artifact_identity_admission[of t] headed_material_old_meaning[of 5 t]
    key_fibre_bag_meaning[of 5 t] headed_material_old_meaning[of 6 t]
    key_fibre_bag_meaning[of 6 t] headed_material_old_meaning[of 28 t] by auto

theorem headed_material_fields:
  "(29,headed_material_argument (artifact_fields_term a e b f) k x y z)\<in>positive_meaning headed_material_system
    \<longleftrightarrow> (\<exists>u v w. (\<exists>R. artifact_value_presents R (artifact_fields_term a e b f)) \<and>
      selected_data_member k a \<and>
      (28,key_fibre_argument k e u)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k b v)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k f w)\<in>positive_meaning key_fibre_system \<and>
      (6,Pair_Term u x)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term v y)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term w z)\<in>positive_meaning bag_comparison_system)"
proof
  assume holds: "(29,headed_material_argument (artifact_fields_term a e b f) k x y z)
    \<in>positive_meaning headed_material_system"
  have consequence: "(29,headed_material_argument (artifact_fields_term a e b f) k x y z)
    \<in>schema_consequences headed_material_system (positive_meaning headed_material_system)"
    using holds positive_meaning_unfold[of headed_material_system] by blast
  obtain c S h where clause: "((29,c),S)\<in>system_clauses headed_material_system"
    and head: "headed_material_argument (artifact_fields_term a e b f) k x y z=
      evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning headed_material_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=headed_material_schema" using clause by simp
  have fields: "h 0=a" "h 1=e" "h 2=b" "h 3=f" "h 4=k" "h 5=x" "h 6=y" "h 7=z"
    using head by (auto simp: schema headed_material_schema_def)
  have children: "(11,artifact_fields_term a e b f)\<in>positive_meaning headed_material_system"
    "(5,Pair_Term k (Pair_Term a (h 11)))\<in>positive_meaning headed_material_system"
    "(28,key_fibre_argument k e (h 8))\<in>positive_meaning headed_material_system"
    "(28,key_fibre_argument k b (h 9))\<in>positive_meaning headed_material_system"
    "(28,key_fibre_argument k f (h 10))\<in>positive_meaning headed_material_system"
    "(6,Pair_Term (h 8) x)\<in>positive_meaning headed_material_system"
    "(6,Pair_Term (h 9) y)\<in>positive_meaning headed_material_system"
    "(6,Pair_Term (h 10) z)\<in>positive_meaning headed_material_system"
    using support[rule_format, of 0 11 "Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))"]
      support[rule_format, of 1 5 "Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 11))"]
      support[rule_format, of 2 28 "Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 8))"]
      support[rule_format, of 3 28 "Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 9))"]
      support[rule_format, of 4 28 "Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 10))"]
      support[rule_format, of 5 6 "Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 5)"]
      support[rule_format, of 6 6 "Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 6)"]
      support[rule_format, of 7 6 "Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 7)"]
    by (simp_all add: schema headed_material_schema_def fields[simplified])
  show "\<exists>u v w. (\<exists>R. artifact_value_presents R (artifact_fields_term a e b f)) \<and>
      selected_data_member k a \<and>
      (28,key_fibre_argument k e u)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k b v)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k f w)\<in>positive_meaning key_fibre_system \<and>
      (6,Pair_Term u x)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term v y)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term w z)\<in>positive_meaning bag_comparison_system"
    by (intro exI[of _ "h 8"] exI[of _ "h 9"] exI[of _ "h 10"])
      (use children in \<open>auto simp: headed_material_components\<close>)
next
  assume "\<exists>u v w. (\<exists>R. artifact_value_presents R (artifact_fields_term a e b f)) \<and>
      selected_data_member k a \<and>
      (28,key_fibre_argument k e u)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k b v)\<in>positive_meaning key_fibre_system \<and>
      (28,key_fibre_argument k f w)\<in>positive_meaning key_fibre_system \<and>
      (6,Pair_Term u x)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term v y)\<in>positive_meaning bag_comparison_system \<and>
      (6,Pair_Term w z)\<in>positive_meaning bag_comparison_system"
  then obtain u v w R rest where source: "artifact_value_presents R (artifact_fields_term a e b f)"
    and selection: "(5,Pair_Term k (Pair_Term a rest))\<in>positive_meaning bag_comparison_system"
    and fibres: "(28,key_fibre_argument k e u)\<in>positive_meaning key_fibre_system"
      "(28,key_fibre_argument k b v)\<in>positive_meaning key_fibre_system"
      "(28,key_fibre_argument k f w)\<in>positive_meaning key_fibre_system"
    and comparisons: "(6,Pair_Term u x)\<in>positive_meaning bag_comparison_system"
      "(6,Pair_Term v y)\<in>positive_meaning bag_comparison_system"
      "(6,Pair_Term w z)\<in>positive_meaning bag_comparison_system" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f"
    "term_formed k" "term_formed rest" "term_formed u" "term_formed v" "term_formed w"
    "term_formed x" "term_formed y" "term_formed z"
    using artifact_value_presents_formed[OF source]
      schema_call_formed_target[OF positive_meaning_formed[OF selection]]
      schema_call_formed_target[OF positive_meaning_formed[OF comparisons(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF comparisons(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF comparisons(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f
    else if i=4 then k else if i=5 then x else if i=6 then y else if i=7 then z
    else if i=8 then u else if i=9 then v else if i=10 then w else rest"
  have result: "(29,evaluate_pattern ?h (schema_conclusion headed_material_schema))
    \<in>positive_meaning headed_material_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed source selection fibres comparisons in \<open>auto simp: headed_material_schema_def
        schema_variables_def headed_material_call headed_material_components\<close>)
  show "(29,headed_material_argument (artifact_fields_term a e b f) k x y z)
    \<in>positive_meaning headed_material_system"
    using result by (simp add: headed_material_schema_def)
qed

lemma artifact_enumeration_key_fibres:
  assumes enumeration: "artifact_enumeration R A E B F"
    and member: "r\<in>rra_carrier (object_structure R)"
  shows "(28,key_fibre_argument (Payload_Term r) (data_list_term (map incidence_data E)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map address_pair_data (key_values r E))"
    and "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data B)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map Payload_Term (key_values r B))"
    and "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data F)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map Payload_Term (key_values r F))"
proof -
  have rf: "octets_formed r"
    using artifact_enumeration_material(1)[OF enumeration] member by (auto simp: exact_formed_def)
  have terms: "term_formed (artifact_data_term A E B F)" by (rule artifact_data_term_formed[OF enumeration])
  have erows: "formed_key_rows (map (\<lambda>(j,v). (Payload_Term j,address_pair_data v)) E)"
    and brows: "formed_key_rows (map (\<lambda>(j,v). (Payload_Term j,Payload_Term v)) B)"
    and frows: "formed_key_rows (map (\<lambda>(j,v). (Payload_Term j,Payload_Term v)) F)"
    using terms by (auto simp: artifact_data_term_def data_list_term_formed incidence_data_def
      address_pair_data_def split: prod.splits)
  show "(28,key_fibre_argument (Payload_Term r) (data_list_term (map incidence_data E)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map address_pair_data (key_values r E))"
    using key_fibre_mapped_lists[where f=Payload_Term and g=address_pair_data,
      OF payload_term_inj _ _ erows, of r t] rf by (simp add: incidence_data_def[abs_def])
  show "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data B)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map Payload_Term (key_values r B))"
    using key_fibre_mapped_lists[where f=Payload_Term and g=Payload_Term,
      OF payload_term_inj _ _ brows, of r t] rf by (simp add: address_pair_data_def[abs_def])
  show "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data F)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map Payload_Term (key_values r F))"
    using key_fibre_mapped_lists[where f=Payload_Term and g=Payload_Term,
      OF payload_term_inj _ _ frows, of r t] rf by (simp add: address_pair_data_def[abs_def])
qed

lemma artifact_enumeration_fibre_data:
  assumes enumeration: "artifact_enumeration R A E B F"
    and member: "r\<in>rra_carrier (object_structure R)"
  shows "data_elements (map address_pair_data (key_values r E))"
    "data_elements (map Payload_Term (key_values r B))"
    "data_elements (map Payload_Term (key_values r F))"
proof -
  have calls:
    "(28,key_fibre_argument (Payload_Term r) (data_list_term (map incidence_data E))
      (data_list_term (map address_pair_data (key_values r E))))\<in>positive_meaning key_fibre_system"
    "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data B))
      (data_list_term (map Payload_Term (key_values r B))))\<in>positive_meaning key_fibre_system"
    "(28,key_fibre_argument (Payload_Term r) (data_list_term (map address_pair_data F))
      (data_list_term (map Payload_Term (key_values r F))))\<in>positive_meaning key_fibre_system"
    by (simp_all only: artifact_enumeration_key_fibres[OF enumeration member])
  show "data_elements (map address_pair_data (key_values r E))"
    "data_elements (map Payload_Term (key_values r B))"
    "data_elements (map Payload_Term (key_values r F))"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]]
    by (auto simp: data_list_term_formed address_pair_data_def)
qed

theorem headed_material_at_source:
  assumes present: "artifact_value_presents R a"
  shows "(29,headed_material_argument a k e b f)\<in>positive_meaning headed_material_system
    \<longleftrightarrow> (\<exists>r. k=Payload_Term r \<and> headed_material_presents R r e b f)"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F" and shape: "a=artifact_data_term A E B F"
    using present unfolding artifact_value_presents_def by blast
  let ?a="data_list_term (map Payload_Term A)"
  let ?e="data_list_term (map incidence_data E)"
  let ?b="data_list_term (map address_pair_data B)"
  let ?f="data_list_term (map address_pair_data F)"
  let ?ce="\<lambda>r. data_list_term (map address_pair_data (key_values r E))"
  let ?cb="\<lambda>r. data_list_term (map Payload_Term (key_values r B))"
  let ?cf="\<lambda>r. data_list_term (map Payload_Term (key_values r F))"
  have source: "artifact_value_presents R (artifact_fields_term ?a ?e ?b ?f)"
    using present by (simp add: shape artifact_data_term_def)
  have carrier: "selected_data_member k ?a \<longleftrightarrow>
    (\<exists>r. k=Payload_Term r \<and> r\<in>rra_carrier (object_structure R))"
    by (rule artifact_carrier_selection[OF source])
  show ?thesis
  proof
    assume holds: "(29,headed_material_argument a k e b f)\<in>positive_meaning headed_material_system"
    obtain u v w where selected: "selected_data_member k ?a"
      and fibres: "(28,key_fibre_argument k ?e u)\<in>positive_meaning key_fibre_system"
        "(28,key_fibre_argument k ?b v)\<in>positive_meaning key_fibre_system"
        "(28,key_fibre_argument k ?f w)\<in>positive_meaning key_fibre_system"
      and comparisons: "(6,Pair_Term u e)\<in>positive_meaning bag_comparison_system"
        "(6,Pair_Term v b)\<in>positive_meaning bag_comparison_system"
        "(6,Pair_Term w f)\<in>positive_meaning bag_comparison_system"
      using holds by (auto simp: shape artifact_data_term_def headed_material_fields)
    obtain r where root: "k=Payload_Term r" "r\<in>rra_carrier (object_structure R)"
      using selected carrier by blast
    have outputs: "u=?ce r" "v=?cb r" "w=?cf r"
      using fibres by (simp_all add: root(1) artifact_enumeration_key_fibres[OF enumeration root(2)])
    have data: "data_elements (map address_pair_data (key_values r E))"
      "data_elements (map Payload_Term (key_values r B))"
      "data_elements (map Payload_Term (key_values r F))"
      by (rule artifact_enumeration_fibre_data[OF enumeration root(2)])+
    obtain es bs fs where local:
      "e=data_list_term (map address_pair_data es)" "mset (key_values r E)=mset es"
      "b=data_list_term (map Payload_Term bs)" "mset (key_values r B)=mset bs"
      "f=data_list_term (map Payload_Term fs)" "mset (key_values r F)=mset fs"
      using comparisons by (auto simp: outputs bag_comparison_encoded[OF address_pair_data_injective data(1)]
        bag_comparison_encoded[OF payload_term_inj data(2)] bag_comparison_encoded[OF payload_term_inj data(3)])
    have result: "headed_material_presents R r e b f"
      using root(2) local by (auto simp: headed_material_enumeration[OF enumeration])
    show "\<exists>r. k=Payload_Term r \<and> headed_material_presents R r e b f"
      using root(1) result by blast
  next
    assume "\<exists>r. k=Payload_Term r \<and> headed_material_presents R r e b f"
    then obtain r es bs fs where root: "k=Payload_Term r" "r\<in>rra_carrier (object_structure R)"
      and local:
        "e=data_list_term (map address_pair_data es)" "mset (key_values r E)=mset es"
        "b=data_list_term (map Payload_Term bs)" "mset (key_values r B)=mset bs"
        "f=data_list_term (map Payload_Term fs)" "mset (key_values r F)=mset fs"
      by (auto simp: headed_material_enumeration[OF enumeration])
    have selected: "selected_data_member k ?a" using carrier root by blast
    have fibres:
      "(28,key_fibre_argument k ?e (?ce r))\<in>positive_meaning key_fibre_system"
      "(28,key_fibre_argument k ?b (?cb r))\<in>positive_meaning key_fibre_system"
      "(28,key_fibre_argument k ?f (?cf r))\<in>positive_meaning key_fibre_system"
      by (simp_all add: root(1) artifact_enumeration_key_fibres[OF enumeration root(2)])
    have data: "data_elements (map address_pair_data (key_values r E))"
      "data_elements (map Payload_Term (key_values r B))"
      "data_elements (map Payload_Term (key_values r F))"
      by (rule artifact_enumeration_fibre_data[OF enumeration root(2)])+
    have comparisons:
      "(6,Pair_Term (?ce r) e)\<in>positive_meaning bag_comparison_system"
      "(6,Pair_Term (?cb r) b)\<in>positive_meaning bag_comparison_system"
      "(6,Pair_Term (?cf r) f)\<in>positive_meaning bag_comparison_system"
      using local by (auto simp: bag_comparison_encoded[OF address_pair_data_injective data(1)]
        bag_comparison_encoded[OF payload_term_inj data(2)] bag_comparison_encoded[OF payload_term_inj data(3)])
    show "(29,headed_material_argument a k e b f)\<in>positive_meaning headed_material_system"
      by (simp only: shape artifact_data_term_def headed_material_fields)
        (intro exI[of _ "?ce r"] exI[of _ "?cb r"] exI[of _ "?cf r"];
          use source selected fibres comparisons in blast)
  qed
qed

theorem headed_material_exact:
  "(29,t)\<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>R a r e b f. t=headed_material_argument a (Payload_Term r) e b f \<and>
      artifact_value_presents R a \<and> headed_material_presents R r e b f)"
proof
  assume holds: "(29,t)\<in>positive_meaning headed_material_system"
  have consequence: "(29,t)\<in>schema_consequences headed_material_system (positive_meaning headed_material_system)"
    using holds positive_meaning_unfold[of headed_material_system] by blast
  obtain c S h where clause: "((29,c),S)\<in>system_clauses headed_material_system"
    and head: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning headed_material_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=headed_material_schema" using clause by simp
  let ?a="artifact_fields_term (h 0) (h 1) (h 2) (h 3)"
  have shape: "t=headed_material_argument ?a (h 4) (h 5) (h 6) (h 7)"
    using head by (simp add: schema headed_material_schema_def)
  obtain R where source: "artifact_value_presents R ?a"
    using support[rule_format, of 0 11 "Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1)
        (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))"]
    by (auto simp: schema headed_material_schema_def headed_material_components)
  obtain r where root: "h 4=Payload_Term r" and local: "headed_material_presents R r (h 5) (h 6) (h 7)"
    using holds by (simp only: shape headed_material_at_source[OF source]) blast
  show "\<exists>R a r e b f. t=headed_material_argument a (Payload_Term r) e b f \<and>
      artifact_value_presents R a \<and> headed_material_presents R r e b f"
    using source shape root local by blast
next
  assume "\<exists>R a r e b f. t=headed_material_argument a (Payload_Term r) e b f \<and>
      artifact_value_presents R a \<and> headed_material_presents R r e b f"
  then obtain R a r e b f where shape: "t=headed_material_argument a (Payload_Term r) e b f"
    and source: "artifact_value_presents R a" and local: "headed_material_presents R r e b f" by blast
  show "(29,t)\<in>positive_meaning headed_material_system"
    using local by (simp add: shape headed_material_at_source[OF source])
qed

corollary headed_material_presentation_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R a'"
  shows "(29,headed_material_argument a k e b f)\<in>positive_meaning headed_material_system \<longleftrightarrow>
    (29,headed_material_argument a' k e b f)\<in>positive_meaning headed_material_system"
  by (simp only: headed_material_at_source[OF assms(1)] headed_material_at_source[OF assms(2)])

corollary headed_material_no_data:
  assumes source: "artifact_value_presents R a"
  shows "(29,headed_material_argument a (Payload_Term r)
      (data_list_term (map address_pair_data E)) (data_list_term []) (data_list_term []))
      \<in>positive_meaning headed_material_system \<longleftrightarrow>
    r\<in>rra_carrier (object_structure R) \<and> distinct E \<and>
      headed_incidence (object_structure R) r=set E \<and> restrict_basis {r} (object_data R)=empty_basis"
  using artifact_value_presents_formed[OF source]
  by (simp add: headed_material_at_source[OF source] headed_material_empty_data[simplified])

corollary headed_material_leaf:
  assumes source: "artifact_value_presents R a"
  shows "(29,headed_material_argument a (Payload_Term r)
      (data_list_term []) (data_list_term []) (data_list_term [Payload_Term v]))
      \<in>positive_meaning headed_material_system \<longleftrightarrow> payload_leaf_at R r v"
  using artifact_value_presents_formed[OF source]
  by (simp add: headed_material_at_source[OF source] headed_material_payload_leaf[simplified])

corollary headed_material_leaf_fields:
  assumes source: "artifact_value_presents R a"
  shows "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [v]))
    \<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>r b. k=Payload_Term r \<and> v=Payload_Term b \<and> payload_leaf_at R r b)"
proof
  assume holds: "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [v]))
    \<in>positive_meaning headed_material_system"
  obtain r where root: "k=Payload_Term r"
    and present: "headed_material_presents R r (Payload_Term []) (Payload_Term []) (data_list_term [v])"
    using holds by (auto simp: headed_material_at_source[OF source])
  obtain F where field: "data_list_term [v]=data_list_term (map Payload_Term F)"
    using present by (auto simp only: headed_material_presents_def)
  have "map Payload_Term F=[v]" using field by (simp only: data_list_term_injective)
  then obtain b where literal: "v=Payload_Term b" by (auto simp: map_eq_Cons_conv)
  have leaf: "payload_leaf_at R r b"
    using holds by (simp add: root literal headed_material_leaf[OF source, simplified])
  show "\<exists>r b. k=Payload_Term r \<and> v=Payload_Term b \<and> payload_leaf_at R r b"
    using root literal leaf by blast
next
  assume "\<exists>r b. k=Payload_Term r \<and> v=Payload_Term b \<and> payload_leaf_at R r b"
  then show "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [v]))
    \<in>positive_meaning headed_material_system"
    by (auto simp: headed_material_leaf[OF source, simplified])
qed

section \<open>One closed native checker serves every future formed input\<close>

theorem native_headed_material_checking:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>R a r e b f. t=headed_material_argument a (Payload_Term r) e b f \<and>
            artifact_value_presents R a \<and> headed_material_presents R r e b f))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions headed_material_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed headed_material_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning headed_material_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF headed_material_system_formed] by blast
  have member: "29\<in>system_definitions headed_material_system" by simp
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 29"], intro conjI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
  next
    fix t assume tf: "term_formed t"
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g 29) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed headed_material_system 29 t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (29,t)\<in>positive_meaning headed_material_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 29) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>R a r e b f. t=headed_material_argument a (Payload_Term r) e b f \<and>
          artifact_value_presents R a \<and> headed_material_presents R r e b f))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member headed_material_exact[of t] in \<open>auto simp: headed_material_call\<close>)
  qed
qed

text \<open>
  The source argument is a complete admitted artifact presentation. The
  selected root must occur in its actual carrier. Three calls collect every
  headed incidence, counted attachment, and functional attachment at that
  exact root. Three separate bag comparisons check the complete results,
  permitting every enumeration order without dropping repeated entries.
  All twelve variables, including the carrier selection remainder and
  three collected lists, belong to the ordinary finite assignment.

  The resulting native checker has an exact contract on every input term.
  Its package is fixed before future arguments are supplied, and each
  actual application preserves the canonical program environment. The
  finite program has thirty definitions and fifty-four clauses.

  This is headed material, not a replacement for the complete relative
  footprint. The whole source remains present, including incoming
  incidence and material at other heads. Those entries neither enter
  this projection nor invalidate a local grammar merely by existing.
  Empty data and a functional payload leaf agree exactly with the existing
  grammar conditions. Record paths, citation interpretation, and the
  higher native admission protocol still require their own checks.
\<close>

end
