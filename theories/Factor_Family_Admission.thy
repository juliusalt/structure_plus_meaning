theory Factor_Family_Admission
  imports Factor_Headed_Material
begin

section \<open>Rooted socket rows retain their exact addresses\<close>

abbreviation rooted_rows_argument :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "rooted_rows_argument a r m \<equiv> Pair_Term (Pair_Term a r) m"

abbreviation headed_material_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "headed_material_pattern a r e b f \<equiv>
    Pattern_Pair a (Pattern_Pair r (Pattern_Pair e (Pattern_Pair b f)))"

lemma headed_rows_data:
  assumes formed: "exact_formed R" and rows: "set xs\<subseteq>headed_incidence (object_structure R) r"
  shows "data_elements (map address_pair_data xs)"
  using formed rows by (auto simp: address_pair_data_def exact_formed_def object_formed_def
    rra_formed_def headed_incidence_def)

lemma headed_material_empty_presents:
  "headed_material_presents R r m (data_list_term []) (data_list_term []) \<longleftrightarrow>
    (\<exists>xs. m=data_list_term (map address_pair_data xs) \<and> exact_formed R \<and>
      r\<in>rra_carrier (object_structure R) \<and> distinct xs \<and>
      headed_incidence (object_structure R) r=set xs \<and>
      restrict_basis {r} (object_data R)=empty_basis)"
proof
  assume read: "headed_material_presents R r m (data_list_term []) (data_list_term [])"
  obtain xs where rows: "m=data_list_term (map address_pair_data xs)"
    using read by (auto simp: headed_material_presents_def)
  show "\<exists>xs. m=data_list_term (map address_pair_data xs) \<and> exact_formed R \<and>
      r\<in>rra_carrier (object_structure R) \<and> distinct xs \<and>
      headed_incidence (object_structure R) r=set xs \<and>
      restrict_basis {r} (object_data R)=empty_basis"
    by (rule exI[of _ xs]) (use read rows in \<open>simp add: headed_material_empty_data[simplified]\<close>)
next
  assume "\<exists>xs. m=data_list_term (map address_pair_data xs) \<and> exact_formed R \<and>
      r\<in>rra_carrier (object_structure R) \<and> distinct xs \<and>
      headed_incidence (object_structure R) r=set xs \<and>
      restrict_basis {r} (object_data R)=empty_basis"
  then show "headed_material_presents R r m (data_list_term []) (data_list_term [])"
    by (auto simp: headed_material_empty_data[simplified])
qed

lemma headed_material_empty_exact:
  "(29,headed_material_argument a k m (data_list_term []) (data_list_term []))
    \<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>R r xs. artifact_value_presents R a \<and> k=Payload_Term r \<and>
      m=data_list_term (map address_pair_data xs) \<and> r\<in>rra_carrier (object_structure R) \<and>
      distinct xs \<and> headed_incidence (object_structure R) r=set xs \<and>
      restrict_basis {r} (object_data R)=empty_basis)"
  using artifact_value_presents_formed
  by (auto simp: headed_material_exact headed_material_empty_presents[simplified]; blast)

lemma headed_material_inequality:
  "(3,Pair_Term x y)\<in>positive_meaning headed_material_system \<longleftrightarrow>
    term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y \<and> x\<noteq>y"
  using headed_material_old_meaning[of 3 "Pair_Term x y"] key_fibre_inequality[of x y] by auto

lemma headed_material_keyed:
  "(21,t)\<in>positive_meaning headed_material_system \<longleftrightarrow>
    (21,t)\<in>positive_meaning keyed_list_system"
  using headed_material_old_meaning[of 21 t] key_fibre_old_meaning[of 21 t]
    environment_identity_previous_meaning[of 21 t] environment_admission_previous_meaning[of 21 t]
    binding_entries_previous_meaning[of 21 t] binding_entry_keyed_meaning[of 21 t] by auto

lemma keyed_address_rows:
  assumes "data_elements (map address_pair_data xs)"
  shows "(21,data_list_term (map address_pair_data xs))\<in>positive_meaning keyed_list_system
    \<longleftrightarrow> distinct xs \<and> single_valued (set xs)"
proof (rule keyed_list_encoded_keys[where R="\<lambda>z t. t=address_pair_data z" and f=Payload_Term,
    OF _ assms payload_term_inj])
  show "list_all2 (\<lambda>z t. t=address_pair_data z) xs (map address_pair_data xs)"
    by (simp add: list_all2_function)
  show "\<And>z t. t=address_pair_data z \<Longrightarrow> \<exists>v. t=Pair_Term (Payload_Term (fst z)) v"
    by (simp add: address_pair_data_def)
qed

section \<open>Every family socket is separate from the root and has empty local material\<close>

definition family_socket_schema :: "(nat,nat,nat) factor_schema" where
  "family_socket_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,29,headed_material_pattern data_x data_z (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload [])),
     (1,3,Pattern_Pair data_z data_y)}"

definition family_socket_system :: "(nat,nat,nat,nat) schema_system" where
  "family_socket_system=add_view_definition headed_material_system 30 data_x {(0,family_socket_schema)}"

lemma family_socket_system_formed [simp]: "schema_system_formed family_socket_system"
  unfolding family_socket_system_def
  by (rule add_recursive_definition_formed[OF headed_material_system_formed])
    (auto simp: family_socket_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma family_socket_definitions [simp]:
  "system_definitions family_socket_system=insert 30 (system_definitions headed_material_system)"
  by (simp add: family_socket_system_def)

lemma family_socket_call:
  "schema_call_formed family_socket_system d t \<longleftrightarrow>
    d\<in>system_definitions family_socket_system \<and> term_formed t"
  using added_variable_calls[OF headed_material_system_formed
    family_socket_system_formed[unfolded family_socket_system_def] headed_material_call]
  by (simp only: family_socket_system_def[symmetric])

lemma family_socket_old_meaning:
  assumes "d\<in>system_definitions headed_material_system"
  shows "(d,t)\<in>positive_meaning family_socket_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning headed_material_system"
  using added_definition_preserves_old(2)[OF headed_material_system_formed
    family_socket_system_formed[unfolded family_socket_system_def], of d t] assms
  by (auto simp: family_socket_system_def)

lemma family_socket_clause [simp]:
  "((30,c),S)\<in>system_clauses family_socket_system \<longleftrightarrow> (c,S)\<in>{(0,family_socket_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses headed_material_system \<Longrightarrow>
    d\<in>system_definitions headed_material_system" for d c S
    using headed_material_system_formed unfolding schema_system_formed_def by blast
  have absent: "((30,c),S)\<notin>system_clauses headed_material_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: family_socket_system_def)
qed

lemma family_socket_valuation:
  "(30,t)\<in>positive_meaning family_socket_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=rooted_rows_argument (h 0) (h 1) (Pair_Term (h 2) (h 3)) \<and>
      (29,headed_material_argument (h 0) (h 2) (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 2) (h 1))\<in>positive_meaning headed_material_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family_socket_schema_def schema_variables_def family_socket_call family_socket_old_meaning)

lemma family_socket_fields:
  "(30,t)\<in>positive_meaning family_socket_system \<longleftrightarrow>
    (\<exists>a r p x. t=rooted_rows_argument a r (Pair_Term p x) \<and> term_formed t \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system)"
proof
  assume "(30,t)\<in>positive_meaning family_socket_system"
  then show "\<exists>a r p x. t=rooted_rows_argument a r (Pair_Term p x) \<and> term_formed t \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system"
    by (auto simp: family_socket_valuation)
next
  assume "\<exists>a r p x. t=rooted_rows_argument a r (Pair_Term p x) \<and> term_formed t \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system"
  then obtain a r p x where parts: "t=rooted_rows_argument a r (Pair_Term p x)" "term_formed t"
    "(29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
    "(3,Pair_Term p r)\<in>positive_meaning headed_material_system" by blast
  show "(30,t)\<in>positive_meaning family_socket_system"
    by (simp only: family_socket_valuation, rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then r else if i=2 then p else x"])
      (use parts in auto)
qed

definition family_sockets_system :: "(nat,nat,nat,nat) schema_system" where
  "family_sockets_system=add_view_definition family_socket_system 31 data_x (context_list_clauses 30 31)"

lemma family_sockets_system_formed [simp]: "schema_system_formed family_sockets_system"
  unfolding family_sockets_system_def
  by (rule add_recursive_definition_formed[OF family_socket_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma family_sockets_definitions [simp]:
  "system_definitions family_sockets_system=insert 31 (system_definitions family_socket_system)"
  by (simp add: family_sockets_system_def)

lemma family_sockets_call:
  "schema_call_formed family_sockets_system d t \<longleftrightarrow>
    d\<in>system_definitions family_sockets_system \<and> term_formed t"
  using added_variable_calls[OF family_socket_system_formed
    family_sockets_system_formed[unfolded family_sockets_system_def] family_socket_call]
  by (simp only: family_sockets_system_def[symmetric])

lemma family_sockets_old_meaning:
  assumes "d\<in>system_definitions family_socket_system"
  shows "(d,t)\<in>positive_meaning family_sockets_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning family_socket_system"
  using added_definition_preserves_old(2)[OF family_socket_system_formed
    family_sockets_system_formed[unfolded family_sockets_system_def], of d t] assms
  by (auto simp: family_sockets_system_def)

lemma family_sockets_clause [simp]:
  "((31,c),S)\<in>system_clauses family_sockets_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 30 31)"
proof -
  have owned: "((d,c),S)\<in>system_clauses family_socket_system \<Longrightarrow>
    d\<in>system_definitions family_socket_system" for d c S
    using family_socket_system_formed unfolding schema_system_formed_def by blast
  have absent: "((31,c),S)\<notin>system_clauses family_socket_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: family_sockets_system_def)
qed

interpretation family_socket_lists: context_list_profile family_sockets_system 30 31
  by (rule context_list_profile.intro) (auto simp: family_sockets_call)

lemma family_sockets_rows:
  assumes source: "artifact_value_presents R a" and root: "octets_formed r"
    and data: "data_elements (map address_pair_data xs)"
  shows "(31,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
    \<in>positive_meaning family_sockets_system \<longleftrightarrow>
    (\<forall>(p,x)\<in>set xs. p\<noteq>r \<and> p\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) p={} \<and> restrict_basis {p} (object_data R)=empty_basis)"
proof -
  have af: "term_formed a" using artifact_value_presents_formed[OF source] by simp
  have element: "(30,rooted_rows_argument a (Payload_Term r) (address_pair_data (p,x)))
      \<in>positive_meaning family_sockets_system \<longleftrightarrow>
      p\<noteq>r \<and> p\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) p={} \<and> restrict_basis {p} (object_data R)=empty_basis"
    if "(p,x)\<in>set xs" for p x
    using data that af root
    by (auto simp: family_sockets_old_meaning family_socket_fields address_pair_data_def
      headed_material_no_data[OF source, of p "[]", simplified] headed_material_inequality)
  have elements: "(\<forall>z\<in>set xs.
      (30,rooted_rows_argument a (Payload_Term r) (address_pair_data z))\<in>positive_meaning family_sockets_system)
    \<longleftrightarrow> (\<forall>(p,x)\<in>set xs. p\<noteq>r \<and> p\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) p={} \<and> restrict_basis {p} (object_data R)=empty_basis)"
    by (rule ball_cong[OF refl]; rename_tac z; case_tac z; simp add: element)
  have lists: "(31,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning family_sockets_system \<longleftrightarrow>
    (\<forall>z\<in>set xs. (30,rooted_rows_argument a (Payload_Term r) (address_pair_data z))
      \<in>positive_meaning family_sockets_system)"
    using af root by (simp add: family_socket_lists.lists)
  show ?thesis using lists elements by blast
qed

section \<open>The complete root graph and every socket form one family check\<close>

definition family_admission_schema :: "(nat,nat,nat) factor_schema" where
  "family_admission_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,29,headed_material_pattern data_x data_y data_z (Pattern_Payload []) (Pattern_Payload [])),
     (1,21,data_z),(2,31,Pattern_Pair (Pattern_Pair data_x data_y) data_z)}"

definition family_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "family_admission_system=add_view_definition family_sockets_system 32 data_x {(0,family_admission_schema)}"

lemma family_admission_system_formed [simp]: "schema_system_formed family_admission_system"
  unfolding family_admission_system_def
  by (rule add_recursive_definition_formed[OF family_sockets_system_formed])
    (auto simp: family_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma family_admission_definitions [simp]:
  "system_definitions family_admission_system=insert 32 (system_definitions family_sockets_system)"
  by (simp add: family_admission_system_def)

lemma family_admission_call:
  "schema_call_formed family_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions family_admission_system \<and> term_formed t"
  using added_variable_calls[OF family_sockets_system_formed
    family_admission_system_formed[unfolded family_admission_system_def] family_sockets_call]
  by (simp only: family_admission_system_def[symmetric])

lemma family_admission_old_meaning:
  assumes "d\<in>system_definitions family_sockets_system"
  shows "(d,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning family_sockets_system"
  using added_definition_preserves_old(2)[OF family_sockets_system_formed
    family_admission_system_formed[unfolded family_admission_system_def], of d t] assms
  by (auto simp: family_admission_system_def)

lemma family_admission_clause [simp]:
  "((32,c),S)\<in>system_clauses family_admission_system \<longleftrightarrow> (c,S)\<in>{(0,family_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses family_sockets_system \<Longrightarrow>
    d\<in>system_definitions family_sockets_system" for d c S
    using family_sockets_system_formed unfolding schema_system_formed_def by blast
  have absent: "((32,c),S)\<notin>system_clauses family_sockets_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: family_admission_system_def)
qed

lemma family_admission_headed_meaning:
  assumes "d\<in>system_definitions headed_material_system"
  shows "(d,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning headed_material_system"
  using family_admission_old_meaning[of d t] family_sockets_old_meaning[of d t]
    family_socket_old_meaning[OF assms, of t] assms by auto

lemma family_admission_components:
  "(29,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (29,t)\<in>positive_meaning headed_material_system"
  "(21,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (21,t)\<in>positive_meaning keyed_list_system"
  "(31,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (31,t)\<in>positive_meaning family_sockets_system"
  using family_admission_old_meaning[of 29 t] family_sockets_old_meaning[of 29 t]
    family_socket_old_meaning[of 29 t] family_admission_old_meaning[of 21 t]
    family_sockets_old_meaning[of 21 t] family_socket_old_meaning[of 21 t]
    headed_material_keyed[of t] family_admission_old_meaning[of 31 t] by auto

lemma family_admission_valuation:
  "(32,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=rooted_rows_argument (h 0) (h 1) (h 2) \<and>
      (29,headed_material_argument (h 0) (h 1) (h 2) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (21,h 2)\<in>positive_meaning keyed_list_system \<and>
      (31,rooted_rows_argument (h 0) (h 1) (h 2))\<in>positive_meaning family_sockets_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family_admission_schema_def schema_variables_def family_admission_call family_admission_components)

lemma family_admission_fields:
  "(32,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (21,m)\<in>positive_meaning keyed_list_system \<and>
      (31,rooted_rows_argument a k m)\<in>positive_meaning family_sockets_system)"
proof
  assume "(32,t)\<in>positive_meaning family_admission_system"
  then show "\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (21,m)\<in>positive_meaning keyed_list_system \<and>
      (31,rooted_rows_argument a k m)\<in>positive_meaning family_sockets_system"
    by (auto simp: family_admission_valuation)
next
  assume "\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (21,m)\<in>positive_meaning keyed_list_system \<and>
      (31,rooted_rows_argument a k m)\<in>positive_meaning family_sockets_system"
  then obtain a k m where parts: "t=rooted_rows_argument a k m"
    "(29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
    "(21,m)\<in>positive_meaning keyed_list_system"
    "(31,rooted_rows_argument a k m)\<in>positive_meaning family_sockets_system" by blast
  have formed: "term_formed a" "term_formed k" "term_formed m"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by auto
  show "(32,t)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then k else m"])
      (use parts formed in auto)
qed

theorem family_admission_exact:
  "(32,t)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> distinct xs \<and> family_at R r (set xs))"
proof
  assume holds: "(32,t)\<in>positive_meaning family_admission_system"
  obtain a k m where input: "t=rooted_rows_argument a k m"
    and headed: "(29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
    and keys: "(21,m)\<in>positive_meaning keyed_list_system"
    and sockets: "(31,rooted_rows_argument a k m)\<in>positive_meaning family_sockets_system"
    using holds by (auto simp: family_admission_fields)
  obtain R r xs where source: "artifact_value_presents R a"
    and shape: "k=Payload_Term r" "m=data_list_term (map address_pair_data xs)"
    and root: "r\<in>rra_carrier (object_structure R)" and distinct: "distinct xs"
    and head: "headed_incidence (object_structure R) r=set xs"
    and root_data: "restrict_basis {r} (object_data R)=empty_basis"
    using headed by (auto simp: headed_material_empty_exact[simplified])
  have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
  have address: "octets_formed r" using rf root by (auto simp: exact_formed_def)
  have rows: "data_elements (map address_pair_data xs)" by (rule headed_rows_data[OF rf, where r=r]) (simp add: head)
  have functional: "single_valued (set xs)" using keys by (simp add: shape keyed_address_rows[OF rows])
  have ports: "\<forall>(p,x)\<in>set xs. p\<noteq>r \<and> p\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) p={} \<and> restrict_basis {p} (object_data R)=empty_basis"
    using sockets by (simp add: shape family_sockets_rows[OF source address rows])
  have read: "family_at R r (set xs)"
    using rf root head functional root_data ports
    by (auto simp: family_at_def exact_formed_def rel_dom_def empty_restriction_iff)
  show "\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> distinct xs \<and> family_at R r (set xs)"
    using input source shape distinct read by blast
next
  assume "\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> distinct xs \<and> family_at R r (set xs)"
  then obtain R a r xs where input: "t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs))"
    and source: "artifact_value_presents R a" and distinct: "distinct xs" and read: "family_at R r (set xs)" by blast
  have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
  have root: "r\<in>rra_carrier (object_structure R)" and head: "headed_incidence (object_structure R) r=set xs"
    and functional: "single_valued (set xs)" using read by (auto simp: family_at_def)
  have address: "octets_formed r" using rf root by (auto simp: exact_formed_def)
  have rows: "data_elements (map address_pair_data xs)" by (rule headed_rows_data[OF rf, where r=r]) (simp add: head)
  have interior: "insert r (rel_dom (set xs))\<subseteq>rra_carrier (object_structure R)"
    by (rule family_interior_in_carrier[OF read])
  have ports: "\<forall>(p,x)\<in>set xs. p\<noteq>r \<and> p\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) p={} \<and> restrict_basis {p} (object_data R)=empty_basis"
    using read interior by (auto simp: family_at_def rel_dom_def empty_restriction_iff)
  have root_data: "restrict_basis {r} (object_data R)=empty_basis"
    using read by (auto simp: family_at_def empty_restriction_iff)
  have headed: "(29,headed_material_argument a (Payload_Term r) (data_list_term (map address_pair_data xs))
      (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
    using root distinct head root_data by (simp add: headed_material_no_data[OF source, simplified])
  have keys: "(21,data_list_term (map address_pair_data xs))\<in>positive_meaning keyed_list_system"
    using distinct functional by (simp add: keyed_address_rows[OF rows])
  have sockets: "(31,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning family_sockets_system"
    using ports by (simp add: family_sockets_rows[OF source address rows])
  show "(32,t)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_fields, intro exI[of _ a] exI[of _ "Payload_Term r"]
      exI[of _ "data_list_term (map address_pair_data xs)"]) (use input headed keys sockets in blast)
qed

corollary family_admission_at_source:
  assumes source: "artifact_value_presents R a"
  shows "(32,rooted_rows_argument a k m)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (\<exists>r xs. k=Payload_Term r \<and> m=data_list_term (map address_pair_data xs) \<and>
      distinct xs \<and> family_at R r (set xs))"
  using artifact_value_presents_unique[OF _ source]
  by (auto simp: family_admission_exact intro: source)

corollary family_admission_rows:
  assumes source: "artifact_value_presents R a"
  shows "(32,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
    \<in>positive_meaning family_admission_system \<longleftrightarrow> distinct xs \<and> family_at R r (set xs)"
  by (simp add: family_admission_at_source[OF source] data_list_term_injective
    injective_mapped_lists[OF address_pair_data_injective])

corollary family_admission_orders:
  assumes source: "artifact_value_presents R a" and same: "mset xs=mset ys"
  shows "(32,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning family_admission_system \<longleftrightarrow>
    (32,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data ys)))
      \<in>positive_meaning family_admission_system"
  using mset_eq_imp_distinct_iff[OF same] mset_eq_setD[OF same]
  by (simp only: family_admission_rows[OF source])

corollary family_admission_presentation_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R b"
  shows "(32,rooted_rows_argument a k m)\<in>positive_meaning family_admission_system \<longleftrightarrow>
    (32,rooted_rows_argument b k m)\<in>positive_meaning family_admission_system"
  by (simp only: family_admission_at_source[OF assms(1)] family_admission_at_source[OF assms(2)])

text \<open>
  The family entry checks the complete root graph, unique socket keys, and
  empty material at every socket distinct from the root. Its meaning is
  exactly the existing relative family grammar at every input term.
  Equal endpoints remain possible at different sockets, and any complete
  enumeration of the socket graph is accepted. Empty families retain the
  root admission check. The complete source stays an ordinary argument;
  no incoming edge or unrelated material is discarded or forbidden.

  All earlier calls and meanings are preserved. The three new definitions
  have four ordinary clauses. The subsequent record extension compiles
  both grammar entries together before arbitrary future input terms.
\<close>

end
