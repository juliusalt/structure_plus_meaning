theory Factor_Package_Requests
  imports Factor_Package_Retention_Admission Factor_Judgment_Retention_Base Factor_Finite_Root_Environments
    Factor_Positive_Parametricity
begin

section \<open>The native request at a package\<close>

text \<open>
  A request at a given package carries a support, a list of the given's definition sites its answer may
  call, and a context, a site value whose environment is the closed package scope at its root. The
  argument holds three fields: the given's site value, the support as a data list of definition-site
  values, and the context's site value. One ordinary rule joins five readers: package admission at the
  given, package membership of every support site (a context-list traversal whose element is membership),
  the root family reading at the context, package retention admission at the context, and two
  environment inclusions sharing one private environment value, which makes the context compatible with
  the given. Each reader is consumed through its exact contract.
\<close>

subsection \<open>Two definitions over the readers' program\<close>

definition package_request_list_system :: "(nat,nat,nat,nat) schema_system" where
  "package_request_list_system=add_view_definition package_retention_admission_system 560 data_x
    (context_list_clauses 83 560)"

lemma package_request_list_formed [simp]: "schema_system_formed package_request_list_system"
  unfolding package_request_list_system_def
  by (rule add_recursive_definition_formed[OF package_retention_admission_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_request_list_definitions [simp]:
  "system_definitions package_request_list_system=insert 560 (system_definitions package_retention_admission_system)"
  by (simp add: package_request_list_system_def)

lemma package_request_list_call:
  "schema_call_formed package_request_list_system d t \<longleftrightarrow>
    d\<in>system_definitions package_request_list_system \<and> term_formed t"
  using added_variable_calls[OF package_retention_admission_system_formed
    package_request_list_formed[unfolded package_request_list_system_def] package_retention_admission_call]
  by (simp only: package_request_list_system_def[symmetric])

lemma package_request_list_old_meaning:
  assumes "d\<in>system_definitions package_retention_admission_system"
  shows "(d,t)\<in>positive_meaning package_request_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_retention_admission_system"
  using added_definition_preserves_old(2)[OF package_retention_admission_system_formed
    package_request_list_formed[unfolded package_request_list_system_def], of d t] assms
  by (auto simp: package_request_list_system_def)

lemma package_request_list_clause [simp]:
  "((560,c),S)\<in>system_clauses package_request_list_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 83 560"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_retention_admission_system \<Longrightarrow>
    d\<in>system_definitions package_retention_admission_system" for d c S
    using package_retention_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((560,c),S)\<notin>system_clauses package_retention_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_request_list_system_def)
qed

text \<open>
  The entry's eight variables: the given's environment value, use and root (0, 1, 2), the support (3), the
  context's environment value, use and root (4, 5, 6), and the private environment value (7) that both
  inclusion premises share.
\<close>

definition package_request_schema :: "(nat,nat,nat) factor_schema" where
  "package_request_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
      (Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)))))
    {(0,80,Pattern_Pair (Pattern_Pair data_x data_y) data_z),
     (1,560,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) data_w),
     (2,79,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Pair (Pattern_Variable 6) data_w)),
     (3,122,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))),
     (4,113,Pattern_Pair data_x (Pattern_Variable 7)),
     (5,113,Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 7))}"

definition package_request_system :: "(nat,nat,nat,nat) schema_system" where
  "package_request_system=add_view_definition package_request_list_system 561 data_x {(0,package_request_schema)}"

lemma package_request_system_formed [simp]: "schema_system_formed package_request_system"
  unfolding package_request_system_def
  by (rule add_recursive_definition_formed[OF package_request_list_formed])
    (auto simp: package_request_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma package_request_definitions [simp]:
  "system_definitions package_request_system=insert 561 (system_definitions package_request_list_system)"
  by (simp add: package_request_system_def)

lemma package_request_call:
  "schema_call_formed package_request_system d t \<longleftrightarrow>
    d\<in>system_definitions package_request_system \<and> term_formed t"
  using added_variable_calls[OF package_request_list_formed
    package_request_system_formed[unfolded package_request_system_def] package_request_list_call]
  by (simp only: package_request_system_def[symmetric])

lemma package_request_old_meaning:
  assumes "d\<in>system_definitions package_request_list_system"
  shows "(d,t)\<in>positive_meaning package_request_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_request_list_system"
  using added_definition_preserves_old(2)[OF package_request_list_formed
    package_request_system_formed[unfolded package_request_system_def], of d t] assms
  by (auto simp: package_request_system_def)

lemma package_request_clauses [simp]:
  "((561,c),S)\<in>system_clauses package_request_system \<longleftrightarrow> c=0 \<and> S=package_request_schema"
  "((560,c),S)\<in>system_clauses package_request_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 83 560"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_request_list_system \<Longrightarrow>
    d\<in>system_definitions package_request_list_system" for d c S
    using package_request_list_formed unfolding schema_system_formed_def by blast
  have absent: "((561,c),S)\<notin>system_clauses package_request_list_system" by (auto dest: owned)
  show "((561,c),S)\<in>system_clauses package_request_system \<longleftrightarrow> c=0 \<and> S=package_request_schema"
    using absent by (auto simp: package_request_system_def)
  show "((560,c),S)\<in>system_clauses package_request_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 83 560"
    by (simp add: package_request_system_def)
qed

subsection \<open>Each reader keeps its meaning\<close>

lemma package_request_lower:
  assumes "d\<in>system_definitions package_retention_admission_system"
  shows "(d,t)\<in>positive_meaning package_request_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_retention_admission_system"
  using package_request_old_meaning[of d t] package_request_list_old_meaning[OF assms, of t] assms by simp

lemma package_request_components:
  "(80,t)\<in>positive_meaning package_request_system \<longleftrightarrow> package_admission_result t"
  "(83,t)\<in>positive_meaning package_request_system \<longleftrightarrow> package_membership_result t"
  "(79,t)\<in>positive_meaning package_request_system \<longleftrightarrow> root_family_reading_result t"
  "(122,t)\<in>positive_meaning package_request_system \<longleftrightarrow> package_retention_admission_result t"
  "(113,t)\<in>positive_meaning package_request_system \<longleftrightarrow> environment_inclusion_result t"
  using package_request_lower[of 80 t] package_retention_admission_components(1)[of t] package_admission_exact[of t]
    package_request_lower[of 83 t] package_retention_admission_replay_meaning[of 83 t]
    replay_slot_reading_components(5)[of t] package_membership_exact[of t]
    package_request_lower[of 79 t] package_retention_admission_replay_meaning[of 79 t]
    replay_slot_reading_old_meaning[of 79 t] replay_source_reading_graph_meaning[of 79 t]
    proof_graph_membership_node_meaning[of 79 t] proof_node_reading_base_meaning[of 79 t]
    admitted_instantiation_previous_meaning[of 79 t] package_admission_operation_components(2)[of t]
    root_family_reading_exact[of t]
    package_request_lower[of 122 t] package_retention_admission_exact[of t]
    package_request_lower[of 113 t] package_retention_admission_old_meaning[of 113 t]
    package_lists_previous_meaning[of 113 t] judgment_retention_component_meanings(7)[of t]
    environment_inclusion_exact[of t]
  by auto

interpretation package_request_list_profile: context_list_profile package_request_system 83 560
  by (rule context_list_profile.intro) (auto simp: package_request_call)

lemma package_request_valuation:
  "(561,t)\<in>positive_meaning package_request_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2)))
        (Pair_Term (h 3) (Pair_Term (h 4) (Pair_Term (h 5) (h 6)))) \<and>
      (80,Pair_Term (Pair_Term (h 0) (h 1)) (h 2))\<in>positive_meaning package_request_system \<and>
      (560,Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3))\<in>positive_meaning package_request_system \<and>
      (79,Pair_Term (Pair_Term (h 4) (h 5)) (Pair_Term (h 6) (h 3)))\<in>positive_meaning package_request_system \<and>
      (122,Pair_Term (h 4) (Pair_Term (h 5) (h 6)))\<in>positive_meaning package_request_system \<and>
      (113,Pair_Term (h 0) (h 7))\<in>positive_meaning package_request_system \<and>
      (113,Pair_Term (h 4) (h 7))\<in>positive_meaning package_request_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: package_request_schema_def schema_variables_def package_request_call)

subsection \<open>What the entry states of the given, the support and the context\<close>

text \<open>
  The relation the entry presents is stated over the three subjects: the given's site context, the
  support's definition sites and the context's site context. The given holds a native package whose
  definitions include every support site; the context's root family is read at exactly the support; the
  context is a closed native package at its root; and one formed environment includes both environments.
\<close>

definition package_request_holds ::
    "site_context \<Rightarrow> local_address option definition_site list \<Rightarrow> site_context \<Rightarrow> bool" where
  "package_request_holds g ds c \<longleftrightarrow>
    (\<exists>P. native_package_at (fst g) (fst (snd g)) (snd (snd g)) P \<and> set ds\<subseteq>system_definitions P) \<and>
    (\<exists>R xs. artifact_at (fst c) (fst (snd c)) R \<and> distinct xs \<and> family_at R (snd (snd c)) (set xs) \<and>
      list_all2 (\<lambda>a d. located_at (fst c) (fst (snd c)) a (fst d) (snd d)) (map snd xs) ds) \<and>
    (\<exists>Q. closed_native_package_at (fst c) (fst (snd c)) (snd (snd c)) Q) \<and>
    (\<exists>W. environment_formed W \<and> environment_included (fst g) W \<and> environment_included (fst c) W)"

definition package_request_relation ::
    "site_context \<times> (local_address option definition_site list \<times> site_context) \<Rightarrow> bool" where
  "package_request_relation z \<longleftrightarrow> package_request_holds (fst z) (fst (snd z)) (snd (snd z))"

abbreviation package_request_presents where
  "package_request_presents \<equiv> factor_pair_presents
    (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
    (factor_pair_presents (data_sequence_presents site_coordinate_presents)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t))"

lemma package_request_presents_at:
  "package_request_presents ((E,(u,r)),(ds,(F,(v,q)))) t \<longleftrightarrow>
    (\<exists>a b. t=Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b) \<and>
      site_value_presents E u r a \<and> site_value_presents F v q b)"
  by (auto simp: factor_pair_presents_def data_sequence_presents_def list_all2_function)

lemma native_package_formed_at:
  assumes "native_package_at E u r P"
  shows "environment_formed E"
  using assms by (auto simp: native_package_at_def native_root_family_at_def)

lemma native_package_members_iff:
  "(\<exists>P. native_package_at E u r P \<and> D\<subseteq>system_definitions P) \<longleftrightarrow>
    (\<exists>P. native_package_at E u r P) \<and> (\<forall>d\<in>D. \<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P)"
proof
  assume "\<exists>P. native_package_at E u r P \<and> D\<subseteq>system_definitions P"
  then show "(\<exists>P. native_package_at E u r P) \<and> (\<forall>d\<in>D. \<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P)"
    by blast
next
  assume both: "(\<exists>P. native_package_at E u r P) \<and> (\<forall>d\<in>D. \<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P)"
  have ex: "\<exists>P. native_package_at E u r P" using both by (rule conjunct1)
  have each: "\<forall>d\<in>D. \<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P" using both by (rule conjunct2)
  obtain P where package: "native_package_at E u r P" using ex by (rule exE)
  have "d\<in>system_definitions P" if in_D: "d\<in>D" for d
  proof -
    obtain T where other: "native_package_at E u r T" and member: "d\<in>system_definitions T"
      using bspec[OF each in_D] by (elim exE conjE)
    show ?thesis using native_package_unique[OF package other] member by simp
  qed
  then show "\<exists>P. native_package_at E u r P \<and> D\<subseteq>system_definitions P" using package by blast
qed

subsection \<open>The contract\<close>

theorem package_request_exact:
  "(561,t)\<in>positive_meaning package_request_system \<longleftrightarrow>
    presented_predicate package_request_presents package_request_relation t"
proof
  assume holds: "(561,t)\<in>positive_meaning package_request_system"
  obtain h :: "nat\<Rightarrow>factor_term"
    where shape: "t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2)))
        (Pair_Term (h 3) (Pair_Term (h 4) (Pair_Term (h 5) (h 6))))"
    and admission: "package_admission_result (Pair_Term (Pair_Term (h 0) (h 1)) (h 2))"
    and support: "(560,Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3))\<in>positive_meaning package_request_system"
    and roots: "root_family_reading_result (Pair_Term (Pair_Term (h 4) (h 5)) (Pair_Term (h 6) (h 3)))"
    and retained: "package_retention_admission_result (Pair_Term (h 4) (Pair_Term (h 5) (h 6)))"
    and given_inclusion: "environment_inclusion_result (Pair_Term (h 0) (h 7))"
    and context_inclusion: "environment_inclusion_result (Pair_Term (h 4) (h 7))"
    using holds unfolding package_request_valuation package_request_components by blast
  obtain E e u r P where given: "h 0=e" "h 1=use_data_term u" "h 2=Payload_Term r"
    and E: "environment_value_presents E e" and P: "native_package_at E u r P"
    using admission by auto
  obtain xs where xs: "h 3=data_list_term xs"
    and members: "\<forall>x\<in>set xs. (83,Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) x)
      \<in>positive_meaning package_request_system"
    using support unfolding package_request_list_profile.exact by auto
  have member_sites: "\<forall>x\<in>set xs. \<exists>d. x=definition_site_value d \<and> d\<in>system_definitions P"
  proof
    fix x assume "x\<in>set xs"
    then have "package_membership_result (Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term r)) x)"
      using members given package_request_components(2) by simp
    then obtain E' e' u' r' d P' where eq: "e'=e" "use_data_term u'=use_data_term u" "r'=r"
        "x=definition_site_value d"
      and E': "environment_value_presents E' e'" and P': "native_package_at E' u' r' P'"
      and d: "d\<in>system_definitions P'"
      by auto
    have "u'=u" using eq(2) use_data_term_injective by (simp add: inj_eq)
    moreover have "E'=E" using environment_value_presents_unique[OF E'[unfolded eq(1)] E] .
    ultimately have "P'=P" using native_package_unique[OF _ P] P' eq(3) by simp
    then show "\<exists>d. x=definition_site_value d \<and> d\<in>system_definitions P" using eq(4) d by blast
  qed
  obtain ds where ds: "xs=map definition_site_value ds" and inside: "\<forall>d\<in>set ds. d\<in>system_definitions P"
    using iffD1[OF list_range_restricted_witnesses member_sites] by blast
  obtain F f v q R ys ds' where scope: "h 4=f" "h 5=use_data_term v" "h 6=Payload_Term q"
      "h 3=data_list_term (map definition_site_value ds')"
    and F: "environment_value_presents F f" and artifact: "artifact_at F v R" and separate: "distinct ys"
    and family: "family_at R q (set ys)"
    and reading: "list_all2 (\<lambda>a d. located_at F v a (fst d) (snd d)) (map snd ys) ds'"
    using roots by auto
  have same_support: "ds'=ds"
    using scope(4) xs ds data_list_term_injective inj_map_eq_map[OF definition_site_value_injective] by simp
  obtain F'' v'' q'' Q where sv: "site_value_presents F'' v'' q'' (Pair_Term (h 4) (Pair_Term (h 5) (h 6)))"
    and closed: "closed_native_package_at F'' v'' q'' Q"
    using retained by blast
  obtain f'' where F'': "environment_value_presents F'' f''"
    and sv_eq: "Pair_Term (h 4) (Pair_Term (h 5) (h 6))=Pair_Term f'' (site_data_term v'' q'')"
    using sv by (auto simp: site_value_presents_def)
  have "f''=f" "v''=v" "q''=q"
    using sv_eq scope use_data_term_injective by (auto simp: site_data_term_def inj_eq)
  then have context_same: "F''=F" using environment_value_presents_unique[OF F''] F by simp
  obtain E1 W e1 w where i1: "Pair_Term (h 0) (h 7)=Pair_Term e1 w" and E1: "environment_value_presents E1 e1"
    and W: "environment_value_presents W w" and incl1: "environment_included E1 W"
    using given_inclusion by blast
  obtain F2 W2 f2 w2 where i2: "Pair_Term (h 4) (h 7)=Pair_Term f2 w2" and F2: "environment_value_presents F2 f2"
    and W2: "environment_value_presents W2 w2" and incl2: "environment_included F2 W2"
    using context_inclusion by blast
  have "E1=E" using environment_value_presents_unique[OF E1] E i1 given(1) by simp
  moreover have "F2=F" using environment_value_presents_unique[OF F2] F i2 scope(1) by simp
  moreover have "W2=W" using environment_value_presents_unique[OF W2] W i1 i2 by simp
  ultimately have compatible: "environment_formed W \<and> environment_included E W \<and> environment_included F W"
    using incl1 incl2 environment_value_presents_formed[OF W] by simp
  have given_value: "site_value_presents E u r (Pair_Term (h 0) (Pair_Term (h 1) (h 2)))"
    using native_package_site_position[OF P] E given by (auto simp: site_value_presents_def site_data_term_def)
  have context_value: "site_value_presents F v q (Pair_Term (h 4) (Pair_Term (h 5) (h 6)))"
    using sv context_same \<open>v''=v\<close> \<open>q''=q\<close> by simp
  have relation: "package_request_relation ((E,(u,r)),(ds,(F,(v,q))))"
    unfolding package_request_relation_def package_request_holds_def
    using P inside artifact separate family reading same_support closed context_same \<open>v''=v\<close> \<open>q''=q\<close>
      compatible by auto
  have presents: "package_request_presents ((E,(u,r)),(ds,(F,(v,q)))) t"
    unfolding package_request_presents_at
    by (rule exI[of _ "Pair_Term (h 0) (Pair_Term (h 1) (h 2))"], rule exI[of _ "Pair_Term (h 4) (Pair_Term (h 5) (h 6))"])
      (use given_value context_value in \<open>simp add: shape xs ds\<close>)
  show "presented_predicate package_request_presents package_request_relation t"
    unfolding presented_predicate_def using presents relation by blast
next
  assume "presented_predicate package_request_presents package_request_relation t"
  then obtain z where presents_z: "package_request_presents z t" and relation_z: "package_request_relation z"
    unfolding presented_predicate_def by blast
  obtain E u r where g: "fst z=(E,(u,r))" by (rule prod_cases3)
  obtain ds F v q where w: "snd z=(ds,(F,(v,q)))" by (rule prod_cases4)
  have z: "z=((E,(u,r)),(ds,(F,(v,q))))" using g w surjective_pairing[of z] by simp
  have presents: "package_request_presents ((E,(u,r)),(ds,(F,(v,q)))) t" using presents_z z by simp
  have relation: "package_request_holds (E,(u,r)) ds (F,(v,q))"
    using relation_z z by (simp add: package_request_relation_def)
  obtain a b where t: "t=Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b)"
    and given_value: "site_value_presents E u r a" and context_value: "site_value_presents F v q b"
    using presents unfolding package_request_presents_at by blast
  obtain e where E: "environment_value_presents E e" and a: "a=Pair_Term e (site_data_term u r)"
    using given_value by (auto simp: site_value_presents_def)
  obtain f where F: "environment_value_presents F f" and b: "b=Pair_Term f (site_data_term v q)"
    using context_value by (auto simp: site_value_presents_def)
  obtain P where P: "native_package_at E u r P" and inside: "set ds\<subseteq>system_definitions P"
    using relation by (auto simp: package_request_holds_def)
  obtain R xs where artifact: "artifact_at F v R" and separate: "distinct xs" and family: "family_at R q (set xs)"
    and reading: "list_all2 (\<lambda>a d. located_at F v a (fst d) (snd d)) (map snd xs) ds"
    using relation by (auto simp: package_request_holds_def)
  obtain Q where closed: "closed_native_package_at F v q Q"
    using relation by (auto simp: package_request_holds_def)
  obtain W where W: "environment_formed W" and incl_E: "environment_included E W" and incl_F: "environment_included F W"
    using relation by (auto simp: package_request_holds_def)
  obtain w where w: "environment_value_presents W w" using environment_value_presents_total[OF W] by blast
  let ?root = "Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term r)"
  let ?support = "data_list_term (map definition_site_value ds)"
  have admitted: "(80,?root)\<in>positive_meaning package_request_system"
    unfolding package_request_components using E P by blast
  have root_formed: "term_formed ?root"
    using schema_call_formed_target[OF positive_meaning_formed[OF admitted]] by blast
  have members: "(560,Pair_Term ?root ?support)\<in>positive_meaning package_request_system"
    unfolding package_request_list_profile.lists
    using root_formed package_membership_at_package[OF E P] inside package_request_components(2)
      package_membership_exact by auto
  have read: "(79,Pair_Term (Pair_Term f (use_data_term v)) (Pair_Term (Payload_Term q) ?support))
      \<in>positive_meaning package_request_system"
    unfolding package_request_components using F artifact separate family reading by blast
  have retained: "(122,Pair_Term f (Pair_Term (use_data_term v) (Payload_Term q)))\<in>positive_meaning package_request_system"
    unfolding package_request_components using context_value closed b by (auto simp: site_data_term_def)
  have include_given: "(113,Pair_Term e w)\<in>positive_meaning package_request_system"
    unfolding package_request_components using E w incl_E by blast
  have include_scope: "(113,Pair_Term f w)\<in>positive_meaning package_request_system"
    unfolding package_request_components using F w incl_F by blast
  have formed_support: "term_formed ?support"
    using schema_call_formed_target[OF positive_meaning_formed[OF members]] by simp
  have formed_scope: "term_formed (Pair_Term f (Pair_Term (use_data_term v) (Payload_Term q)))"
    using schema_call_formed_target[OF positive_meaning_formed[OF retained]] by blast
  have formed_w: "term_formed w" using environment_value_presents_formed[OF w] by blast
  have formed_parts: "term_formed e" "term_formed (use_data_term u)" "term_formed (Payload_Term r)"
    "term_formed f" "term_formed (use_data_term v)" "term_formed (Payload_Term q)"
    using root_formed formed_scope by simp_all
  have shape: "t=Pair_Term (Pair_Term e (Pair_Term (use_data_term u) (Payload_Term r)))
      (Pair_Term ?support (Pair_Term f (Pair_Term (use_data_term v) (Payload_Term q))))"
    using t a b by (simp add: site_data_term_def)
  let ?h = "\<lambda>i::nat. if i=0 then e else if i=1 then use_data_term u else if i=2 then Payload_Term r
    else if i=3 then ?support else if i=4 then f else if i=5 then use_data_term v
    else if i=6 then Payload_Term q else w"
  show "(561,t)\<in>positive_meaning package_request_system"
    unfolding package_request_valuation
    apply (rule exI[of _ ?h])
    apply (intro conjI)
    using formed_parts formed_support formed_w shape admitted members read retained include_given include_scope
    by simp_all
qed

corollary package_request_on_values:
  assumes given: "site_value_presents E u r a" and scope: "site_value_presents F v q b"
  shows "(561,Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))
      \<in>positive_meaning package_request_system \<longleftrightarrow> package_request_holds (E,(u,r)) ds (F,(v,q))"
proof -
  have unique: "package_request_presents z (Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))
      \<Longrightarrow> z=((E,(u,r)),(ds,(F,(v,q))))" for z
  proof -
    assume presents: "package_request_presents z (Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))"
    obtain E' u' r' where g: "fst z=(E',(u',r'))" by (rule prod_cases3)
    obtain ds' F' v' q' where w: "snd z=(ds',(F',(v',q')))" by (rule prod_cases4)
    have z: "z=((E',(u',r')),(ds',(F',(v',q'))))" using g w surjective_pairing[of z] by simp
    obtain a' b' where eq: "Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b)=
        Pair_Term a' (Pair_Term (data_list_term (map definition_site_value ds')) b')"
      and a': "site_value_presents E' u' r' a'" and b': "site_value_presents F' v' q' b'"
      using presents unfolding z package_request_presents_at by blast
    have "ds'=ds" using eq data_list_term_injective inj_map_eq_map[OF definition_site_value_injective] by simp
    then show ?thesis using z eq site_value_presents_unique[OF given, of E' u' r'] a'
      site_value_presents_unique[OF scope, of F' v' q'] b' by simp
  qed
  have presents: "package_request_presents ((E,(u,r)),(ds,(F,(v,q))))
      (Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))"
    unfolding package_request_presents_at using given scope by blast
  have "presented_predicate package_request_presents package_request_relation
      (Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b)) \<longleftrightarrow>
    package_request_relation ((E,(u,r)),(ds,(F,(v,q))))"
    unfolding presented_predicate_def using unique presents by blast
  then show ?thesis unfolding package_request_exact package_request_relation_def by simp
qed

corollary package_request_presentation_invariance:
  assumes "site_value_presents E u r a" "site_value_presents E u r a'"
    "site_value_presents F v q b" "site_value_presents F v q b'"
  shows "(561,Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))
      \<in>positive_meaning package_request_system \<longleftrightarrow>
    (561,Pair_Term a' (Pair_Term (data_list_term (map definition_site_value ds)) b'))
      \<in>positive_meaning package_request_system"
  using package_request_on_values[OF assms(1,3)] package_request_on_values[OF assms(2,4)] by simp

subsection \<open>The least scope of a support\<close>

text \<open>
  The support's sites reach, in the given's environment, the given package's definitions and no others;
  the program they read is the context's package, each definition with its meaning in the given, and the
  context's environment is its package's least.
\<close>

lemma native_package_support_formed:
  assumes package: "native_package_at E u r P" and support: "D\<subseteq>system_definitions P"
  shows "native_package_formed E D" and "native_definition_sites E D\<subseteq>system_definitions P"
proof -
  obtain Q where "native_root_family_at E u r Q" and formed: "native_package_formed E (rel_ran Q)"
    and program: "P=native_program E (rel_ran Q)"
    using package unfolding native_package_at_def by blast
  have program_defs: "system_definitions P=native_definition_sites E (rel_ran Q)"
    using native_program_definitions[OF formed] program by simp
  show sites: "native_definition_sites E D\<subseteq>system_definitions P"
    unfolding program_defs by (rule native_definition_sites_least) (use support program_defs native_definition_step in auto)
  show "native_package_formed E D" using formed sites program_defs by (auto simp: native_package_formed_def)
qed


theorem package_request_least_scope:
  assumes holds: "package_request_holds (E,(u,r)) ds (F,(v,q))"
    and given: "native_package_at E u r P" and scope: "closed_native_package_at F v q Q"
  shows "Q=native_program E (set ds)" and "set ds\<subseteq>system_definitions Q"
    and "system_definitions Q=native_definition_sites E (set ds)"
    and "system_definitions Q\<subseteq>system_definitions P"
    and "\<And>d t. d\<in>system_definitions Q \<Longrightarrow> (d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    and "native_package_environment F v q=F"
    and "\<exists>Qr. native_root_family_at F v q Qr \<and> rel_ran Qr=set ds"
proof -
  obtain P' where P': "native_package_at E u r P'" and inside': "set ds\<subseteq>system_definitions P'"
    using holds by (auto simp: package_request_holds_def)
  have inside: "set ds\<subseteq>system_definitions P" using native_package_unique[OF P' given] inside' by simp
  obtain R xs where artifact: "artifact_at F v R" and separate: "distinct xs" and family: "family_at R q (set xs)"
    and reading: "list_all2 (\<lambda>a d. located_at F v a (fst d) (snd d)) (map snd xs) ds"
    using holds by (auto simp: package_request_holds_def)
  obtain W where W: "environment_formed W" and incl_E: "environment_included E W" and incl_F: "environment_included F W"
    using holds by (auto simp: package_request_holds_def)
  have package: "native_package_at F v q Q" using scope by (simp add: closed_native_package_at_def)
  have formed_F: "environment_formed F" by (rule native_package_formed_at[OF package])
  have roots: "native_root_family_at F v q (set (zip (map fst xs) ds))" and range: "rel_ran (set (zip (map fst xs) ds))=set ds"
    using native_root_family_from_list[OF formed_F artifact family separate reading] by blast+
  show "\<exists>Qr. native_root_family_at F v q Qr \<and> rel_ran Qr=set ds" using roots range by blast
  obtain Qr where Qr: "native_root_family_at F v q Qr" and formed_Qr: "native_package_formed F (rel_ran Qr)"
    and program: "Q=native_program F (rel_ran Qr)"
    using package by (auto simp: native_package_at_def)
  have "Qr=set (zip (map fst xs) ds)" by (rule native_root_family_unique[OF Qr roots])
  then have from_support: "native_package_formed F (set ds)" "Q=native_program F (set ds)"
    using formed_Qr program range by simp_all
  have given_support: "native_package_formed E (set ds)" "native_definition_sites E (set ds)\<subseteq>system_definitions P"
    using native_package_support_formed[OF given inside] by blast+
  have "native_program W (set ds)=native_program F (set ds)"
    using native_dependency_package_included[OF from_support(1) incl_F W] by blast
  moreover have "native_program W (set ds)=native_program E (set ds)"
    using native_dependency_package_included[OF given_support(1) incl_E W] by blast
  ultimately show program_E: "Q=native_program E (set ds)" using from_support(2) by simp
  show program_defs: "system_definitions Q=native_definition_sites E (set ds)"
    using native_program_definitions[OF given_support(1)] program_E by simp
  show "set ds\<subseteq>system_definitions Q" using program_defs native_definition_roots by blast
  show "system_definitions Q\<subseteq>system_definitions P" using program_defs given_support(2) by simp
  show "native_package_environment F v q=F" by (rule native_package_closed_environment_fixed[OF scope])
  fix d t assume member: "d\<in>system_definitions Q"
  have in_P: "d\<in>system_definitions P" using member program_defs given_support(2) by blast
  show "(d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    using native_packages_shared_meaning[OF native_package_included[OF package incl_F W]
      native_package_included[OF given incl_E W] member in_P] .
qed

subsection \<open>Every support of a package has its context\<close>

text \<open>
  A root family whose sockets are a distinct key list, each key citing the support site at its position,
  is read at exactly that support.
\<close>

lemma root_family_reading_listed:
  assumes raw: "native_root_family_at E u r (set (zip ks ds))" and keys: "distinct ks"
    and len: "length ks=length ds"
  shows "\<exists>R xs. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
    list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
proof -
  obtain R M where source: "artifact_at E u R" and family: "family_at R r M"
    and domain: "rel_dom (set (zip ks ds))=rel_dom M"
    and children: "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>d. (s,d)\<in>set (zip ks ds) \<and> located_at E u a (fst d) (snd d))"
    using raw unfolding native_root_family_at_def by (elim conjE exE) (rule that; assumption)
  have sv: "single_valued M" using family by (simp add: family_at_def)
  have zsv: "single_valued (set (zip ks ds))" by (rule single_valued_zip[OF keys])
  have keys_M: "rel_dom M=set ks" using trans[OF domain[symmetric] zip_domain[OF len]] .
  define f where "f k=rel_value M k" for k
  have member: "(k,f k)\<in>M" if in_ks: "k\<in>set ks" for k
  proof -
    obtain a where "(k,a)\<in>M" using in_ks keys_M unfolding rel_dom_def by blast
    then show ?thesis using rel_value_eq[OF sv] by (simp add: f_def)
  qed
  let ?xs = "map (\<lambda>k. (k,f k)) ks"
  have separate: "distinct ?xs" using keys by (simp add: distinct_map inj_on_def)
  have rows: "set ?xs=M"
  proof
    show "set ?xs\<subseteq>M" using member by auto
    show "M\<subseteq>set ?xs"
    proof
      fix z assume z: "z\<in>M"
      obtain k a where zk: "z=(k,a)" by (cases z)
      have k: "k\<in>set ks" using z zk keys_M by (auto simp: rel_dom_def)
      have "a=f k" by (rule single_valued_outputs[OF sv z[unfolded zk] member[OF k]])
      then show "z\<in>set ?xs" using zk k by auto
    qed
  qed
  have reading: "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd ?xs) ds"
  proof (rule list_all2_all_nthI)
    show "length (map snd ?xs)=length ds" using len by simp
    fix i assume i: "i<length (map snd ?xs)"
    then have ik: "i<length ks" by simp
    obtain d where row: "(ks!i,d)\<in>set (zip ks ds)" and at: "located_at E u (f (ks!i)) (fst d) (snd d)"
      using children member[OF nth_mem[OF ik]] by blast
    have "(ks!i,ds!i)\<in>set (zip ks ds)" using nth_mem[of i "zip ks ds"] ik len by simp
    then have "d=ds!i" by (rule single_valued_outputs[OF zsv row])
    then show "located_at E u (map snd ?xs!i) (fst (ds!i)) (snd (ds!i))" using at ik by simp
  qed
  have family_rows: "family_at R r (set ?xs)" using family rows by simp
  show ?thesis using source separate family_rows reading by blast
qed

text \<open>
  The context of a support is constructed by the executable root selector over the support in a finite
  presentation of the given's environment (@{thm [source] finite_select_roots_correct}), restricted to its
  package's least scope (@{thm [source] native_package_closed_restriction}); the selector's own environment
  includes both.
\<close>

theorem package_request_complete:
  assumes given: "native_package_at E u r P" and support: "set ds\<subseteq>system_definitions P"
  shows "\<exists>F v. package_request_holds (E,(u,r)) ds (F,(v,[])) \<and> native_package_environment F v []=F"
proof -
  have formed_E: "environment_formed E" by (rule native_package_formed_at[OF given])
  obtain C where C: "finite_environment_formed C" and decoded: "decode_finite_environment C=E"
    using finite_environment_representation[OF formed_E] by blast
  obtain G0 w where selected: "finite_select_roots C ds=(G0,w)" by (cases "finite_select_roots C ds") blast
  have targets: "set ds\<subseteq>environment_positions (decode_finite_environment C)"
  proof
    fix d assume d: "d\<in>set ds"
    obtain R where "artifact_at E (fst d) R" "anchor_formed (R,snd d)"
      using native_package_definition_anchor[OF given] d support by blast
    then show "d\<in>environment_positions (decode_finite_environment C)"
      using decoded by (cases d) (auto simp: anchor_formed_def)
  qed
  note correct = finite_select_roots_correct[OF C targets selected]
  define G where "G=decode_finite_environment G0"
  have formed_G: "environment_formed G" using correct(1) by (simp add: G_def finite_environment_formed_correct)
  have incl_EG: "environment_included E G" using correct(2) decoded by (simp add: G_def)
  have family_G: "native_root_family_at G w [] (set (zip (family_ports (length ds)) ds))"
    and range: "rel_ran (set (zip (family_ports (length ds)) ds))=set ds"
    using correct(4,5) by (simp_all add: G_def)
  have formed_support: "native_package_formed G (set ds)"
    using native_dependency_package_included[OF native_package_support_formed(1)[OF given support] incl_EG formed_G]
    by blast
  have package_G: "native_package_at G w [] (native_program G (set ds))"
    unfolding native_package_at_def using family_G range formed_support by (intro exI[of _ "set (zip (family_ports (length ds)) ds)"]) simp
  define F where "F=native_package_environment G w []"
  have closed: "closed_native_package_at F w [] (native_program G (set ds))"
    unfolding F_def by (rule native_package_closed_restriction[OF package_G])
  have package_F: "native_package_at F w [] (native_program G (set ds))"
    using closed by (simp add: closed_native_package_at_def)
  have incl_FG: "environment_included F G" unfolding F_def by (rule native_package_environment_included)
  obtain Qf where Qf: "native_root_family_at F w [] Qf"
    using package_F by (auto simp: native_package_at_def)
  have "Qf=set (zip (family_ports (length ds)) ds)"
    using native_root_family_unique[OF native_root_family_included[OF Qf incl_FG formed_G] family_G] .
  then have family_F: "native_root_family_at F w [] (set (zip (family_ports (length ds)) ds))" using Qf by simp
  have reading: "\<exists>R xs. artifact_at F w R \<and> distinct xs \<and> family_at R [] (set xs) \<and>
      list_all2 (\<lambda>a d. located_at F w a (fst d) (snd d)) (map snd xs) ds"
    by (rule root_family_reading_listed[OF family_F]) simp_all
  have "package_request_holds (E,(u,r)) ds (F,(w,[]))"
    unfolding package_request_holds_def using given support reading closed formed_G incl_EG incl_FG by auto
  then show ?thesis using native_package_closed_environment_fixed[OF closed] by blast
qed

corollary package_request_complete_presented:
  assumes given: "native_package_at E u r P" and support: "set ds\<subseteq>system_definitions P"
    and given_site: "site_value_presents E u r a"
  shows "\<exists>b. (561,Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))
    \<in>positive_meaning package_request_system"
proof -
  obtain F v where holds: "package_request_holds (E,(u,r)) ds (F,(v,[]))"
    using package_request_complete[OF given support] by blast
  obtain Q where "closed_native_package_at F v [] Q" using holds by (auto simp: package_request_holds_def)
  then have package: "native_package_at F v [] Q" by (simp add: closed_native_package_at_def)
  obtain b where b: "site_value_presents F v [] b"
    using site_value_presents_total[OF native_package_formed_at[OF package] native_package_site_position[OF package]]
    by blast
  show ?thesis using package_request_on_values[OF given_site b] holds by blast
qed

subsection \<open>The packet\<close>

text \<open>
  The packet pairs the question's term with the context's site value. The support is read back from the
  context's root family (@{thm [source] package_request_least_scope}) and is not stored again.
\<close>

definition package_request_packet :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "package_request_packet x c=Pair_Term x c"

lemma package_request_packet_recovers:
  assumes "package_request_packet x c=package_request_packet y c'"
    and "site_value_presents F v q c" and "site_value_presents F' v' q' c'"
  shows "x=y \<and> F=F' \<and> v=v' \<and> q=q'"
  using assms site_value_presents_unique[of F v q c F' v' q'] by (simp add: package_request_packet_def)

lemma package_request_packet_formed:
  assumes "term_formed x" "self_contained_term x" and "site_value_presents F v q c"
  shows "term_formed (package_request_packet x c) \<and> self_contained_term (package_request_packet x c)"
  using assms site_value_presents_formed[OF assms(3)] by (simp add: package_request_packet_def)

subsection \<open>The payloads the two definitions read\<close>

lemma package_request_leaves:
  "schema_leaves package_request_schema={}"
  "(c,S)\<in>context_list_clauses 83 560 \<Longrightarrow> schema_leaves S\<subseteq>{Payload_Term []}"
  by (auto simp: schema_leaves_def package_request_schema_def context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

subsection \<open>The least package environment commutes with use permutations\<close>

lemma native_package_environment_renamed:
  fixes E :: "local_address option artifact_environment" and h :: "local_address option \<Rightarrow> local_address option"
  assumes h: "bij h" and package: "native_package_at E u r P"
  shows "native_package_environment (rename_environment h E) (h u) r=
    rename_environment h (native_package_environment E u r)"
proof -
  have package_ren: "(\<exists>Q. native_package_at (rename_environment g X) (g a) b Q) \<longleftrightarrow> (\<exists>Q. native_package_at X a b Q)"
    if "bij g" "environment_formed X" "(a,b)\<in>environment_positions X"
    for g :: "local_address option \<Rightarrow> local_address option" and X :: "local_address option artifact_environment" and a b
    using package_admission_equivariant[unfolded renaming_equivariant_def, rule_format, OF that(1), of "(X,(a,b))"]
      that(2,3) by simp
  have closed_ren: "(\<exists>Q. closed_native_package_at (rename_environment g X) (g a) b Q) \<longleftrightarrow>
      (\<exists>Q. closed_native_package_at X a b Q)"
    if "bij g" "environment_formed X" "(a,b)\<in>environment_positions X"
    for g :: "local_address option \<Rightarrow> local_address option" and X :: "local_address option artifact_environment" and a b
    using package_retention_admission_equivariant[unfolded renaming_equivariant_def, rule_format, OF that(1),
      of "(X,(a,b))"] that(2,3) by simp
  have incl_ren: "environment_included (rename_environment g A) (rename_environment g B) \<longleftrightarrow> environment_included A B"
    if "bij g" "environment_formed A" "environment_formed B"
    for g :: "local_address option \<Rightarrow> local_address option" and A B :: "local_address option artifact_environment"
    using environment_inclusion_equivariant[unfolded renaming_equivariant_def, rule_format, OF that(1), of "(A,B)"]
      that(2,3) by simp
  have ren_formed: "environment_formed (rename_environment g X)" if "bij g" "environment_formed X"
    for g :: "local_address option \<Rightarrow> local_address option" and X :: "local_address option artifact_environment"
    using environment_renaming_formed[OF that(2) bij_is_inj[OF that(1)]] .
  let ?M = "native_package_environment E u r"
  let ?N = "native_package_environment (rename_environment h E) (h u) r"
  have formed_E: "environment_formed E" by (rule native_package_formed_at[OF package])
  have closed_M: "closed_native_package_at ?M u r P" by (rule native_package_closed_restriction[OF package])
  have package_M: "native_package_at ?M u r P" using closed_M by (simp add: closed_native_package_at_def)
  have formed_M: "environment_formed ?M" by (rule native_package_formed_at[OF package_M])
  obtain PE where package_RE: "native_package_at (rename_environment h E) (h u) r PE"
    using package_ren[OF h formed_E native_package_site_position[OF package]] package by blast
  obtain PM where closed_RM: "closed_native_package_at (rename_environment h ?M) (h u) r PM"
    using closed_ren[OF h formed_M native_package_site_position[OF package_M]] closed_M by blast
  have package_RM: "native_package_at (rename_environment h ?M) (h u) r PM"
    using closed_RM by (simp add: closed_native_package_at_def)
  have incl_RM: "environment_included (rename_environment h ?M) (rename_environment h E)"
    using incl_ren[OF h formed_M formed_E] native_package_environment_included[of E u r] by simp
  have N_M: "environment_included ?N (rename_environment h ?M)"
    by (rule native_package_dependency_material_required[OF package_RE package_RM incl_RM])
  have closed_N: "closed_native_package_at ?N (h u) r PE" by (rule native_package_closed_restriction[OF package_RE])
  have package_N: "native_package_at ?N (h u) r PE" using closed_N by (simp add: closed_native_package_at_def)
  have formed_N: "environment_formed ?N" by (rule native_package_formed_at[OF package_N])
  have inverse: "bij (inv h)" by (rule bij_imp_bij_inv[OF h])
  have back_u: "inv h (h u)=u" by (rule inv_f_f[OF bij_is_inj[OF h]])
  have "\<exists>Q. closed_native_package_at (rename_environment (inv h) ?N) (inv h (h u)) r Q"
    using closed_ren[OF inverse formed_N native_package_site_position[OF package_N]] closed_N by blast
  then obtain PN where closed_IN: "closed_native_package_at (rename_environment (inv h) ?N) u r PN"
    unfolding back_u by blast
  have package_IN: "native_package_at (rename_environment (inv h) ?N) u r PN"
    using closed_IN by (simp add: closed_native_package_at_def)
  have undo_E: "rename_environment (inv h) (rename_environment h E)=E"
    using rename_environment_comp[of "inv h" h E] inj_iff[THEN iffD1, OF bij_is_inj[OF h]] by simp
  have "environment_included (rename_environment (inv h) ?N) (rename_environment (inv h) (rename_environment h E))"
    using incl_ren[OF inverse formed_N ren_formed[OF h formed_E]]
      native_package_environment_included[of "rename_environment h E" "h u" r] by simp
  then have incl_IN: "environment_included (rename_environment (inv h) ?N) E" using undo_E by simp
  have M_IN: "environment_included ?M (rename_environment (inv h) ?N)"
    by (rule native_package_dependency_material_required[OF package package_IN incl_IN])
  have redo_N: "rename_environment h (rename_environment (inv h) ?N)=?N"
    using rename_environment_comp[of h "inv h" ?N] surj_iff[THEN iffD1, OF bij_is_surj[OF h]] by simp
  have "environment_included (rename_environment h ?M) (rename_environment h (rename_environment (inv h) ?N))"
    using incl_ren[OF h formed_M ren_formed[OF inverse formed_N]] M_IN by simp
  then have M_N: "environment_included (rename_environment h ?M) ?N" using redo_N by simp
  show ?thesis by (rule environment_included_antisym[OF N_M M_N])
qed

subsection \<open>The request is equivariant under permutations of uses\<close>

text \<open>
  One permutation acts on the given, every support site and the context at once. The relation is the
  conjunction of the five readers' relations, each equivariant by its own clause: package admission and
  membership at the given (@{thm [source] package_admission_equivariant},
  @{thm [source] package_membership_equivariant}), the root family reading and retention at the context
  (@{thm [source] root_family_reading_equivariant}, @{thm [source] package_retention_admission_equivariant}),
  and the compatibility, the composition of inclusion with inclusion through one environment
  (@{thm [source] renaming_equivariant_relation_compose} at @{thm [source] environment_renaming_action} and
  @{thm [source] environment_inclusion_equivariant}).
\<close>

abbreviation package_request_renaming where
  "package_request_renaming \<equiv> product_action site_context_renaming
    (product_action (\<lambda>h. map (map_prod h id)) site_context_renaming)"

abbreviation package_request_domain where
  "package_request_domain \<equiv> \<lambda>z. site_context_formed (fst z) \<and>
    ((\<forall>a\<in>set (fst (snd z)). True) \<and> site_context_formed (snd (snd z)))"

theorem package_request_equivariant:
  "renaming_equivariant bij package_request_renaming package_request_domain package_request_relation"
  unfolding renaming_equivariant_def
proof (intro allI impI)
  fix h :: "local_address option \<Rightarrow> local_address option"
    and z :: "site_context \<times> (local_address option definition_site list \<times> site_context)"
  assume h: "bij h" and domain: "package_request_domain z"
  obtain E u r where g: "fst z=(E,(u,r))" by (rule prod_cases3)
  obtain ds F v q where w: "snd z=(ds,(F,(v,q)))" by (rule prod_cases4)
  have z: "z=((E,(u,r)),(ds,(F,(v,q))))" using g w surjective_pairing[of z] by simp
  have formed_E: "environment_formed E" and position_E: "(u,r)\<in>environment_positions E"
    and formed_F: "environment_formed F" and position_F: "(v,q)\<in>environment_positions F"
    using domain z by auto
  have admission: "(\<exists>P. native_package_at (rename_environment h E) (h u) r P) \<longleftrightarrow> (\<exists>P. native_package_at E u r P)"
    using package_admission_equivariant[unfolded renaming_equivariant_def, rule_format, OF h, of "(E,(u,r))"]
      formed_E position_E by simp
  have membership: "(\<exists>P. native_package_at (rename_environment h E) (h u) r P \<and> map_prod h id d\<in>system_definitions P)
      \<longleftrightarrow> (\<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P)" for d
    using package_membership_equivariant[unfolded renaming_equivariant_def, rule_format, OF h, of "((E,(u,r)),d)"]
      formed_E position_E by simp
  have members: "(\<exists>P. native_package_at (rename_environment h E) (h u) r P \<and>
      set (map (map_prod h id) ds)\<subseteq>system_definitions P) \<longleftrightarrow>
    (\<exists>P. native_package_at E u r P \<and> set ds\<subseteq>system_definitions P)"
    unfolding native_package_members_iff using admission membership by auto
  have roots: "(\<exists>R xs. artifact_at (rename_environment h F) (h v) R \<and> distinct xs \<and> family_at R q (set xs) \<and>
      list_all2 (\<lambda>a d. located_at (rename_environment h F) (h v) a (fst d) (snd d)) (map snd xs)
        (map (map_prod h id) ds)) \<longleftrightarrow>
    (\<exists>R xs. artifact_at F v R \<and> distinct xs \<and> family_at R q (set xs) \<and>
      list_all2 (\<lambda>a d. located_at F v a (fst d) (snd d)) (map snd xs) ds)"
    using root_family_reading_equivariant[unfolded renaming_equivariant_def, rule_format, OF h, of "((F,v),(q,ds))"]
      formed_F by simp
  have closed: "(\<exists>Q. closed_native_package_at (rename_environment h F) (h v) q Q) \<longleftrightarrow>
      (\<exists>Q. closed_native_package_at F v q Q)"
    using package_retention_admission_equivariant[unfolded renaming_equivariant_def, rule_format, OF h, of "(F,(v,q))"]
      formed_F position_F by simp
  have exchanged: "renaming_equivariant bij (product_action rename_environment rename_environment)
      (\<lambda>z. environment_formed (fst z) \<and> environment_formed (snd z)) (\<lambda>z. environment_included (snd z) (fst z))"
    by (rule iffD2[OF renaming_equivariant_relation[where Q="\<lambda>a b. environment_included b a"]])
      (use environment_inclusion_equivariant[unfolded renaming_equivariant_relation] in blast)
  have composed: "renaming_equivariant bij (product_action rename_environment rename_environment)
      (\<lambda>z. environment_formed (fst z) \<and> environment_formed (snd z))
      (\<lambda>z. \<exists>W. environment_formed W \<and> environment_included (fst z) W \<and> environment_included (snd z) W)"
    by (rule renaming_equivariant_relation_compose[OF environment_renaming_action
      environment_inclusion_equivariant exchanged])
  have compatible: "(\<exists>W. environment_formed W \<and> environment_included (rename_environment h E) W \<and>
      environment_included (rename_environment h F) W) \<longleftrightarrow>
    (\<exists>W. environment_formed W \<and> environment_included E W \<and> environment_included F W)"
    using composed[unfolded renaming_equivariant_def, rule_format, OF h, of "(E,F)"] formed_E formed_F by simp
  show "package_request_relation (package_request_renaming h z) \<longleftrightarrow> package_request_relation z"
    unfolding z package_request_relation_def package_request_holds_def
    using members roots closed compatible by simp
qed


text \<open>
  In its presented form the entry's observation is invariant along every renaming correspondence of the
  three fields' classes: the notion's contract (@{thm [source] presented_predicate_renaming}) at the product
  of the site value, sequence and site value classes.
\<close>

corollary package_request_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence package_request_presents package_request_renaming h) (=)
    (\<lambda>z. (561,z)\<in>positive_meaning package_request_system)
    (\<lambda>z. (561,z)\<in>positive_meaning package_request_system)"
  by (rule iffD2[OF presented_predicate_renaming[OF
      factor_pair_class[OF site_presentations.presentation_class_axioms
        factor_pair_class[OF data_sequence_presentation_class[OF site_coordinate_presentation]
          site_presentations.presentation_class_axioms]]
      renaming_action_product[OF site_context_renaming_action
        renaming_action_product[OF renaming_action_lists[OF site_renaming_action] site_context_renaming_action]]
      package_request_exact] package_request_equivariant])

end
