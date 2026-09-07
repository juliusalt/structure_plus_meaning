theory Factor_Definition_Callee_Inclusion
  imports Factor_Schema_Callee_Inclusion
begin

section \<open>Complete family properties belong to every actual socket\<close>

lemma native_schema_family_at_graph:
  assumes family: "native_schema_family_at E u r C" and source: "artifact_at E u R" and graph: "family_at R r M"
  shows "(c,S)\<in>C \<longleftrightarrow> (\<exists>a. (c,a)\<in>M \<and> native_schema_at E u a S)"
    and "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
proof -
  obtain A N where parts: "environment_formed E" "artifact_at E u A" "family_at A r N"
    "single_valued C" "rel_dom C=rel_dom N"
    "\<forall>s a. (s,a)\<in>N \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using family by (auto simp: native_schema_family_at_def)
  have same: "A=R" by (rule environment_artifact_unique[OF parts(1,2) source])
  have other: "family_at R r N" using parts(3) same by simp
  have edges: "N=M" by (rule family_at_unique[OF other graph])
  have domain: "rel_dom C=rel_dom M" using parts(5) edges by simp
  have reads: "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using parts(6) edges by simp
  show "(c,S)\<in>C \<longleftrightarrow> (\<exists>a. (c,a)\<in>M \<and> native_schema_at E u a S)"
  proof
    assume member: "(c,S)\<in>C"
    have "c\<in>rel_dom M" using member domain by (auto simp: rel_dom_def)
    then obtain a where edge: "(c,a)\<in>M" by (auto simp: rel_dom_def)
    obtain T where read: "(c,T)\<in>C" "native_schema_at E u a T" using reads edge by blast
    have same: "T=S" by (rule single_valued_outputs[OF parts(4) read(1) member])
    show "\<exists>a. (c,a)\<in>M \<and> native_schema_at E u a S" using edge read(2) same by blast
  next
    assume "\<exists>a. (c,a)\<in>M \<and> native_schema_at E u a S"
    then obtain a where edge: "(c,a)\<in>M" and raw: "native_schema_at E u a S" by blast
    obtain T where read: "(c,T)\<in>C" "native_schema_at E u a T" using reads edge by blast
    have same: "T=S" by (rule native_schema_unique[OF read(2) raw])
    show "(c,S)\<in>C" using read(1) same by simp
  qed
  show "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)" by (rule reads)
qed

lemma native_schema_family_property:
  assumes family: "native_schema_family_at E u r C" and source: "artifact_at E u R" and graph: "family_at R r M"
  shows "(\<forall>s S. (s,S)\<in>C \<longrightarrow> P S) \<longleftrightarrow>
    (\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. native_schema_at E u a S \<and> P S))"
proof
  assume property: "\<forall>s S. (s,S)\<in>C \<longrightarrow> P S"
  show "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. native_schema_at E u a S \<and> P S)"
    using native_schema_family_at_graph(2)[OF family source graph] property by blast
next
  assume property: "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. native_schema_at E u a S \<and> P S)"
  show "\<forall>s S. (s,S)\<in>C \<longrightarrow> P S"
  proof (intro allI impI)
    fix s S assume member: "(s,S)\<in>C"
    obtain a where edge: "(s,a)\<in>M" and raw: "native_schema_at E u a S"
      using member by (simp only: native_schema_family_at_graph(1)[OF family source graph]) blast
    obtain T where read: "native_schema_at E u a T" "P T" using property edge by blast
    have same: "S=T" by (rule native_schema_unique[OF raw read(1)])
    show "P S" using read(2) same by simp
  qed
qed

lemma native_definition_record_family:
  assumes raw: "native_definition_at E u r p C" and source: "artifact_at E u R"
    and rec: "record_at R r ps [i,m]"
  shows "native_schema_family_at E u m C"
proof -
  obtain A qs j n where parts: "environment_formed E" "artifact_at E u A"
    "record_at A r qs [j,n]" "native_schema_family_at E u n C"
    using raw by (auto simp: native_definition_at_def)
  have same: "A=R" by (rule environment_artifact_unique[OF parts(1,2) source])
  have other: "record_at R r qs [j,n]" using parts(3) same by simp
  have "n=m" using record_at_unique[OF other rec] by auto
  then show ?thesis using parts(4) by simp
qed

section \<open>Every actual definition clause checks its callees\<close>

abbreviation definition_callee_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "definition_callee_argument e w d \<equiv> Pair_Term (Pair_Term e w) d"

abbreviation definition_callee_inclusion_result :: "factor_term \<Rightarrow> bool" where
  "definition_callee_inclusion_result z \<equiv> \<exists>E e ys u r p C.
    z=definition_callee_argument e (data_list_term ys) (site_data_term u r) \<and>
    environment_value_presents E e \<and> data_elements ys \<and> native_definition_at E u r p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"

definition definition_callee_inclusion_schema :: "(nat,nat,nat) factor_schema" where
  "definition_callee_inclusion_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,72,citation_observation_pattern data_x data_z data_w (Pattern_Variable 4)),
     (1,37,artifact_lookup_pattern data_x data_z (Pattern_Variable 5)),
     (2,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) data_w)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 8),
         Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 9)])),
     (3,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9)) (Pattern_Variable 10)),
     (4,59,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)),
     (5,74,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Variable 11)),
     (6,47,Pattern_Pair (Pattern_Payload []) data_y)}"

definition definition_callee_inclusion_system :: "(nat,nat,nat,nat) schema_system" where
  "definition_callee_inclusion_system=add_view_definition schema_callee_list_system 75 data_x {(0,definition_callee_inclusion_schema)}"

lemma definition_callee_inclusion_system_formed [simp]: "schema_system_formed definition_callee_inclusion_system"
  unfolding definition_callee_inclusion_system_def
  by (rule add_recursive_definition_formed[OF schema_callee_list_system_formed])
    (auto simp: definition_callee_inclusion_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma definition_callee_inclusion_definitions [simp]:
  "system_definitions definition_callee_inclusion_system=insert 75 (system_definitions schema_callee_list_system)"
  by (simp add: definition_callee_inclusion_system_def)

lemma definition_callee_inclusion_call:
  "schema_call_formed definition_callee_inclusion_system d t \<longleftrightarrow>
    d\<in>system_definitions definition_callee_inclusion_system \<and> term_formed t"
  using added_variable_calls[OF schema_callee_list_system_formed
    definition_callee_inclusion_system_formed[unfolded definition_callee_inclusion_system_def] schema_callee_list_call]
  by (simp only: definition_callee_inclusion_system_def[symmetric])

lemma definition_callee_inclusion_old_meaning:
  assumes "d\<in>system_definitions schema_callee_list_system"
  shows "(d,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (d,t)\<in>positive_meaning schema_callee_list_system"
  using added_definition_preserves_old(2)[OF schema_callee_list_system_formed
    definition_callee_inclusion_system_formed[unfolded definition_callee_inclusion_system_def], of d t] assms
  by (auto simp: definition_callee_inclusion_system_def)

lemma definition_callee_inclusion_clause [simp]:
  "((75,c),S)\<in>system_clauses definition_callee_inclusion_system \<longleftrightarrow> (c,S)\<in>{(0,definition_callee_inclusion_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses schema_callee_list_system \<Longrightarrow>
    d\<in>system_definitions schema_callee_list_system" for d c S
    using schema_callee_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((75,c),S)\<notin>system_clauses schema_callee_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: definition_callee_inclusion_system_def)
qed

lemma definition_callee_previous_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning definition_call_admission_system"
  using definition_callee_inclusion_old_meaning[of d t] schema_callee_list_old_meaning[of d t]
    schema_callee_inclusion_old_meaning[OF assms, of t] assms by auto

lemma definition_callee_inclusion_components:
  "(72,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (72,t)\<in>positive_meaning definition_call_admission_system"
  "(37,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(59,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(74,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (74,t)\<in>positive_meaning schema_callee_list_system"
  "(47,t)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  using definition_callee_previous_meaning[of 72 t]
    definition_callee_previous_meaning[of 37 t] definition_call_admission_components(1)[of t]
    definition_callee_previous_meaning[of 34 t] definition_call_admission_components(2)[of t]
    definition_callee_previous_meaning[of 32 t] definition_call_admission_old_meaning[of 32 t]
    schema_family_admission_components(2)[of t]
    definition_callee_previous_meaning[of 59 t] definition_call_admission_old_meaning[of 59 t]
    schema_family_admission_components(3)[of t]
    definition_callee_inclusion_old_meaning[of 74 t]
    definition_callee_inclusion_old_meaning[of 47 t] schema_callee_list_old_meaning[of 47 t]
    schema_callee_inclusion_components(4)[of t] by auto

lemma definition_callee_inclusion_step:
  assumes admission: "(72,citation_observation_argument e u r t)\<in>positive_meaning definition_call_admission_system"
    and lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p i,Pair_Term q m]))\<in>positive_meaning record_admission_system"
    and family: "(32,rooted_rows_argument a m rows)\<in>positive_meaning family_admission_system"
    and projection: "(59,Pair_Term rows roots)\<in>positive_meaning row_values_system"
    and children: "(74,Pair_Term (Pair_Term e (Pair_Term w u)) roots)\<in>positive_meaning schema_callee_list_system"
    and bound: "(47,Pair_Term (Payload_Term []) w)\<in>positive_meaning data_subset_system"
  shows "(75,definition_callee_argument e w (Pair_Term u r))\<in>positive_meaning definition_callee_inclusion_system"
proof -
  have formed: "term_formed e" "term_formed w" "term_formed u" "term_formed r" "term_formed t"
    "term_formed a" "term_formed p" "term_formed q" "term_formed i" "term_formed m" "term_formed rows" "term_formed roots"
    using schema_call_formed_target[OF positive_meaning_formed[OF admission]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF projection]]
      schema_call_formed_target[OF positive_meaning_formed[OF bound]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then w else if n=2 then u else if n=3 then r
    else if n=4 then t else if n=5 then a else if n=6 then p else if n=7 then q
    else if n=8 then i else if n=9 then m else if n=10 then rows else roots"
  have result: "(75,evaluate_pattern ?h (schema_conclusion definition_callee_inclusion_schema))
      \<in>positive_meaning definition_callee_inclusion_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: definition_callee_inclusion_schema_def schema_variables_def
        definition_callee_inclusion_call definition_callee_inclusion_components\<close>)
  show ?thesis using result by (simp add: definition_callee_inclusion_schema_def)
qed

theorem definition_callee_inclusion_sound:
  assumes holds: "(75,z)\<in>positive_meaning definition_callee_inclusion_system"
  shows "definition_callee_inclusion_result z"
proof -
  have consequence: "(75,z)\<in>schema_consequences definition_callee_inclusion_system (positive_meaning definition_callee_inclusion_system)"
    using holds positive_meaning_unfold[of definition_callee_inclusion_system] by blast
  obtain n S h where clause: "((75,n),S)\<in>system_clauses definition_callee_inclusion_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning definition_callee_inclusion_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=definition_callee_inclusion_schema" using clause by simp
  have calls: "(72,citation_observation_argument (h 0) (h 2) (h 3) (h 4))\<in>positive_meaning definition_call_admission_system"
    "(37,artifact_lookup_argument (h 0) (h 2) (h 5))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 5) (h 3) (data_list_term [Pair_Term (h 6) (h 8),Pair_Term (h 7) (h 9)]))
      \<in>positive_meaning record_admission_system"
    "(32,rooted_rows_argument (h 5) (h 9) (h 10))\<in>positive_meaning family_admission_system"
    "(59,Pair_Term (h 10) (h 11))\<in>positive_meaning row_values_system"
    "(74,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (h 11))\<in>positive_meaning schema_callee_list_system"
    "(47,Pair_Term (Payload_Term []) (h 1))\<in>positive_meaning data_subset_system"
    using support by (auto simp: schema definition_callee_inclusion_schema_def definition_callee_inclusion_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 2=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 5)"
    using calls(2) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r p i q m where rec: "h 3=Payload_Term r" "h 6=Payload_Term p" "h 8=Payload_Term i"
    "h 7=Payload_Term q" "h 9=Payload_Term m" "record_at R r [p,q] [i,m]"
    using calls(3) by (simp only: record_admission_pair_fields[OF source(4)]) blast
  obtain xs where graph: "h 10=data_list_term (map address_pair_data xs)" "distinct xs" "family_at R m (set xs)"
    using calls(4) by (simp only: rec(5) family_admission_at_source[OF source(4)] factor_term.inject) blast
  obtain pat C where raw: "native_definition_at E u r pat C"
    using calls(1) by (simp only: source(2) rec(1) definition_call_admission_on_values[OF source(1)]) blast
  have family: "native_schema_family_at E u m C" by (rule native_definition_record_family[OF raw source(3) rec(6)])
  obtain ys where bound: "h 1=data_list_term ys" "data_elements ys"
    using calls(7) by (auto simp: data_subset_exact)
  have roots: "h 11=data_list_term (map Payload_Term (map snd xs))"
    using calls(5) by (simp only: graph(1) address_row_values)
  have children: "\<forall>s a. (s,a)\<in>set xs \<longrightarrow> (\<exists>T. native_schema_at E u a T \<and>
      (\<lambda>d. definition_site_value d) ` schema_dependencies T\<subseteq>set ys)"
    using calls(6) by (simp only: source(2) bound(1) roots schema_callee_list_on_values[OF source(1) bound(2)]) force
  have included: "\<forall>c T. (c,T)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies T\<subseteq>set ys"
    by (rule iffD2[OF native_schema_family_property[OF family source(3) graph(3)] children])
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ ys], rule exI[of _ u],
        rule exI[of _ r], rule exI[of _ pat], rule exI[of _ C])
      (use source rec bound raw included conclusion in \<open>simp add: schema definition_callee_inclusion_schema_def site_data_term_def\<close>)
qed

theorem definition_callee_inclusion_complete:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r pat C"
    and data: "data_elements ys"
    and included: "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
  shows "(75,definition_callee_argument e (data_list_term ys) (site_data_term u r))
    \<in>positive_meaning definition_callee_inclusion_system"
proof -
  obtain t where admission: "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
      \<in>positive_meaning definition_call_admission_system"
    using definition_call_admission_inhabited[OF source] raw by blast
  obtain R ps i m where parts: "artifact_at E u R" "record_at R r ps [i,m]" "native_schema_family_at E u m C"
    using raw by (auto simp: native_definition_at_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain A M where family: "artifact_at E u A" "family_at A m M"
    using parts(3) by (auto simp: native_schema_family_at_def)
  have same: "A=R" by (rule environment_artifact_unique[OF ef family(1) parts(1)])
  have graph: "family_at R m M" using family(2) same by simp
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  obtain p q where ports: "ps=[p,q]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  obtain xs where rows: "set xs=M" "distinct xs" using finite_distinct_list[OF family_socket_graph_finite[OF graph]] by blast
  let ?rows="data_list_term (map address_pair_data xs)"
  let ?roots="data_list_term (map Payload_Term (map snd xs))"
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term p) (Payload_Term i),Pair_Term (Payload_Term q) (Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF presented]) (use parts(2) in \<open>auto simp: ports\<close>)
  have family_read: "(32,rooted_rows_argument a (Payload_Term m) ?rows)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_rows[OF presented]) (use graph rows in auto)
  have rows_formed: "term_formed ?rows" using schema_call_formed_target[OF positive_meaning_formed[OF family_read]] by auto
  have projection: "(59,Pair_Term ?rows ?roots)\<in>positive_meaning row_values_system"
    by (simp only: address_row_values) (use rows_formed in blast)
  have property: "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. native_schema_at E u a S \<and>
      (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
    by (rule iffD1[OF native_schema_family_property[OF parts(3) parts(1) graph] included])
  have children: "(74,Pair_Term (Pair_Term e (Pair_Term (data_list_term ys) (use_data_term u))) ?roots)
      \<in>positive_meaning schema_callee_list_system"
    by (simp only: schema_callee_list_on_values[OF source data]) (use property rows(1) in \<open>auto; blast\<close>)
  have bound: "(47,Pair_Term (Payload_Term []) (data_list_term ys))\<in>positive_meaning data_subset_system"
    using data data_subset_complete[of "[]" ys] by simp
  show ?thesis
    using definition_callee_inclusion_step[OF admission lookup rec family_read projection children bound]
    by (simp only: site_data_term_def)
qed

theorem definition_callee_inclusion_exact:
  "(75,z)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow> definition_callee_inclusion_result z"
proof
  assume "(75,z)\<in>positive_meaning definition_callee_inclusion_system"
  then show "definition_callee_inclusion_result z" by (rule definition_callee_inclusion_sound)
next
  assume "definition_callee_inclusion_result z"
  then obtain E e ys u r p C where parts:
    "z=definition_callee_argument e (data_list_term ys) (site_data_term u r)"
    "environment_value_presents E e" "data_elements ys" "native_definition_at E u r p C"
    "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by auto
  show "(75,z)\<in>positive_meaning definition_callee_inclusion_system"
    by (simp only: parts(1); rule definition_callee_inclusion_complete[OF parts(2,4,3,5)])
qed

corollary definition_callee_inclusion_at_source:
  assumes source: "environment_value_presents E e"
  shows "(75,definition_callee_argument e w d)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow>
    (\<exists>ys u r p C. w=data_list_term ys \<and> d=site_data_term u r \<and> data_elements ys \<and>
      native_definition_at E u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys))"
proof
  assume holds: "(75,definition_callee_argument e w d)\<in>positive_meaning definition_callee_inclusion_system"
  obtain F f ys u r p C where parts:
    "definition_callee_argument e w d=definition_callee_argument f (data_list_term ys) (site_data_term u r)"
    "environment_value_presents F f" "data_elements ys" "native_definition_at F u r p C"
    "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
    using definition_callee_inclusion_sound[OF holds] by blast
  have input: "f=e" "w=data_list_term ys" "d=site_data_term u r" using parts(1) by auto
  have same: "F=E"
    by (rule environment_value_presents_unique[OF _ source]) (use parts(2) input(1) in simp)
  show "\<exists>ys u r p C. w=data_list_term ys \<and> d=site_data_term u r \<and> data_elements ys \<and>
    native_definition_at E u r p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
    by (rule exI[of _ ys], rule exI[of _ u], rule exI[of _ r], rule exI[of _ p], rule exI[of _ C])
      (use parts input same in simp)
next
  assume "\<exists>ys u r p C. w=data_list_term ys \<and> d=site_data_term u r \<and> data_elements ys \<and>
    native_definition_at E u r p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  then obtain ys u r p C where parts: "w=data_list_term ys" "d=site_data_term u r"
    "data_elements ys" "native_definition_at E u r p C"
    "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by blast
  show "(75,definition_callee_argument e w d)\<in>positive_meaning definition_callee_inclusion_system"
    by (simp only: parts(1,2); rule definition_callee_inclusion_complete[OF source parts(4,3,5)])
qed

corollary definition_callee_inclusion_on_values:
  assumes source: "environment_value_presents E e"
  shows "(75,definition_callee_argument e (data_list_term ys) (site_data_term u r))
      \<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow>
    data_elements ys \<and> (\<exists>p C. native_definition_at E u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys))"
  by (simp only: definition_callee_inclusion_at_source[OF source] data_list_term_injective site_data_term_eq) blast

corollary definition_callee_inclusion_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(75,definition_callee_argument e w d)\<in>positive_meaning definition_callee_inclusion_system \<longleftrightarrow>
    (75,definition_callee_argument f w d)\<in>positive_meaning definition_callee_inclusion_system"
  by (simp only: definition_callee_inclusion_at_source[OF assms(1)] definition_callee_inclusion_at_source[OF assms(2)])

section \<open>Every bound definition is itself checked\<close>

abbreviation definition_callee_list_result :: "factor_term \<Rightarrow> bool" where
  "definition_callee_list_result z \<equiv> \<exists>a xs. z=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. definition_callee_inclusion_result (Pair_Term a x))"

definition definition_callee_list_system :: "(nat,nat,nat,nat) schema_system" where
  "definition_callee_list_system=add_view_definition definition_callee_inclusion_system 76 data_x (context_list_clauses 75 76)"

lemma definition_callee_list_system_formed [simp]: "schema_system_formed definition_callee_list_system"
  unfolding definition_callee_list_system_def
  by (rule add_recursive_definition_formed[OF definition_callee_inclusion_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma definition_callee_list_definitions [simp]:
  "system_definitions definition_callee_list_system=insert 76 (system_definitions definition_callee_inclusion_system)"
  by (simp add: definition_callee_list_system_def)

lemma definition_callee_list_call:
  "schema_call_formed definition_callee_list_system d t \<longleftrightarrow>
    d\<in>system_definitions definition_callee_list_system \<and> term_formed t"
  using added_variable_calls[OF definition_callee_inclusion_system_formed
    definition_callee_list_system_formed[unfolded definition_callee_list_system_def] definition_callee_inclusion_call]
  by (simp only: definition_callee_list_system_def[symmetric])

lemma definition_callee_list_old_meaning:
  assumes "d\<in>system_definitions definition_callee_inclusion_system"
  shows "(d,t)\<in>positive_meaning definition_callee_list_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_callee_inclusion_system"
  using added_definition_preserves_old(2)[OF definition_callee_inclusion_system_formed
    definition_callee_list_system_formed[unfolded definition_callee_list_system_def], of d t] assms
  by (auto simp: definition_callee_list_system_def)

lemma definition_callee_list_clause [simp]:
  "((76,c),S)\<in>system_clauses definition_callee_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 75 76)"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_callee_inclusion_system \<Longrightarrow>
    d\<in>system_definitions definition_callee_inclusion_system" for d c S
    using definition_callee_inclusion_system_formed unfolding schema_system_formed_def by blast
  have absent: "((76,c),S)\<notin>system_clauses definition_callee_inclusion_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: definition_callee_list_system_def)
qed

lemma definition_callee_list_element:
  "(75,t)\<in>positive_meaning definition_callee_list_system \<longleftrightarrow> (75,t)\<in>positive_meaning definition_callee_inclusion_system"
  by (rule definition_callee_list_old_meaning) simp

interpretation definition_callee_list_profile: context_list_profile definition_callee_list_system 75 76
  by (rule context_list_profile.intro) (auto simp: definition_callee_list_call)

theorem definition_callee_list_exact:
  "(76,z)\<in>positive_meaning definition_callee_list_system \<longleftrightarrow> definition_callee_list_result z"
  by (simp only: definition_callee_list_profile.exact definition_callee_list_element definition_callee_inclusion_exact)

corollary definition_callee_list_on_values:
  assumes source: "environment_value_presents E e" and data: "data_elements ys"
  shows "(76,Pair_Term (Pair_Term e (data_list_term ys)) (data_list_term xs))
      \<in>positive_meaning definition_callee_list_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>u r p C. x=site_data_term u r \<and> native_definition_at E u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys))"
  by (simp only: definition_callee_list_profile.lists definition_callee_list_element)
    (use environment_value_presents_formed[OF source] data in
      \<open>auto simp: definition_callee_inclusion_at_source[OF source] data_list_term_injective data_list_term_formed\<close>)

corollary definition_callee_list_at_sites:
  assumes source: "environment_value_presents E e" and data: "data_elements ys"
  shows "(76,Pair_Term (Pair_Term e (data_list_term ys)) (data_list_term (map (\<lambda>d. definition_site_value d) ds)))
      \<in>positive_meaning definition_callee_list_system \<longleftrightarrow>
    (\<forall>d\<in>set ds. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys))"
  by (simp only: definition_callee_list_profile.lists definition_callee_list_element)
    (use environment_value_presents_formed[OF source] data in
      \<open>auto simp: definition_callee_inclusion_on_values[OF source] data_list_term_formed\<close>)

text \<open>
  Definition admission first checks the actual interface and complete clause
  family, without requiring any clause to hold. The same actual record and
  family graph then determine every schema root passed to callee inclusion.
  Unique recovery identifies these schemas with precisely the definition's
  clauses, including distinct sockets with shared endpoints.

  The empty-list inclusion premise checks the complete bound even when the
  definition has no clauses. It reuses the existing list operation. A separate
  context-carrying list entry admits every supplied definition and its callees
  against one unchanged bound. Its empty case still checks context formation;
  package closure supplies its own environment and bound checks.
\<close>

end
