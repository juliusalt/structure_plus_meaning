theory Factor_Scope_Admission
  imports Factor_Positive_Admission Factor_Scope_Forwarding Factor_Native_Syntax_Determination
begin

section \<open>The complete forwarding profile has ordinary finite admission\<close>

abbreviation scope_forwarding_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "scope_forwarding_argument e u r k x y z \<equiv>
    citation_observation_argument e u r (Pair_Term k (source_root_argument x y z))"

abbreviation scope_forwarding_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "scope_forwarding_pattern e u r k x y z \<equiv>
    citation_observation_pattern e u r (Pattern_Pair k (source_root_pattern x y z))"

abbreviation scope_forwarding_result :: "factor_term \<Rightarrow> bool" where
  "scope_forwarding_result t \<equiv> \<exists>E e u r k x y z.
    t=scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z \<and>
    environment_value_presents E e \<and> native_scope_forwarding_at E u r k x y z"

definition scope_forwarding_schema :: "(nat,nat,nat) factor_schema" where
  "scope_forwarding_schema=data_rule
    (scope_forwarding_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,72,citation_observation_pattern data_x data_y data_z (Pattern_Payload [])),
     (1,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 7)),
     (2,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10),
         Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 11)])),
     (3,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 11))
       (data_list_pattern [Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13)])),
     (4,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 10)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 14)])
       (Pattern_Variable 14) (Pattern_Variable 17) (Pattern_Variable 18)),
     (5,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 10)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 14) (Pattern_Target (Whole_Artifact empty_artifact))])
       (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 17) (Pattern_Variable 18)),
     (6,65,schema_instantiation_pattern data_x data_y (Pattern_Variable 13)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 15)])
       (Pattern_Variable 15)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 16) (Pattern_Pair data_w
         (package_subject_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 15)))])
       (Pattern_Payload [])),
     (7,65,schema_instantiation_pattern data_x data_y (Pattern_Variable 13)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 15) (Pattern_Target (Whole_Artifact empty_artifact))])
       (Pattern_Target (Whole_Artifact empty_artifact))
       (data_list_pattern [Pattern_Pair (Pattern_Variable 16) (Pattern_Pair data_w
         (package_subject_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)
           (Pattern_Target (Whole_Artifact empty_artifact))))])
       (Pattern_Payload []))}"

definition scope_forwarding_system :: "(nat,nat,nat,nat) schema_system" where
  "scope_forwarding_system=add_view_definition native_positive_admission_system 116 data_x {(0,scope_forwarding_schema)}"

lemma scope_forwarding_system_formed [simp]: "schema_system_formed scope_forwarding_system"
  unfolding scope_forwarding_system_def
  by (rule add_recursive_definition_formed[OF native_positive_admission_system_formed])
    (auto simp: scope_forwarding_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma scope_forwarding_definitions [simp]:
  "system_definitions scope_forwarding_system=insert 116 (system_definitions native_positive_admission_system)"
  by (simp add: scope_forwarding_system_def)

lemma scope_forwarding_call:
  "schema_call_formed scope_forwarding_system d t \<longleftrightarrow>
    d\<in>system_definitions scope_forwarding_system \<and> term_formed t"
  using added_variable_calls[OF native_positive_admission_system_formed
    scope_forwarding_system_formed[unfolded scope_forwarding_system_def] native_positive_admission_call]
  by (simp only: scope_forwarding_system_def[symmetric])

lemma scope_forwarding_old_meaning:
  assumes "d\<in>system_definitions native_positive_admission_system"
  shows "(d,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_positive_admission_system"
  using added_definition_preserves_old(2)[OF native_positive_admission_system_formed
    scope_forwarding_system_formed[unfolded scope_forwarding_system_def], of d t] assms
  by (auto simp: scope_forwarding_system_def)

lemma scope_forwarding_clause [simp]:
  "((116,c),S)\<in>system_clauses scope_forwarding_system \<longleftrightarrow> (c,S)\<in>{(0,scope_forwarding_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses native_positive_admission_system \<Longrightarrow>
    d\<in>system_definitions native_positive_admission_system" for d c S
    using native_positive_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((116,c),S)\<notin>system_clauses native_positive_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: scope_forwarding_system_def)
qed

lemma scope_forwarding_definition_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning definition_call_admission_system"
  using assms
  by (simp add: scope_forwarding_old_meaning native_positive_admission_old_meaning
    positive_query_old_meaning environment_inclusion_old_meaning artifact_inclusion_old_meaning
    replay_admission_old_meaning retention_admission_slot_meaning replay_slot_reading_old_meaning
    replay_source_reading_graph_meaning proof_graph_membership_node_meaning
    proof_node_reading_base_meaning admitted_instantiation_previous_meaning
    package_admission_previous_meaning package_closure_previous_meaning)

lemma scope_forwarding_components:
  "(72,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (72,t)\<in>positive_meaning definition_call_admission_system"
  "(37,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (32,t)\<in>positive_meaning family_admission_system"
  "(56,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (56,t)\<in>positive_meaning scoped_instantiation_system"
  "(65,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (65,t)\<in>positive_meaning schema_instantiation_system"
  using scope_forwarding_definition_meaning[of 72 t] scope_forwarding_definition_meaning[of 37 t]
    scope_forwarding_definition_meaning[of 34 t] scope_forwarding_definition_meaning[of 32 t]
    scope_forwarding_definition_meaning[of 56 t] scope_forwarding_definition_meaning[of 65 t]
    definition_call_admission_components(1-3)[of t]
    definition_call_admission_old_meaning[of 32 t] schema_family_admission_components(2)[of t]
    definition_call_admission_instantiation_meaning[of 65 t] by auto

lemma scope_forwarding_valuation:
  "(116,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18}. term_formed (h j)) \<and>
      t=scope_forwarding_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (72,citation_observation_argument (h 0) (h 1) (h 2) (Payload_Term []))\<in>positive_meaning definition_call_admission_system \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 7) (h 2) (pair_list_term [(h 8,h 10),(h 9,h 11)]))
        \<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument (h 7) (h 11) (pair_list_term [(h 12,h 13)]))
        \<in>positive_meaning family_admission_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,h 14)]) (h 14) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact)) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 13) (pair_list_term [(h 15,h 15)]) (h 15)
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6) (h 15)))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 13)
        (pair_list_term [(h 15,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact))
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6)
          (Target_Term (Whole_Artifact empty_artifact))))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system)"
proof -
  have family: "((116,c),S)\<in>system_clauses scope_forwarding_system \<longleftrightarrow>
      c=0 \<and> S=scope_forwarding_schema" for c S by simp
  have ordinary: "schema_material_premises scope_forwarding_schema={}"
    by (simp add: scope_forwarding_schema_def)
  have boundary: "schema_call_formed scope_forwarding_system 116
    (evaluate_pattern h (schema_conclusion scope_forwarding_schema))"
    if assignment: "\<forall>a\<in>schema_variables scope_forwarding_schema. term_formed (h a)" for h
    using assignment by (auto simp: scope_forwarding_call scope_forwarding_schema_def schema_variables_def)
  have variables: "schema_variables scope_forwarding_schema={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18}"
    by (auto simp: scope_forwarding_schema_def schema_variables_def)
  have head: "evaluate_pattern h (schema_conclusion scope_forwarding_schema)=
    scope_forwarding_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)" for h
    by (simp add: scope_forwarding_schema_def)
  have calls: "(\<forall>s d p. (s,d,p)\<in>schema_premises scope_forwarding_schema \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning scope_forwarding_system) \<longleftrightarrow>
      (72,citation_observation_argument (h 0) (h 1) (h 2) (Payload_Term []))\<in>positive_meaning definition_call_admission_system \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 7) (h 2) (pair_list_term [(h 8,h 10),(h 9,h 11)]))
        \<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument (h 7) (h 11) (pair_list_term [(h 12,h 13)]))
        \<in>positive_meaning family_admission_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,h 14)]) (h 14) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact)) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 13) (pair_list_term [(h 15,h 15)]) (h 15)
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6) (h 15)))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 13)
        (pair_list_term [(h 15,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact))
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6)
          (Target_Term (Whole_Artifact empty_artifact))))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system" for h
  proof -
    have rows: "(\<forall>s d p. (s,d,p)\<in>schema_premises scope_forwarding_schema \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning scope_forwarding_system) \<longleftrightarrow>
      (\<forall>(s,d,p)\<in>schema_premises scope_forwarding_schema.
        (d,evaluate_pattern h p)\<in>positive_meaning scope_forwarding_system)"
      by (auto split: prod.splits)
    show ?thesis by (simp only: rows)
      (simp add: scope_forwarding_schema_def scope_forwarding_components)
  qed
  note equation=ordinary_single_clause_valuation[OF family ordinary boundary, where t=t]
  show ?thesis by (rule equation[unfolded variables head calls])
qed

section \<open>Finite row shapes expose their actual coordinates\<close>

lemma binding_rows_singleton_iff:
  "binding_rows_term xs=pair_list_term [(a,t)] \<longleftrightarrow> (\<exists>b. a=Payload_Term b \<and> xs=[(b,t)])"
  by (simp only: pair_list_term_injective; cases xs) (auto split: prod.splits)

lemma call_rows_singleton_iff:
  "call_instance_rows_term xs=pair_list_term [(s,Pair_Term k t)] \<longleftrightarrow>
    (\<exists>a d. s=Payload_Term a \<and> k=definition_site_value d \<and> xs=[(a,d,t)])"
  by (simp only: pair_list_term_injective; cases xs)
    (auto simp: call_instance_value_def split: prod.splits)

lemma native_definition_record_interface:
  assumes raw: "native_definition_at E u r p C" and source: "artifact_at E u R"
    and rec: "record_at R r ps [i,m]"
  shows "\<exists>I K. scoped_pattern_at E u i p I K"
proof -
  obtain A qs j n I K where parts: "environment_formed E" "artifact_at E u A"
    "record_at A r qs [j,n]" "scoped_pattern_at E u j p I K"
    using raw by (auto simp: native_definition_at_def)
  have same: "A=R" by (rule environment_artifact_unique[OF parts(1,2) source])
  have other: "record_at R r qs [j,n]" using parts(3) same by simp
  have "j=i" using record_at_unique[OF other rec] by auto
  then show ?thesis using parts(4) by blast
qed


lemma scoped_variable_readings:
  assumes source: "environment_value_presents E e" and address: "octets_formed a"
    and orders: "distinct Is" "distinct Ks"
  shows "scoped_pattern_at E u r (Pattern_Variable a) (set Is) (set Ks) \<longleftrightarrow>
    (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term [(a,Payload_Term a)]) (Payload_Term a)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
        \<in>positive_meaning scoped_instantiation_system \<and>
    (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term [(a,Target_Term (Whole_Artifact empty_artifact))])
      (Target_Term (Whole_Artifact empty_artifact))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
        \<in>positive_meaning scoped_instantiation_system"
  using scoped_pattern_two_instances[OF source, where p="Pattern_Variable a" and u=u and r=r
    and xs="[(a,Payload_Term a)]" and ys="[(a,Target_Term (Whole_Artifact empty_artifact))]"
    and Is=Is and Ks=Ks] address orders by auto

lemma scope_schema_readings:
  assumes source: "environment_value_presents E e" and address: "octets_formed b"
    and fields: "term_formed x" "term_formed y" "term_formed z"
  shows "native_schema_at E u r (scope_call_schema b s k x y z) \<longleftrightarrow>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term [(b,Payload_Term b)]) (Payload_Term b)
      (call_instance_rows_term [(s,k,package_subject_argument x y z (Payload_Term b))])
      (binding_rows_term []))\<in>positive_meaning schema_instantiation_system \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term [(b,Target_Term (Whole_Artifact empty_artifact))])
      (Target_Term (Whole_Artifact empty_artifact))
      (call_instance_rows_term [(s,k,package_subject_argument x y z (Target_Term (Whole_Artifact empty_artifact)))])
      (binding_rows_term []))\<in>positive_meaning schema_instantiation_system"
proof -
  have first: "schema_instance (scope_call_schema b s k x y z) {(b,Payload_Term b)}
      (Payload_Term b) {(s,k,package_subject_argument x y z (Payload_Term b))}"
    by (rule scope_call_schema_instance[OF fields]) (use address in simp)
  have second: "schema_instance (scope_call_schema b s k x y z) {(b,Target_Term (Whole_Artifact empty_artifact))}
      (Target_Term (Whole_Artifact empty_artifact))
      {(s,k,package_subject_argument x y z (Target_Term (Whole_Artifact empty_artifact)))}"
    by (rule scope_call_schema_instance[OF fields]) simp
  show ?thesis by (rule native_schema_two_instances[OF source, where B="{b}"])
    (use first second in \<open>auto simp: material_instance_relation_def scope_call_schema_def\<close>)
qed

section \<open>Soundness recovers the whole definition, not a selected execution\<close>

theorem scope_forwarding_sound:
  assumes holds: "(116,t)\<in>positive_meaning scope_forwarding_system"
  shows "scope_forwarding_result t"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where
    formed: "\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18}. term_formed (h j)"
    and shape: "t=scope_forwarding_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)"
    and reads:
      "(72,citation_observation_argument (h 0) (h 1) (h 2) (Payload_Term []))\<in>positive_meaning definition_call_admission_system"
      "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
      "(34,rooted_rows_argument (h 7) (h 2) (pair_list_term [(h 8,h 10),(h 9,h 11)]))
        \<in>positive_meaning record_admission_system"
      "(32,rooted_rows_argument (h 7) (h 11) (pair_list_term [(h 12,h 13)]))
        \<in>positive_meaning family_admission_system"
      "(56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,h 14)]) (h 14) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system"
      "(56,scoped_instantiation_argument (h 0) (h 1) (h 10)
        (pair_list_term [(h 14,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact)) (h 17) (h 18))\<in>positive_meaning scoped_instantiation_system"
      "(65,schema_instantiation_argument (h 0) (h 1) (h 13) (pair_list_term [(h 15,h 15)]) (h 15)
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6) (h 15)))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system"
      "(65,schema_instantiation_argument (h 0) (h 1) (h 13)
        (pair_list_term [(h 15,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact))
        (pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6)
          (Target_Term (Whole_Artifact empty_artifact))))])
        (Payload_Term []))\<in>positive_meaning schema_instantiation_system"
    using holds by (simp only: scope_forwarding_valuation) blast
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 7)"
    using reads(2) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r p q i m where rec: "h 2=Payload_Term r" "h 8=Payload_Term p" "h 10=Payload_Term i"
    "h 9=Payload_Term q" "h 11=Payload_Term m" "record_at R r [p,q] [i,m]"
    using reads(3) by (simp only: list.map prod.case record_admission_pair_fields[OF source(4)]) blast
  obtain pat C where raw: "native_definition_at E u r pat C"
    using reads(1) by (simp only: source(2) rec(1) definition_call_admission_on_values[OF source(1)]) blast
  obtain xs where family: "pair_list_term [(h 12,h 13)]=data_list_term (map address_pair_data xs)"
    "family_at R m (set xs)"
    using reads(4) by (simp only: rec(5) family_admission_at_source[OF source(4)] factor_term.inject) blast
  have rows: "[Pair_Term (h 12) (h 13)]=map address_pair_data xs"
    using family(1) by (simp only: list.map prod.case data_list_term_injective)
  obtain c a where row: "h 12=Payload_Term c" "h 13=Payload_Term a" "xs=[(c,a)]"
    using rows by (cases xs) (auto simp: address_pair_data_def split: prod.splits)
  have singleton: "family_at R m {(c,a)}" using family(2) row(3) by simp
  obtain bs Is Ks where interface_rows:
    "pair_list_term [(h 14,h 14)]=binding_rows_term bs"
    "h 17=data_list_term (map Payload_Term Is)" "h 18=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks"
    using reads(5) by (simp only: source(2) rec(3) scoped_instantiation_at_source[OF source(1)]
      factor_term.inject inj_eq[OF use_data_term_injective]) blast
  obtain ib where ib: "h 14=Payload_Term ib"
    using interface_rows(1)[symmetric] by (simp only: binding_rows_singleton_iff) blast
  have ib_formed: "octets_formed ib" using formed ib by auto
  have interface: "scoped_pattern_at E u i (Pattern_Variable ib) (set Is) (set Ks)"
    using reads(5,6)[unfolded source(2) rec(3) ib interface_rows(2,3)]
    by (simp only: scoped_variable_readings[OF source(1) ib_formed interface_rows(4,5)]) simp
  obtain bs qs where schema_rows:
    "pair_list_term [(h 15,h 15)]=binding_rows_term bs"
    "pair_list_term [(h 16,Pair_Term (h 3) (package_subject_argument (h 4) (h 5) (h 6) (h 15)))]=call_instance_rows_term qs"
    using reads(7) by (simp only: source(2) row(2) schema_instantiation_at_source[OF source(1)]
      factor_term.inject inj_eq[OF use_data_term_injective]) blast
  obtain b where b: "h 15=Payload_Term b"
    using schema_rows(1)[symmetric] by (simp only: binding_rows_singleton_iff) blast
  obtain s k where call: "h 16=Payload_Term s" "h 3=definition_site_value k"
    using schema_rows(2)[symmetric] by (simp only: call_rows_singleton_iff) blast
  have b_formed: "octets_formed b" using formed b by auto
  have fields: "term_formed (h 4)" "term_formed (h 5)" "term_formed (h 6)" using formed by auto
  let ?S="scope_call_schema b s k (h 4) (h 5) (h 6)"
  have schema: "native_schema_at E u a ?S"
    using reads(7,8)[unfolded source(2) row(2) b call]
    by (simp only: scope_schema_readings[OF source(1) b_formed fields])
      (simp add: call_instance_value_def)
  obtain I K where other_interface: "scoped_pattern_at E u i pat I K"
    using native_definition_record_interface[OF raw source(3) rec(6)] by blast
  have pat: "pat=Pattern_Variable ib" using scoped_pattern_unique[OF other_interface interface] by blast
  have family_read: "native_schema_family_at E u m C"
    by (rule native_definition_record_family[OF raw source(3) rec(6)])
  have same_schema: "native_schema_at E u a T \<longleftrightarrow> T=?S" for T
  proof
    assume other: "native_schema_at E u a T"
    show "T=?S" by (rule native_schema_unique[OF other schema])
  next
    assume "T=?S"
    then show "native_schema_at E u a T" using schema by simp
  qed
  have clauses: "(d,T)\<in>C \<longleftrightarrow> d=c \<and> T=?S" for d T
    by (simp only: native_schema_family_at_graph(1)[OF family_read source(3) singleton])
      (simp add: same_schema)
  have C: "C={(c,?S)}"
  proof (rule set_eqI)
    fix q :: "local_address \<times> local_address option native_schema"
    obtain d T where shape: "q=(d,T)" by (cases q)
    show "q\<in>C \<longleftrightarrow> q\<in>{(c,?S)}" by (simp only: shape clauses; simp)
  qed
  have forwarding: "native_scope_forwarding_at E u r k (h 4) (h 5) (h 6)"
    using raw pat C by (auto simp: native_scope_forwarding_at_def)
  show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u],
      rule exI[of _ r], rule exI[of _ k], rule exI[of _ "h 4"],
      rule exI[of _ "h 5"], rule exI[of _ "h 6"])
    (use shape source(1,2) rec(1) call(2) forwarding in simp)
qed


lemma scoped_pattern_variables_formed:
  assumes raw: "scoped_pattern_at E u r p I K"
  shows "\<forall>a\<in>pattern_variables p. octets_formed a"
proof -
  obtain R b where parts: "environment_formed E" "artifact_at E u R"
    "binder_scope_at R b (pattern_variables p)"
    using raw by (auto simp: scoped_pattern_at_def)
  have formed: "exact_formed R" using parts(1,2) by (auto simp: environment_formed_def)
  show ?thesis using binder_scope_properties(2)[OF parts(3)] formed
    by (auto simp: exact_formed_def)
qed

section \<open>Every actual forwarding definition supplies the finite readings\<close>

theorem scope_forwarding_complete:
  assumes source: "environment_value_presents E e"
    and forwarding: "native_scope_forwarding_at E u r k x y z"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<in>positive_meaning scope_forwarding_system"
proof -
  obtain ib c b s where raw: "native_definition_at E u r (Pattern_Variable ib)
      {(c,scope_call_schema b s k x y z)}"
    using forwarding by (auto simp: native_scope_forwarding_at_def)
  let ?S="scope_call_schema b s k x y z"
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i (Pattern_Variable ib) I K"
    "native_schema_family_at E u m {(c,?S)}"
    using raw by (auto simp: native_definition_at_def)
  obtain A M a where origin: "artifact_at E u A" "family_at A m M" "(c,a)\<in>M" "native_schema_at E u a ?S"
    using native_schema_family_origin[OF parts(4), of c ?S] by auto
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have same: "A=R" by (rule environment_artifact_unique[OF ef origin(1) parts(1)])
  have family: "family_at R m M" using origin(2) same by simp
  have socket: "d=c" if row: "(d,w)\<in>M" for d w
  proof -
    obtain T where member: "(d,T)\<in>{(c,?S)}"
      using native_schema_family_at_graph(2)[OF parts(4) parts(1) family, rule_format, OF row] by blast
    show "d=c" using member by simp
  qed
  have keys: "rel_dom M={c}"
  proof (rule set_eqI, rule iffI)
    fix d assume "d\<in>rel_dom M"
    then obtain w where row: "(d,w)\<in>M" by (auto simp: rel_dom_def)
    have "d=c" by (rule socket[OF row])
    then show "d\<in>{c}" by simp
  next
    fix d assume "d\<in>{c}"
    then have "d=c" by simp
    then show "d\<in>rel_dom M" using rel_domI[OF origin(3)] by simp
  qed
  have sv: "single_valued M" using family by (simp add: family_at_def)
  have M: "M={(c,a)}"
  proof
    show "M\<subseteq>{(c,a)}"
    proof
      fix q assume member: "q\<in>M"
      obtain d w where shape: "q=(d,w)" by (cases q)
      have row: "(d,w)\<in>M" using member shape by simp
      have key: "d=c" using rel_domI[OF row] keys by simp
      have same_output: "w=a" using single_valued_outputs[OF sv row] origin(3) key by blast
      show "q\<in>{(c,a)}" using shape key same_output by simp
    qed
    show "{(c,a)}\<subseteq>M" using origin(3) by simp
  qed
  have singleton: "family_at R m {(c,a)}" using family M by simp
  have fields: "term_formed x" "term_formed y" "term_formed z"
    by (rule native_scope_forwarding_fields[OF forwarding])+
  have ib_formed: "octets_formed ib" using scoped_pattern_variables_formed[OF parts(3)] by simp
  have b_formed: "octets_formed b" using native_schema_variables_formed[OF origin(4)] by simp
  obtain Is where Is: "set Is=I" "distinct Is"
    using scoped_pattern_formed[OF parts(3)] finite_distinct_list[of I] by blast
  obtain Ks where Ks: "set Ks=K" "distinct Ks"
    using scoped_pattern_formed[OF parts(3)] finite_distinct_list[of K] by blast
  have interface: "scoped_pattern_at E u i (Pattern_Variable ib) (set Is) (set Ks)"
    using parts(3) Is(1) Ks(1) by simp
  have interface_reads:
    "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i)
      (binding_rows_term [(ib,Payload_Term ib)]) (Payload_Term ib)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
        \<in>positive_meaning scoped_instantiation_system"
    "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i)
      (binding_rows_term [(ib,Target_Term (Whole_Artifact empty_artifact))])
      (Target_Term (Whole_Artifact empty_artifact))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
        \<in>positive_meaning scoped_instantiation_system"
    using interface by (simp_all only: scoped_variable_readings[OF source ib_formed Is(2) Ks(2)])
  have schema_reads:
    "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a)
      (binding_rows_term [(b,Payload_Term b)]) (Payload_Term b)
      (call_instance_rows_term [(s,k,package_subject_argument x y z (Payload_Term b))])
      (binding_rows_term []))\<in>positive_meaning schema_instantiation_system"
    "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a)
      (binding_rows_term [(b,Target_Term (Whole_Artifact empty_artifact))])
      (Target_Term (Whole_Artifact empty_artifact))
      (call_instance_rows_term [(s,k,package_subject_argument x y z (Target_Term (Whole_Artifact empty_artifact)))])
      (binding_rows_term []))\<in>positive_meaning schema_instantiation_system"
    using origin(4) by (simp_all only: scope_schema_readings[OF source b_formed fields])
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain v where presented: "artifact_value_presents R v" using artifact_value_presents_total[OF rf] by blast
  obtain p q where ports: "ps=[p,q]" using record_at_preserves_socket_occurrences[OF parts(2)]
    by (auto simp: length_Suc_conv)
  have admitted: "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term []))
      \<in>positive_meaning definition_call_admission_system"
    by (rule definition_call_admission_complete[OF source raw]) (simp add: octets_formed_def)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) v)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument v (Payload_Term r)
      (pair_list_term [(Payload_Term p,Payload_Term i),(Payload_Term q,Payload_Term m)]))
        \<in>positive_meaning record_admission_system"
    by (simp only: list.map prod.case record_admission_pair_fields[OF presented]) (use parts(2) ports in auto)
  have family_read: "(32,rooted_rows_argument v (Payload_Term m)
      (pair_list_term [(Payload_Term c,Payload_Term a)]))\<in>positive_meaning family_admission_system"
    using family_admission_rows[OF presented, of m "[(c,a)]"] singleton
    by (simp add: address_pair_data_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term u else if j=2 then Payload_Term r
    else if j=3 then definition_site_value k else if j=4 then x else if j=5 then y else if j=6 then z
    else if j=7 then v else if j=8 then Payload_Term p else if j=9 then Payload_Term q
    else if j=10 then Payload_Term i else if j=11 then Payload_Term m else if j=12 then Payload_Term c
    else if j=13 then Payload_Term a else if j=14 then Payload_Term ib else if j=15 then Payload_Term b
    else if j=16 then Payload_Term s else if j=17 then data_list_term (map Payload_Term Is)
    else data_list_term (map Payload_Term Ks)"
  show ?thesis by (simp only: scope_forwarding_valuation, rule exI[of _ ?h])
    (use admitted lookup rec family_read interface_reads schema_reads fields
      schema_call_formed_target[OF positive_meaning_formed[OF admitted]]
      schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF family_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF interface_reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF schema_reads(1)]]
      in \<open>auto simp: call_instance_value_def\<close>)
qed

theorem scope_forwarding_exact:
  "(116,t)\<in>positive_meaning scope_forwarding_system \<longleftrightarrow> scope_forwarding_result t"
  using scope_forwarding_sound scope_forwarding_complete by blast

corollary scope_forwarding_on_values:
  assumes source: "environment_value_presents E e"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<in>positive_meaning scope_forwarding_system \<longleftrightarrow> native_scope_forwarding_at E u r k x y z"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis
    by (simp only: scope_forwarding_exact factor_term.inject
        inj_eq[OF use_data_term_injective] definition_site_value_eq)
      (use source unique in blast)
qed

corollary scope_forwarding_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
      \<in>positive_meaning scope_forwarding_system \<longleftrightarrow>
    (116,scope_forwarding_argument f (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
      \<in>positive_meaning scope_forwarding_system"
  by (simp only: scope_forwarding_on_values[OF assms(1)] scope_forwarding_on_values[OF assms(2)])

theorem scope_forwarding_admission_total:
  fixes E :: "local_address option artifact_environment"
  assumes formed: "environment_formed E"
    and callee: "\<exists>R. artifact_at E (fst k) R \<and> anchor_formed (R,snd k)"
    and fields: "term_formed x" "term_formed y" "term_formed z"
  shows "\<exists>F f u. environment_included E F \<and> u\<notin>environment_uses E \<and>
    environment_value_presents F f \<and>
    (116,scope_forwarding_argument f (use_data_term u) (Payload_Term []) (definition_site_value k) x y z)
      \<in>positive_meaning scope_forwarding_system"
proof -
  obtain F u where built: "environment_formed F" "environment_included E F"
    "u\<notin>environment_uses E" "native_scope_forwarding_at F u [] k x y z"
    using native_scope_forwarding_total[OF formed callee fields] by blast
  obtain f where source: "environment_value_presents F f"
    using environment_value_presents_total[OF built(1)] by blast
  show ?thesis using built(2,3) source scope_forwarding_complete[OF source built(4)] by blast
qed

theorem admitted_scope_forwarding_meaning:
  assumes source: "environment_value_presents E e"
    and package: "native_package_at E pu pr P" and reference: "native_package_at E qu qr Q"
    and members: "d\<in>system_definitions P" "k\<in>system_definitions Q"
    and admitted: "(116,scope_forwarding_argument e (use_data_term (fst d)) (Payload_Term (snd d))
      (definition_site_value k) x y z)\<in>positive_meaning scope_forwarding_system"
  shows "schema_call_formed P d w \<longleftrightarrow> term_formed w"
    and "(d,w)\<in>positive_meaning P \<longleftrightarrow>
      (k,package_subject_argument x y z w)\<in>positive_meaning Q"
proof -
  have read: "native_scope_forwarding_at E (fst d) (snd d) k x y z"
    using admitted by (simp only: scope_forwarding_on_values[OF source])
  show "schema_call_formed P d w \<longleftrightarrow> term_formed w"
    by (rule native_scope_forwarding_call[OF package members(1) read])
  show "(d,w)\<in>positive_meaning P \<longleftrightarrow>
      (k,package_subject_argument x y z w)\<in>positive_meaning Q"
    by (rule native_scope_forwarding_shared_meaning[OF package reference members read])
qed

section \<open>Complete families exclude omitted alternatives and conditions\<close>

theorem scope_forwarding_empty_clauses_rejected:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p {}"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<notin>positive_meaning scope_forwarding_system"
proof
  assume holds: "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<in>positive_meaning scope_forwarding_system"
  obtain i c b s where read: "native_definition_at E u r (Pattern_Variable i)
    {(c,scope_call_schema b s k x y z)}"
    using holds by (simp only: scope_forwarding_on_values[OF source] native_scope_forwarding_at_def) blast
  have "{}={(c,scope_call_schema b s k x y z)}"
    using native_definition_unique[OF raw read] by blast
  then show False by simp
qed

theorem scope_forwarding_material_clause_rejected:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
    and member: "(c,S)\<in>C" and material: "schema_material_premises S\<noteq>{}"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<notin>positive_meaning scope_forwarding_system"
proof -
  have rejected: "\<not>native_scope_forwarding_at E u r k x y z"
  proof
    assume "native_scope_forwarding_at E u r k x y z"
    then obtain i d b s where read: "native_definition_at E u r (Pattern_Variable i)
      {(d,scope_call_schema b s k x y z)}" by (auto simp: native_scope_forwarding_at_def)
    have "S=scope_call_schema b s k x y z"
      using native_definition_unique[OF raw read] member by auto
    then show False using material by (simp add: scope_call_schema_def)
  qed
  show ?thesis using rejected by (simp add: scope_forwarding_on_values[OF source])
qed

theorem scope_forwarding_extra_clause_rejected:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
    and clauses: "(c,S)\<in>C" "(d,T)\<in>C" "c\<noteq>d"
  shows "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<notin>positive_meaning scope_forwarding_system"
proof
  assume holds: "(116,scope_forwarding_argument e (use_data_term u) (Payload_Term r) (definition_site_value k) x y z)
    \<in>positive_meaning scope_forwarding_system"
  obtain i f b s where read: "native_definition_at E u r (Pattern_Variable i)
    {(f,scope_call_schema b s k x y z)}"
    using holds by (simp only: scope_forwarding_on_values[OF source] native_scope_forwarding_at_def) blast
  have "C={(f,scope_call_schema b s k x y z)}"
    using native_definition_unique[OF raw read] by blast
  then show False using clauses by auto
qed

section \<open>One fixed native checker serves every future submitted definition\<close>

theorem native_scope_forwarding_checker:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu Q d.
    closed_native_package_at C cu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] d t I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> scope_forwarding_result t) \<and>
        (\<forall>v\<in>environment_uses C. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at C v R) \<and>
        (\<forall>v\<in>environment_uses C. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot C v k w)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q
    where closed: "closed_native_package_at C cu [] Q"
    and future: "\<forall>d\<in>system_definitions scope_forwarding_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F cu []=C \<and>
        (native_application_formed F cu [] au [] \<longleftrightarrow> schema_call_formed scope_forwarding_system d t) \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning scope_forwarding_system) \<and>
        (\<forall>v\<in>environment_uses C. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at C v R) \<and>
        (\<forall>v\<in>environment_uses C. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot C v k w))"
    using compiled_program_future_applications[OF scope_forwarding_system_formed] by blast
  have member: "116\<in>system_definitions scope_forwarding_system" by simp
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q], rule exI[of _ "g 116"])
    (use closed future[rule_format, OF member] in \<open>auto simp: scope_forwarding_call scope_forwarding_exact\<close>)
qed

text \<open>
  Eight ordinary premises inspect the actual definition: native definition
  admission, source artifact lookup, its complete two-field record, its complete
  singleton clause family, and two readings each of the interface and schema.
  Both schema outputs require the complete empty material relation. The finite
  readings determine syntax; they are not samples of the submitted program's
  behavior. The callee's actual use and root remain data in those readings.

  In a formed package containing an admitted entry, every formed future argument
  is accepted and forwarded exactly to its actual callee at the fixed scope.
  Admission of the definition alone does not supply that package. Shared-package
  agreement then relates that call to an independently established package.
  Empty, additional, and material clauses are rejected. Every actual profile
  and every complete source presentation has admission, and one fixed native
  checker precedes all future input terms while preserving its original scope.

  This sufficient definition profile does not decide equivalence of arbitrary
  programs. The separate interpreter admission theory binds both entries to
  the actual submitted package and retains a fixed, independently proved
  interpreter as their common semantic dependency.
\<close>

end
