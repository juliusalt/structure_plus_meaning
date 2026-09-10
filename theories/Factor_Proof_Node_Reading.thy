theory Factor_Proof_Node_Reading
  imports Factor_Discharge_Table_Reading Factor_Proof_Metadata
begin

section \<open>The recovered node value has exactly the existing zero or three fields\<close>

fun proof_node_value_presents ::
  "(local_address option definition_site,local_address option definition_site) schema_graph_node \<Rightarrow>
    (local_address option definition_site\<times>local_address option definition_site) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "proof_node_value_presents Schema_Assertion D t \<longleftrightarrow> D={} \<and> t=Payload_Term []"
| "proof_node_value_presents (Schema_Inference c V) D t \<longleftrightarrow>
    (\<exists>bs ds. t=data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds] \<and>
      distinct bs \<and> distinct ds \<and> set bs=fset V \<and> set ds=D)"

lemmas positioned_binding_rows_term_injective=
  keyed_rows_term_injective[OF definition_site_value_injective inj_on_id]
lemmas discharge_rows_term_injective=
  keyed_rows_term_injective[OF definition_site_value_injective definition_site_value_injective]

lemma proof_node_value_assertion:
  "proof_node_value_presents N D (Payload_Term []) \<longleftrightarrow> N=Schema_Assertion \<and> D={}"
  by (cases N) auto

lemma proof_node_value_inference:
  "proof_node_value_presents N D
      (data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds]) \<longleftrightarrow>
    distinct bs \<and> distinct ds \<and> N=Schema_Inference c (fset_of_list bs) \<and> D=set ds"
proof -
  have finite_equality: "V=fset_of_list xs \<longleftrightarrow> fset V=set xs" for V xs
    by (simp only: fset_inject[symmetric] fset_of_list.rep_eq)
  show ?thesis
  proof (cases N)
    case Schema_Assertion
    then show ?thesis by simp
  next
    case (Schema_Inference c' V)
    show ?thesis
      by (simp only: Schema_Inference proof_node_value_presents.simps data_list_term.simps factor_term.inject
        inference_node.inject definition_site_value_eq positioned_binding_rows_term_injective
        discharge_rows_term_injective finite_equality; blast)
  qed
qed

lemma proof_node_value_unique:
  assumes "proof_node_value_presents N D t" "proof_node_value_presents M F t"
  shows "N=M \<and> D=F"
proof (cases N)
  case Schema_Assertion
  have fields: "t=Payload_Term []" "D={}" using assms(1) Schema_Assertion by simp_all
  have other: "M=Schema_Assertion \<and> F={}" using assms(2) fields(1) proof_node_value_assertion by blast
  show ?thesis using Schema_Assertion fields other by simp
next
  case (Schema_Inference c V)
  obtain bs ds where fields: "t=data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds]"
    "set bs=fset V" "set ds=D" using assms(1) Schema_Inference by auto
  have other: "M=Schema_Inference c (fset_of_list bs) \<and> F=set ds"
    using assms(2) by (simp only: fields(1) proof_node_value_inference; blast)
  have bindings: "fset_of_list bs=V"
    by (rule fset_inject[THEN iffD1]) (simp only: fset_of_list.rep_eq; rule fields(2))
  show ?thesis using Schema_Inference fields(3) other bindings by simp
qed

lemma proof_node_value_total:
  assumes raw: "native_proof_node_at E u r N D I K"
  shows "\<exists>t. proof_node_value_presents N D t"
proof (cases N)
  case Schema_Assertion
  have empty: "D={}" using native_proof_node_assertion[of E u r D I K] raw Schema_Assertion by blast
  show ?thesis by (rule exI[of _ "Payload_Term []"]) (simp add: Schema_Assertion empty)
next
  case (Schema_Inference c V)
  obtain bs where bindings: "set bs=fset V" "distinct bs" using finite_distinct_list[of "fset V"] by auto
  obtain ds where links: "set ds=D" "distinct ds"
    using finite_distinct_list[OF native_proof_node_properties(3)[OF raw]] by blast
  show ?thesis by (rule exI[of _ "data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds]"])
    (use bindings links in \<open>auto simp: Schema_Inference\<close>)
qed

abbreviation proof_node_reading_result :: "factor_term\<Rightarrow>bool" where
  "proof_node_reading_result z \<equiv> \<exists>E e u r N D n Is Ks.
    z=term_quotation_argument e (use_data_term u) (Payload_Term r) n
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
    environment_value_presents E e \<and> distinct Is \<and> distinct Ks \<and>
    proof_node_value_presents N D n \<and> native_proof_node_at E u r N D (set Is) (set Ks)"

section \<open>Two ordinary clauses read the complete native forms\<close>

definition proof_node_assertion_schema :: "(nat,nat,nat) factor_schema" where
  "proof_node_assertion_schema=data_rule
    (term_quotation_pattern data_x data_y data_z (Pattern_Payload []) (data_list_pattern [data_z]) (Pattern_Payload []))
    {(0,37,artifact_lookup_pattern data_x data_y data_w),
     (1,34,Pattern_Pair (Pattern_Pair data_w data_z) (Pattern_Payload []))}"

definition proof_node_inference_schema :: "(nat,nat,nat) factor_schema" where
  "proof_node_inference_schema=data_rule
    (term_quotation_pattern data_x data_y data_z
      (data_list_pattern [data_w,Pattern_Variable 4,Pattern_Variable 5]) (Pattern_Variable 6) (Pattern_Variable 7))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 8)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12),
         Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 13),Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 14)])),
     (2,88,term_quotation_pattern data_x data_y (Pattern_Variable 12) data_w (Pattern_Variable 15) (Pattern_Variable 16)),
     (3,92,term_quotation_pattern data_x data_y (Pattern_Variable 13) (Pattern_Variable 4) (Pattern_Variable 17) (Pattern_Variable 18)),
     (4,93,term_quotation_pattern data_x data_y (Pattern_Variable 14) (Pattern_Variable 5) (Pattern_Variable 19) (Pattern_Variable 20)),
     (5,46,collection_join_pattern (data_list_pattern [data_z,Pattern_Variable 9,Pattern_Variable 10,Pattern_Variable 11])
       (Pattern_Variable 15) (Pattern_Variable 21)),
     (6,46,collection_join_pattern (Pattern_Variable 21) (Pattern_Variable 17) (Pattern_Variable 22)),
     (7,46,collection_join_pattern (Pattern_Variable 22) (Pattern_Variable 19) (Pattern_Variable 23)),
     (8,6,Pattern_Pair (Pattern_Variable 23) (Pattern_Variable 6)),
     (9,48,collection_join_pattern (Pattern_Variable 16) (Pattern_Variable 18) (Pattern_Variable 24)),
     (10,48,collection_join_pattern (Pattern_Variable 24) (Pattern_Variable 20) (Pattern_Variable 7)),
     (11,49,Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))}"

definition proof_node_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "proof_node_reading_clauses={(0,proof_node_assertion_schema),(1,proof_node_inference_schema)}"

definition proof_node_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_node_reading_system=add_view_definition discharge_table_reading_system 94 data_x proof_node_reading_clauses"

lemma proof_node_reading_system_formed [simp]: "schema_system_formed proof_node_reading_system"
  unfolding proof_node_reading_system_def
  by (rule add_recursive_definition_formed[OF discharge_table_reading_system_formed])
    (auto simp: proof_node_reading_clauses_def proof_node_assertion_schema_def proof_node_inference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_node_reading_definitions [simp]:
  "system_definitions proof_node_reading_system=insert 94 (system_definitions discharge_table_reading_system)"
  by (simp add: proof_node_reading_system_def)

lemma proof_node_reading_call:
  "schema_call_formed proof_node_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_node_reading_system \<and> term_formed t"
  using added_variable_calls[OF discharge_table_reading_system_formed
    proof_node_reading_system_formed[unfolded proof_node_reading_system_def] discharge_table_reading_call]
  by (simp only: proof_node_reading_system_def[symmetric])

lemma proof_node_reading_old_meaning:
  assumes "d\<in>system_definitions discharge_table_reading_system"
  shows "(d,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning discharge_table_reading_system"
  using added_definition_preserves_old(2)[OF discharge_table_reading_system_formed
    proof_node_reading_system_formed[unfolded proof_node_reading_system_def], of d t] assms
  by (auto simp: proof_node_reading_system_def)

lemma proof_node_reading_clause [simp]:
  "((94,c),S)\<in>system_clauses proof_node_reading_system \<longleftrightarrow> (c,S)\<in>proof_node_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses discharge_table_reading_system \<Longrightarrow>
    d\<in>system_definitions discharge_table_reading_system" for d c S
    using discharge_table_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((94,c),S)\<notin>system_clauses discharge_table_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_node_reading_system_def)
qed

lemma proof_node_reading_base_meaning:
  assumes "d\<in>system_definitions admitted_instantiation_system"
  shows "(d,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning admitted_instantiation_system"
  using proof_node_reading_old_meaning[of d t] discharge_table_reading_base_meaning[OF assms, of t] assms by auto

lemma proof_node_reading_components:
  "(37,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(88,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (88,t)\<in>positive_meaning site_citation_reading_system"
  "(92,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (92,t)\<in>positive_meaning binding_table_reading_system"
  "(93,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (93,t)\<in>positive_meaning discharge_table_reading_system"
  "(46,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(6,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(48,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (48,t)\<in>positive_meaning data_union_system"
  "(49,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using proof_node_reading_base_meaning[of 37 t] metadata_reading_components(1)[of t]
    proof_node_reading_base_meaning[of 34 t] metadata_reading_components(3)[of t]
    proof_node_reading_old_meaning[of 88 t] discharge_table_reading_old_meaning[of 88 t]
    binding_table_reading_old_meaning[of 88 t] site_link_vector_old_meaning[of 88 t]
    application_vector_old_meaning[of 88 t] site_link_reading_old_meaning[of 88 t]
    proof_node_reading_old_meaning[of 92 t] discharge_table_reading_old_meaning[of 92 t]
    proof_node_reading_old_meaning[of 93 t]
    proof_node_reading_base_meaning[of 46 t] metadata_reading_components(7)[of t]
    proof_node_reading_base_meaning[of 6 t] metadata_reading_components(8)[of t]
    proof_node_reading_base_meaning[of 48 t] metadata_reading_components(9)[of t]
    proof_node_reading_base_meaning[of 49 t] metadata_reading_components(10)[of t] by auto

theorem proof_node_reading_sound:
  assumes holds: "(94,z)\<in>positive_meaning proof_node_reading_system"
  shows "proof_node_reading_result z"
proof -
  have consequence: "(94,z)\<in>schema_consequences proof_node_reading_system (positive_meaning proof_node_reading_system)"
    using holds positive_meaning_unfold[of proof_node_reading_system] by blast
  obtain c S h where clause: "((94,c),S)\<in>system_clauses proof_node_reading_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning proof_node_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  consider (assertion) "S=proof_node_assertion_schema" | (inference) "S=proof_node_inference_schema"
    using clause by (auto simp: proof_node_reading_clauses_def)
  then show ?thesis
  proof cases
    case assertion
    have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 3))\<in>positive_meaning artifact_lookup_system"
      "(34,rooted_rows_argument (h 3) (h 2) (Payload_Term []))\<in>positive_meaning record_admission_system"
      using support by (auto simp: assertion proof_node_assertion_schema_def proof_node_reading_components)
    obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
      "artifact_at E u R" "artifact_value_presents R (h 3)" using calls(1) by (auto simp: artifact_lookup_exact)
    have empty_rows: "Payload_Term []=data_list_term (map address_pair_data xs) \<longleftrightarrow> xs=[]" for xs
      by (cases xs) auto
    obtain r where rec: "h 2=Payload_Term r" "record_at R r [] []"
      using calls(2) by (auto simp: record_admission_at_source[OF source(4)] empty_rows)
    have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
    have raw: "native_proof_node_at E u r Schema_Assertion {} {r} {}"
      by (rule native_proof_node_at.assertion[OF ef source(3) rec(2)])
    show ?thesis
      by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
        rule exI[of _ Schema_Assertion], rule exI[of _ "{}"], rule exI[of _ "Payload_Term []"],
        rule exI[of _ "[r]"], rule exI[of _ "[]"])
        (use conclusion source rec raw in \<open>auto simp: assertion proof_node_assertion_schema_def\<close>)
  next
    case inference
    have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 8))\<in>positive_meaning artifact_lookup_system"
      "(34,rooted_rows_argument (h 8) (h 2) (data_list_term
        [Pair_Term (h 9) (h 12),Pair_Term (h 10) (h 13),Pair_Term (h 11) (h 14)]))\<in>positive_meaning record_admission_system"
      "(88,term_quotation_argument (h 0) (h 1) (h 12) (h 3) (h 15) (h 16))\<in>positive_meaning site_citation_reading_system"
      "(92,term_quotation_argument (h 0) (h 1) (h 13) (h 4) (h 17) (h 18))\<in>positive_meaning binding_table_reading_system"
      "(93,term_quotation_argument (h 0) (h 1) (h 14) (h 5) (h 19) (h 20))\<in>positive_meaning discharge_table_reading_system"
      "(46,collection_join_argument (data_list_term [h 2,h 9,h 10,h 11]) (h 15) (h 21))\<in>positive_meaning data_append_system"
      "(46,collection_join_argument (h 21) (h 17) (h 22))\<in>positive_meaning data_append_system"
      "(46,collection_join_argument (h 22) (h 19) (h 23))\<in>positive_meaning data_append_system"
      "(6,Pair_Term (h 23) (h 6))\<in>positive_meaning bag_comparison_system"
      "(48,collection_join_argument (h 16) (h 18) (h 24))\<in>positive_meaning data_union_system"
      "(48,collection_join_argument (h 24) (h 20) (h 7))\<in>positive_meaning data_union_system"
      "(49,Pair_Term (h 6) (h 7))\<in>positive_meaning payload_disjoint_system"
      using support by (auto simp: inference proof_node_inference_schema_def proof_node_reading_components)
    obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
      "artifact_at E u R" "artifact_value_presents R (h 8)" using calls(1) by (auto simp: artifact_lookup_exact)
    obtain r pc a pb b pd p where rec: "h 2=Payload_Term r" "h 9=Payload_Term pc" "h 12=Payload_Term a"
      "h 10=Payload_Term pb" "h 13=Payload_Term b" "h 11=Payload_Term pd" "h 14=Payload_Term p"
      "record_at R r [pc,pb,pd] [a,b,p]"
      using calls(2) by (simp only: record_admission_three_fields[OF source(4)]) blast
    obtain d Cis Cks where citation: "h 3=definition_site_value d" "h 15=data_list_term (map Payload_Term Cis)"
      "h 16=data_list_term (map Payload_Term Cks)" "distinct Cis" "distinct Cks"
      "site_citation_at E u a d (set Cis) (set Cks)"
      using calls(3) by (simp only: site_citation_reading_at_source[OF source(1)] source(2) rec(3)
        inj_eq[OF use_data_term_injective] factor_term.inject) blast
    obtain bs Bis Bks where binding: "h 4=positioned_binding_rows_term bs"
      "h 17=data_list_term (map Payload_Term Bis)" "h 18=data_list_term (map Payload_Term Bks)"
      "distinct bs" "distinct Bis" "distinct Bks" "native_binding_table_at E u b (set bs) (set Bis) (set Bks)"
      using calls(4) by (simp only: binding_table_reading_at_source[OF source(1)] source(2) rec(5)
        inj_eq[OF use_data_term_injective] factor_term.inject) blast
    obtain ds Dis Dks where discharge: "h 5=discharge_rows_term ds"
      "h 19=data_list_term (map Payload_Term Dis)" "h 20=data_list_term (map Payload_Term Dks)"
      "distinct ds" "distinct Dis" "distinct Dks" "native_discharge_table_at E u p (set ds) (set Dis) (set Dks)"
      using calls(5) by (simp only: discharge_table_reading_at_source[OF source(1)] source(2) rec(7)
        inj_eq[OF use_data_term_injective] factor_term.inject) blast
    obtain Is Ks where metadata: "h 6=data_list_term (map Payload_Term Is)" "h 7=data_list_term (map Payload_Term Ks)"
      "distinct Is" "distinct Ks" "set Is\<inter>set Ks={}" using calls(12) by (auto simp: payload_disjoint_exact)
    have prefix: "h 21=data_list_term (map Payload_Term (r#pc#pb#pd#Cis))"
      using calls(6) by (simp only: rec(1,2,4,6) citation(2) data_append_at_lists) auto
    have second: "h 22=data_list_term (map Payload_Term (r#pc#pb#pd#Cis@Bis))"
      using calls(7) by (simp only: prefix binding(2) data_append_at_lists) auto
    have joined: "h 23=data_list_term (map Payload_Term (r#pc#pb#pd#Cis@Bis@Dis))"
      using calls(8) by (simp only: second discharge(2) data_append_at_lists) auto
    have counts: "mset (r#pc#pb#pd#Cis@Bis@Dis)=mset Is"
      using calls(9) by (simp only: joined metadata(1) bag_comparison_lists injective_mapped_multisets[OF payload_term_inj])
    have distinct_all: "distinct (r#pc#pb#pd#Cis@Bis@Dis)"
      using mset_eq_imp_distinct_iff[OF counts] metadata(3) by blast
    have geometry: "insert r (set [pc,pb,pd])\<inter>(set Cis\<union>set Bis\<union>set Dis)={}"
      "set Cis\<inter>set Bis={}" "set Cis\<inter>set Dis={}" "set Bis\<inter>set Dis={}"
      "set Is=insert r (set [pc,pb,pd]\<union>set Cis\<union>set Bis\<union>set Dis)"
      using distinct_all mset_eq_setD[OF counts] by (auto simp: distinct_append)
    obtain Xs where first_slots: "h 24=data_list_term Xs" "set Xs=set (map Payload_Term Cks)\<union>set (map Payload_Term Bks)"
      using calls(10) by (auto simp: citation(3) binding(3) data_union_exact data_list_term_injective)
    have slots_encoded: "set (map Payload_Term Ks)=set Xs\<union>set (map Payload_Term Dks)"
      using calls(11) by (simp only: first_slots(1) discharge(3) metadata(2) data_union_lists; blast)
    have slots: "set Ks=set Cks\<union>set Bks\<union>set Dks"
      using slots_encoded first_slots(2) by auto
    have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
    have raw_binding: "native_binding_table_at E u b (fset (fset_of_list bs)) (set Bis) (set Bks)"
      using binding(7) by (simp add: fset_of_list.rep_eq)
    have raw: "native_proof_node_at E u r (Schema_Inference d (fset_of_list bs)) (set ds) (set Is) (set Ks)"
      using native_proof_node_at.inference[OF ef source(3) rec(8) citation(6) raw_binding discharge(7) geometry(1-4)]
        geometry(5) slots metadata(5) by simp
    have presented: "proof_node_value_presents (Schema_Inference d (fset_of_list bs)) (set ds)
      (data_list_term [definition_site_value d,positioned_binding_rows_term bs,discharge_rows_term ds])"
      using binding(4) discharge(4) by (simp only: proof_node_value_inference; blast)
    show ?thesis
      by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
        rule exI[of _ "Schema_Inference d (fset_of_list bs)"], rule exI[of _ "set ds"],
        rule exI[of _ "data_list_term [definition_site_value d,positioned_binding_rows_term bs,discharge_rows_term ds]"],
        rule exI[of _ Is], rule exI[of _ Ks])
        (use conclusion source rec citation binding discharge metadata raw presented in
          \<open>auto simp: inference proof_node_inference_schema_def\<close>)
  qed
qed

theorem proof_node_reading_complete:
  assumes source: "environment_value_presents E e" and order: "distinct Is" "distinct Ks"
    and raw: "native_proof_node_at E u r N D (set Is) (set Ks)"
    and presented: "proof_node_value_presents N D n"
  shows "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system"
proof (cases N)
  case Schema_Assertion
  have fields: "D={}" "set Is={r}" "set Ks={}"
    using native_proof_node_assertion[of E u r D "set Is" "set Ks"] raw Schema_Assertion by blast+
  have metadata: "Is=[r]" "Ks=[]"
    using distinct_singleton_enumeration[OF order(1) fields(2)] fields(3) by simp_all
  have n: "n=Payload_Term []" using presented Schema_Assertion by simp
  obtain R where actual: "artifact_at E u R" "record_at R r [] []"
    using raw Schema_Assertion by (cases rule: native_proof_node_at.cases) auto
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef actual(1) by (auto simp: environment_formed_def)
  obtain material where quotation: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source actual(1) quotation by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r) (Payload_Term []))\<in>positive_meaning record_admission_system"
    using record_admission_rows[OF quotation, of r "[]"] actual(2) by simp
  have formed: "term_formed e" "term_formed (use_data_term u)" "term_formed (Payload_Term r)" "term_formed material"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term u else if j=2 then Payload_Term r else material"
  have result: "(94,evaluate_pattern ?h (schema_conclusion proof_node_assertion_schema))\<in>positive_meaning proof_node_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed lookup rec in \<open>auto simp: proof_node_reading_clauses_def proof_node_assertion_schema_def
        schema_variables_def proof_node_reading_call proof_node_reading_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: metadata n proof_node_assertion_schema_def)
next
  case (Schema_Inference c V)
  obtain bs ds where value_fields: "n=data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds]"
    "distinct bs" "distinct ds" "set bs=fset V" "set ds=D"
    using presented by (auto simp: Schema_Inference)
  obtain R ps a b p C A B L J W where actual: "artifact_at E u R" "record_at R r ps [a,b,p]"
    "site_citation_at E u a c C A" "native_binding_table_at E u b (fset V) B L"
    "native_discharge_table_at E u p D J W"
    "insert r (set ps)\<inter>(C\<union>B\<union>J)={}" "C\<inter>B={}" "C\<inter>J={}" "B\<inter>J={}"
    "set Is=insert r (set ps\<union>C\<union>B\<union>J)" "set Ks=A\<union>L\<union>W" "set Is\<inter>set Ks={}"
    using raw Schema_Inference by (cases rule: native_proof_node_at.cases) auto
  obtain pc pb pd where ps: "ps=[pc,pb,pd]" using record_at_preserves_socket_occurrences[OF actual(2)]
    by (auto simp: length_Suc_conv)
  have ports: "distinct [pc,pb,pd]" "r\<notin>set [pc,pb,pd]"
    using record_at_preserves_socket_occurrences[OF actual(2)] by (auto simp: ps)
  obtain Cis where cis: "set Cis=C" "distinct Cis"
    using finite_distinct_list[OF site_citation_properties(2)[OF actual(3)]] by blast
  obtain Cks where cks: "set Cks=A" "distinct Cks"
    using finite_distinct_list[OF site_citation_properties(3)[OF actual(3)]] by blast
  obtain Bis where bis: "set Bis=B" "distinct Bis"
    using finite_distinct_list[OF native_binding_table_properties(4)[OF actual(4)]] by blast
  obtain Bks where bks: "set Bks=L" "distinct Bks"
    using finite_distinct_list[OF native_binding_table_properties(5)[OF actual(4)]] by blast
  obtain Dis where dis: "set Dis=J" "distinct Dis"
    using finite_distinct_list[OF native_discharge_table_properties(4)[OF actual(5)]] by blast
  obtain Dks where dks: "set Dks=W" "distinct Dks"
    using finite_distinct_list[OF native_discharge_table_properties(5)[OF actual(5)]] by blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef actual(1) by (auto simp: environment_formed_def)
  obtain material where quotation: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source actual(1) quotation by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r) (data_list_term
      [Pair_Term (Payload_Term pc) (Payload_Term a),Pair_Term (Payload_Term pb) (Payload_Term b),
       Pair_Term (Payload_Term pd) (Payload_Term p)]))\<in>positive_meaning record_admission_system"
    by (simp only: record_admission_three_fields[OF quotation]) (use actual(2) ps in auto)
  have citation: "(88,term_quotation_argument e (use_data_term u) (Payload_Term a) (definition_site_value c)
      (data_list_term (map Payload_Term Cis)) (data_list_term (map Payload_Term Cks)))\<in>positive_meaning site_citation_reading_system"
    by (rule site_citation_reading_complete[OF source cis(2) cks(2)]) (use actual(3) cis(1) cks(1) in simp)
  have binding: "(92,term_quotation_argument e (use_data_term u) (Payload_Term b) (positioned_binding_rows_term bs)
      (data_list_term (map Payload_Term Bis)) (data_list_term (map Payload_Term Bks)))\<in>positive_meaning binding_table_reading_system"
    by (rule binding_table_reading_complete[OF source value_fields(2) bis(2) bks(2)])
      (use actual(4) value_fields(4) bis(1) bks(1) in simp)
  have discharge: "(93,term_quotation_argument e (use_data_term u) (Payload_Term p) (discharge_rows_term ds)
      (data_list_term (map Payload_Term Dis)) (data_list_term (map Payload_Term Dks)))\<in>positive_meaning discharge_table_reading_system"
    by (rule discharge_table_reading_complete[OF source value_fields(3) dis(2) dks(2)])
      (use actual(5) value_fields(5) dis(1) dks(1) in simp)
  have formed: "term_formed e" "term_formed (use_data_term u)" "term_formed material"
    "octets_formed r" "octets_formed pc" "octets_formed pb" "octets_formed pd"
    "octets_formed a" "octets_formed b" "octets_formed p"
    "term_formed (definition_site_value c)" "term_formed (positioned_binding_rows_term bs)" "term_formed (discharge_rows_term ds)"
    "\<forall>x\<in>set Cis\<union>set Cks\<union>set Bis\<union>set Bks\<union>set Dis\<union>set Dks. octets_formed x"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF citation]]
      schema_call_formed_target[OF positive_meaning_formed[OF binding]]
      schema_call_formed_target[OF positive_meaning_formed[OF discharge]]
    by (auto simp: data_list_term_formed)
  have bytes: "\<forall>x\<in>set Is\<union>set Ks. octets_formed x"
    using formed actual(10,11) ps cis(1) cks(1) bis(1) bks(1) dis(1) dks(1) by auto
  have distinct_all: "distinct (r#pc#pb#pd#Cis@Bis@Dis)"
    using ports cis(2) bis(2) dis(2) actual(6-9) ps cis(1) bis(1) dis(1) by (auto simp: distinct_append)
  have set_all: "set (r#pc#pb#pd#Cis@Bis@Dis)=set Is"
    using actual(10) ps cis(1) bis(1) dis(1) by auto
  have counts: "mset (r#pc#pb#pd#Cis@Bis@Dis)=mset Is"
    using distinct_source_mset[OF order(1), of "r#pc#pb#pd#Cis@Bis@Dis"] distinct_all set_all by auto
  let ?prefix="data_list_term (map Payload_Term (r#pc#pb#pd#Cis))"
  let ?second="data_list_term (map Payload_Term (r#pc#pb#pd#Cis@Bis))"
  let ?joined="data_list_term (map Payload_Term (r#pc#pb#pd#Cis@Bis@Dis))"
  let ?slots="data_list_term (map Payload_Term (Cks@Bks))"
  have prefix: "(46,collection_join_argument (data_list_term [Payload_Term r,Payload_Term pc,Payload_Term pb,Payload_Term pd])
      (data_list_term (map Payload_Term Cis)) ?prefix)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use formed in auto)
  have second: "(46,collection_join_argument ?prefix (data_list_term (map Payload_Term Bis)) ?second)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use formed in auto)
  have joined: "(46,collection_join_argument ?second (data_list_term (map Payload_Term Dis)) ?joined)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use formed in auto)
  have interior: "(6,Pair_Term ?joined (data_list_term (map Payload_Term Is)))\<in>positive_meaning bag_comparison_system"
    by (simp only: bag_comparison_lists injective_mapped_multisets[OF payload_term_inj]) (use formed bytes counts in auto)
  have first_slots: "(48,collection_join_argument (data_list_term (map Payload_Term Cks))
      (data_list_term (map Payload_Term Bks)) ?slots)\<in>positive_meaning data_union_system"
    by (simp only: data_union_payload_lists) (use formed in auto)
  have slots: "(48,collection_join_argument ?slots (data_list_term (map Payload_Term Dks))
      (data_list_term (map Payload_Term Ks)))\<in>positive_meaning data_union_system"
    by (simp only: data_union_payload_lists) (use formed bytes actual(11) cks(1) bks(1) dks(1) in auto)
  have boundary: "(49,Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp only: payload_disjoint_lists) (use order bytes actual(12) in blast)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term u else if j=2 then Payload_Term r
    else if j=3 then definition_site_value c else if j=4 then positioned_binding_rows_term bs else if j=5 then discharge_rows_term ds
    else if j=6 then data_list_term (map Payload_Term Is) else if j=7 then data_list_term (map Payload_Term Ks)
    else if j=8 then material else if j=9 then Payload_Term pc else if j=10 then Payload_Term pb else if j=11 then Payload_Term pd
    else if j=12 then Payload_Term a else if j=13 then Payload_Term b else if j=14 then Payload_Term p
    else if j=15 then data_list_term (map Payload_Term Cis) else if j=16 then data_list_term (map Payload_Term Cks)
    else if j=17 then data_list_term (map Payload_Term Bis) else if j=18 then data_list_term (map Payload_Term Bks)
    else if j=19 then data_list_term (map Payload_Term Dis) else if j=20 then data_list_term (map Payload_Term Dks)
    else if j=21 then ?prefix else if j=22 then ?second else if j=23 then ?joined else ?slots"
  have empty_payload: "octets_formed []" by (simp add: octets_formed_def)
  have result: "(94,evaluate_pattern ?h (schema_conclusion proof_node_inference_schema))\<in>positive_meaning proof_node_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed bytes empty_payload lookup rec citation binding discharge prefix second joined interior first_slots slots boundary in
        \<open>auto simp: proof_node_reading_clauses_def proof_node_inference_schema_def schema_variables_def
          proof_node_reading_call proof_node_reading_components data_list_term_formed\<close>)
  show ?thesis using result by (simp add: proof_node_inference_schema_def value_fields(1))
qed

theorem proof_node_reading_exact:
  "(94,z)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> proof_node_reading_result z"
  using proof_node_reading_sound proof_node_reading_complete by blast

corollary proof_node_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    (\<exists>v a N D Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> proof_node_value_presents N D n \<and>
      native_proof_node_at E v a N D (set Is) (set Ks))"
proof
  assume holds: "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system"
  obtain F v a N D Is Ks where parts: "environment_value_presents F e" "u=use_data_term v" "r=Payload_Term a"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)" "distinct Is" "distinct Ks"
    "proof_node_value_presents N D n" "native_proof_node_at F v a N D (set Is) (set Ks)"
    using holds by (simp only: proof_node_reading_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>v a N D Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> proof_node_value_presents N D n \<and>
      native_proof_node_at E v a N D (set Is) (set Ks)"
    by (rule exI[of _ v], rule exI[of _ a], rule exI[of _ N], rule exI[of _ D], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts same in auto)
next
  assume "\<exists>v a N D Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> proof_node_value_presents N D n \<and>
      native_proof_node_at E v a N D (set Is) (set Ks)"
  then show "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system"
    using proof_node_reading_complete[OF source] by blast
qed

corollary proof_node_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    distinct Is \<and> distinct Ks \<and> (\<exists>N D. proof_node_value_presents N D n \<and>
      native_proof_node_at E u r N D (set Is) (set Ks))"
  by (simp only: proof_node_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
    factor_term.inject data_list_term_injective injective_mapped_lists[OF payload_term_inj]) blast

corollary proof_node_reading_at_node:
  assumes source: "environment_value_presents E e" and raw: "native_proof_node_at E u r N D (set Is) (set Ks)"
  shows "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    distinct Is \<and> distinct Ks \<and> proof_node_value_presents N D n"
  by (simp only: proof_node_reading_on_values[OF source])
    (use raw native_proof_node_unique[OF _ raw] in blast)

corollary proof_node_reading_assertion:
  assumes source: "environment_value_presents E e"
  shows "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) (Payload_Term [])
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    distinct Is \<and> distinct Ks \<and> native_proof_node_at E u r Schema_Assertion {} (set Is) (set Ks)"
  by (simp only: proof_node_reading_on_values[OF source] proof_node_value_assertion) blast

corollary proof_node_reading_inference:
  assumes source: "environment_value_presents E e"
  shows "(94,term_quotation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term [definition_site_value c,positioned_binding_rows_term bs,discharge_rows_term ds])
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    distinct bs \<and> distinct ds \<and> distinct Is \<and> distinct Ks \<and>
    native_proof_node_at E u r (Schema_Inference c (fset_of_list bs)) (set ds) (set Is) (set Ks)"
  by (simp only: proof_node_reading_on_values[OF source] proof_node_value_inference) blast

corollary proof_node_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow>
    (94,term_quotation_argument f u r n i k)\<in>positive_meaning proof_node_reading_system"
  by (simp only: proof_node_reading_at_source[OF assms(1)] proof_node_reading_at_source[OF assms(2)])

corollary proof_node_reading_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system"
    and second: "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) m
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term As)))\<in>positive_meaning proof_node_reading_system"
  shows "\<exists>N D. proof_node_value_presents N D n \<and> proof_node_value_presents N D m \<and>
    mset Is=mset Js \<and> mset Ks=mset As"
proof -
  obtain N D where left: "distinct Is" "distinct Ks" "proof_node_value_presents N D n"
    "native_proof_node_at E u r N D (set Is) (set Ks)" using first by (simp only: proof_node_reading_on_values[OF source]) blast
  obtain M F where right: "distinct Js" "distinct As" "proof_node_value_presents M F m"
    "native_proof_node_at E u r M F (set Js) (set As)" using second by (simp only: proof_node_reading_on_values[OF source]) blast
  have same: "N=M \<and> D=F \<and> set Is=set Js \<and> set Ks=set As" by (rule native_proof_node_unique[OF left(4) right(4)])
  show ?thesis by (rule exI[of _ N], rule exI[of _ D])
    (use left right same distinct_source_mset[of Is Js] distinct_source_mset[of Ks As] in auto)
qed

section \<open>One fixed native program reads every future metadata argument\<close>

lemma proof_metadata_operation_components:
  "(88,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (88,t)\<in>positive_meaning site_citation_reading_system"
  "(89,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (89,t)\<in>positive_meaning site_link_reading_system"
  "(90,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (90,t)\<in>positive_meaning application_vector_system"
  "(91,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (91,t)\<in>positive_meaning site_link_vector_system"
  "(92,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (92,t)\<in>positive_meaning binding_table_reading_system"
  "(93,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> (93,t)\<in>positive_meaning discharge_table_reading_system"
  using proof_node_reading_components(3)[of t]
    proof_node_reading_old_meaning[of 89 t] discharge_table_reading_old_meaning[of 89 t]
    binding_table_reading_old_meaning[of 89 t] site_link_vector_old_meaning[of 89 t] application_vector_old_meaning[of 89 t]
    proof_node_reading_old_meaning[of 90 t] discharge_table_reading_old_meaning[of 90 t]
    binding_table_reading_old_meaning[of 90 t] site_link_vector_old_meaning[of 90 t]
    proof_node_reading_old_meaning[of 91 t] discharge_table_reading_old_meaning[of 91 t] binding_table_reading_old_meaning[of 91 t]
    proof_node_reading_components(4,5)[of t] by auto

abbreviation proof_metadata_operation_result :: "nat\<Rightarrow>factor_term\<Rightarrow>bool" where
  "proof_metadata_operation_result d t \<equiv>
    (d=88 \<and> site_citation_reading_result t) \<or> (d=89 \<and> site_link_reading_result t) \<or>
    (d=90 \<and> application_vector_result t) \<or> (d=91 \<and> site_link_vector_result t) \<or>
    (d=92 \<and> binding_table_reading_result t) \<or> (d=93 \<and> discharge_table_reading_result t) \<or>
    (d=94 \<and> proof_node_reading_result t)"

lemma proof_metadata_operations_exact:
  assumes "d\<in>{88,89,90,91,92,93,94}"
  shows "(d,t)\<in>positive_meaning proof_node_reading_system \<longleftrightarrow> proof_metadata_operation_result d t"
proof -
  consider "d=88" | "d=89" | "d=90" | "d=91" | "d=92" | "d=93" | "d=94" using assms by auto
  then show ?thesis by cases
    (simp_all add: proof_metadata_operation_components site_citation_reading_exact site_link_reading_exact
      application_vector_exact site_link_vector_exact binding_table_reading_exact discharge_table_reading_exact proof_node_reading_exact)
qed

theorem native_proof_metadata_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {88::nat,89,90,91,92,93,94} \<and>
    (\<forall>d\<in>{88,89,90,91,92,93,94}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> proof_metadata_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions proof_node_reading_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions proof_node_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed proof_node_reading_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF proof_node_reading_system_formed] by blast
  have sites: "inj_on g {88,89,90,91,92,93,94}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {88,89,90,91,92,93,94}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{88,89,90,91,92,93,94}" and tf: "term_formed t"
    have member: "d\<in>system_definitions proof_node_reading_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed proof_node_reading_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> proof_metadata_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member proof_metadata_operations_exact[OF selected] in \<open>auto simp: proof_node_reading_call\<close>)
  qed
qed

text \<open>
  Assertions have the empty value, and inferences have the three recovered
  fields already specified by the native grammar: clause site, complete
  bindings, and complete premise links. Their different shapes require no
  added role tag. Binding and link enumeration can vary independently, while
  each complete value uniquely recovers its node and discharge relation.
  Neither form stores a conclusion or an assumption collection.

  The two ordinary clauses recover exactly that native metadata and its
  complete physical boundary. They do not check graph formation, the supplied
  root claim, clause admission, or assumption truth. The existing proof-node
  datatype and raw reader are imported to state this contract; no derivation
  or evidence predicate occurs in a program clause.

  Seven entries with ten ordinary clauses have exact contracts over all
  terms and preserve every earlier meaning. One fixed closed native program
  supplies seven distinct sites before all future formed operands and retains
  its canonical environment. It has ninety-five definitions and one hundred
  and fifty clauses. Further entries separately derive complete native graph
  admission and reachability. Derivation and replay-retention checking remains,
  as do the full transition protocol, reflection, and genesis.
\<close>

end
