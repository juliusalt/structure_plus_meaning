theory Factor_Proof_Graph_Membership
  imports Factor_Proof_Graph_Admission
begin

section \<open>Membership follows actual premise links from an admitted root\<close>

abbreviation proof_graph_subject_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "proof_graph_subject_argument e u r n \<equiv> Pair_Term (source_root_argument e u r) n"

abbreviation proof_graph_subject_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "proof_graph_subject_pattern e u r n \<equiv> Pattern_Pair (source_root_pattern e u r) n"

abbreviation proof_graph_membership_result :: "factor_term \<Rightarrow> bool" where
  "proof_graph_membership_result z \<equiv> \<exists>E e u r n G.
    z=proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n) \<and>
    environment_value_presents E e \<and> native_schema_graph_at E (u,r) G \<and> n\<in>schema_graph_nodes G"

definition proof_graph_membership_root_schema :: "(nat,nat,nat) factor_schema" where
  "proof_graph_membership_root_schema=data_rule
    (proof_graph_subject_pattern data_x data_y data_z (Pattern_Pair data_y data_z))
    {(0,97,source_root_pattern data_x data_y data_z)}"

definition proof_graph_membership_step_schema :: "(nat,nat,nat) factor_schema" where
  "proof_graph_membership_step_schema=data_rule (proof_graph_subject_pattern data_x data_y data_z data_w)
    {(0,98,proof_graph_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))),
     (1,94,term_quotation_pattern data_x (Pattern_Variable 4) (Pattern_Variable 5)
       (data_list_pattern [Pattern_Variable 6,Pattern_Variable 7,Pattern_Variable 8]) (Pattern_Variable 9) (Pattern_Variable 10)),
     (2,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 11) data_w) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 12)))}"

definition proof_graph_membership_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "proof_graph_membership_clauses={(0,proof_graph_membership_root_schema),(1,proof_graph_membership_step_schema)}"

definition proof_graph_membership_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_graph_membership_system=add_view_definition proof_graph_admission_system 98 data_x proof_graph_membership_clauses"

lemma proof_graph_membership_system_formed [simp]: "schema_system_formed proof_graph_membership_system"
  unfolding proof_graph_membership_system_def
  by (rule add_recursive_definition_formed[OF proof_graph_admission_system_formed])
    (auto simp: proof_graph_membership_clauses_def proof_graph_membership_root_schema_def proof_graph_membership_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_graph_membership_definitions [simp]:
  "system_definitions proof_graph_membership_system=insert 98 (system_definitions proof_graph_admission_system)"
  by (simp add: proof_graph_membership_system_def)

lemma proof_graph_membership_call:
  "schema_call_formed proof_graph_membership_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_graph_membership_system \<and> term_formed t"
  using added_variable_calls[OF proof_graph_admission_system_formed
    proof_graph_membership_system_formed[unfolded proof_graph_membership_system_def] proof_graph_admission_call]
  by (simp only: proof_graph_membership_system_def[symmetric])

lemma proof_graph_membership_old_meaning:
  assumes "d\<in>system_definitions proof_graph_admission_system"
  shows "(d,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_admission_system"
  using added_definition_preserves_old(2)[OF proof_graph_admission_system_formed
    proof_graph_membership_system_formed[unfolded proof_graph_membership_system_def], of d t] assms
  by (auto simp: proof_graph_membership_system_def)

lemma proof_graph_membership_clause [simp]:
  "((98,c),S)\<in>system_clauses proof_graph_membership_system \<longleftrightarrow> (c,S)\<in>proof_graph_membership_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_graph_admission_system \<Longrightarrow> d\<in>system_definitions proof_graph_admission_system" for d c S
    using proof_graph_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((98,c),S)\<notin>system_clauses proof_graph_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_graph_membership_system_def)
qed

lemma proof_graph_membership_node_meaning:
  assumes "d\<in>system_definitions proof_node_reading_system"
  shows "(d,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system"
  using proof_graph_membership_old_meaning[of d t] proof_graph_admission_node_meaning[OF assms, of t] assms by auto

lemma proof_graph_membership_components:
  "(97,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (97,t)\<in>positive_meaning proof_graph_admission_system"
  "(94,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (94,t)\<in>positive_meaning proof_node_reading_system"
  "(5,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  using proof_graph_membership_old_meaning[of 97 t] proof_graph_membership_node_meaning[of 94 t]
    proof_graph_membership_node_meaning[of 5 t] proof_node_reading_base_meaning[of 5 t]
    metadata_reading_quotation_meaning[of 5 t] quotation_admission_projection_meaning[of 5 t]
    target_projection_bag_meaning[of 5 t] by auto

lemma proof_graph_membership_root:
  assumes admitted: "(97,source_root_argument e u r)\<in>positive_meaning proof_graph_admission_system"
  shows "(98,proof_graph_subject_argument e u r (Pair_Term u r))\<in>positive_meaning proof_graph_membership_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF admitted]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else r"
  have result: "(98,evaluate_pattern ?h (schema_conclusion proof_graph_membership_root_schema))\<in>positive_meaning proof_graph_membership_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed admitted in \<open>auto simp: proof_graph_membership_clauses_def proof_graph_membership_root_schema_def
        schema_variables_def proof_graph_membership_call proof_graph_membership_components\<close>)
  show ?thesis using result by (simp add: proof_graph_membership_root_schema_def)
qed

lemma proof_graph_membership_step:
  assumes parent: "(98,proof_graph_subject_argument e u r (Pair_Term v a))\<in>positive_meaning proof_graph_membership_system"
    and read: "(94,term_quotation_argument e v a (data_list_term [c,b,ds]) i k)\<in>positive_meaning proof_node_reading_system"
    and selected: "(5,Pair_Term (Pair_Term s n) (Pair_Term ds rest))\<in>positive_meaning bag_comparison_system"
  shows "(98,proof_graph_subject_argument e u r n)\<in>positive_meaning proof_graph_membership_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a"
    "term_formed c" "term_formed b" "term_formed ds" "term_formed i" "term_formed k"
    "term_formed s" "term_formed n" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF parent]]
      schema_call_formed_target[OF positive_meaning_formed[OF read]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then n
    else if j=4 then v else if j=5 then a else if j=6 then c else if j=7 then b else if j=8 then ds
    else if j=9 then i else if j=10 then k else if j=11 then s else rest"
  have result: "(98,evaluate_pattern ?h (schema_conclusion proof_graph_membership_step_schema))\<in>positive_meaning proof_graph_membership_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed assms in \<open>auto simp: proof_graph_membership_clauses_def proof_graph_membership_step_schema_def
        schema_variables_def proof_graph_membership_call proof_graph_membership_components\<close>)
  show ?thesis using result by (simp add: proof_graph_membership_step_schema_def)
qed

theorem proof_graph_membership_sound:
  assumes holds: "(98,z)\<in>positive_meaning proof_graph_membership_system"
  shows "proof_graph_membership_result z"
proof -
  let ?Q="\<lambda>z. proof_graph_membership_result z"
  have invariant: "(98::nat)=98 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=98 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses proof_graph_membership_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed proof_graph_membership_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning proof_graph_membership_system \<and>
        (e=98 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=98 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=98"
      then consider (root) "S=proof_graph_membership_root_schema" | (step) "S=proof_graph_membership_step_schema"
        using clause by (auto simp: proof_graph_membership_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case root
        have admitted: "(97,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning proof_graph_admission_system"
          using support by (auto simp: root proof_graph_membership_root_schema_def proof_graph_membership_components)
        obtain E u r G where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          and graph: "native_schema_graph_at E (u,r) G"
          using admitted by (simp only: proof_graph_admission_exact factor_term.inject) blast
        have member: "(u,r)\<in>schema_graph_nodes G" using graph by (simp add: native_schema_graph_at_def schema_graph_formed_def)
        show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u],
            rule exI[of _ r], rule exI[of _ "(u,r)"], rule exI[of _ G])
          (use source graph member in \<open>simp add: root proof_graph_membership_root_schema_def site_data_term_def\<close>)
      next
        case step
        have previous: "?Q (proof_graph_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 4) (h 5)))"
          and read: "(94,term_quotation_argument (h 0) (h 4) (h 5) (data_list_term [h 6,h 7,h 8]) (h 9) (h 10))
            \<in>positive_meaning proof_node_reading_system"
          and selection: "(5,Pair_Term (Pair_Term (h 11) (h 3)) (Pair_Term (h 8) (h 12)))
            \<in>positive_meaning bag_comparison_system"
          using support by (auto simp: step proof_graph_membership_step_schema_def proof_graph_membership_components)
        obtain E u r p G where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          "Pair_Term (h 4) (h 5)=definition_site_value p"
          and graph: "native_schema_graph_at E (u,r) G" and parent: "p\<in>schema_graph_nodes G"
          using previous by (simp only: factor_term.inject) blast
        have p: "h 4=use_data_term (fst p)" "h 5=Payload_Term (snd p)" using source(4) by (simp_all add: site_data_term_def)
        obtain N D Is Ks where presented: "proof_node_value_presents N D (data_list_term [h 6,h 7,h 8])"
          and raw: "native_proof_node_at E (fst p) (snd p) N D (set Is) (set Ks)"
          using read by (simp only: p proof_node_reading_at_source[OF source(1)]
            inj_eq[OF use_data_term_injective] factor_term.inject) blast
        obtain c vs ds where fields: "h 6=definition_site_value c" "h 7=positioned_binding_rows_term vs" "h 8=discharge_rows_term ds"
          using presented by (cases N) auto
        have links: "D=set ds" using presented by (simp only: fields proof_node_value_inference; blast)
        have selected: "selected_data_member (Pair_Term (h 11) (h 3)) (h 8)" using selection by blast
        have ds_term: "discharge_rows_term ds =
          data_list_term (map (\<lambda>(s,n). Pair_Term (definition_site_value s) (definition_site_value n)) ds)"
          by (simp add: comp_def case_prod_unfold)
        have row: "Pair_Term (h 11) (h 3)\<in>set (map (\<lambda>(s,n). Pair_Term (definition_site_value s) (definition_site_value n)) ds)"
          using selected by (simp only: fields(3) ds_term selected_data_member_exact data_list_term_injective; blast)
        obtain s n where target: "h 3=definition_site_value n" and premise: "(s,n)\<in>D"
          using row links by auto
        have edge: "(n,p)\<in>native_proof_edges E"
          by (simp only: native_proof_edges_at_node[OF raw]) (rule rel_ranI[OF premise])
        have actual: "(n,p)\<in>schema_graph_edges G" using native_schema_graph_edge_at[OF graph parent] edge by simp
        have formed: "schema_graph_formed G (u,r)" using graph by (simp add: native_schema_graph_at_def)
        have member: "n\<in>schema_graph_nodes G" by (rule schema_graph_edge_nodes(1)[OF formed actual])
        show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u],
            rule exI[of _ r], rule exI[of _ n], rule exI[of _ G])
          (use source target graph member in \<open>simp add: step proof_graph_membership_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem proof_graph_membership_complete:
  assumes source: "environment_value_presents E e" and graph: "native_schema_graph_at E (u,r) G"
    and member: "n\<in>schema_graph_nodes G"
  shows "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n))
    \<in>positive_meaning proof_graph_membership_system"
proof -
  have formed: "schema_graph_formed G (u,r)" using graph by (simp add: native_schema_graph_at_def)
  have path: "(n,(u,r))\<in>(schema_graph_edges G)\<^sup>*"
    using formed member by (simp add: schema_graph_formed_def)
  have admitted: "(97,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning proof_graph_admission_system"
    by (rule proof_graph_admission_complete[OF source graph])
  have initial: "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value (u,r)))
    \<in>positive_meaning proof_graph_membership_system"
    using proof_graph_membership_root[OF admitted] by (simp add: site_data_term_def)
  show ?thesis using path
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case by (rule initial)
  next
    case (step x y)
    have parent: "y\<in>schema_graph_nodes G" by (rule schema_graph_edge_nodes(2)[OF formed step.hyps(1)])
    obtain N I K where raw: "native_proof_node_at E (fst y) (snd y) N (schema_graph_premises G y) I K"
      using native_schema_graph_node[OF graph parent] by blast
    obtain s where premise: "(s,x)\<in>schema_graph_premises G y"
      using step.hyps(1) by (auto simp: schema_graph_edges_def schema_graph_premises_def)
    have not_assertion: "N\<noteq>Schema_Assertion"
      using raw premise native_proof_node_assertion[of E "fst y" "snd y" "schema_graph_premises G y" I K] by blast
    obtain c V where node: "N=Schema_Inference c V" using not_assertion by (cases N) auto
    obtain t where presented: "proof_node_value_presents N (schema_graph_premises G y) t"
      using proof_node_value_total[OF raw] by blast
    obtain vs ds where fields: "t=data_list_term [definition_site_value c,positioned_binding_rows_term vs,discharge_rows_term ds]"
      "set ds=schema_graph_premises G y" using presented node by auto
    obtain i k where read: "(94,term_quotation_argument e (use_data_term (fst y)) (Payload_Term (snd y)) t i k)
      \<in>positive_meaning proof_node_reading_system"
      using proof_node_reading_value[OF source raw presented] by blast
    have sites: "\<forall>(s,m)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value m)"
      by (rule native_discharge_values_formed[OF raw]) (simp add: fields(2))
    have data: "data_elements (map (\<lambda>(s,m). Pair_Term (definition_site_value s) (definition_site_value m)) ds)"
      using sites by auto
    have ds_term: "discharge_rows_term ds =
      data_list_term (map (\<lambda>(s,m). Pair_Term (definition_site_value s) (definition_site_value m)) ds)"
      by (simp add: comp_def case_prod_unfold)
    have actual_row: "(s,x)\<in>set ds" using premise fields(2) by simp
    have picked: "Pair_Term (definition_site_value s) (definition_site_value x)\<in>
      set (map (\<lambda>(s,m). Pair_Term (definition_site_value s) (definition_site_value m)) ds)"
      by (simp only: set_map; rule image_eqI[OF _ actual_row]) simp
    have selected: "selected_data_member (Pair_Term (definition_site_value s) (definition_site_value x)) (discharge_rows_term ds)"
      by (simp only: ds_term selected_data_member_exact data_list_term_injective; use data picked in blast)
    obtain rest where selection: "(5,Pair_Term (Pair_Term (definition_site_value s) (definition_site_value x))
      (Pair_Term (discharge_rows_term ds) rest))\<in>positive_meaning bag_comparison_system" using selected by blast
    show ?case by (rule proof_graph_membership_step[OF _ _ selection])
      (use step.IH read in \<open>simp_all add: fields(1) site_data_term_def\<close>)
  qed
qed

theorem proof_graph_membership_exact:
  "(98,z)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> proof_graph_membership_result z"
  using proof_graph_membership_sound proof_graph_membership_complete by blast

corollary proof_graph_membership_at_source:
  assumes source: "environment_value_presents E e"
  shows "(98,proof_graph_subject_argument e u r n)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow>
    (\<exists>v a m G. u=use_data_term v \<and> r=Payload_Term a \<and> n=definition_site_value m \<and>
      native_schema_graph_at E (v,a) G \<and> m\<in>schema_graph_nodes G)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: proof_graph_membership_exact factor_term.inject) (use unique source in blast)
qed

corollary proof_graph_membership_on_values:
  assumes source: "environment_value_presents E e"
  shows "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n))
      \<in>positive_meaning proof_graph_membership_system \<longleftrightarrow>
    (\<exists>G. native_schema_graph_at E (u,r) G \<and> n\<in>schema_graph_nodes G)"
  by (simp only: proof_graph_membership_at_source[OF source] inj_eq[OF use_data_term_injective]
      factor_term.inject definition_site_value_eq) blast

corollary proof_graph_membership_at_graph:
  assumes source: "environment_value_presents E e" and graph: "native_schema_graph_at E (u,r) G"
  shows "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n))
    \<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> n\<in>schema_graph_nodes G"
  by (simp only: proof_graph_membership_on_values[OF source])
    (use graph native_schema_graph_unique[OF _ graph] in blast)

corollary proof_graph_membership_reachable:
  assumes source: "environment_value_presents E e" and graph: "native_schema_graph_at E (u,r) G"
  shows "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n))
    \<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> n\<in>native_proof_sites E (u,r)"
  by (simp only: proof_graph_membership_at_graph[OF source graph] native_schema_graph_exact_sites[OF graph])

corollary proof_graph_membership_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(98,proof_graph_subject_argument e u r n)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow>
    (98,proof_graph_subject_argument f u r n)\<in>positive_meaning proof_graph_membership_system"
  by (simp only: proof_graph_membership_at_source[OF assms(1)] proof_graph_membership_at_source[OF assms(2)])

corollary proof_graph_membership_assertion:
  assumes source: "environment_value_presents E e"
    and raw: "native_proof_node_at E u r Schema_Assertion {} I K"
  shows "(98,proof_graph_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value n))
    \<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> n=(u,r)"
proof -
  obtain G where graph: "native_schema_graph_at E (u,r) G"
    using proof_graph_admission_assertion[OF source raw] by (simp only: proof_graph_admission_on_values[OF source]) blast
  have sites: "native_proof_sites E (u,r)={(u,r)}"
    by (rule native_assertion_root_sites) (use raw in simp)
  show ?thesis by (simp only: proof_graph_membership_reachable[OF source graph] sites singleton_iff)
qed

section \<open>One fixed native program checks every future graph argument\<close>

lemma proof_graph_operation_components:
  "(95,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (95,t)\<in>positive_meaning proof_link_checking_system"
  "(96,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (96,t)\<in>positive_meaning proof_bound_checking_system"
  "(97,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> (97,t)\<in>positive_meaning proof_graph_admission_system"
  using proof_graph_membership_old_meaning[of 95 t] proof_graph_admission_old_meaning[of 95 t] proof_bound_checking_old_meaning[of 95 t]
    proof_graph_membership_old_meaning[of 96 t] proof_graph_admission_old_meaning[of 96 t]
    proof_graph_membership_old_meaning[of 97 t] by auto

abbreviation proof_graph_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "proof_graph_operation_result d t \<equiv>
    if d=95 then proof_link_checking_result t else if d=96 then proof_bound_checking_result t
    else if d=97 then proof_graph_admission_result t else proof_graph_membership_result t"

lemma proof_graph_operations_exact:
  assumes "d\<in>{95,96,97,98}"
  shows "(d,t)\<in>positive_meaning proof_graph_membership_system \<longleftrightarrow> proof_graph_operation_result d t"
proof -
  consider (links) "d=95" | (bound) "d=96" | (graph) "d=97" | (member) "d=98"
    using assms by auto
  then show ?thesis
  proof cases
    case links
    show ?thesis by (simp only: links proof_graph_operation_components proof_link_checking_exact; simp)
  next
    case bound
    show ?thesis by (simp only: bound proof_graph_operation_components proof_bound_checking_exact; simp)
  next
    case graph
    show ?thesis by (simp only: graph proof_graph_operation_components proof_graph_admission_exact; simp)
  next
    case member
    show ?thesis by (simp only: member proof_graph_membership_exact; simp)
  qed
qed

theorem native_proof_graph_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {95::nat,96,97,98} \<and>
    (\<forall>d\<in>{95,96,97,98}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> proof_graph_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions proof_graph_membership_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions proof_graph_membership_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed proof_graph_membership_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_membership_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF proof_graph_membership_system_formed] by blast
  have sites: "inj_on g {95,96,97,98}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {95,96,97,98}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{95,96,97,98}" and tf: "term_formed t"
    have member: "d\<in>system_definitions proof_graph_membership_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed proof_graph_membership_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_membership_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> proof_graph_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member proof_graph_operations_exact[OF selected] in \<open>auto simp: proof_graph_membership_call\<close>)
  qed
qed

text \<open>
  Root membership starts with actual graph admission. Each recursive step
  rereads the current native node and selects one actual complete premise
  row. Membership is exactly the graph's actual root closure, independently
  of a larger bound used by admission. Shared nodes retain one physical
  identity, and an assertion root has exactly itself as the reachable graph.

  Four new entries with nine ordinary clauses have exact contracts over all
  terms and preserve every earlier meaning. One fixed closed native program
  provides four distinct sites before all future formed operands and retains
  its canonical environment. It has ninety-nine definitions and one hundred
  and fifty-nine clauses. Ordinary derivation and replay-retention checking
  remains, as do the full transition protocol, reflection, and genesis.
\<close>

end
