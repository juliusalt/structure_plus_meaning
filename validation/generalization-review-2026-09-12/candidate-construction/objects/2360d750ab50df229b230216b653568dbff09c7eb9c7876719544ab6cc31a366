theory Factor_Proof_Bound_Checking
  imports Factor_Proof_Bound_Values
begin

section \<open>Ordinary clauses check every actual node in a finite bound\<close>

abbreviation proof_bound_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "proof_bound_argument e b h \<equiv> Pair_Term e (Pair_Term b h)"

abbreviation proof_bound_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "proof_bound_pattern e b h \<equiv> Pattern_Pair e (Pattern_Pair b h)"

abbreviation proof_bound_checking_result :: "factor_term \<Rightarrow> bool" where
  "proof_bound_checking_result z \<equiv> \<exists>e. term_formed e \<and>
    (z=proof_bound_argument e (Payload_Term []) (Payload_Term []) \<or>
      (\<exists>E bs hs. z=proof_bound_argument e (proof_bound_term bs) (pair_list_term hs) \<and>
        environment_value_presents E e \<and> proof_bound_values E bs hs))"

lemma proof_bound_checking_resultI:
  assumes source: "environment_value_presents E e" and bound: "proof_bound_values E bs hs"
  shows "proof_bound_checking_result (proof_bound_argument e (proof_bound_term bs) (pair_list_term hs))"
  using source bound environment_value_presents_formed[OF source] by blast

lemma proof_bound_checking_result_at_source:
  assumes source: "environment_value_presents E e"
  shows "proof_bound_checking_result (proof_bound_argument e b h) \<longleftrightarrow>
    (\<exists>bs hs. b=proof_bound_term bs \<and> h=pair_list_term hs \<and> proof_bound_values E bs hs)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  have empty: "\<exists>bs hs. Payload_Term []=proof_bound_term bs \<and> Payload_Term []=pair_list_term hs \<and> proof_bound_values E bs hs"
    by (rule exI[of _ "[]"], rule exI[of _ "[]"]) simp
  show ?thesis by (simp only: factor_term.inject)
    (use unique empty environment_value_presents_formed[OF source] source in blast)
qed

definition proof_bound_nil_schema :: "(nat,nat,nat) factor_schema" where
  "proof_bound_nil_schema=data_rule
    (proof_bound_pattern data_x (Pattern_Payload []) (Pattern_Payload [])) {}"

definition proof_bound_assertion_schema :: "(nat,nat,nat) factor_schema" where
  "proof_bound_assertion_schema=data_rule
    (proof_bound_pattern data_x
      (Pattern_Pair (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Payload [])) data_w) (Pattern_Variable 4))
    {(0,94,term_quotation_pattern data_x data_y data_z (Pattern_Payload [])
       (data_list_pattern [data_z]) (Pattern_Payload [])),
     (1,20,Pattern_Pair (Pattern_Pair data_y data_z) data_w),
     (2,96,proof_bound_pattern data_x data_w (Pattern_Variable 4))}"

definition proof_bound_inference_schema :: "(nat,nat,nat) factor_schema" where
  "proof_bound_inference_schema=data_rule
    (proof_bound_pattern data_x
      (Pattern_Pair (Pattern_Pair (Pattern_Pair data_y data_z)
        (data_list_pattern [data_w,Pattern_Variable 4,Pattern_Variable 5])) (Pattern_Variable 6)) (Pattern_Variable 9))
    {(0,94,term_quotation_pattern data_x data_y data_z
       (data_list_pattern [data_w,Pattern_Variable 4,Pattern_Variable 5]) (Pattern_Variable 10) (Pattern_Variable 11)),
     (1,20,Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Variable 6)),
     (2,95,proof_links_pattern (Pattern_Variable 6) (Pattern_Pair data_y data_z) (Pattern_Variable 5) (Pattern_Variable 7)),
     (3,96,proof_bound_pattern data_x (Pattern_Variable 6) (Pattern_Variable 8)),
     (4,46,collection_join_pattern (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9))}"

definition proof_bound_checking_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "proof_bound_checking_clauses={(0,proof_bound_nil_schema),(1,proof_bound_assertion_schema),(2,proof_bound_inference_schema)}"

definition proof_bound_checking_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_bound_checking_system=add_view_definition proof_link_checking_system 96 data_x proof_bound_checking_clauses"

lemma proof_bound_checking_system_formed [simp]: "schema_system_formed proof_bound_checking_system"
  unfolding proof_bound_checking_system_def
  by (rule add_recursive_definition_formed[OF proof_link_checking_system_formed])
    (auto simp: proof_bound_checking_clauses_def proof_bound_nil_schema_def proof_bound_assertion_schema_def proof_bound_inference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_bound_checking_definitions [simp]:
  "system_definitions proof_bound_checking_system=insert 96 (system_definitions proof_link_checking_system)"
  by (simp add: proof_bound_checking_system_def)

lemma proof_bound_checking_call:
  "schema_call_formed proof_bound_checking_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_bound_checking_system \<and> term_formed t"
  using added_variable_calls[OF proof_link_checking_system_formed
    proof_bound_checking_system_formed[unfolded proof_bound_checking_system_def] proof_link_checking_call]
  by (simp only: proof_bound_checking_system_def[symmetric])

lemma proof_bound_checking_old_meaning:
  assumes "d\<in>system_definitions proof_link_checking_system"
  shows "(d,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_link_checking_system"
  using added_definition_preserves_old(2)[OF proof_link_checking_system_formed
    proof_bound_checking_system_formed[unfolded proof_bound_checking_system_def], of d t] assms
  by (auto simp: proof_bound_checking_system_def)

lemma proof_bound_checking_clause [simp]:
  "((96,c),S)\<in>system_clauses proof_bound_checking_system \<longleftrightarrow> (c,S)\<in>proof_bound_checking_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_link_checking_system \<Longrightarrow> d\<in>system_definitions proof_link_checking_system" for d c S
    using proof_link_checking_system_formed unfolding schema_system_formed_def by blast
  have absent: "((96,c),S)\<notin>system_clauses proof_link_checking_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_bound_checking_system_def)
qed

lemma proof_bound_checking_node_meaning:
  assumes "d\<in>system_definitions proof_node_reading_system"
  shows "(d,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system"
  using proof_bound_checking_old_meaning[of d t] proof_link_checking_old_meaning[OF assms, of t] assms by auto

lemma proof_bound_checking_components:
  "(94,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (94,t)\<in>positive_meaning proof_node_reading_system"
  "(20,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (20,t)\<in>positive_meaning key_absence_system"
  "(95,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (95,t)\<in>positive_meaning proof_link_checking_system"
  "(46,t)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  using proof_bound_checking_node_meaning[of 94 t]
    proof_bound_checking_old_meaning[of 20 t] proof_link_checking_keyed_meaning[of 20 t] keyed_list_previous_meaning[of 20 t]
    proof_bound_checking_old_meaning[of 95 t]
    proof_bound_checking_node_meaning[of 46 t] proof_node_reading_components(6)[of t] by auto

lemma proof_bound_checking_empty:
  assumes "term_formed e"
  shows "(96,proof_bound_argument e (Payload_Term []) (Payload_Term []))\<in>positive_meaning proof_bound_checking_system"
proof -
  have result: "(96,evaluate_pattern (\<lambda>_. e) (schema_conclusion proof_bound_nil_schema))\<in>positive_meaning proof_bound_checking_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use assms in \<open>auto simp: proof_bound_checking_clauses_def proof_bound_nil_schema_def schema_variables_def
        proof_bound_checking_call octets_formed_def\<close>)
  show ?thesis using result by (simp add: proof_bound_nil_schema_def)
qed

theorem proof_bound_checking_sound:
  assumes holds: "(96,z)\<in>positive_meaning proof_bound_checking_system"
  shows "proof_bound_checking_result z"
proof -
  let ?Q="\<lambda>z. proof_bound_checking_result z"
  have invariant: "(96::nat)=96 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=96 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses proof_bound_checking_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed proof_bound_checking_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning proof_bound_checking_system \<and>
        (e=96 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=96 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=96"
      then consider (nil) "S=proof_bound_nil_schema" | (assertion) "S=proof_bound_assertion_schema"
        | (inference) "S=proof_bound_inference_schema"
        using clause by (auto simp: proof_bound_checking_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        have tf: "term_formed (h 0)" using assignment by (auto simp: nil proof_bound_nil_schema_def schema_variables_def)
        show ?thesis by (rule exI[of _ "h 0"]) (use tf in \<open>simp add: nil proof_bound_nil_schema_def\<close>)
      next
        case assertion
        have read: "(94,term_quotation_argument (h 0) (h 1) (h 2) (Payload_Term [])
            (data_list_term [h 2]) (Payload_Term []))\<in>positive_meaning proof_node_reading_system"
          and absence: "(20,Pair_Term (Pair_Term (h 1) (h 2)) (h 3))\<in>positive_meaning key_absence_system"
          and previous: "?Q (proof_bound_argument (h 0) (h 3) (h 4))"
          using support by (auto simp: assertion proof_bound_assertion_schema_def proof_bound_checking_components)
        obtain E u r Is Ks where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          and raw: "native_proof_node_at E u r Schema_Assertion {} (set Is) (set Ks)"
          using read by (clarsimp simp: proof_node_reading_exact proof_node_value_assertion; blast)
        obtain bs hs where tail: "h 3=proof_bound_term bs" "h 4=pair_list_term hs" "proof_bound_values E bs hs"
          using previous by (simp only: proof_bound_checking_result_at_source[OF source(1)]) blast
        have site: "term_formed (definition_site_value (u,r))"
          using native_proof_node_value_formed(1)[of E "(u,r)" Schema_Assertion "{}" "set Is" "set Ks" "Payload_Term []"] raw by simp
        have site_code: "Pair_Term (h 1) (h 2)=definition_site_value (u,r)" by (simp only: source(2,3) fst_conv snd_conv site_data_term_def)
        have fresh: "(u,r)\<notin>set (map fst bs)"
          using absence by (simp only: site_code tail(1) proof_bound_key_absence[OF site proof_bound_values_reads[OF tail(3)]]; blast)
        have extended: "proof_bound_values E (((u,r),Payload_Term [])#bs) (native_link_origins E (u,r) [] @ hs)"
          by (rule proof_bound_values_cons[OF fresh _ _ _ _ tail(3), where N=Schema_Assertion and D="{}"])
            (use raw in auto)
        have bound: "proof_bound_values E (((u,r),Payload_Term [])#bs) hs"
          using extended by (simp add: native_link_origins_def)
        have result: "?Q (proof_bound_argument (h 0) (proof_bound_term (((u,r),Payload_Term [])#bs)) (pair_list_term hs))"
          by (rule proof_bound_checking_resultI[OF source(1) bound])
        have evaluated: "evaluate_pattern h (schema_conclusion S)=
          proof_bound_argument (h 0)
            (Pair_Term (Pair_Term (Pair_Term (h 1) (h 2)) (Payload_Term [])) (h 3)) (h 4)"
          by (simp add: assertion proof_bound_assertion_schema_def)
        have conclusion_value: "evaluate_pattern h (schema_conclusion S)=
          proof_bound_argument (h 0) (proof_bound_term (((u,r),Payload_Term [])#bs)) (pair_list_term hs)"
          by (simp only: evaluated source(2,3) tail(1,2) list.map case_prod_conv data_list_term.simps
            id_apply site_data_term_def fst_conv snd_conv)
        show ?thesis by (simp only: conclusion_value) (rule result)
      next
        case inference
        have read: "(94,term_quotation_argument (h 0) (h 1) (h 2) (data_list_term [h 3,h 4,h 5]) (h 10) (h 11))
            \<in>positive_meaning proof_node_reading_system"
          and absence: "(20,Pair_Term (Pair_Term (h 1) (h 2)) (h 6))\<in>positive_meaning key_absence_system"
          and links: "(95,proof_links_argument (h 6) (Pair_Term (h 1) (h 2)) (h 5) (h 7))\<in>positive_meaning proof_link_checking_system"
          and previous: "?Q (proof_bound_argument (h 0) (h 6) (h 8))"
          and joined: "(46,collection_join_argument (h 7) (h 8) (h 9))\<in>positive_meaning data_append_system"
          using support by (auto simp: inference proof_bound_inference_schema_def proof_bound_checking_components)
        obtain E u r N D Is Ks where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          and presented: "proof_node_value_presents N D (data_list_term [h 3,h 4,h 5])"
          and raw: "native_proof_node_at E u r N D (set Is) (set Ks)"
          using read by (simp only: proof_node_reading_exact factor_term.inject) blast
        obtain c vs ds where fields: "h 3=definition_site_value c" "h 4=positioned_binding_rows_term vs" "h 5=discharge_rows_term ds"
          and order: "distinct vs" "distinct ds"
          using presented by (cases N) auto
        have node: "N=Schema_Inference c (fset_of_list vs)" "D=set ds"
          using presented by (simp only: fields proof_node_value_inference; blast)+
        obtain bs us where tail: "h 6=proof_bound_term bs" "h 8=pair_list_term us" "proof_bound_values E bs us"
          using previous by (simp only: proof_bound_checking_result_at_source[OF source(1)]) blast
        have rows: "native_value_rows E bs" by (rule proof_bound_values_reads[OF tail(3)])
        have keys: "distinct (map fst bs)" by (rule proof_bound_values_keys[OF tail(3)])
        have site: "term_formed (definition_site_value (u,r))"
          using native_proof_node_value_formed(1)[of E "(u,r)" N D "set Is" "set Ks" "data_list_term [h 3,h 4,h 5]"] raw presented by simp
        have site_code: "Pair_Term (h 1) (h 2)=definition_site_value (u,r)" by (simp only: source(2,3) fst_conv snd_conv site_data_term_def)
        have fresh: "(u,r)\<notin>set (map fst bs)"
          using absence by (simp only: site_code tail(1) proof_bound_key_absence[OF site rows]; blast)
        obtain os where os: "h 7=pair_list_term os"
          "proof_link_rows (proof_bound_term bs) (definition_site_value (u,r)) (encoded_discharge_rows ds) os"
          using links by (simp only: site_code fields tail(1) proof_link_checking_exact factor_term.inject pair_list_term_injective; blast)
        have sites: "\<forall>(s,n)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
          by (rule native_discharge_values_formed[OF raw]) (simp add: node(2))
        have checked: "rel_ran (set ds)\<subseteq>set (map fst bs)" "os=native_link_origins E (u,r) ds"
          using os(2) by (simp only: proof_link_rows_on_sites[OF rows keys sites]; blast)+
        have h9: "h 9=pair_list_term (os@us)"
          using joined by (simp only: os(1) tail(2) data_append_at_lists) (auto simp: data_list_term_injective)
        have extended: "proof_bound_values E (((u,r),data_list_term [h 3,h 4,h 5])#bs)
          (native_link_origins E (u,r) ds @ us)"
          by (rule proof_bound_values_cons[OF fresh presented _ _ _ tail(3)])
            (use raw fields node(2) checked(1) in auto)
        have bound: "proof_bound_values E (((u,r),data_list_term [h 3,h 4,h 5])#bs) (os@us)"
          using extended checked(2) by simp
        have result: "?Q (proof_bound_argument (h 0)
            (proof_bound_term (((u,r),data_list_term [h 3,h 4,h 5])#bs)) (pair_list_term (os@us)))"
          by (rule proof_bound_checking_resultI[OF source(1) bound])
        have evaluated: "evaluate_pattern h (schema_conclusion S)=
          proof_bound_argument (h 0)
            (Pair_Term (Pair_Term (Pair_Term (h 1) (h 2)) (data_list_term [h 3,h 4,h 5])) (h 6)) (h 9)"
          by (simp add: inference proof_bound_inference_schema_def)
        have conclusion_value: "evaluate_pattern h (schema_conclusion S)=
          proof_bound_argument (h 0) (proof_bound_term (((u,r),data_list_term [h 3,h 4,h 5])#bs)) (pair_list_term (os@us))"
          by (simp only: evaluated source(2,3) tail(1) h9 list.map case_prod_conv data_list_term.simps
            id_apply site_data_term_def fst_conv snd_conv)
        show ?thesis by (simp only: conclusion_value) (rule result)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem proof_bound_checking_complete:
  assumes source: "environment_value_presents E e" and bound: "proof_bound_values E bs hs"
  shows "(96,proof_bound_argument e (proof_bound_term bs) (pair_list_term hs))\<in>positive_meaning proof_bound_checking_system"
  using bound
proof (induction bs arbitrary: hs)
  case Nil
  have tf: "term_formed e" using environment_value_presents_formed[OF source] by blast
  show ?case using proof_bound_checking_empty[OF tf] Nil.prems by simp
next
  case (Cons row bs)
  obtain n t where row: "row=(n,t)" by (cases row)
  obtain N D I K ds us where fresh: "n\<notin>set (map fst bs)" and presented: "proof_node_value_presents N D t"
    and raw: "native_proof_node_at E (fst n) (snd n) N D I K" and projection: "proof_value_links t ds"
    and children: "rel_ran D\<subseteq>set (map fst bs)" and rest: "proof_bound_values E bs us"
    and result_shape: "hs=native_link_origins E n ds @ us"
    using Cons.prems by (simp only: row proof_bound_values.simps) blast
  have tail: "(96,proof_bound_argument e (proof_bound_term bs) (pair_list_term us))\<in>positive_meaning proof_bound_checking_system"
    by (rule Cons.IH[OF rest])
  have rows: "native_value_rows E bs" by (rule proof_bound_values_reads[OF rest])
  have keys: "distinct (map fst bs)" by (rule proof_bound_values_keys[OF rest])
  have site: "term_formed (definition_site_value n)" by (rule native_proof_node_value_formed(1)[OF raw presented])
  have absence: "(20,Pair_Term (definition_site_value n) (proof_bound_term bs))\<in>positive_meaning key_absence_system"
    by (simp only: proof_bound_key_absence[OF site rows]) (rule fresh)
  have tail_formed: "term_formed e" "term_formed (proof_bound_term bs)" "term_formed (pair_list_term us)"
    using schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  show ?case
  proof (cases N)
    case Schema_Assertion
    have empty: "t=Payload_Term []" "D={}" using presented Schema_Assertion by simp_all
    have ds: "ds=[]" by (rule proof_value_links_unique[OF projection]) (simp add: empty(1))
    have hs: "hs=us" using result_shape ds by (simp add: native_link_origins_def)
    have metadata: "I={snd n}" "K={}" using native_proof_node_assertion[of E "fst n" "snd n" D I K] raw Schema_Assertion by blast+
    have at: "native_proof_node_at E (fst n) (snd n) Schema_Assertion {} (set [snd n]) (set [])"
      using raw Schema_Assertion empty(2) metadata by simp
    have read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n)) (Payload_Term [])
        (data_list_term [Payload_Term (snd n)]) (Payload_Term []))\<in>positive_meaning proof_node_reading_system"
      using proof_node_reading_complete[OF source, of "[snd n]" "[]" "fst n" "snd n" Schema_Assertion "{}" "Payload_Term []"] at by auto
    have terms: "term_formed (use_data_term (fst n))" "term_formed (Payload_Term (snd n))"
      using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
    let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then use_data_term (fst n) else if i=2 then Payload_Term (snd n)
      else if i=3 then proof_bound_term bs else pair_list_term us"
    have result: "(96,evaluate_pattern ?h (schema_conclusion proof_bound_assertion_schema))\<in>positive_meaning proof_bound_checking_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use read absence tail tail_formed terms in \<open>auto simp: proof_bound_checking_clauses_def proof_bound_assertion_schema_def
          schema_variables_def proof_bound_checking_call proof_bound_checking_components site_data_term_def octets_formed_def\<close>)
    show ?thesis using result by (simp add: proof_bound_assertion_schema_def row empty(1) hs site_data_term_def)
  next
    case (Schema_Inference c V)
    obtain vs es where fields: "t=data_list_term [definition_site_value c,positioned_binding_rows_term vs,discharge_rows_term es]"
      "distinct vs" "distinct es" "set vs=fset V" "set es=D"
      using presented Schema_Inference by auto
    have ds: "ds=es" by (rule proof_value_links_unique[OF projection]) (use fields(1) in blast)
    have sites: "\<forall>(s,m)\<in>set es. term_formed (definition_site_value s) \<and> term_formed (definition_site_value m)"
      by (rule native_discharge_values_formed[OF raw]) (simp add: fields(5))
    let ?os="native_link_origins E n es"
    have trace: "proof_link_rows (proof_bound_term bs) (definition_site_value n) (encoded_discharge_rows es) ?os"
      by (simp only: proof_link_rows_on_sites[OF rows keys sites]) (use children fields(5) in simp)
    have links: "(95,proof_links_argument (proof_bound_term bs) (definition_site_value n) (discharge_rows_term es) (pair_list_term ?os))
      \<in>positive_meaning proof_link_checking_system"
      by (simp only: proof_link_checking_lists) (use trace site tail_formed(2) in auto)
    have first_data: "data_elements (map (\<lambda>(n,q). Pair_Term n q) ?os)"
      by (rule proof_link_rows_formed(2)[OF trace site]) simp
    have tail_data: "data_elements (map (\<lambda>(n,q). Pair_Term n q) us)"
      by (rule proof_bound_values_formed(2)[OF rest])
    have joined: "(46,collection_join_argument (pair_list_term ?os) (pair_list_term us) (pair_list_term (?os@us)))
      \<in>positive_meaning data_append_system"
      using first_data tail_data by (simp add: data_append_lists)
    obtain i k where read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n)) t i k)
      \<in>positive_meaning proof_node_reading_system"
      using proof_node_reading_value[OF source raw presented] by blast
    have read_formed: "term_formed (use_data_term (fst n))" "term_formed (Payload_Term (snd n))"
      "term_formed (definition_site_value c)" "term_formed (positioned_binding_rows_term vs)" "term_formed (discharge_rows_term es)"
      "term_formed i" "term_formed k"
      using schema_call_formed_target[OF positive_meaning_formed[OF read]] by (auto simp: fields(1))
    have origin_formed: "term_formed (pair_list_term ?os)" "term_formed (pair_list_term (?os@us))"
      using schema_call_formed_target[OF positive_meaning_formed[OF joined]] by auto
    let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term (fst n) else if j=2 then Payload_Term (snd n)
      else if j=3 then definition_site_value c else if j=4 then positioned_binding_rows_term vs else if j=5 then discharge_rows_term es
      else if j=6 then proof_bound_term bs else if j=7 then pair_list_term ?os else if j=8 then pair_list_term us
      else if j=9 then pair_list_term (?os@us) else if j=10 then i else k"
    have result: "(96,evaluate_pattern ?h (schema_conclusion proof_bound_inference_schema))\<in>positive_meaning proof_bound_checking_system"
      by (rule ordinary_positive_valuation_step[where c=2])
        (use read absence links tail joined tail_formed read_formed origin_formed in
          \<open>auto simp: proof_bound_checking_clauses_def proof_bound_inference_schema_def schema_variables_def
            proof_bound_checking_call proof_bound_checking_components fields(1) site_data_term_def octets_formed_def\<close>)
    show ?thesis using result by (simp add: proof_bound_inference_schema_def row fields(1) result_shape ds site_data_term_def)
  qed
qed

theorem proof_bound_checking_exact:
  "(96,z)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow> proof_bound_checking_result z"
  using proof_bound_checking_sound proof_bound_checking_complete proof_bound_checking_empty by blast

corollary proof_bound_checking_at_source:
  assumes source: "environment_value_presents E e"
  shows "(96,proof_bound_argument e b h)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow>
    (\<exists>bs hs. b=proof_bound_term bs \<and> h=pair_list_term hs \<and> proof_bound_values E bs hs)"
  by (simp only: proof_bound_checking_exact proof_bound_checking_result_at_source[OF source])

corollary proof_bound_checking_on_values:
  assumes source: "environment_value_presents E e"
  shows "(96,proof_bound_argument e (proof_bound_term bs) (pair_list_term hs))\<in>positive_meaning proof_bound_checking_system
    \<longleftrightarrow> proof_bound_values E bs hs"
  by (simp only: proof_bound_checking_at_source[OF source] positioned_binding_rows_term_injective;
      simp only: pair_list_term_injective; blast)

corollary proof_bound_checking_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(96,proof_bound_argument e b h)\<in>positive_meaning proof_bound_checking_system \<longleftrightarrow>
    (96,proof_bound_argument f b h)\<in>positive_meaning proof_bound_checking_system"
  by (simp only: proof_bound_checking_at_source[OF assms(1)] proof_bound_checking_at_source[OF assms(2)])

corollary proof_bound_checking_empty_exact:
  "(96,proof_bound_argument e (Payload_Term []) h)\<in>positive_meaning proof_bound_checking_system
    \<longleftrightarrow> term_formed e \<and> h=Payload_Term []"
proof -
  have empty_bound: "Payload_Term []=proof_bound_term bs \<longleftrightarrow> bs=[]" for bs
    by (cases bs) auto
  show ?thesis by (simp only: proof_bound_checking_exact factor_term.inject empty_bound; auto)
qed

text \<open>
  Every nonempty bound reads actual complete node metadata from the same
  environment presentation. Keys are unique, and every premise points into
  the strict tail. The assertion-origin list is combined through ordinary
  data append; bound values themselves are never subjected to data-only
  comparison or append. Node syntax may be shared across distinct nodes as
  permitted by the raw grammar. The standalone empty bound accepts any
  formed context and returns the empty origin list. Root admission below
  supplies actual membership and the assertion-use restriction.
\<close>

end
