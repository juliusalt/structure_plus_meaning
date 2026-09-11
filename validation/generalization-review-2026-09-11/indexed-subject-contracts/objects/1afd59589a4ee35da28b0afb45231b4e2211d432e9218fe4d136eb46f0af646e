theory Factor_Proof_Claim_Checking
  imports Factor_Proof_Claim_Instances
begin

section \<open>The claim table is checked once and shared by the complete traversal\<close>

abbreviation proof_claim_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "proof_claim_argument e u r v a j xs hs \<equiv>
    package_subject_argument e u r (Pair_Term (Pair_Term v a) (Pair_Term j (Pair_Term xs hs)))"

abbreviation proof_claim_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "proof_claim_pattern e u r v a j xs hs \<equiv>
    package_subject_pattern e u r (Pattern_Pair (Pattern_Pair v a) (Pattern_Pair j (Pattern_Pair xs hs)))"

abbreviation proof_claim_checking_result :: "factor_term \<Rightarrow> bool" where
  "proof_claim_checking_result z \<equiv>
    (\<exists>e u r v a js. z=proof_claim_argument e u r v a (pair_list_term js) (Payload_Term []) (Payload_Term []) \<and>
      term_formed e \<and> term_formed u \<and> term_formed r \<and> term_formed v \<and> term_formed a \<and>
      formed_key_rows js \<and> distinct (map fst js)) \<or>
    (\<exists>E e pu pr ru rr P G js xs hs.
      z=proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
        (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs) \<and>
      environment_value_presents E e \<and> native_package_at E pu pr P \<and> native_schema_graph_at E (ru,rr) G \<and>
      formed_key_rows js \<and> distinct (map fst js) \<and> proof_claim_values (positioned_program P) G js xs hs)"

lemma proof_claim_checking_resultI:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E (ru,rr) G" and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    and checked: "proof_claim_values (positioned_program P) G js xs hs"
  shows "proof_claim_checking_result (proof_claim_argument e (use_data_term pu) (Payload_Term pr)
    (use_data_term ru) (Payload_Term rr) (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs))"
  by (rule disjI2, rule exI[of _ E], rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr],
      rule exI[of _ ru], rule exI[of _ rr], rule exI[of _ P], rule exI[of _ G],
      rule exI[of _ js], rule exI[of _ xs], rule exI[of _ hs])
    (use assms in simp)

lemma proof_claim_checking_resultE:
  assumes result: "proof_claim_checking_result (proof_claim_argument e u r v a j x h)"
    and nonempty: "x\<noteq>Payload_Term []"
  obtains E pu pr ru rr P G js xs hs where "environment_value_presents E e"
    "u=use_data_term pu" "r=Payload_Term pr" "v=use_data_term ru" "a=Payload_Term rr"
    "j=pair_list_term js" "x=positioned_call_rows_term xs" "h=positioned_call_rows_term hs"
    "native_package_at E pu pr P" "native_schema_graph_at E (ru,rr) G"
    "formed_key_rows js" "distinct (map fst js)" "proof_claim_values (positioned_program P) G js xs hs"
  using result
proof (elim disjE exE conjE)
  fix e0 u0 r0 v0 a0 js
  assume shape: "proof_claim_argument e u r v a j x h=
      proof_claim_argument e0 u0 r0 v0 a0 (pair_list_term js) (Payload_Term []) (Payload_Term [])"
    and context_formed: "term_formed e0" "term_formed u0" "term_formed r0" "term_formed v0" "term_formed a0"
    and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
  have "x=Payload_Term []" using shape by (simp only: factor_term.inject; blast)
  then show thesis using nonempty by contradiction
next
  fix F e0 pu pr ru rr P G js xs hs
  assume shape: "proof_claim_argument e u r v a j x h=
      proof_claim_argument e0 (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
        (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs)"
    and source: "environment_value_presents F e0" and package: "native_package_at F pu pr P"
    and graph: "native_schema_graph_at F (ru,rr) G" and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    and checked: "proof_claim_values (positioned_program P) G js xs hs"
  have fields: "e0=e" "u=use_data_term pu" "r=Payload_Term pr" "v=use_data_term ru" "a=Payload_Term rr"
    "j=pair_list_term js" "x=positioned_call_rows_term xs" "h=positioned_call_rows_term hs"
    using shape by (simp only: factor_term.inject; blast)+
  have actual_source: "environment_value_presents F e" using source by (simp only: fields(1))
  show thesis by (rule that[OF actual_source fields(2-8) package graph rows keys checked])
qed

lemma proof_claim_checking_result_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E (ru,rr) G"
  shows "proof_claim_checking_result (proof_claim_argument e (use_data_term pu) (Payload_Term pr)
      (use_data_term ru) (Payload_Term rr) j x h) \<longleftrightarrow>
    (\<exists>js xs hs. j=pair_list_term js \<and> x=positioned_call_rows_term xs \<and> h=positioned_call_rows_term hs \<and>
      formed_key_rows js \<and> distinct (map fst js) \<and> proof_claim_values (positioned_program P) G js xs hs)"
proof
  let ?arg="proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr) j x h"
  assume result: "proof_claim_checking_result ?arg"
  then show "\<exists>js xs hs. j=pair_list_term js \<and> x=positioned_call_rows_term xs \<and> h=positioned_call_rows_term hs \<and>
      formed_key_rows js \<and> distinct (map fst js) \<and> proof_claim_values (positioned_program P) G js xs hs"
  proof (elim disjE exE conjE)
    fix e0 u0 r0 v0 a0 js
    assume shape: "?arg=proof_claim_argument e0 u0 r0 v0 a0 (pair_list_term js) (Payload_Term []) (Payload_Term [])"
      and context_formed: "term_formed e0" "term_formed u0" "term_formed r0" "term_formed v0" "term_formed a0"
      and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    have fields: "j=pair_list_term js" "x=Payload_Term []" "h=Payload_Term []"
      using shape by (simp only: factor_term.inject; blast)+
    show ?thesis by (rule exI[of _ js], rule exI[of _ "[]"], rule exI[of _ "[]"])
      (use fields rows keys in simp)
  next
    fix F e0 pu0 pr0 ru0 rr0 Q X js xs hs
    assume shape: "?arg=proof_claim_argument e0 (use_data_term pu0) (Payload_Term pr0) (use_data_term ru0) (Payload_Term rr0)
        (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs)"
      and other_source: "environment_value_presents F e0" and other_package: "native_package_at F pu0 pr0 Q"
      and other_graph: "native_schema_graph_at F (ru0,rr0) X" and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
      and checked: "proof_claim_values (positioned_program Q) X js xs hs"
    have fields: "e0=e" "pu0=pu" "pr0=pr" "ru0=ru" "rr0=rr"
      "j=pair_list_term js" "x=positioned_call_rows_term xs" "h=positioned_call_rows_term hs"
      using shape by (simp only: factor_term.inject inj_eq[OF use_data_term_injective]; blast)+
    have actual_source: "environment_value_presents F e" using other_source by (simp only: fields(1))
    have environments: "F=E" by (rule environment_value_presents_unique[OF actual_source source])
    have actual_package: "native_package_at E pu pr Q" using other_package by (simp only: environments fields(2,3))
    have actual_graph: "native_schema_graph_at E (ru,rr) X" using other_graph by (simp only: environments fields(4,5))
    have programs: "Q=P" by (rule native_package_unique[OF actual_package package])
    have graphs: "X=G" by (rule native_schema_graph_unique[OF actual_graph graph])
    show ?thesis by (rule exI[of _ js], rule exI[of _ xs], rule exI[of _ hs])
      (use fields rows keys checked programs graphs in simp)
  qed
next
  assume result: "\<exists>js xs hs. j=pair_list_term js \<and> x=positioned_call_rows_term xs \<and> h=positioned_call_rows_term hs \<and>
    formed_key_rows js \<and> distinct (map fst js) \<and> proof_claim_values (positioned_program P) G js xs hs"
  then obtain js xs hs where fields: "j=pair_list_term js" "x=positioned_call_rows_term xs" "h=positioned_call_rows_term hs"
    and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    and checked: "proof_claim_values (positioned_program P) G js xs hs"
    by (elim exE conjE) (rule that; assumption)
  show "proof_claim_checking_result (proof_claim_argument e (use_data_term pu) (Payload_Term pr)
      (use_data_term ru) (Payload_Term rr) j x h)"
    using proof_claim_checking_resultI[OF source package graph rows keys checked] by (simp only: fields)
qed

definition proof_claim_nil_schema :: "(nat,nat,nat) factor_schema" where
  "proof_claim_nil_schema=data_rule
    (proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
      (Pattern_Payload []) (Pattern_Payload [])) {(0,21,Pattern_Variable 5)}"

definition proof_claim_assertion_schema :: "(nat,nat,nat) factor_schema" where
  "proof_claim_assertion_schema=data_rule
    (proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
      (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)) (Pattern_Variable 10))) (Pattern_Variable 11))
      (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)) (Pattern_Variable 10))) (Pattern_Variable 12)))
    {(0,98,proof_graph_subject_pattern data_x data_w (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))),
     (1,94,term_quotation_pattern data_x (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Payload [])
       (data_list_pattern [Pattern_Variable 7]) (Pattern_Payload [])),
     (2,84,package_subject_pattern data_x data_y data_z
       (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)) (Pattern_Variable 10))),
     (3,101,proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
       (Pattern_Variable 11) (Pattern_Variable 12))}"

definition proof_claim_inference_schema :: "(nat,nat,nat) factor_schema" where
  "proof_claim_inference_schema=data_rule
    (proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
      (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)) (Pattern_Variable 10))) (Pattern_Variable 11))
      (Pattern_Variable 12))
    {(0,98,proof_graph_subject_pattern data_x data_w (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))),
     (1,94,term_quotation_pattern data_x (Pattern_Variable 6) (Pattern_Variable 7)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 13),Pattern_Variable 15,Pattern_Variable 16])
       (Pattern_Variable 19) (Pattern_Variable 20)),
     (2,99,row_qualification_pattern (Pattern_Variable 8) (Pattern_Variable 14) (Pattern_Variable 15)),
     (3,100,keyed_row_join_pattern (Pattern_Variable 5) (Pattern_Variable 16) (Pattern_Variable 17)),
     (4,99,row_qualification_pattern (Pattern_Variable 8) (Pattern_Variable 18) (Pattern_Variable 17)),
     (5,87,admitted_instantiation_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))
       (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 10) (Pattern_Variable 18)),
     (6,101,proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
       (Pattern_Variable 11) (Pattern_Variable 12))}"

definition proof_claim_checking_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "proof_claim_checking_clauses={(0,proof_claim_nil_schema),(1,proof_claim_assertion_schema),(2,proof_claim_inference_schema)}"

definition proof_claim_checking_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_claim_checking_system=add_view_definition keyed_row_join_system 101 data_x proof_claim_checking_clauses"

lemma proof_claim_checking_system_formed [simp]: "schema_system_formed proof_claim_checking_system"
  unfolding proof_claim_checking_system_def
  by (rule add_recursive_definition_formed[OF keyed_row_join_system_formed])
    (auto simp: proof_claim_checking_clauses_def proof_claim_nil_schema_def proof_claim_assertion_schema_def proof_claim_inference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_claim_checking_definitions [simp]:
  "system_definitions proof_claim_checking_system=insert 101 (system_definitions keyed_row_join_system)"
  by (simp add: proof_claim_checking_system_def)

lemma proof_claim_checking_call:
  "schema_call_formed proof_claim_checking_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_claim_checking_system \<and> term_formed t"
  using added_variable_calls[OF keyed_row_join_system_formed
    proof_claim_checking_system_formed[unfolded proof_claim_checking_system_def] keyed_row_join_call]
  by (simp only: proof_claim_checking_system_def[symmetric])

lemma proof_claim_checking_old_meaning:
  assumes "d\<in>system_definitions keyed_row_join_system"
  shows "(d,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning keyed_row_join_system"
  using added_definition_preserves_old(2)[OF keyed_row_join_system_formed
    proof_claim_checking_system_formed[unfolded proof_claim_checking_system_def], of d t] assms
  by (auto simp: proof_claim_checking_system_def)

lemma proof_claim_checking_clause [simp]:
  "((101,c),S)\<in>system_clauses proof_claim_checking_system \<longleftrightarrow> (c,S)\<in>proof_claim_checking_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses keyed_row_join_system \<Longrightarrow> d\<in>system_definitions keyed_row_join_system" for d c S
    using keyed_row_join_system_formed unfolding schema_system_formed_def by blast
  have absent: "((101,c),S)\<notin>system_clauses keyed_row_join_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_claim_checking_system_def)
qed

lemma proof_claim_checking_graph_meaning:
  assumes "d\<in>system_definitions proof_graph_membership_system"
  shows "(d,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_membership_system"
  using proof_claim_checking_old_meaning[of d t] keyed_row_join_graph_meaning[OF assms, of t] assms by auto

lemma proof_claim_checking_components:
  "(21,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(98,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (98,t)\<in>positive_meaning proof_graph_membership_system"
  "(94,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (94,t)\<in>positive_meaning proof_node_reading_system"
  "(84,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (84,t)\<in>positive_meaning program_call_admission_system"
  "(99,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (99,t)\<in>positive_meaning row_qualification_system"
  "(100,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (100,t)\<in>positive_meaning keyed_row_join_system"
  "(87,t)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> (87,t)\<in>positive_meaning admitted_instantiation_system"
  using proof_claim_checking_graph_meaning[of 21 t] proof_graph_membership_old_meaning[of 21 t]
    proof_graph_admission_components(3)[of t] proof_claim_checking_graph_meaning[of 98 t]
    proof_claim_checking_graph_meaning[of 94 t] proof_graph_membership_node_meaning[of 94 t]
    proof_claim_checking_graph_meaning[of 84 t] proof_graph_membership_node_meaning[of 84 t]
    proof_node_reading_base_meaning[of 84 t] admitted_instantiation_components(1)[of t]
    proof_claim_checking_old_meaning[of 99 t] keyed_row_join_old_meaning[of 99 t]
    proof_claim_checking_old_meaning[of 100 t]
    proof_claim_checking_graph_meaning[of 87 t] proof_graph_membership_node_meaning[of 87 t]
    proof_node_reading_base_meaning[of 87 t] by auto

lemma proof_claim_checking_empty:
  assumes formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a"
    and table: "(21,j)\<in>positive_meaning keyed_list_system"
  shows "(101,proof_claim_argument e u r v a j (Payload_Term []) (Payload_Term []))\<in>positive_meaning proof_claim_checking_system"
proof -
  have jf: "term_formed j" using schema_call_formed_target[OF positive_meaning_formed[OF table]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else if i=4 then a else j"
  have result: "(101,evaluate_pattern ?h (schema_conclusion proof_claim_nil_schema))\<in>positive_meaning proof_claim_checking_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use assms jf in \<open>auto simp: proof_claim_checking_clauses_def proof_claim_nil_schema_def
        schema_variables_def proof_claim_checking_call proof_claim_checking_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: proof_claim_nil_schema_def)
qed

lemma proof_claim_checking_assertion_step:
  assumes member: "(98,proof_graph_subject_argument e v a (Pair_Term nu nr))\<in>positive_meaning proof_graph_membership_system"
    and read: "(94,term_quotation_argument e nu nr (Payload_Term []) (data_list_term [nr]) (Payload_Term []))
      \<in>positive_meaning proof_node_reading_system"
    and call: "(84,package_subject_argument e u r (Pair_Term (Pair_Term du dr) t))\<in>positive_meaning program_call_admission_system"
    and tail: "(101,proof_claim_argument e u r v a j xs hs)\<in>positive_meaning proof_claim_checking_system"
  shows "(101,proof_claim_argument e u r v a j
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs)
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) hs))\<in>positive_meaning proof_claim_checking_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a" "term_formed j"
    "term_formed nu" "term_formed nr" "term_formed du" "term_formed dr" "term_formed t" "term_formed xs" "term_formed hs"
    using schema_call_formed_target[OF positive_meaning_formed[OF member]]
      schema_call_formed_target[OF positive_meaning_formed[OF call]]
      schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else if i=4 then a
    else if i=5 then j else if i=6 then nu else if i=7 then nr else if i=8 then du else if i=9 then dr else if i=10 then t
    else if i=11 then xs else hs"
  have result: "(101,evaluate_pattern ?h (schema_conclusion proof_claim_assertion_schema))\<in>positive_meaning proof_claim_checking_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use assms formed in \<open>auto simp: proof_claim_checking_clauses_def proof_claim_assertion_schema_def
        schema_variables_def proof_claim_checking_call proof_claim_checking_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: proof_claim_assertion_schema_def)
qed

lemma proof_claim_checking_inference_step:
  assumes member: "(98,proof_graph_subject_argument e v a (Pair_Term nu nr))\<in>positive_meaning proof_graph_membership_system"
    and read: "(94,term_quotation_argument e nu nr (data_list_term [Pair_Term du c,vs,ds]) i k)\<in>positive_meaning proof_node_reading_system"
    and bindings: "(99,row_qualification_argument du bs vs)\<in>positive_meaning row_qualification_system"
    and join: "(100,keyed_row_join_argument j ds ps)\<in>positive_meaning keyed_row_join_system"
    and qualified_calls: "(99,row_qualification_argument du qs ps)\<in>positive_meaning row_qualification_system"
    and admitted: "(87,admitted_instantiation_argument e u r (Pair_Term du dr) c bs t qs)\<in>positive_meaning admitted_instantiation_system"
    and tail: "(101,proof_claim_argument e u r v a j xs hs)\<in>positive_meaning proof_claim_checking_system"
  shows "(101,proof_claim_argument e u r v a j
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs) hs)\<in>positive_meaning proof_claim_checking_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a" "term_formed j"
    "term_formed nu" "term_formed nr" "term_formed du" "term_formed dr" "term_formed t" "term_formed xs" "term_formed hs"
    "term_formed c" "term_formed bs" "term_formed vs" "term_formed ds" "term_formed ps" "term_formed qs" "term_formed i" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF member]]
      schema_call_formed_target[OF positive_meaning_formed[OF read]]
      schema_call_formed_target[OF positive_meaning_formed[OF admitted]]
      schema_call_formed_target[OF positive_meaning_formed[OF join]]
      schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?h="\<lambda>x::nat. if x=0 then e else if x=1 then u else if x=2 then r else if x=3 then v else if x=4 then a
    else if x=5 then j else if x=6 then nu else if x=7 then nr else if x=8 then du else if x=9 then dr else if x=10 then t
    else if x=11 then xs else if x=12 then hs else if x=13 then c else if x=14 then bs else if x=15 then vs
    else if x=16 then ds else if x=17 then ps else if x=18 then qs else if x=19 then i else k"
  have result: "(101,evaluate_pattern ?h (schema_conclusion proof_claim_inference_schema))\<in>positive_meaning proof_claim_checking_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use assms formed in \<open>auto simp: proof_claim_checking_clauses_def proof_claim_inference_schema_def
        schema_variables_def proof_claim_checking_call proof_claim_checking_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: proof_claim_inference_schema_def)
qed

lemma proof_claim_assertion_result_step:
  assumes member: "(98,proof_graph_subject_argument e v a (Pair_Term nu nr))\<in>positive_meaning proof_graph_membership_system"
    and read: "(94,term_quotation_argument e nu nr (Payload_Term []) (data_list_term [nr]) (Payload_Term []))
      \<in>positive_meaning proof_node_reading_system"
    and call: "(84,package_subject_argument e u r (Pair_Term (Pair_Term du dr) t))\<in>positive_meaning program_call_admission_system"
    and tail: "proof_claim_checking_result (proof_claim_argument e u r v a j xs hs)"
  shows "proof_claim_checking_result (proof_claim_argument e u r v a j
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs)
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) hs))"
proof -
  obtain E ru rr n G where source: "environment_value_presents E e" and header_fields: "v=use_data_term ru" "a=Payload_Term rr"
    and nvalue: "Pair_Term nu nr=definition_site_value n"
    and graph: "native_schema_graph_at E (ru,rr) G" and inside: "n\<in>schema_graph_nodes G"
    using member by (simp only: proof_graph_membership_exact factor_term.inject; blast)
  obtain pu pr d P where program: "u=use_data_term pu" "r=Payload_Term pr"
    "Pair_Term du dr=definition_site_value d" and package: "native_package_at E pu pr P" and formed: "schema_call_formed P d t"
    using call by (simp only: program_call_admission_at_source[OF source]; blast)
  have coordinates: "nu=use_data_term (fst n)" "nr=Payload_Term (snd n)"
    using nvalue by (simp_all add: site_data_term_def)
  obtain I K where raw: "native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K"
    using read by (simp only: coordinates proof_node_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
      factor_term.inject proof_node_value_assertion; blast)
  have node: "(n,Schema_Assertion)\<in>fset (graph_inferences G)" and empty: "schema_graph_premises G n={}"
    using native_graph_read_node[OF graph inside raw] by auto
  obtain js ys zs where rest: "j=pair_list_term js" "xs=positioned_call_rows_term ys" "hs=positioned_call_rows_term zs"
    "formed_key_rows js" "distinct (map fst js)" "proof_claim_values (positioned_program P) G js ys zs"
    using tail by (simp only: header_fields program(1,2) proof_claim_checking_result_at_reads[OF source package graph]; blast)
  have at: "proof_claim_at (positioned_program P) G js n d t"
    using node empty formed positioned_program_calls[OF native_package_system_formed[OF package], of d t]
    by (auto simp: proof_claim_at_def)
  have checked: "proof_claim_values (positioned_program P) G js ((n,d,t)#ys) ((n,d,t)#zs)"
    by (simp only: proof_claim_values_cons) (use at node rest(6) in auto)
  have result: "proof_claim_checking_result (proof_claim_argument e (use_data_term pu) (Payload_Term pr)
      (use_data_term ru) (Payload_Term rr) (pair_list_term js)
      (positioned_call_rows_term ((n,d,t)#ys)) (positioned_call_rows_term ((n,d,t)#zs)))"
    by (rule proof_claim_checking_resultI[OF source package graph rest(4,5) checked])
  have argument: "proof_claim_argument e u r v a j
      (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs)
      (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) hs)=
    proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
      (pair_list_term js) (positioned_call_rows_term ((n,d,t)#ys)) (positioned_call_rows_term ((n,d,t)#zs))"
    by (simp only: header_fields program rest(1-3) nvalue positioned_call_rows_cons
      list.map case_prod_conv data_list_term.simps call_instance_value_def)
  show ?thesis by (simp only: argument; rule result)
qed

lemma proof_claim_inference_result_step:
  assumes member: "(98,proof_graph_subject_argument e v a (Pair_Term nu nr))\<in>positive_meaning proof_graph_membership_system"
    and read: "(94,term_quotation_argument e nu nr (data_list_term [Pair_Term du c,vs,ds]) i k)\<in>positive_meaning proof_node_reading_system"
    and bindings: "(99,row_qualification_argument du bs vs)\<in>positive_meaning row_qualification_system"
    and join: "(100,keyed_row_join_argument j ds ps)\<in>positive_meaning keyed_row_join_system"
    and qualified_calls: "(99,row_qualification_argument du qs ps)\<in>positive_meaning row_qualification_system"
    and admitted: "(87,admitted_instantiation_argument e u r (Pair_Term du dr) c bs t qs)\<in>positive_meaning admitted_instantiation_system"
    and tail: "proof_claim_checking_result (proof_claim_argument e u r v a j xs hs)"
  shows "proof_claim_checking_result (proof_claim_argument e u r v a j
    (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs) hs)"
proof -
  obtain E ru rr n G where source: "environment_value_presents E e" and header_fields: "v=use_data_term ru" "a=Payload_Term rr"
    and nvalue: "Pair_Term nu nr=definition_site_value n"
    and graph: "native_schema_graph_at E (ru,rr) G" and inside: "n\<in>schema_graph_nodes G"
    using member by (simp only: proof_graph_membership_exact factor_term.inject; blast)
  obtain pu pr d c0 bs0 qs0 P where program: "u=use_data_term pu" "r=Payload_Term pr"
    "Pair_Term du dr=definition_site_value d" "c=Payload_Term c0" "bs=binding_rows_term bs0" "qs=call_instance_rows_term qs0"
    and package: "native_package_at E pu pr P" and inst: "admitted_schema_instance P d c0 (set bs0) t (set qs0)"
    using admitted by (simp only: admitted_instantiation_at_source[OF source]; blast)
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have gf: "schema_graph_formed G (ru,rr)" using graph by (simp add: native_schema_graph_at_def)
  have coordinates: "nu=use_data_term (fst n)" "nr=Payload_Term (snd n)" "du=use_data_term (fst d)"
    using nvalue program(3) by (simp_all add: site_data_term_def)
  let ?vs="map (\<lambda>(a,t). ((fst d,a),t)) bs0"
  let ?ps="map (\<lambda>(s,q). ((fst d,s),q)) qs0"
  have binding_value: "vs=positioned_binding_rows_term ?vs"
    using bindings by (simp only: coordinates(3) program(5) row_qualification_lists qualify_binding_rows; blast)
  have premise_value: "ps=positioned_call_rows_term ?ps"
    using qualified_calls by (simp only: coordinates(3) program(6) local_call_rows_encoding row_qualification_lists qualify_call_rows; blast)
  have clause_value: "Pair_Term du c=definition_site_value (fst d,c0)"
    by (simp add: coordinates(3) program(4) site_data_term_def)
  have reading: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n))
      (data_list_term [definition_site_value (fst d,c0),positioned_binding_rows_term ?vs,ds]) i k)
      \<in>positive_meaning proof_node_reading_system"
    using read by (simp only: coordinates(1,2) clause_value binding_value)
  obtain ds0 I K where discharge_value: "ds=discharge_rows_term ds0"
    and raw: "native_proof_node_at E (fst n) (snd n) (Schema_Inference (fst d,c0) (fset_of_list ?vs)) (set ds0) I K"
    by (rule proof_node_inference_fields[OF source reading]) (rule that; assumption)
  have node: "(n,Schema_Inference (fst d,c0) (fset_of_list ?vs))\<in>fset (graph_inferences G)"
    and actual_premises: "set ds0=schema_graph_premises G n"
    using native_graph_read_node[OF graph inside raw] by blast+
  obtain js ys zs where rest: "j=pair_list_term js" "xs=positioned_call_rows_term ys" "hs=positioned_call_rows_term zs"
    "formed_key_rows js" "distinct (map fst js)" "proof_claim_values (positioned_program P) G js ys zs"
    using tail by (simp only: header_fields program(1,2) proof_claim_checking_result_at_reads[OF source package graph]; blast)
  have joined: "keyed_row_join (pair_list_term js) (encoded_discharge_rows ds0) (encoded_positioned_calls ?ps)"
    using join by (simp only: rest(1) discharge_value premise_value keyed_row_join_lists; blast)
  have binding_set: "fset (fset_of_list ?vs)=rename_term_bindings (Pair (fst d)) (set bs0)"
    by (simp only: fset_of_list.rep_eq set_map rename_term_bindings_def)
  have premise_set: "set ?ps=map_socket_graph (Pair (fst d)) id id (set qs0)"
    by (auto simp: map_socket_graph_def map_prod_def)
  have positioned: "admitted_schema_instance (positioned_program P) d (fst d,c0) (fset (fset_of_list ?vs)) t (set ?ps)"
    using positioned_admitted_instanceI[OF pf inst] by (simp only: binding_set premise_set)
  have at: "proof_claim_at (positioned_program P) G js n d t"
    by (rule positioned_join_claim[OF node positioned actual_premises joined])
  have not_assertion: "(n,Schema_Assertion)\<notin>fset (graph_inferences G)"
    by (rule schema_graph_inference_not_assertion[OF gf node])
  have checked: "proof_claim_values (positioned_program P) G js ((n,d,t)#ys) zs"
    by (simp only: proof_claim_values_cons) (use at not_assertion rest(6) in auto)
  have result: "proof_claim_checking_result (proof_claim_argument e (use_data_term pu) (Payload_Term pr)
      (use_data_term ru) (Payload_Term rr) (pair_list_term js)
      (positioned_call_rows_term ((n,d,t)#ys)) (positioned_call_rows_term zs))"
    by (rule proof_claim_checking_resultI[OF source package graph rest(4,5) checked])
  have argument: "proof_claim_argument e u r v a j
      (Pair_Term (Pair_Term (Pair_Term nu nr) (Pair_Term (Pair_Term du dr) t)) xs) hs=
    proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
      (pair_list_term js) (positioned_call_rows_term ((n,d,t)#ys)) (positioned_call_rows_term zs)"
    by (simp only: header_fields program rest(1-3) nvalue positioned_call_rows_cons
      list.map case_prod_conv data_list_term.simps call_instance_value_def)
  show ?thesis by (simp only: argument; rule result)
qed

theorem proof_claim_checking_sound:
  assumes holds: "(101,z)\<in>positive_meaning proof_claim_checking_system"
  shows "proof_claim_checking_result z"
proof -
  let ?Q="\<lambda>z. proof_claim_checking_result z"
  have invariant: "(101::nat)=101 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=101 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses proof_claim_checking_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed proof_claim_checking_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning proof_claim_checking_system \<and>
        (e=101 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=101 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=101"
      then consider (nil) "S=proof_claim_nil_schema" | (assertion) "S=proof_claim_assertion_schema"
        | (inference) "S=proof_claim_inference_schema"
        using clause by (auto simp: proof_claim_checking_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        obtain js where table: "h 5=pair_list_term js" "formed_key_rows js" "distinct (map fst js)"
          using support by (auto simp: nil proof_claim_nil_schema_def proof_claim_checking_components keyed_list_exact)
        have formed: "term_formed (h 0)" "term_formed (h 1)" "term_formed (h 2)" "term_formed (h 3)" "term_formed (h 4)"
          using assignment by (auto simp: nil proof_claim_nil_schema_def schema_variables_def)
        show ?thesis by (rule disjI1, rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
            rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ js])
          (use table formed in \<open>simp add: nil proof_claim_nil_schema_def\<close>)
      next
        case assertion
        have result: "?Q (proof_claim_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)
          (Pair_Term (Pair_Term (Pair_Term (h 6) (h 7)) (Pair_Term (Pair_Term (h 8) (h 9)) (h 10))) (h 11))
          (Pair_Term (Pair_Term (Pair_Term (h 6) (h 7)) (Pair_Term (Pair_Term (h 8) (h 9)) (h 10))) (h 12)))"
          by (rule proof_claim_assertion_result_step)
            (use support in \<open>auto simp: assertion proof_claim_assertion_schema_def proof_claim_checking_components\<close>)
        show ?thesis using result by (simp add: assertion proof_claim_assertion_schema_def)
      next
        case inference
        have result: "?Q (proof_claim_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)
          (Pair_Term (Pair_Term (Pair_Term (h 6) (h 7)) (Pair_Term (Pair_Term (h 8) (h 9)) (h 10))) (h 11)) (h 12))"
          by (rule proof_claim_inference_result_step[where c="h 13" and vs="h 15" and ds="h 16" and i="h 19" and k="h 20"
            and bs="h 14" and ps="h 17" and qs="h 18"])
            (use support in \<open>auto simp: inference proof_claim_inference_schema_def proof_claim_checking_components\<close>)
        show ?thesis using result by (simp add: inference proof_claim_inference_schema_def)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem proof_claim_checking_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E (ru,rr) G" and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    and checked: "proof_claim_values (positioned_program P) G js xs hs"
  shows "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
    (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs))\<in>positive_meaning proof_claim_checking_system"
proof -
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have gf: "schema_graph_formed G (ru,rr)" using graph by (simp add: native_schema_graph_at_def)
  have header_fields: "term_formed e" "term_formed (use_data_term pu)" "term_formed (Payload_Term pr)"
    "term_formed (use_data_term ru)" "term_formed (Payload_Term rr)"
    using native_claim_context_formed[OF source package graph] by auto
  have table: "(21,pair_list_term js)\<in>positive_meaning keyed_list_system"
    by (rule keyed_list_complete[OF rows keys])
  show ?thesis using checked
  proof (induction xs arbitrary: hs)
    case Nil
    have result: "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
      (pair_list_term js) (Payload_Term []) (Payload_Term []))\<in>positive_meaning proof_claim_checking_system"
      by (rule proof_claim_checking_empty[OF header_fields table])
    show ?case using Nil.prems result by simp
  next
    case (Cons row xs)
    obtain n d t where row: "row=(n,d,t)" by (cases row) auto
    obtain ts where at: "proof_claim_at (positioned_program P) G js n d t"
      and rest: "proof_claim_values (positioned_program P) G js xs ts"
        "hs=(if (n,Schema_Assertion)\<in>fset (graph_inferences G) then (n,d,t)#ts else ts)"
      using Cons.prems by (simp only: row proof_claim_values_cons; blast)
    have tail: "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
      (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term ts))\<in>positive_meaning proof_claim_checking_system"
      by (rule Cons.IH[OF rest(1)])
    have inside: "n\<in>schema_graph_nodes G" by (rule proof_claim_at_node_call(1)[OF at])
    have membership: "(98,proof_graph_subject_argument e (use_data_term ru) (Payload_Term rr) (definition_site_value n))
        \<in>positive_meaning proof_graph_membership_system"
      by (rule proof_graph_membership_complete[OF source graph inside])
    have member: "(98,proof_graph_subject_argument e (use_data_term ru) (Payload_Term rr)
        (Pair_Term (use_data_term (fst n)) (Payload_Term (snd n))))\<in>positive_meaning proof_graph_membership_system"
      using membership by (simp add: site_data_term_def)
    consider (assertion) "(n,Schema_Assertion)\<in>fset (graph_inferences G)"
      | (inference) c V where "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
      using at by (auto simp: proof_claim_at_def)
    then show ?case
    proof cases
      case assertion
      obtain I K where raw: "native_proof_node_at E (fst n) (snd n) Schema_Assertion (schema_graph_premises G n) I K"
        using native_schema_graph_entry[OF graph assertion] by blast
      have actual: "native_proof_node_at E (fst n) (snd n) Schema_Assertion {} (set [snd n]) (set [])"
        using raw native_proof_node_assertion[OF raw] by simp
      have read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n)) (Payload_Term [])
          (data_list_term [Payload_Term (snd n)]) (Payload_Term []))\<in>positive_meaning proof_node_reading_system"
        using proof_node_reading_assertion[OF source, where u="fst n" and r="snd n" and Is="[snd n]" and Ks="[]"] actual by simp
      have original: "schema_call_formed P d t"
        using proof_claim_at_node_call(2)[OF at] by (simp only: positioned_program_calls[OF pf])
      have call: "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr)
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) t))\<in>positive_meaning program_call_admission_system"
        using program_call_admission_complete[OF source package original] by (simp add: site_data_term_def)
      have result: "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
        (pair_list_term js)
        (Pair_Term (Pair_Term (Pair_Term (use_data_term (fst n)) (Payload_Term (snd n)))
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) t)) (positioned_call_rows_term xs))
        (Pair_Term (Pair_Term (Pair_Term (use_data_term (fst n)) (Payload_Term (snd n)))
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) t)) (positioned_call_rows_term ts)))
        \<in>positive_meaning proof_claim_checking_system"
        by (rule proof_claim_checking_assertion_step[OF member read call tail])
      show ?thesis using result rest(2) assertion
        by (simp add: row positioned_call_rows_cons call_instance_value_def site_data_term_def)
    next
      case (inference c V)
      obtain a bs vs ds qs ps i k where fields: "c=(fst d,a)"
        "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n))
          (data_list_term [definition_site_value c,positioned_binding_rows_term vs,discharge_rows_term ds]) i k)
          \<in>positive_meaning proof_node_reading_system"
        "(99,row_qualification_argument (use_data_term (fst d)) (binding_rows_term bs) (positioned_binding_rows_term vs))
          \<in>positive_meaning row_qualification_system"
        "(100,keyed_row_join_argument (pair_list_term js) (discharge_rows_term ds) (positioned_call_rows_term ps))
          \<in>positive_meaning keyed_row_join_system"
        "(99,row_qualification_argument (use_data_term (fst d)) (call_instance_rows_term qs) (positioned_call_rows_term ps))
          \<in>positive_meaning row_qualification_system"
        "(87,admitted_instantiation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
          (Payload_Term a) (binding_rows_term bs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system"
        by (rule native_inference_claim_operands[OF source package graph inference rows at]) (rule that; assumption)
      have read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n))
          (data_list_term [Pair_Term (use_data_term (fst d)) (Payload_Term a),positioned_binding_rows_term vs,discharge_rows_term ds]) i k)
          \<in>positive_meaning proof_node_reading_system"
        using fields(2) by (simp add: fields(1) site_data_term_def)
      have admitted: "(87,admitted_instantiation_argument e (use_data_term pu) (Payload_Term pr)
          (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) (Payload_Term a)
          (binding_rows_term bs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system"
        using fields(6) by (simp add: site_data_term_def)
      have result: "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
        (pair_list_term js)
        (Pair_Term (Pair_Term (Pair_Term (use_data_term (fst n)) (Payload_Term (snd n)))
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) t)) (positioned_call_rows_term xs))
        (positioned_call_rows_term ts))\<in>positive_meaning proof_claim_checking_system"
        by (rule proof_claim_checking_inference_step[OF member read fields(3-5) admitted tail])
      have not_assertion: "(n,Schema_Assertion)\<notin>fset (graph_inferences G)"
        by (rule schema_graph_inference_not_assertion[OF gf inference])
      show ?thesis using result rest(2) not_assertion
        by (simp add: row positioned_call_rows_cons call_instance_value_def site_data_term_def)
    qed
  qed
qed

theorem proof_claim_checking_exact:
  "(101,z)\<in>positive_meaning proof_claim_checking_system \<longleftrightarrow> proof_claim_checking_result z"
proof
  assume "(101,z)\<in>positive_meaning proof_claim_checking_system"
  then show "proof_claim_checking_result z" by (rule proof_claim_checking_sound)
next
  assume "proof_claim_checking_result z"
  then show "(101,z)\<in>positive_meaning proof_claim_checking_system"
  proof (elim disjE exE conjE)
    fix e u r v a js
    assume shape: "z=proof_claim_argument e u r v a (pair_list_term js) (Payload_Term []) (Payload_Term [])"
      and formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a"
      and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
    have table: "(21,pair_list_term js)\<in>positive_meaning keyed_list_system" by (rule keyed_list_complete[OF rows keys])
    show ?thesis using proof_claim_checking_empty[OF formed table] by (simp only: shape)
  next
    fix E e pu pr ru rr P G js xs hs
    assume shape: "z=proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr)
        (pair_list_term js) (positioned_call_rows_term xs) (positioned_call_rows_term hs)"
      and source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
      and graph: "native_schema_graph_at E (ru,rr) G" and rows: "formed_key_rows js" and keys: "distinct (map fst js)"
      and checked: "proof_claim_values (positioned_program P) G js xs hs"
    show ?thesis using proof_claim_checking_complete[OF source package graph rows keys checked] by (simp only: shape)
  qed
qed

corollary proof_claim_checking_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr) j x h)
      \<in>positive_meaning proof_claim_checking_system \<longleftrightarrow>
    (\<exists>js xs hs. j=pair_list_term js \<and> x=positioned_call_rows_term xs \<and> h=positioned_call_rows_term hs \<and>
      formed_key_rows js \<and> distinct (map fst js) \<and> proof_claim_values (positioned_program P) G js xs hs)"
  by (simp only: proof_claim_checking_exact proof_claim_checking_result_at_reads[OF source package graph])

corollary proof_claim_checking_presentation_invariance:
  assumes source: "environment_value_presents E e" "environment_value_presents E f"
    and package: "native_package_at E pu pr P" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr) j x h)
      \<in>positive_meaning proof_claim_checking_system \<longleftrightarrow>
    (101,proof_claim_argument f (use_data_term pu) (Payload_Term pr) (use_data_term ru) (Payload_Term rr) j x h)
      \<in>positive_meaning proof_claim_checking_system"
  by (simp only: proof_claim_checking_at_reads[OF source(1) package graph]
    proof_claim_checking_at_reads[OF source(2) package graph])

text \<open>
  The empty clause checks the shared table's distinct keys once. Every
  nonempty row checks an actual graph member and its complete native node.
  Assertions add the supplied call to the output; inferences use the actual
  package instance and join every premise to the same complete table.

  The walker may visit a supplied sublist while carrying a larger table.
  Its exact contract exposes both lists. The derivation entry supplies that
  table as the whole traversal and checks the root's one call. No node claim
  or assertion truth is added to the native proof metadata.
\<close>

end
