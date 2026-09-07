theory Factor_Proof_Link_Checking
  imports Factor_Proof_Node_Reading
begin

section \<open>Complete premise traversal retains each assertion origin\<close>

lemma key_values_unique_key:
  assumes keys: "distinct (map fst xs)" and row: "(k,v)\<in>set xs"
  shows "key_values k xs=[v]"
proof -
  have distinct: "distinct xs" and functional: "single_valued (set xs)"
    using keys by (simp only: distinct_keys_iff; blast)+
  have distinct_values: "distinct (key_values k xs)" by (rule key_values_distinct[OF distinct])
  have collected: "set (key_values k xs)={v}"
  proof (rule set_eqI)
    fix w
    show "w\<in>set (key_values k xs) \<longleftrightarrow> w\<in>{v}"
    proof
      assume member: "w\<in>set (key_values k xs)"
      have other: "(k,w)\<in>set xs" using member by (simp only: key_values_set mem_Collect_eq)
      have same: "w=v" by (rule single_valued_outputs[OF functional other row])
      show "w\<in>{v}" by (simp only: same singleton_iff)
    next
      assume member: "w\<in>{v}"
      have same: "w=v" using member by (simp only: singleton_iff)
      show "w\<in>set (key_values k xs)" by (simp only: same key_values_set mem_Collect_eq) (rule row)
    qed
  qed
  show ?thesis by (rule distinct_singleton_enumeration[OF distinct_values collected])
qed

lemma key_fibre_singleton_rows:
  assumes holds: "(28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
  obtains rs where "b=pair_list_term rs" "term_formed k" "self_contained_term k"
    "formed_key_rows rs" "key_values k rs=[v]"
proof -
  obtain j rs where found: "k=j" "b=pair_list_term rs" "[v]=key_values j rs"
    "term_formed j" "self_contained_term j" "formed_key_rows rs"
    using holds
    by (simp only: key_fibre_exact factor_term.inject data_list_term_injective; elim exE conjE)
      (rule that; assumption)
  show thesis by (rule that[of rs]) (use found in simp_all)
qed

fun proof_link_rows ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> (factor_term\<times>factor_term) list \<Rightarrow>
    (factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "proof_link_rows b p [] hs \<longleftrightarrow> hs=[]"
| "proof_link_rows b p ((s,n)#ds) hs \<longleftrightarrow>
    (\<exists>rs us. b=pair_list_term rs \<and> formed_key_rows rs \<and> term_formed s \<and> self_contained_term s \<and>
      proof_link_rows b p ds us \<and>
      ((key_values n rs=[Payload_Term []] \<and> hs=(n,Pair_Term p s)#us) \<or>
       (\<exists>c v d. key_values n rs=[data_list_term [c,v,d]] \<and> hs=us)))"

abbreviation proof_links_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "proof_links_argument b p ds hs \<equiv> Pair_Term (Pair_Term b p) (Pair_Term ds hs)"

abbreviation proof_links_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "proof_links_pattern b p ds hs \<equiv> Pattern_Pair (Pattern_Pair b p) (Pattern_Pair ds hs)"

abbreviation proof_link_checking_result :: "factor_term \<Rightarrow> bool" where
  "proof_link_checking_result z \<equiv> \<exists>b p ds hs.
    z=proof_links_argument b p (pair_list_term ds) (pair_list_term hs) \<and>
    term_formed b \<and> term_formed p \<and> self_contained_term p \<and> proof_link_rows b p ds hs"

lemma proof_link_rows_formed:
  assumes read: "proof_link_rows b p ds hs" and parent: "term_formed p" "self_contained_term p"
  shows "data_elements (map (\<lambda>(s,n). Pair_Term s n) ds)"
    "data_elements (map (\<lambda>(n,q). Pair_Term n q) hs)"
proof -
  have both: "data_elements (map (\<lambda>(s,n). Pair_Term s n) ds) \<and>
    data_elements (map (\<lambda>(n,q). Pair_Term n q) hs)"
    using read
  proof (induction ds arbitrary: hs)
    case Nil
    then show ?case by simp
  next
    case (Cons row ds)
    obtain s n where row: "row=(s,n)" by (cases row)
    obtain rs us where parts: "formed_key_rows rs" "term_formed s" "self_contained_term s"
      "proof_link_rows b p ds us"
      "(key_values n rs=[Payload_Term []] \<and> hs=(n,Pair_Term p s)#us) \<or>
        (\<exists>c v d. key_values n rs=[data_list_term [c,v,d]] \<and> hs=us)"
      using Cons.prems by (simp only: row proof_link_rows.simps) blast
    have key: "\<exists>v. (n,v)\<in>set rs" using parts(5) key_values_set[of n rs] by auto
    have formed: "term_formed n" "self_contained_term n" using key parts(1) by auto
    have tail: "data_elements (map (\<lambda>(s,n). Pair_Term s n) ds)"
      "data_elements (map (\<lambda>(n,q). Pair_Term n q) us)"
      using Cons.IH[OF parts(4)] by blast+
    have result_shape: "hs=(n,Pair_Term p s)#us \<or> hs=us" using parts(5) by blast
    show ?case
    proof (cases "hs=us")
      case True
      show ?thesis using tail parts(2,3) parent formed by (simp add: row True)
    next
      case False
      have head: "hs=(n,Pair_Term p s)#us" using result_shape False by blast
      show ?thesis using tail parts(2,3) parent formed by (simp add: row head)
    qed
  qed
  show "data_elements (map (\<lambda>(s,n). Pair_Term s n) ds)"
    "data_elements (map (\<lambda>(n,q). Pair_Term n q) hs)" using both by blast+
qed

definition proof_link_nil_schema :: "(nat,nat,nat) factor_schema" where
  "proof_link_nil_schema=data_rule
    (proof_links_pattern data_x data_y (Pattern_Payload []) (Pattern_Payload [])) {(0,2,data_y)}"

definition proof_link_assertion_schema :: "(nat,nat,nat) factor_schema" where
  "proof_link_assertion_schema=data_rule
    (proof_links_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Variable 4))
      (Pattern_Pair (Pattern_Pair data_w (Pattern_Pair data_y data_z)) (Pattern_Variable 5)))
    {(0,28,Pattern_Pair data_w (Pattern_Pair data_x (data_list_pattern [Pattern_Payload []]))),
     (1,2,data_z),
     (2,95,proof_links_pattern data_x data_y (Pattern_Variable 4) (Pattern_Variable 5))}"

definition proof_link_inference_schema :: "(nat,nat,nat) factor_schema" where
  "proof_link_inference_schema=data_rule
    (proof_links_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,28,Pattern_Pair data_w (Pattern_Pair data_x
       (data_list_pattern [data_list_pattern [Pattern_Variable 6,Pattern_Variable 7,Pattern_Variable 8]]))),
     (1,2,data_z),
     (2,95,proof_links_pattern data_x data_y (Pattern_Variable 4) (Pattern_Variable 5))}"

definition proof_link_checking_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "proof_link_checking_clauses={(0,proof_link_nil_schema),(1,proof_link_assertion_schema),(2,proof_link_inference_schema)}"

definition proof_link_checking_system :: "(nat,nat,nat,nat) schema_system" where
  "proof_link_checking_system=add_view_definition proof_node_reading_system 95 data_x proof_link_checking_clauses"

lemma proof_link_checking_system_formed [simp]: "schema_system_formed proof_link_checking_system"
  unfolding proof_link_checking_system_def
  by (rule add_recursive_definition_formed[OF proof_node_reading_system_formed])
    (auto simp: proof_link_checking_clauses_def proof_link_nil_schema_def proof_link_assertion_schema_def proof_link_inference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma proof_link_checking_definitions [simp]:
  "system_definitions proof_link_checking_system=insert 95 (system_definitions proof_node_reading_system)"
  by (simp add: proof_link_checking_system_def)

lemma proof_link_checking_call:
  "schema_call_formed proof_link_checking_system d t \<longleftrightarrow>
    d\<in>system_definitions proof_link_checking_system \<and> term_formed t"
  using added_variable_calls[OF proof_node_reading_system_formed
    proof_link_checking_system_formed[unfolded proof_link_checking_system_def] proof_node_reading_call]
  by (simp only: proof_link_checking_system_def[symmetric])

lemma proof_link_checking_old_meaning:
  assumes "d\<in>system_definitions proof_node_reading_system"
  shows "(d,t)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_node_reading_system"
  using added_definition_preserves_old(2)[OF proof_node_reading_system_formed
    proof_link_checking_system_formed[unfolded proof_link_checking_system_def], of d t] assms
  by (auto simp: proof_link_checking_system_def)

lemma proof_link_checking_clause [simp]:
  "((95,c),S)\<in>system_clauses proof_link_checking_system \<longleftrightarrow> (c,S)\<in>proof_link_checking_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_node_reading_system \<Longrightarrow> d\<in>system_definitions proof_node_reading_system" for d c S
    using proof_node_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((95,c),S)\<notin>system_clauses proof_node_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: proof_link_checking_system_def)
qed

lemma proof_link_checking_fibre_meaning:
  assumes "d\<in>system_definitions key_fibre_system"
  shows "(d,t)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning key_fibre_system"
  using proof_link_checking_old_meaning[of d t] proof_node_reading_base_meaning[of d t]
    metadata_reading_quotation_meaning[of d t] quotation_admission_record_meaning[of d t]
    record_admission_old_meaning[of d t] socket_chain_old_meaning[of d t]
    family_admission_headed_meaning[of d t] headed_material_old_meaning[OF assms, of t] assms by auto

lemma proof_link_checking_keyed_meaning:
  assumes "d\<in>system_definitions keyed_list_system"
  shows "(d,t)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning keyed_list_system"
  using proof_link_checking_fibre_meaning[of d t] key_fibre_old_meaning[of d t]
    environment_identity_previous_meaning[of d t] environment_admission_previous_meaning[of d t]
    binding_entries_previous_meaning[of d t] binding_entry_keyed_meaning[of d t] assms by auto

lemma proof_link_checking_components:
  "(28,t)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  "(2,t)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using proof_link_checking_fibre_meaning[of 28 t] proof_link_checking_fibre_meaning[of 2 t]
    key_fibre_data[of t] by auto

theorem proof_link_checking_sound:
  assumes holds: "(95,z)\<in>positive_meaning proof_link_checking_system"
  shows "proof_link_checking_result z"
proof -
  let ?Q="\<lambda>z. proof_link_checking_result z"
  have invariant: "(95::nat)=95 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=95 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses proof_link_checking_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed proof_link_checking_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning proof_link_checking_system \<and>
        (e=95 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=95 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=95"
      then consider (nil) "S=proof_link_nil_schema"
        | (assertion) "S=proof_link_assertion_schema" | (inference) "S=proof_link_inference_schema"
        using clause by (auto simp: proof_link_checking_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        have terms: "term_formed (h 0)" "term_formed (h 1)" "self_contained_term (h 1)"
          using assignment support by (auto simp: nil proof_link_nil_schema_def schema_variables_def proof_link_checking_components)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "[]"], rule exI[of _ "[]"])
          (use terms in \<open>simp add: nil proof_link_nil_schema_def\<close>)
      next
        case assertion
        obtain ds hs where tail: "h 4=pair_list_term ds" "h 5=pair_list_term hs"
          "term_formed (h 0)" "term_formed (h 1)" "self_contained_term (h 1)" "proof_link_rows (h 0) (h 1) ds hs"
          using support[rule_format, of 2 95 "proof_links_pattern data_x data_y (Pattern_Variable 4) (Pattern_Variable 5)"]
          by (auto simp: assertion proof_link_assertion_schema_def)
        have lookup: "(28,key_fibre_argument (h 3) (h 0) (data_list_term [Payload_Term []]))\<in>positive_meaning key_fibre_system"
          and socket: "term_formed (h 2)" "self_contained_term (h 2)"
          using support by (auto simp: assertion proof_link_assertion_schema_def proof_link_checking_components)
        obtain rs where bound: "h 0=pair_list_term rs" "formed_key_rows rs" "key_values (h 3) rs=[Payload_Term []]"
          by (rule key_fibre_singleton_rows[OF lookup]) (rule that; assumption)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "h 1"],
            rule exI[of _ "(h 2,h 3)#ds"], rule exI[of _ "(h 3,Pair_Term (h 1) (h 2))#hs"])
          (use tail socket bound in \<open>auto simp: assertion proof_link_assertion_schema_def\<close>)
      next
        case inference
        obtain ds hs where tail: "h 4=pair_list_term ds" "h 5=pair_list_term hs"
          "term_formed (h 0)" "term_formed (h 1)" "self_contained_term (h 1)" "proof_link_rows (h 0) (h 1) ds hs"
          using support[rule_format, of 2 95 "proof_links_pattern data_x data_y (Pattern_Variable 4) (Pattern_Variable 5)"]
          by (auto simp: inference proof_link_inference_schema_def)
        have lookup: "(28,key_fibre_argument (h 3) (h 0) (data_list_term [data_list_term [h 6,h 7,h 8]]))
          \<in>positive_meaning key_fibre_system" and socket: "term_formed (h 2)" "self_contained_term (h 2)"
          using support by (auto simp: inference proof_link_inference_schema_def proof_link_checking_components)
        obtain rs where bound: "h 0=pair_list_term rs" "formed_key_rows rs"
          "key_values (h 3) rs=[data_list_term [h 6,h 7,h 8]]"
          by (rule key_fibre_singleton_rows[OF lookup]) (rule that; assumption)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "h 1"],
            rule exI[of _ "(h 2,h 3)#ds"], rule exI[of _ hs])
          (use tail socket bound in \<open>auto simp: inference proof_link_inference_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem proof_link_checking_complete:
  assumes bound: "term_formed b" and parent: "term_formed p" "self_contained_term p"
    and read: "proof_link_rows b p ds hs"
  shows "(95,proof_links_argument b p (pair_list_term ds) (pair_list_term hs))\<in>positive_meaning proof_link_checking_system"
  using read
proof (induction ds arbitrary: hs)
  case Nil
  have result: "(95,evaluate_pattern (\<lambda>i::nat. if i=0 then b else p) (schema_conclusion proof_link_nil_schema))
    \<in>positive_meaning proof_link_checking_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use bound parent in \<open>auto simp: proof_link_checking_clauses_def proof_link_nil_schema_def
        schema_variables_def proof_link_checking_call proof_link_checking_components octets_formed_def\<close>)
  show ?case using result Nil.prems by (simp add: proof_link_nil_schema_def)
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  obtain rs us where parts: "b=pair_list_term rs" "formed_key_rows rs" "term_formed s" "self_contained_term s"
    "proof_link_rows b p ds us"
    "(key_values n rs=[Payload_Term []] \<and> hs=(n,Pair_Term p s)#us) \<or>
      (\<exists>c v d. key_values n rs=[data_list_term [c,v,d]] \<and> hs=us)"
    using Cons.prems by (simp only: row proof_link_rows.simps) blast
  have tail: "(95,proof_links_argument b p (pair_list_term ds) (pair_list_term us))\<in>positive_meaning proof_link_checking_system"
    by (rule Cons.IH[OF parts(5)])
  have tail_formed: "term_formed (pair_list_term ds)" "term_formed (pair_list_term us)"
    using schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  have key_member: "\<exists>v. (n,v)\<in>set rs" using parts(6) key_values_set[of n rs] by auto
  have key: "term_formed n" "self_contained_term n" using key_member parts(2) by auto
  show ?case
  proof (cases "key_values n rs=[Payload_Term []]")
    case True
    have hs: "hs=(n,Pair_Term p s)#us" using parts(6) True by auto
    have lookup: "(28,key_fibre_argument n b (data_list_term [Payload_Term []]))\<in>positive_meaning key_fibre_system"
      using key parts(2) True by (simp add: parts(1) key_fibre_lists)
    let ?h="\<lambda>i::nat. if i=0 then b else if i=1 then p else if i=2 then s else if i=3 then n
      else if i=4 then pair_list_term ds else pair_list_term us"
    have result: "(95,evaluate_pattern ?h (schema_conclusion proof_link_assertion_schema))\<in>positive_meaning proof_link_checking_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use bound parent parts(3,4) tail tail_formed key lookup in
          \<open>auto simp: proof_link_checking_clauses_def proof_link_assertion_schema_def schema_variables_def
            proof_link_checking_call proof_link_checking_components\<close>)
    show ?thesis using result by (simp add: row hs proof_link_assertion_schema_def)
  next
    case False
    obtain c v d where child: "key_values n rs=[data_list_term [c,v,d]]" and hs: "hs=us"
      using parts(6) False by blast
    have lookup: "(28,key_fibre_argument n b (data_list_term [data_list_term [c,v,d]]))\<in>positive_meaning key_fibre_system"
      using key parts(2) child by (simp add: parts(1) key_fibre_lists)
    have fields: "term_formed c" "term_formed v" "term_formed d"
      using schema_call_formed_target[OF positive_meaning_formed[OF lookup]] by auto
    let ?h="\<lambda>i::nat. if i=0 then b else if i=1 then p else if i=2 then s else if i=3 then n
      else if i=4 then pair_list_term ds else if i=5 then pair_list_term us else if i=6 then c else if i=7 then v else d"
    have result: "(95,evaluate_pattern ?h (schema_conclusion proof_link_inference_schema))\<in>positive_meaning proof_link_checking_system"
      by (rule ordinary_positive_valuation_step[where c=2])
        (use bound parent parts(3,4) tail tail_formed key lookup fields in
          \<open>auto simp: proof_link_checking_clauses_def proof_link_inference_schema_def schema_variables_def
            proof_link_checking_call proof_link_checking_components\<close>)
    show ?thesis using result by (simp add: row hs proof_link_inference_schema_def)
  qed
qed

theorem proof_link_checking_exact:
  "(95,z)\<in>positive_meaning proof_link_checking_system \<longleftrightarrow> proof_link_checking_result z"
  using proof_link_checking_sound proof_link_checking_complete by blast

corollary proof_link_checking_lists:
  "(95,proof_links_argument b p (pair_list_term ds) (pair_list_term hs))\<in>positive_meaning proof_link_checking_system \<longleftrightarrow>
    term_formed b \<and> term_formed p \<and> self_contained_term p \<and> proof_link_rows b p ds hs"
  by (simp only: proof_link_checking_exact factor_term.inject pair_list_term_injective) blast

text \<open>
  Every supplied link uses the existing complete key collector on the same
  bound. Its child must have exactly one value, even when repeated values
  would agree. Empty child values retain the child's site and the complete
  parent-and-socket origin; three-field child values contribute no assertion
  origin. Both cases check the rest of the links. Shared inference targets
  remain possible. The enclosing bound separately reads every node value
  from its actual source; this traversal alone makes no native-node claim.
  Bound values may contain arbitrary formed literal targets.
\<close>

end
