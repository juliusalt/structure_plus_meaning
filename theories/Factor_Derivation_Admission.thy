theory Factor_Derivation_Admission
  imports Factor_Proof_Claim_Checking
begin

section \<open>The complete traversal and the root's one supplied call\<close>

abbreviation derivation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "derivation_argument e u r n d t h \<equiv>
    package_subject_argument e u r (Pair_Term n (Pair_Term (Pair_Term d t) h))"

abbreviation derivation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "derivation_pattern e u r n d t h \<equiv>
    package_subject_pattern e u r (Pattern_Pair n (Pattern_Pair (Pattern_Pair d t) h))"

abbreviation derivation_admission_result :: "factor_term \<Rightarrow> bool" where
  "derivation_admission_result z \<equiv> \<exists>E e pu pr root d t hs P G.
    z=derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs) \<and>
    environment_value_presents E e \<and> native_package_at E pu pr P \<and> native_schema_graph_at E root G \<and>
    distinct hs \<and> schema_graph_derives (positioned_program P) G root d t (set hs)"

definition derivation_admission_schema :: "(nat,nat,nat) factor_schema" where
  "derivation_admission_schema=data_rule
    (derivation_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))
    {(0,101,proof_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 8)
       (Pattern_Variable 8) (Pattern_Variable 7)),
     (1,28,Pattern_Pair (Pattern_Pair data_w (Pattern_Variable 4))
       (Pattern_Pair (Pattern_Variable 8) (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)])))}"

definition derivation_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "derivation_admission_system=add_view_definition proof_claim_checking_system 102 data_x {(0,derivation_admission_schema)}"

lemma derivation_admission_system_formed [simp]: "schema_system_formed derivation_admission_system"
  unfolding derivation_admission_system_def
  by (rule add_recursive_definition_formed[OF proof_claim_checking_system_formed])
    (auto simp: derivation_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma derivation_admission_definitions [simp]:
  "system_definitions derivation_admission_system=insert 102 (system_definitions proof_claim_checking_system)"
  by (simp add: derivation_admission_system_def)

lemma derivation_admission_call:
  "schema_call_formed derivation_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions derivation_admission_system \<and> term_formed t"
  using added_variable_calls[OF proof_claim_checking_system_formed
    derivation_admission_system_formed[unfolded derivation_admission_system_def] proof_claim_checking_call]
  by (simp only: derivation_admission_system_def[symmetric])

lemma derivation_admission_old_meaning:
  assumes "d\<in>system_definitions proof_claim_checking_system"
  shows "(d,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_claim_checking_system"
  using added_definition_preserves_old(2)[OF proof_claim_checking_system_formed
    derivation_admission_system_formed[unfolded derivation_admission_system_def], of d t] assms
  by (auto simp: derivation_admission_system_def)

lemma derivation_admission_clause [simp]:
  "((102,c),S)\<in>system_clauses derivation_admission_system \<longleftrightarrow> (c,S)\<in>{(0,derivation_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_claim_checking_system \<Longrightarrow> d\<in>system_definitions proof_claim_checking_system" for d c S
    using proof_claim_checking_system_formed unfolding schema_system_formed_def by blast
  have absent: "((102,c),S)\<notin>system_clauses proof_claim_checking_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: derivation_admission_system_def)
qed

lemma derivation_admission_components:
  "(101,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (101,t)\<in>positive_meaning proof_claim_checking_system"
  "(28,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  using derivation_admission_old_meaning[of 101 t] derivation_admission_old_meaning[of 28 t]
    proof_claim_checking_old_meaning[of 28 t] keyed_row_join_fibre[of t] by auto

lemma derivation_admission_step:
  assumes checked: "(101,proof_claim_argument e u r v a j j h)\<in>positive_meaning proof_claim_checking_system"
    and root: "(28,key_fibre_argument (Pair_Term v a) j (data_list_term [Pair_Term d t]))\<in>positive_meaning key_fibre_system"
  shows "(102,derivation_argument e u r (Pair_Term v a) d t h)\<in>positive_meaning derivation_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a"
    "term_formed d" "term_formed t" "term_formed h" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF checked]]
      schema_call_formed_target[OF positive_meaning_formed[OF root]] by auto
  let ?f="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else if i=4 then a
    else if i=5 then d else if i=6 then t else if i=7 then h else j"
  have result: "(102,evaluate_pattern ?f (schema_conclusion derivation_admission_schema))\<in>positive_meaning derivation_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use assms formed in \<open>auto simp: derivation_admission_schema_def schema_variables_def
        derivation_admission_call derivation_admission_components\<close>)
  show ?thesis using result by (simp add: derivation_admission_schema_def)
qed

lemma derivation_admission_from_components:
  assumes checked: "(101,proof_claim_argument e u r v a j j h)\<in>positive_meaning proof_claim_checking_system"
    and root: "(28,key_fibre_argument (Pair_Term v a) j (data_list_term [Pair_Term d t]))\<in>positive_meaning key_fibre_system"
  shows "derivation_admission_result (derivation_argument e u r (Pair_Term v a) d t h)"
proof -
  obtain rs where lookup: "j=pair_list_term rs" "key_values (Pair_Term v a) rs=[Pair_Term d t]"
    by (rule key_fibre_singleton_rows[OF root]) (rule that; assumption)
  have nonempty: "j\<noteq>Payload_Term []"
  proof
    assume empty: "j=Payload_Term []"
    have "rs=[]" using lookup(1) empty by (cases rs) auto
    then show False using lookup(2) by simp
  qed
  have result: "proof_claim_checking_result (proof_claim_argument e u r v a j j h)"
    by (rule proof_claim_checking_sound[OF checked])
  obtain E pu pr ru rr P G js xs hs where source: "environment_value_presents E e"
    and header_fields: "u=use_data_term pu" "r=Payload_Term pr" "v=use_data_term ru" "a=Payload_Term rr"
    and fields: "j=pair_list_term js" "j=positioned_call_rows_term xs" "h=positioned_call_rows_term hs"
    and package: "native_package_at E pu pr P" and graph: "native_schema_graph_at E (ru,rr) G"
    and rows: "formed_key_rows js" and distinct: "distinct (map fst js)"
    and claims: "proof_claim_values (positioned_program P) G js xs hs"
    by (rule proof_claim_checking_resultE[OF result nonempty]) (rule that; assumption)
  have encoded: "js=encoded_positioned_calls xs" using fields(1,2) by (simp only: pair_list_term_injective)
  have same: "rs=js" using lookup(1) fields(1) by (simp only: pair_list_term_injective)
  have keys: "distinct (map fst xs)" using distinct by (simp only: encoded positioned_calls_key_order)
  have member: "(Pair_Term v a,Pair_Term d t)\<in>set (encoded_positioned_calls xs)"
    using lookup(2) key_values_set[of "Pair_Term v a" rs] same encoded by auto
  obtain n f x where row: "(n,f,x)\<in>set xs" and nvalue: "Pair_Term v a=definition_site_value n"
    and row_value: "Pair_Term d t=call_instance_value f x" using member by auto
  have root_value: "Pair_Term v a=definition_site_value (ru,rr)" by (simp add: header_fields(3,4) site_data_term_def)
  have root_site: "n=(ru,rr)" using nvalue root_value by (simp only: definition_site_value_eq)
  have call_value: "d=definition_site_value f" "t=x" using row_value by (simp_all add: call_instance_value_def)
  have actual_root: "((ru,rr),f,t)\<in>set xs" using row root_site call_value(2) by simp
  have gf: "schema_graph_formed G (ru,rr)" using graph by (simp add: native_schema_graph_at_def)
  have actual_claims: "proof_claim_values (positioned_program P) G (encoded_positioned_calls xs) xs hs"
    using claims by (simp only: encoded)
  have reading: "schema_graph_reading (positioned_program P) G (ru,rr) f t (set xs)"
    and boundary: "set hs=schema_graph_assumptions G (set xs)"
    using proof_claim_values_to_reading[OF gf keys actual_claims actual_root] by blast+
  have derived: "schema_graph_derives (positioned_program P) G (ru,rr) f t (set hs)"
    using reading boundary unfolding schema_graph_derives_def by blast
  have order: "distinct hs" using keys claims by (auto simp: proof_claim_values_def distinct_keys_iff)
  show ?thesis by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr],
      rule exI[of _ "(ru,rr)"], rule exI[of _ f], rule exI[of _ t], rule exI[of _ hs], rule exI[of _ P], rule exI[of _ G])
    (use source package graph order derived in \<open>simp only: header_fields(1,2) root_value call_value(1) fields(3); blast\<close>)
qed

theorem derivation_admission_sound:
  assumes holds: "(102,z)\<in>positive_meaning derivation_admission_system"
  shows "derivation_admission_result z"
proof -
  have consequence: "(102,z)\<in>schema_consequences derivation_admission_system (positive_meaning derivation_admission_system)"
    using holds positive_meaning_unfold[of derivation_admission_system] by blast
  obtain c S f where clause: "((102,c),S)\<in>system_clauses derivation_admission_system"
    and conclusion: "z=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning derivation_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=derivation_admission_schema" using clause by simp
  have result: "derivation_admission_result (derivation_argument (f 0) (f 1) (f 2) (Pair_Term (f 3) (f 4)) (f 5) (f 6) (f 7))"
    by (rule derivation_admission_from_components[where j="f 8"])
      (use support in \<open>auto simp: schema derivation_admission_schema_def derivation_admission_components\<close>)
  show ?thesis using result conclusion by (simp add: schema derivation_admission_schema_def)
qed

theorem derivation_admission_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G" and order: "distinct hs"
    and derived: "schema_graph_derives (positioned_program P) G root d t (set hs)"
  shows "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
    (definition_site_value d) t (positioned_call_rows_term hs))\<in>positive_meaning derivation_admission_system"
proof -
  obtain J where reading: "schema_graph_reading (positioned_program P) G root d t J"
    and boundary: "set hs=schema_graph_assumptions G J"
    using derived by (auto simp: schema_graph_derives_def)
  obtain xs where enumeration: "set xs=J" "distinct (map fst xs)"
    "filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs=hs"
    by (rule schema_graph_claim_order[OF reading order boundary]) (rule that; assumption)
  have read: "schema_graph_reading (positioned_program P) G root d t (set xs)"
    using reading enumeration(1) by simp
  have checked_rows: "proof_claim_values (positioned_program P) G (encoded_positioned_calls xs) xs hs"
    using reading_to_proof_claim_values[OF read enumeration(2)] by (simp only: enumeration(3))
  have formed: "formed_key_rows (encoded_positioned_calls xs)"
    by (rule native_claim_rows_formed(1)[OF source package graph checked_rows])
  have keys: "distinct (map fst (encoded_positioned_calls xs))"
    by (simp only: positioned_calls_key_order; rule enumeration(2))
  have graph_pair: "native_schema_graph_at E (fst root,snd root) G" using graph by simp
  have checked: "(101,proof_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term (fst root)) (Payload_Term (snd root))
      (positioned_call_rows_term xs) (positioned_call_rows_term xs) (positioned_call_rows_term hs))\<in>positive_meaning proof_claim_checking_system"
    by (rule proof_claim_checking_complete[OF source package graph_pair formed keys checked_rows])
  have row: "(root,d,t)\<in>set xs" using read by (simp add: schema_graph_reading_def)
  have fibre: "key_values (definition_site_value root) (encoded_positioned_calls xs)=[call_instance_value d t]"
    by (simp only: positioned_calls_fibre[OF enumeration(2)]; rule row)
  have rf: "term_formed (definition_site_value root)" by (rule native_claim_context_formed(4)[OF source package graph])
  have lookup: "(28,key_fibre_argument (definition_site_value root) (positioned_call_rows_term xs)
      (data_list_term [Pair_Term (definition_site_value d) t]))\<in>positive_meaning key_fibre_system"
    by (simp only: key_fibre_lists) (use formed rf fibre in \<open>simp add: call_instance_value_def\<close>)
  have actual_lookup: "(28,key_fibre_argument (Pair_Term (use_data_term (fst root)) (Payload_Term (snd root)))
      (positioned_call_rows_term xs) (data_list_term [Pair_Term (definition_site_value d) t]))\<in>positive_meaning key_fibre_system"
    using lookup by (simp add: site_data_term_def)
  show ?thesis using derivation_admission_step[OF checked actual_lookup] by (simp add: site_data_term_def)
qed

theorem derivation_admission_exact:
  "(102,z)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> derivation_admission_result z"
proof
  assume "(102,z)\<in>positive_meaning derivation_admission_system"
  then show "derivation_admission_result z" by (rule derivation_admission_sound)
next
  assume "derivation_admission_result z"
  then obtain E e pu pr root d t hs P G where shape:
    "z=derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs)"
    and source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G" and order: "distinct hs"
    and derived: "schema_graph_derives (positioned_program P) G root d t (set hs)"
    by (elim exE conjE) (rule that; assumption)
  show "(102,z)\<in>positive_meaning derivation_admission_system"
    using derivation_admission_complete[OF source package graph order derived] by (simp only: shape)
qed

corollary derivation_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(102,derivation_argument e u r n d t h)\<in>positive_meaning derivation_admission_system \<longleftrightarrow>
    (\<exists>pu pr root f hs P G. u=use_data_term pu \<and> r=Payload_Term pr \<and> n=definition_site_value root \<and>
      d=definition_site_value f \<and> h=positioned_call_rows_term hs \<and> native_package_at E pu pr P \<and>
      native_schema_graph_at E root G \<and> distinct hs \<and> schema_graph_derives (positioned_program P) G root f t (set hs))"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: derivation_admission_exact factor_term.inject) (use source unique in blast)
qed

corollary derivation_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs))\<in>positive_meaning derivation_admission_system \<longleftrightarrow>
    distinct hs \<and> (\<exists>P G. native_package_at E pu pr P \<and> native_schema_graph_at E root G \<and>
      schema_graph_derives (positioned_program P) G root d t (set hs))"
  by (simp only: derivation_admission_at_source[OF source] inj_eq[OF use_data_term_injective]
    factor_term.inject definition_site_value_eq positioned_call_rows_term_injective; blast)

corollary derivation_admission_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G"
  shows "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs))\<in>positive_meaning derivation_admission_system \<longleftrightarrow>
    distinct hs \<and> schema_graph_derives (positioned_program P) G root d t (set hs)"
  by (simp only: derivation_admission_on_values[OF source])
    (use package graph native_package_unique[OF _ package] native_schema_graph_unique[OF _ graph] in blast)

corollary derivation_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(102,derivation_argument e u r n d t h)\<in>positive_meaning derivation_admission_system \<longleftrightarrow>
    (102,derivation_argument f u r n d t h)\<in>positive_meaning derivation_admission_system"
  by (simp only: derivation_admission_at_source[OF assms(1)] derivation_admission_at_source[OF assms(2)])

corollary derivation_admission_orders:
  assumes source: "environment_value_presents E e" and order: "mset hs=mset ks"
  shows "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs))\<in>positive_meaning derivation_admission_system \<longleftrightarrow>
    (102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term ks))\<in>positive_meaning derivation_admission_system"
  using mset_eq_setD[OF order] mset_eq_imp_distinct_iff[OF order]
  by (simp only: derivation_admission_on_values[OF source])

corollary derivation_admission_boundary_unique:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G"
    and first: "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term hs))\<in>positive_meaning derivation_admission_system"
    and second: "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (positioned_call_rows_term ks))\<in>positive_meaning derivation_admission_system"
  shows "mset hs=mset ks"
proof -
  have left: "distinct hs" "schema_graph_derives (positioned_program P) G root d t (set hs)"
    using first by (simp only: derivation_admission_at_reads[OF source package graph]; blast)+
  have right: "distinct ks" "schema_graph_derives (positioned_program P) G root d t (set ks)"
    using second by (simp only: derivation_admission_at_reads[OF source package graph]; blast)+
  have same: "set hs=set ks" by (rule schema_graph_assumptions_unique[OF left(2) right(2)])
  show ?thesis by (simp only: distinct_source_mset[OF left(1)]) (use right(1) same in auto)
qed

corollary derivation_admission_closed_sound:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G"
    and checked: "(102,derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (Payload_Term []))\<in>positive_meaning derivation_admission_system"
  shows "(d,t)\<in>positive_meaning P"
proof -
  have derived: "schema_graph_derives (positioned_program P) G root d t {}"
    using derivation_admission_at_reads[OF source package graph, where hs="[]" and d=d and t=t] checked by simp
  have truth: "(d,t)\<in>positive_meaning (positioned_program P)" by (rule schema_graph_closed_sound[OF derived])
  show ?thesis using truth by (simp only: positioned_program_meaning[OF native_package_system_formed[OF package]])
qed

section \<open>One fixed native program precedes every future derivation argument\<close>

lemma derivation_operation_components:
  "(99,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (99,t)\<in>positive_meaning row_qualification_system"
  "(100,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (100,t)\<in>positive_meaning keyed_row_join_system"
  "(101,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (101,t)\<in>positive_meaning proof_claim_checking_system"
  using derivation_admission_old_meaning[of 99 t] proof_claim_checking_components(5)[of t]
    derivation_admission_old_meaning[of 100 t] proof_claim_checking_components(6)[of t]
    derivation_admission_old_meaning[of 101 t] by auto

abbreviation derivation_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "derivation_operation_result d t \<equiv>
    if d=99 then row_qualification_result t else if d=100 then keyed_row_join_result t
    else if d=101 then proof_claim_checking_result t else derivation_admission_result t"

lemma derivation_operations_exact:
  assumes "d\<in>{99,100,101,102}"
  shows "(d,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> derivation_operation_result d t"
proof -
  consider (qualification) "d=99" | (join) "d=100" | (claims) "d=101" | (derivation) "d=102" using assms by auto
  then show ?thesis
  proof cases
    case qualification
    show ?thesis by (simp only: qualification derivation_operation_components row_qualification_exact; simp)
  next
    case join
    show ?thesis by (simp only: join derivation_operation_components keyed_row_join_exact; simp)
  next
    case claims
    show ?thesis by (simp only: claims derivation_operation_components proof_claim_checking_exact; simp)
  next
    case derivation
    show ?thesis by (simp only: derivation derivation_admission_exact; simp)
  qed
qed

theorem native_derivation_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {99::nat,100,101,102} \<and>
    (\<forall>d\<in>{99,100,101,102}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> derivation_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions derivation_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions derivation_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed derivation_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning derivation_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF derivation_admission_system_formed] by blast
  have sites: "inj_on g {99,100,101,102}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {99,100,101,102}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{99,100,101,102}" and tf: "term_formed t"
    have member: "d\<in>system_definitions derivation_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed derivation_admission_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning derivation_admission_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> derivation_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member derivation_operations_exact[OF selected] in \<open>auto simp: derivation_admission_call\<close>)
  qed
qed


text \<open>
  The root lookup forces a nonempty complete traversal. Every claim uses an
  actual node in one admitted native graph and the same actual native package.
  Shared nodes have one call in the functional table. Its keys are exactly
  the root's reachable nodes, and its assertion filter is the exact identified
  assumption boundary in every complete distinct presentation order.

  All four entries have exact contracts over every term and preserve all
  earlier meanings. Eight ordinary clauses give one fixed closed native
  program with four distinct sites before all future formed operands and
  retain its canonical environment. The resulting program has one hundred
  and three definitions and one hundred and sixty-seven clauses.

  A derivation with no assertion establishes the supplied call's positive
  meaning. Conditional assertions acquire no truth through checking. Joining
  an actual application to its derivation and checking closed replay retention
  is a further requirement; full transition protocol, reflection, and genesis checking
  also remain to be derived through ordinary clauses.
\<close>

end
