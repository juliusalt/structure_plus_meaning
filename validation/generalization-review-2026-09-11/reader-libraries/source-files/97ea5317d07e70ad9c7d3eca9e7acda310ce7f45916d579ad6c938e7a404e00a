theory Factor_Quotation_Admission
  imports Factor_Data_Collection_Operations
begin

section \<open>Complete quotation operands and their metadata\<close>

abbreviation term_quotation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "term_quotation_argument e u r t i k \<equiv> citation_observation_argument e u r (Pair_Term t (Pair_Term i k))"

abbreviation term_quotation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "term_quotation_pattern e u r t i k \<equiv> citation_observation_pattern e u r (Pattern_Pair t (Pattern_Pair i k))"

abbreviation quotation_admission_result :: "factor_term \<Rightarrow> bool" where
  "quotation_admission_result z \<equiv>
    \<exists>E e u r t Is Ks. z=term_quotation_argument e (use_data_term u) (Payload_Term r) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
      environment_value_presents E e \<and> distinct Is \<and> distinct Ks \<and>
      term_quoted_at E u r t (set Is) (set Ks)"

lemma quotation_result_at_source:
  assumes source: "environment_value_presents E e"
  shows "quotation_admission_result (term_quotation_argument e u r t i k) \<longleftrightarrow>
    (\<exists>v a Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> term_quoted_at E v a t (set Is) (set Ks))"
proof
  assume admitted: "quotation_admission_result (term_quotation_argument e u r t i k)"
  obtain F v a Is Ks where parts: "u=use_data_term v" "r=Payload_Term a"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "environment_value_presents F e" "distinct Is" "distinct Ks" "term_quoted_at F v a t (set Is) (set Ks)"
    using admitted by auto
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(5) source])
  show "\<exists>v a Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> term_quoted_at E v a t (set Is) (set Ks)"
    by (rule exI[of _ v], rule exI[of _ a], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts same in simp)
next
  assume "\<exists>v a Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> term_quoted_at E v a t (set Is) (set Ks)"
  then obtain v a Is Ks where parts: "u=use_data_term v" "r=Payload_Term a"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks" "term_quoted_at E v a t (set Is) (set Ks)" by blast
  show "quotation_admission_result (term_quotation_argument e u r t i k)"
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ v], rule exI[of _ a],
      rule exI[of _ t], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts source in simp)
qed

lemma quotation_result_on_source:
  assumes source: "environment_value_presents E e"
  shows "quotation_admission_result (term_quotation_argument e (use_data_term u) (Payload_Term r) t i k)
    \<longleftrightarrow> (\<exists>Is Ks. i=data_list_term (map Payload_Term Is) \<and>
      k=data_list_term (map Payload_Term Ks) \<and> distinct Is \<and> distinct Ks \<and>
      term_quoted_at E u r t (set Is) (set Ks))"
  by (subst quotation_result_at_source[OF source])
    (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj]
      dest: injD[OF use_data_term_injective])

lemma distinct_singleton_enumeration:
  assumes "distinct xs" "set xs={x}"
  shows "xs=[x]"
proof (cases xs)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons a ys)
  have first: "a=x" and rest: "set ys\<subseteq>{x}" "a\<notin>set ys"
    using assms by (auto simp: Cons)
  have "set ys={}" by (rule set_eqI) (use first rest in auto)
  then show ?thesis using Cons first by simp
qed

lemma quotation_interior_lists:
  assumes "distinct ps" "r\<notin>set ps" "distinct ls" "distinct qs" "distinct is"
  shows "mset (r#ps@ls@qs)=mset is \<longleftrightarrow>
    insert r (set ps)\<inter>(set ls\<union>set qs)={} \<and> set ls\<inter>set qs={} \<and>
    set is=insert r (set ps\<union>set ls\<union>set qs)"
proof -
  have comparison: "mset (r#ps@ls@qs)=mset is \<longleftrightarrow>
    distinct (r#ps@ls@qs) \<and> set (r#ps@ls@qs)=set is"
    using distinct_source_mset[OF assms(5), of "r#ps@ls@qs"] by auto
  show ?thesis by (subst comparison) (use assms in \<open>auto simp: distinct_append\<close>)
qed

section \<open>Three ordinary clauses with actual recursive callees\<close>

definition quotation_payload_schema :: "(nat,nat,nat) factor_schema" where
  "quotation_payload_schema=data_rule
    (term_quotation_pattern data_x data_y data_z data_w (data_list_pattern [data_z]) (Pattern_Payload []))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (1,29,headed_material_pattern (Pattern_Variable 4) data_z
       (Pattern_Payload []) (Pattern_Payload []) (data_list_pattern [data_w]))}"

definition quotation_target_schema :: "(nat,nat,nat) factor_schema" where
  "quotation_target_schema=data_rule
    (term_quotation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (data_list_pattern [Pattern_Variable 5]))
    {(0,42,citation_reading_pattern data_x data_y data_z
       (Pattern_Pair (data_list_pattern [Pattern_Variable 5]) (Pattern_Variable 6)) (Pattern_Variable 4)),
     (1,40,citation_observation_pattern data_x data_y
       (Pattern_Pair (data_list_pattern [Pattern_Variable 5]) (Pattern_Variable 6)) (Pattern_Variable 7)),
     (2,45,Pattern_Pair data_w (Pattern_Variable 7))}"

definition quotation_pair_schema :: "(nat,nat,nat) factor_schema" where
  "quotation_pair_schema=data_rule
    (term_quotation_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
      (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 7)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10),
         Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 11)])),
     (2,50,term_quotation_pattern data_x data_y (Pattern_Variable 10) data_w
       (Pattern_Variable 12) (Pattern_Variable 13)),
     (3,50,term_quotation_pattern data_x data_y (Pattern_Variable 11) (Pattern_Variable 4)
       (Pattern_Variable 14) (Pattern_Variable 15)),
     (4,46,collection_join_pattern (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9])
       (Pattern_Variable 12) (Pattern_Variable 16)),
     (5,46,collection_join_pattern (Pattern_Variable 16) (Pattern_Variable 14) (Pattern_Variable 17)),
     (6,6,Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 5)),
     (7,48,collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 15) (Pattern_Variable 6)),
     (8,49,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))}"

definition quotation_admission_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "quotation_admission_clauses={(0,quotation_payload_schema),(1,quotation_target_schema),(2,quotation_pair_schema)}"

definition quotation_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "quotation_admission_system=add_view_definition payload_disjoint_system 50 data_x quotation_admission_clauses"

lemma quotation_admission_system_formed [simp]: "schema_system_formed quotation_admission_system"
  unfolding quotation_admission_system_def
  by (rule add_recursive_definition_formed[OF payload_disjoint_system_formed])
    (auto simp: quotation_admission_clauses_def quotation_payload_schema_def quotation_target_schema_def
      quotation_pair_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma quotation_admission_definitions [simp]:
  "system_definitions quotation_admission_system=insert 50 (system_definitions payload_disjoint_system)"
  by (simp add: quotation_admission_system_def)

lemma quotation_admission_call:
  "schema_call_formed quotation_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions quotation_admission_system \<and> term_formed t"
  using added_variable_calls[OF payload_disjoint_system_formed
    quotation_admission_system_formed[unfolded quotation_admission_system_def] payload_disjoint_call]
  by (simp only: quotation_admission_system_def[symmetric])

lemma quotation_admission_old_meaning:
  assumes "d\<in>system_definitions payload_disjoint_system"
  shows "(d,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning payload_disjoint_system"
  using added_definition_preserves_old(2)[OF payload_disjoint_system_formed
    quotation_admission_system_formed[unfolded quotation_admission_system_def], of d t] assms
  by (auto simp: quotation_admission_system_def)

lemma quotation_admission_clause [simp]:
  "((50,c),S)\<in>system_clauses quotation_admission_system \<longleftrightarrow> (c,S)\<in>quotation_admission_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses payload_disjoint_system \<Longrightarrow>
    d\<in>system_definitions payload_disjoint_system" for d c S
    using payload_disjoint_system_formed unfolding schema_system_formed_def by blast
  have absent: "((50,c),S)\<notin>system_clauses payload_disjoint_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: quotation_admission_system_def)
qed

lemma quotation_admission_projection_meaning:
  assumes "d\<in>system_definitions target_projection_system"
  shows "(d,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_projection_system"
  using quotation_admission_old_meaning[of d t] payload_disjoint_old_meaning[of d t]
    data_union_old_meaning[of d t] data_subset_old_meaning[of d t] data_append_old_meaning[of d t] assms by auto

lemma quotation_admission_reading_meaning:
  assumes "d\<in>system_definitions citation_reading_system"
  shows "(d,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning citation_reading_system"
  using quotation_admission_projection_meaning[of d t] target_projection_old_meaning[of d t]
    located_admission_old_meaning[of d t] anchored_admission_old_meaning[of d t] assms by auto

lemma quotation_admission_record_meaning:
  assumes "d\<in>system_definitions record_admission_system"
  shows "(d,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning record_admission_system"
  using quotation_admission_reading_meaning[of d t] citation_reading_old_meaning[of d t]
    citation_location_old_meaning[of d t] citation_interpretation_old_meaning[of d t]
    citation_resolution_old_meaning[of d t] binding_lookup_old_meaning[of d t]
    artifact_lookup_old_meaning[of d t] citation_admission_old_meaning[of d t]
    target_admission_old_meaning[of d t] assms by auto

lemma quotation_admission_components:
  "(37,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(29,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (29,t)\<in>positive_meaning headed_material_system"
  "(42,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (42,t)\<in>positive_meaning citation_reading_system"
  "(40,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (40,t)\<in>positive_meaning citation_interpretation_system"
  "(45,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (45,t)\<in>positive_meaning target_projection_system"
  "(34,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(46,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(6,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(48,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (48,t)\<in>positive_meaning data_union_system"
  "(49,t)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using quotation_admission_reading_meaning[of 37 t] citation_reading_components(2)[of t]
    quotation_admission_record_meaning[of 29 t] record_admission_components(1)[of t]
    quotation_admission_reading_meaning[of 42 t] quotation_admission_reading_meaning[of 40 t]
    citation_reading_components(3)[of t] quotation_admission_projection_meaning[of 45 t]
    quotation_admission_record_meaning[of 34 t] quotation_admission_old_meaning[of 46 t]
    payload_disjoint_prior_entries(2)[of t] quotation_admission_projection_meaning[of 6 t]
    target_projection_bag_meaning[of 6 t] quotation_admission_old_meaning[of 48 t]
    payload_disjoint_prior_entries(4)[of t] quotation_admission_old_meaning[of 49 t] by auto

lemma quotation_payload_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and leaf: "(29,headed_material_argument a r (Payload_Term []) (Payload_Term []) (data_list_term [v]))
      \<in>positive_meaning headed_material_system"
  shows "(50,term_quotation_argument e u r v (data_list_term [r]) (Payload_Term []))
    \<in>positive_meaning quotation_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed a" "term_formed r" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF leaf]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else a"
  have result: "(50,evaluate_pattern ?h (schema_conclusion quotation_payload_schema))
    \<in>positive_meaning quotation_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed lookup leaf in \<open>auto simp: quotation_admission_clauses_def quotation_payload_schema_def
        schema_variables_def quotation_admission_call quotation_admission_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: quotation_payload_schema_def)
qed

lemma quotation_target_step:
  assumes reading: "(42,citation_reading_argument e u r (Pair_Term (data_list_term [s]) a) i)
      \<in>positive_meaning citation_reading_system"
    and interpreted_call: "(40,citation_observation_argument e u (Pair_Term (data_list_term [s]) a) v)
      \<in>positive_meaning citation_interpretation_system"
    and projection: "(45,Pair_Term t v)\<in>positive_meaning target_projection_system"
  shows "(50,term_quotation_argument e u r t i (data_list_term [s]))\<in>positive_meaning quotation_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed t"
    "term_formed i" "term_formed s" "term_formed a" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF interpreted_call]]
      schema_call_formed_target[OF positive_meaning_formed[OF projection]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then t
    else if j=4 then i else if j=5 then s else if j=6 then a else v"
  have result: "(50,evaluate_pattern ?h (schema_conclusion quotation_target_schema))
    \<in>positive_meaning quotation_admission_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed reading interpreted_call projection in \<open>auto simp: quotation_admission_clauses_def
        quotation_target_schema_def schema_variables_def quotation_admission_call quotation_admission_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: quotation_target_schema_def)
qed

lemma quotation_pair_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p l,Pair_Term q m]))
      \<in>positive_meaning record_admission_system"
    and left: "(50,term_quotation_argument e u l x li lk)\<in>positive_meaning quotation_admission_system"
    and right: "(50,term_quotation_argument e u m y ri rk)\<in>positive_meaning quotation_admission_system"
    and prefix: "(46,collection_join_argument (data_list_term [r,p,q]) li d)\<in>positive_meaning data_append_system"
    and joined: "(46,collection_join_argument d ri j)\<in>positive_meaning data_append_system"
    and interior: "(6,Pair_Term j i)\<in>positive_meaning bag_comparison_system"
    and slots: "(48,collection_join_argument lk rk k)\<in>positive_meaning data_union_system"
    and boundary: "(49,Pair_Term i k)\<in>positive_meaning payload_disjoint_system"
  shows "(50,term_quotation_argument e u r (Pair_Term x y) i k)\<in>positive_meaning quotation_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed x" "term_formed y"
    "term_formed i" "term_formed k" "term_formed a" "term_formed p" "term_formed q" "term_formed l" "term_formed m"
    "term_formed li" "term_formed lk" "term_formed ri" "term_formed rk" "term_formed d" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF left]]
      schema_call_formed_target[OF positive_meaning_formed[OF right]]
      schema_call_formed_target[OF positive_meaning_formed[OF prefix]]
      schema_call_formed_target[OF positive_meaning_formed[OF joined]]
      schema_call_formed_target[OF positive_meaning_formed[OF interior]]
      schema_call_formed_target[OF positive_meaning_formed[OF slots]]
      schema_call_formed_target[OF positive_meaning_formed[OF boundary]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then x
    else if n=4 then y else if n=5 then i else if n=6 then k else if n=7 then a
    else if n=8 then p else if n=9 then q else if n=10 then l else if n=11 then m
    else if n=12 then li else if n=13 then lk else if n=14 then ri else if n=15 then rk
    else if n=16 then d else j"
  have result: "(50,evaluate_pattern ?h (schema_conclusion quotation_pair_schema))
    \<in>positive_meaning quotation_admission_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use formed assms in \<open>auto simp: quotation_admission_clauses_def quotation_pair_schema_def
        schema_variables_def quotation_admission_call quotation_admission_components octets_formed_def\<close>)
  show ?thesis using result by (simp add: quotation_pair_schema_def)
qed

section \<open>Every accepted term has the independently defined reading\<close>

theorem quotation_admission_sound:
  assumes holds: "(50,z)\<in>positive_meaning quotation_admission_system"
  shows "quotation_admission_result z"
proof -
  have invariant: "(50::nat)=50 \<longrightarrow> quotation_admission_result z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=50 \<longrightarrow> quotation_admission_result z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses quotation_admission_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed quotation_admission_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning quotation_admission_system \<and>
        (e=50 \<longrightarrow> quotation_admission_result (evaluate_pattern h p))"
    have available: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning quotation_admission_system"
      using support by blast
    show "d=50 \<longrightarrow> quotation_admission_result (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=50"
      then consider (payload) "S=quotation_payload_schema" | (target) "S=quotation_target_schema" | (pair) "S=quotation_pair_schema"
        using clause by (auto simp: quotation_admission_clauses_def)
      then show "quotation_admission_result (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case payload
        have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
          "(29,headed_material_argument (h 4) (h 2) (Payload_Term []) (Payload_Term []) (data_list_term [h 3]))
            \<in>positive_meaning headed_material_system"
          using available by (auto simp: payload quotation_payload_schema_def quotation_admission_components)
        obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
          "artifact_at E u R" "artifact_value_presents R (h 4)"
          using calls(1) by (auto simp: artifact_lookup_exact)
        obtain r v where leaf: "h 2=Payload_Term r" "h 3=Payload_Term v" "payload_leaf_at R r v"
          using calls(2) by (simp only: headed_material_leaf_fields[OF source(4)]) blast
        have formed: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
        have reading: "term_quoted_at E u r (Payload_Term v) {r} {}"
          by (rule term_quoted_at.payload[OF formed source(3) leaf(3)])
        show ?thesis
          by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
            rule exI[of _ "Payload_Term v"], rule exI[of _ "[r]"], rule exI[of _ "[]"])
            (use source leaf reading in \<open>simp add: payload quotation_payload_schema_def\<close>)
      next
        case target
        let ?c="Pair_Term (data_list_term [h 5]) (h 6)"
        have calls: "(42,citation_reading_argument (h 0) (h 1) (h 2) ?c (h 4))
            \<in>positive_meaning citation_reading_system"
          "(40,citation_observation_argument (h 0) (h 1) ?c (h 7))\<in>positive_meaning citation_interpretation_system"
          "(45,Pair_Term (h 3) (h 7))\<in>positive_meaning target_projection_system"
          using available by (auto simp: target quotation_target_schema_def quotation_admission_components)
        obtain E u r c Is R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
          "h 2=Payload_Term r" "?c=citation_data_term c" "h 4=data_list_term (map Payload_Term Is)"
          "distinct Is" "artifact_at E u R" "citation_at R r c (set Is)"
          using calls(1) by (auto simp: citation_reading_exact)
        obtain s where slot: "h 5=Payload_Term s" "citation_slots c={s}"
          using citation_data_external_fields[OF source(4)[symmetric]] by blast
        obtain x where projected: "h 3=Target_Term x" "target_value_presents x (h 7)"
          using calls(3) by (auto simp: target_projection_exact)
        have interpreted: "interpret_citation E u c x"
          using calls(2) by (simp only: source(2,4) citation_interpretation_on_values[OF source(1) projected(2)])
        have formed: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
        have external: "citation_slots c\<noteq>{}" using slot(2) by simp
        have reading: "term_quoted_at E u r (Target_Term x) (set Is) {s}"
          using term_quoted_at.target[OF formed source(7,8) external interpreted] by (simp add: slot)
        show ?thesis
          by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
            rule exI[of _ "Target_Term x"], rule exI[of _ Is], rule exI[of _ "[s]"])
            (use source slot projected reading in \<open>simp add: target quotation_target_schema_def\<close>)
      next
        case pair
        have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
          "(34,rooted_rows_argument (h 7) (h 2) (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))
            \<in>positive_meaning record_admission_system"
          "(46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (h 12) (h 16))\<in>positive_meaning data_append_system"
          "(46,collection_join_argument (h 16) (h 14) (h 17))\<in>positive_meaning data_append_system"
          "(6,Pair_Term (h 17) (h 5))\<in>positive_meaning bag_comparison_system"
          "(48,collection_join_argument (h 13) (h 15) (h 6))\<in>positive_meaning data_union_system"
          "(49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system"
          using available by (auto simp: pair quotation_pair_schema_def quotation_admission_components)
        have left_result: "quotation_admission_result (term_quotation_argument (h 0) (h 1) (h 10) (h 3) (h 12) (h 13))"
          using support[rule_format, of 2 50 "term_quotation_pattern data_x data_y (Pattern_Variable 10) data_w
            (Pattern_Variable 12) (Pattern_Variable 13)"]
          by (auto simp: pair quotation_pair_schema_def)
        have right_result: "quotation_admission_result (term_quotation_argument (h 0) (h 1) (h 11) (h 4) (h 14) (h 15))"
          using support[rule_format, of 3 50 "term_quotation_pattern data_x data_y (Pattern_Variable 11) (Pattern_Variable 4)
            (Pattern_Variable 14) (Pattern_Variable 15)"]
          by (auto simp: pair quotation_pair_schema_def)
        obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
          "artifact_at E u R" "artifact_value_presents R (h 7)"
          using calls(1) by (auto simp: artifact_lookup_exact)
        obtain r p l q m where rec: "h 2=Payload_Term r" "h 8=Payload_Term p" "h 10=Payload_Term l"
          "h 9=Payload_Term q" "h 11=Payload_Term m" "record_at R r [p,q] [l,m]"
          using calls(2) by (simp only: record_admission_pair_fields[OF source(4)]) blast
        obtain L A where left: "h 12=data_list_term (map Payload_Term L)" "h 13=data_list_term (map Payload_Term A)"
          "distinct L" "distinct A" "term_quoted_at E u l (h 3) (set L) (set A)"
          using left_result by (simp only: source(2) rec(3) quotation_result_on_source[OF source(1)]) blast
        obtain Q B where right: "h 14=data_list_term (map Payload_Term Q)" "h 15=data_list_term (map Payload_Term B)"
          "distinct Q" "distinct B" "term_quoted_at E u m (h 4) (set Q) (set B)"
          using right_result by (simp only: source(2) rec(5) quotation_result_on_source[OF source(1)]) blast
        obtain Is Ks where boundary: "h 5=data_list_term (map Payload_Term Is)" "h 6=data_list_term (map Payload_Term Ks)"
          "distinct Is" "distinct Ks" "set Is\<inter>set Ks={}"
          using calls(7) by (auto simp: payload_disjoint_exact)
        have prefix: "h 16=data_list_term (map Payload_Term (r#p#q#L))"
          using calls(3) by (simp only: rec(1,2,4) left(1) data_append_at_lists) auto
        have joined: "h 17=data_list_term (map Payload_Term (r#p#q#L@Q))"
          using calls(4) by (simp only: prefix right(1) data_append_at_lists) auto
        have comparison: "mset (r#p#q#L@Q)=mset Is"
          using calls(5) by (simp only: joined boundary(1) bag_comparison_lists
            injective_mapped_multisets[OF payload_term_inj])
        have slots: "set Ks=set A\<union>set B"
          using calls(6) by (simp only: left(2) right(2) boundary(2) data_union_payload_lists)
        have ports: "distinct [p,q]" "r\<notin>set [p,q]"
          using record_at_preserves_socket_occurrences[OF rec(6)] by auto
        have separation: "insert r (set [p,q])\<inter>(set L\<union>set Q)={}" "set L\<inter>set Q={}"
          "set Is=insert r (set [p,q]\<union>set L\<union>set Q)"
          using quotation_interior_lists[OF ports left(3) right(3) boundary(3)] comparison by auto
        have outside: "insert r (set [p,q]\<union>set L\<union>set Q)\<inter>(set A\<union>set B)={}"
          using boundary(5) by (simp only: separation(3)[symmetric] slots[symmetric])
        have formed: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
        have reading: "term_quoted_at E u r (Pair_Term (h 3) (h 4)) (set Is) (set Ks)"
          using term_quoted_at.pair[OF formed source(3) rec(6) left(5) right(5) separation(1,2) outside]
          by (simp only: separation(3)[symmetric] slots[symmetric])
        show ?thesis
          by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r],
            rule exI[of _ "Pair_Term (h 3) (h 4)"], rule exI[of _ Is], rule exI[of _ Ks])
            (use source rec boundary reading in \<open>simp add: pair quotation_pair_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

section \<open>Every complete presentation of a quotation is accepted\<close>

theorem quotation_admission_complete:
  assumes quote: "term_quoted_at E u r t I K" and source: "environment_value_presents E e"
    and order: "distinct Is" "distinct Ks" and collections: "set Is=I" "set Ks=K"
  shows "(50,term_quotation_argument e (use_data_term u) (Payload_Term r) t
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
    \<in>positive_meaning quotation_admission_system"
  using quote source order collections
proof (induction arbitrary: e Is Ks rule: term_quoted_at.induct)
  case (target u R r c I t)
  obtain s a where shape: "citation_data_term c=Pair_Term (data_list_term [Payload_Term s]) a"
    "citation_slots c={s}"
    using citation_data_external_shape[OF target.hyps(4)] by blast
  have slots: "Ks=[s]"
    by (rule distinct_singleton_enumeration[OF target.prems(3)])
      (use target.prems(5) shape(2) in simp)
  have raw: "citation_at R r c (set Is)" using target.hyps(3) target.prems(4) by simp
  have reading: "(42,citation_reading_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (data_list_term [Payload_Term s]) a) (data_list_term (map Payload_Term Is)))
      \<in>positive_meaning citation_reading_system"
    using citation_reading_complete[OF target.prems(1) target.hyps(2) target.prems(2) raw]
    by (simp only: shape(1))
  obtain v where presented_value: "target_value_presents t v"
    using target_value_presents_total[OF citation_interpretation_formed[OF target.hyps(5)]] by blast
  have interpreted_call: "(40,citation_observation_argument e (use_data_term u)
      (Pair_Term (data_list_term [Payload_Term s]) a) v)\<in>positive_meaning citation_interpretation_system"
    using target.hyps(5)
    by (simp only: shape(1)[symmetric] citation_interpretation_on_values[OF target.prems(1) presented_value])
  have projection: "(45,Pair_Term (Target_Term t) v)\<in>positive_meaning target_projection_system"
    by (rule target_projection_complete[OF presented_value])
  show ?case using quotation_target_step[OF reading interpreted_call projection] by (simp add: slots)
next
  case (pair u R r ps l q x L A y Q B)
  have finite: "finite L" "finite A" "finite Q" "finite B"
    using term_quoted_finite[OF pair.hyps(4)] term_quoted_finite[OF pair.hyps(5)] by auto
  obtain Ls where ls: "set Ls=L" "distinct Ls" using finite_distinct_list[OF finite(1)] by blast
  obtain As where as_rows: "set As=A" "distinct As" using finite_distinct_list[OF finite(2)] by blast
  obtain Qs where qs: "set Qs=Q" "distinct Qs" using finite_distinct_list[OF finite(3)] by blast
  obtain Bs where bs_rows: "set Bs=B" "distinct Bs" using finite_distinct_list[OF finite(4)] by blast
  have left: "(50,term_quotation_argument e (use_data_term u) (Payload_Term l) x
      (data_list_term (map Payload_Term Ls)) (data_list_term (map Payload_Term As)))
      \<in>positive_meaning quotation_admission_system"
    by (rule pair.IH(1)[OF pair.prems(1) ls(2) as_rows(2) ls(1) as_rows(1)])
  have right: "(50,term_quotation_argument e (use_data_term u) (Payload_Term q) y
      (data_list_term (map Payload_Term Qs)) (data_list_term (map Payload_Term Bs)))
      \<in>positive_meaning quotation_admission_system"
    by (rule pair.IH(2)[OF pair.prems(1) qs(2) bs_rows(2) qs(1) bs_rows(1)])
  obtain p s where ports: "ps=[p,s]"
    using record_at_preserves_socket_occurrences[OF pair.hyps(3)] by (auto simp: length_Suc_conv)
  have ports_distinct: "distinct [p,s]" "r\<notin>set [p,s]"
    using record_at_preserves_socket_occurrences[OF pair.hyps(3)] by (auto simp: ports)
  have rf: "exact_formed R" using pair.hyps(1,2) by (auto simp: environment_formed_def)
  obtain a where material: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using pair.prems(1) pair.hyps(2) material by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term p) (Payload_Term l),Pair_Term (Payload_Term s) (Payload_Term q)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF material])
      (use pair.hyps(3) in \<open>auto simp: ports\<close>)
  have reading: "term_quoted_at E u r (Pair_Term x y) (insert r (set ps\<union>L\<union>Q)) (A\<union>B)"
    by (rule term_quoted_at.pair[OF pair.hyps])
  have addresses: "\<forall>a\<in>insert r (set ps\<union>L\<union>Q)\<union>(A\<union>B). octets_formed a"
    by (rule term_quoted_addresses_formed[OF reading])
  have data: "data_elements (map Payload_Term (r#p#s#Ls))" "data_elements (map Payload_Term Qs)"
    "data_elements (map Payload_Term Is)" "data_elements (map Payload_Term Ks)"
    "data_elements (map Payload_Term As)" "data_elements (map Payload_Term Bs)"
    using addresses by (auto simp: ports ls(1) qs(1) as_rows(1) bs_rows(1) pair.prems(4,5))
  have comparison: "mset (r#p#s#Ls@Qs)=mset Is"
    using quotation_interior_lists[OF ports_distinct ls(2) qs(2) pair.prems(2)]
      pair.hyps(6,7) pair.prems(4) by (auto simp: ports ls(1) qs(1))
  let ?d="data_list_term (map Payload_Term (r#p#s#Ls))"
  let ?j="data_list_term (map Payload_Term (r#p#s#Ls@Qs))"
  have prefix: "(46,collection_join_argument (data_list_term [Payload_Term r,Payload_Term p,Payload_Term s])
      (data_list_term (map Payload_Term Ls)) ?d)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use data in auto)
  have joined: "(46,collection_join_argument ?d (data_list_term (map Payload_Term Qs)) ?j)
      \<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use data in auto)
  have interior: "(6,Pair_Term ?j (data_list_term (map Payload_Term Is)))\<in>positive_meaning bag_comparison_system"
    by (simp only: bag_comparison_lists injective_mapped_multisets[OF payload_term_inj])
      (use data comparison in auto)
  have slots: "(48,collection_join_argument (data_list_term (map Payload_Term As))
      (data_list_term (map Payload_Term Bs)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning data_union_system"
    by (simp only: data_union_payload_lists) (use data pair.prems(5) as_rows(1) bs_rows(1) in auto)
  have boundary: "(49,Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp only: payload_disjoint_lists)
      (use pair.prems(2-5) pair.hyps(8) addresses in auto)
  show ?case by (rule quotation_pair_step[OF lookup rec left right prefix joined interior slots boundary])
next
  case (payload u R r v)
  have interior: "Is=[r]"
    by (rule distinct_singleton_enumeration[OF payload.prems(2)]) (rule payload.prems(4))
  have slots: "Ks=[]" using payload.prems(5) by simp
  have rf: "exact_formed R" using payload.hyps(1,2) by (auto simp: environment_formed_def)
  obtain a where material: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using payload.prems(1) payload.hyps(2) material by (auto simp: artifact_lookup_exact)
  have leaf: "(29,headed_material_argument a (Payload_Term r) (Payload_Term []) (Payload_Term [])
      (data_list_term [Payload_Term v]))\<in>positive_meaning headed_material_system"
    using payload.hyps(3) by (simp add: headed_material_leaf[OF material, simplified])
  show ?case using quotation_payload_step[OF lookup leaf] by (simp add: interior slots)
qed

theorem quotation_admission_exact:
  "(50,z)\<in>positive_meaning quotation_admission_system \<longleftrightarrow> quotation_admission_result z"
  using quotation_admission_sound quotation_admission_complete by blast

corollary quotation_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(50,term_quotation_argument e u r t i k)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (\<exists>v a Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> term_quoted_at E v a t (set Is) (set Ks))"
  by (simp only: quotation_admission_exact quotation_result_at_source[OF source])

corollary quotation_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(50,term_quotation_argument e (use_data_term u) (Payload_Term r) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    distinct Is \<and> distinct Ks \<and> term_quoted_at E u r t (set Is) (set Ks)"
  by (simp only: quotation_admission_exact quotation_result_on_source[OF source]
    data_list_term_injective injective_mapped_lists[OF payload_term_inj]) auto

corollary quotation_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(50,term_quotation_argument e u r t i k)\<in>positive_meaning quotation_admission_system \<longleftrightarrow>
    (50,term_quotation_argument f u r t i k)\<in>positive_meaning quotation_admission_system"
  by (simp only: quotation_admission_at_source[OF assms(1)] quotation_admission_at_source[OF assms(2)])

corollary quotation_admission_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(50,term_quotation_argument e u r t i k)\<in>positive_meaning quotation_admission_system"
    and second: "(50,term_quotation_argument e u r s j w)\<in>positive_meaning quotation_admission_system"
  shows "t=s \<and> (6,Pair_Term i j)\<in>positive_meaning bag_comparison_system \<and>
    (6,Pair_Term k w)\<in>positive_meaning bag_comparison_system"
proof -
  obtain v a Is Ks where left: "u=use_data_term v" "r=Payload_Term a"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks" "term_quoted_at E v a t (set Is) (set Ks)"
    using first by (auto simp: quotation_admission_at_source[OF source])
  obtain Js Ws where right: "j=data_list_term (map Payload_Term Js)" "w=data_list_term (map Payload_Term Ws)"
    "distinct Js" "distinct Ws" "term_quoted_at E v a s (set Js) (set Ws)"
    using second by (simp only: left(1,2) quotation_admission_exact quotation_result_on_source[OF source]) blast
  have same: "t=s" "set Is=set Js" "set Ks=set Ws"
    using term_quoted_unique[OF left(7) right(5)] by auto
  have counts: "mset Is=mset Js" "mset Ks=mset Ws"
    using distinct_source_mset[OF left(5), of Js] distinct_source_mset[OF left(6), of Ws] right(3,4) same(2,3) by auto
  have formed: "term_formed i" "term_formed j" "term_formed k" "term_formed w"
    using schema_call_formed_target[OF positive_meaning_formed[OF first]]
      schema_call_formed_target[OF positive_meaning_formed[OF second]] by auto
  show ?thesis using same(1) counts formed
    by (simp add: left(3,4) right(1,2) bag_comparison_lists data_list_term_formed
      injective_mapped_multisets[OF payload_term_inj])
qed

section \<open>One fixed native reader accepts every future formed operand\<close>

theorem native_term_quotation_checking:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> quotation_admission_result t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions quotation_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed quotation_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning quotation_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF quotation_admission_system_formed] by blast
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 50"], intro conjI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
  next
    fix t :: factor_term
    assume tf: "term_formed t"
    have member: "50\<in>system_definitions quotation_admission_system" by simp
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g 50) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed quotation_admission_system 50 t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (50,t)\<in>positive_meaning quotation_admission_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 50) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> quotation_admission_result t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf in \<open>auto simp: quotation_admission_call quotation_admission_exact\<close>)
  qed
qed

text \<open>
  The three ordinary clauses derive the existing recursive quotation grammar.
  Payloads use the complete headed material equation. Targets join structural
  external citation reading, interpretation, and the existing literal projection.
  No constructor name is attached as data, and no new observation is introduced.

  Pair interiors concatenate the root, ordered sockets, and both child interiors.
  Counted comparison against the proposed distinct interior admits every complete
  order and enforces separation of the record and both child interiors. External slots
  use membership union and may be shared by both children. The final boundary
  requires distinct interior and slot enumerations and separates those two sets.

  Exactness holds over all input terms, with every complete environment
  presentation and every distinct metadata order. The recovered term and both
  metadata sets are unique. The one finite program is compiled before arbitrary
  future operands, admits recursion through the generic positive meaning, and
  preserves every earlier entry and its canonical native package environment.
  Higher grammar admission and the complete transition protocol remain separate.
\<close>

end
