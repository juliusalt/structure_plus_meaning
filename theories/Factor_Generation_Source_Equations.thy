theory Factor_Generation_Source_Equations
  imports Factor_Generation_Field_Admission
begin

section \<open>The actual core report admits its entire expected value\<close>

lemma generation_core_report_valuation:
  "(151,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8}. term_formed (h i)) \<and>
      t=generation_fields_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (139,generation_fields_term (h 3) (h 4) (h 5) (h 6))\<in>positive_meaning generation_value_system \<and>
      (148,generation_fields_argument (h 0) (h 1) (h 2) (h 3) (h 7) (h 5) (h 6))
        \<in>positive_meaning generation_source_system \<and>
      (150,context_relation_argument (Pair_Term (h 0) (h 1)) (h 7) (h 8))
        \<in>positive_meaning generation_source_system \<and>
      (145,Pair_Term (h 8) (h 4))\<in>positive_meaning generation_value_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_core_report_schema_def schema_variables_def generation_source_call generation_source_components)

lemma generation_core_report_fields:
  "(151,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>e u r l ps p c m hs. t=generation_fields_argument e u r l ps p c \<and>
      (139,generation_fields_term l ps p c)\<in>positive_meaning generation_value_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (150,context_relation_argument (Pair_Term e u) m hs)\<in>positive_meaning generation_source_system \<and>
      (145,Pair_Term hs ps)\<in>positive_meaning generation_value_system)"
proof
  assume "(151,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>e u r l ps p c m hs. t=generation_fields_argument e u r l ps p c \<and>
      (139,generation_fields_term l ps p c)\<in>positive_meaning generation_value_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (150,context_relation_argument (Pair_Term e u) m hs)\<in>positive_meaning generation_source_system \<and>
      (145,Pair_Term hs ps)\<in>positive_meaning generation_value_system"
    by (simp only: generation_core_report_valuation) blast
next
  assume "\<exists>e u r l ps p c m hs. t=generation_fields_argument e u r l ps p c \<and>
      (139,generation_fields_term l ps p c)\<in>positive_meaning generation_value_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (150,context_relation_argument (Pair_Term e u) m hs)\<in>positive_meaning generation_source_system \<and>
      (145,Pair_Term hs ps)\<in>positive_meaning generation_value_system"
  then obtain e u r l ps p c m hs where parts: "t=generation_fields_argument e u r l ps p c"
    "(139,generation_fields_term l ps p c)\<in>positive_meaning generation_value_system"
    "(148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system"
    "(150,context_relation_argument (Pair_Term e u) m hs)\<in>positive_meaning generation_source_system"
    "(145,Pair_Term hs ps)\<in>positive_meaning generation_value_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed l" "term_formed ps"
    "term_formed p" "term_formed c" "term_formed m" "term_formed hs"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by auto
  show "(151,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_core_report_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then l
        else if i=4 then ps else if i=5 then p else if i=6 then c else if i=7 then m else hs"])
      (use parts formed in auto)
qed

lemma generation_core_report_admitted:
  assumes "(151,Pair_Term source value)\<in>positive_meaning generation_source_system"
  shows "\<exists>G. generation_value_presents G value"
  using assms by (auto simp: generation_core_report_fields generation_admission_exact)

lemma generation_core_report_source:
  assumes "(151,Pair_Term source value)\<in>positive_meaning generation_source_system"
  shows "\<exists>E e u r. source=generation_source_term e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents E e"
  using assms by (auto simp: generation_core_report_fields generation_fields_exact)

section \<open>A child row keeps the native cited destination\<close>

lemma generation_child_row_valuation:
  "(153,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6}. term_formed (h i)) \<and>
      t=context_relation_argument (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3))
        (generation_predecessor_row_term (h 2) (h 3) (Pair_Term (h 4) (h 5)) (h 6)) \<and>
      (1,data_list_term [h 2])\<in>positive_meaning generation_source_system \<and>
      (44,citation_observation_argument (h 0) (h 1) (h 3) (Pair_Term (h 4) (h 5)))
        \<in>positive_meaning located_admission_system \<and>
      (151,Pair_Term (generation_source_term (h 0) (h 4) (h 5)) (h 6))
        \<in>positive_meaning generation_source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_child_row_schema_def schema_variables_def generation_source_call generation_source_components)

lemma generation_child_row_equation:
  "(153,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h) \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system)"
proof
  assume holds: "(153,t)\<in>positive_meaning generation_source_system"
  obtain f :: "nat\<Rightarrow>factor_term" where fields:
    "t=context_relation_argument (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))
      (generation_predecessor_row_term (f 2) (f 3) (Pair_Term (f 4) (f 5)) (f 6))"
    "(1,data_list_term [f 2])\<in>positive_meaning generation_source_system"
    "(44,citation_observation_argument (f 0) (f 1) (f 3) (Pair_Term (f 4) (f 5)))
      \<in>positive_meaning located_admission_system"
    "(151,Pair_Term (generation_source_term (f 0) (f 4) (f 5)) (f 6))
      \<in>positive_meaning generation_source_system"
    using holds by (simp only: generation_child_row_valuation) blast
  obtain s where socket: "octets_formed s" "f 2=Payload_Term s"
    using fields(2) by (simp only: generation_source_payload) blast
  obtain E u d v a where location: "environment_value_presents E (f 0)" "f 1=use_data_term u"
    "f 3=Payload_Term d" "f 4=use_data_term v" "f 5=Payload_Term a" "located_at E u d v a"
    using fields(3) by (auto simp: located_admission_exact site_data_term_def)
  show "\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h) \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system"
    by (rule exI[of _ E], rule exI[of _ "f 0"], rule exI[of _ u], rule exI[of _ s],
      rule exI[of _ d], rule exI[of _ v], rule exI[of _ a], rule exI[of _ "f 6"])
      (use fields socket location in \<open>simp add: address_pair_data_def site_data_term_def\<close>)
next
  assume "\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h) \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system"
  then obtain E e u s d v a h where parts:
    "t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h)"
    "environment_value_presents E e" "octets_formed s" "located_at E u d v a"
    "(151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
      \<in>positive_meaning generation_source_system" by blast
  have located: "(44,citation_observation_argument e (use_data_term u) (Payload_Term d) (site_data_term v a))
      \<in>positive_meaning located_admission_system"
    using parts(4) by (simp add: located_admission_on_values[OF parts(2)])
  have formed: "term_formed e" "octets_formed d" "octets_formed a" "term_formed h"
    using schema_call_formed_target[OF positive_meaning_formed[OF located]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(5)]] by auto
  have socket_read: "(1,data_list_term [Payload_Term s])\<in>positive_meaning generation_source_system"
    using parts(3) by (simp only: generation_source_payload factor_term.inject; blast)
  show "(153,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_child_row_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then use_data_term u else if i=2 then Payload_Term s
        else if i=3 then Payload_Term d else if i=4 then use_data_term v else if i=5 then Payload_Term a else h"])
      (use parts formed located socket_read in \<open>auto simp: address_pair_data_def site_data_term_def\<close>)
qed

corollary generation_child_row_at_source:
  assumes source: "environment_value_presents E e"
  shows "(153,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) row)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>v a h. row=generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h \<and>
      octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system)"
proof -
  have recovery: "environment_value_presents F e \<longleftrightarrow> F=E" for F
    using source environment_value_presents_unique by blast
  show ?thesis by (auto simp: generation_child_row_equation address_pair_data_def
    recovery inj_eq[OF use_data_term_injective])
qed

lemma generation_child_value_valuation:
  "(149,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6}. term_formed (h i)) \<and>
      t=context_relation_argument (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)) (h 6) \<and>
      (153,context_relation_argument (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3))
        (generation_predecessor_row_term (h 2) (h 3) (Pair_Term (h 4) (h 5)) (h 6)))
        \<in>positive_meaning generation_source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_child_value_schema_def schema_variables_def generation_source_call)

lemma generation_child_value_equation:
  "(149,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system)"
proof
  assume "(149,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system"
    by (auto simp: generation_child_value_valuation generation_child_row_equation address_pair_data_def; blast)
next
  assume "\<exists>E e u s d v a h. t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h \<and>
      environment_value_presents E e \<and> octets_formed s \<and> located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system"
  then obtain E e u s d v a h where parts:
    "t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h"
    "environment_value_presents E e" "octets_formed s" "located_at E u d v a"
    "(151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
      \<in>positive_meaning generation_source_system" by blast
  have row: "(153,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h))
      \<in>positive_meaning generation_source_system"
    using parts(2-5) by (auto simp: generation_child_row_equation)
  have formed: "term_formed e" "octets_formed s" "octets_formed d" "octets_formed a" "term_formed h"
    using schema_call_formed_target[OF positive_meaning_formed[OF row]] by (auto simp: address_pair_data_def)
  show "(149,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_child_value_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then use_data_term u else if i=2 then Payload_Term s
        else if i=3 then Payload_Term d else if i=4 then use_data_term v else if i=5 then Payload_Term a else h"])
      (use parts(1) row formed in \<open>auto simp: address_pair_data_def site_data_term_def\<close>)
qed

corollary generation_child_value_at_source:
  assumes source: "environment_value_presents E e"
  shows "(149,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (octets_formed s \<and> (\<exists>v a. located_at E u d v a \<and>
      (151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
        \<in>positive_meaning generation_source_system))"
  using environment_value_presents_unique[OF _ source]
  by (auto simp: generation_child_value_equation address_pair_data_def
    intro: source dest: injD[OF use_data_term_injective])

lemma generation_child_value_admitted:
  assumes "(149,context_relation_argument a row h)\<in>positive_meaning generation_source_system"
  shows "\<exists>H. generation_value_presents H h"
  using assms generation_core_report_admitted by (auto simp: generation_child_value_equation)

section \<open>Source and complete-row admission project the same reading\<close>

lemma generation_source_valuation:
  "(152,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=generation_source_term (h 0) (h 1) (h 2) \<and>
      (151,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3))
        \<in>positive_meaning generation_source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_source_schema_def schema_variables_def generation_source_call)

lemma generation_source_equation:
  "(152,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>value. (151,Pair_Term t value)\<in>positive_meaning generation_source_system)"
proof
  assume "(152,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>value. (151,Pair_Term t value)\<in>positive_meaning generation_source_system"
    by (auto simp: generation_source_valuation)
next
  assume "\<exists>value. (151,Pair_Term t value)\<in>positive_meaning generation_source_system"
  then obtain "value" where report: "(151,Pair_Term t value)\<in>positive_meaning generation_source_system" by blast
  obtain E e u r where source: "t=generation_source_term e (use_data_term u) (Payload_Term r)"
    using generation_core_report_source[OF report] by blast
  have formed: "term_formed e" "octets_formed r" "term_formed value"
    using schema_call_formed_target[OF positive_meaning_formed[OF report]] by (simp_all add: source)
  show "(152,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_source_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then use_data_term u else if i=2 then Payload_Term r else value"])
      (use report source formed in auto)
qed

lemma generation_predecessor_report_valuation:
  "(155,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3) \<and>
      (152,generation_source_term (h 0) (h 1) (h 2))\<in>positive_meaning generation_source_system \<and>
      (148,generation_fields_argument (h 0) (h 1) (h 2) (h 4) (h 5) (h 6) (h 7))
        \<in>positive_meaning generation_source_system \<and>
      (154,context_relation_argument (Pair_Term (h 0) (h 1)) (h 5) (h 3))
        \<in>positive_meaning generation_source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_predecessor_report_schema_def schema_variables_def generation_source_call)

lemma generation_predecessor_report_calls:
  "(155,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>e u r rows l m p c. t=Pair_Term (generation_source_term e u r) rows \<and>
      (152,generation_source_term e u r)\<in>positive_meaning generation_source_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (154,context_relation_argument (Pair_Term e u) m rows)\<in>positive_meaning generation_source_system)"
proof
  assume "(155,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>e u r rows l m p c. t=Pair_Term (generation_source_term e u r) rows \<and>
      (152,generation_source_term e u r)\<in>positive_meaning generation_source_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (154,context_relation_argument (Pair_Term e u) m rows)\<in>positive_meaning generation_source_system"
    by (simp only: generation_predecessor_report_valuation) blast
next
  assume "\<exists>e u r rows l m p c. t=Pair_Term (generation_source_term e u r) rows \<and>
      (152,generation_source_term e u r)\<in>positive_meaning generation_source_system \<and>
      (148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system \<and>
      (154,context_relation_argument (Pair_Term e u) m rows)\<in>positive_meaning generation_source_system"
  then obtain e u r rows l m p c where parts: "t=Pair_Term (generation_source_term e u r) rows"
    "(152,generation_source_term e u r)\<in>positive_meaning generation_source_system"
    "(148,generation_fields_argument e u r l m p c)\<in>positive_meaning generation_source_system"
    "(154,context_relation_argument (Pair_Term e u) m rows)\<in>positive_meaning generation_source_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed rows"
    "term_formed l" "term_formed m" "term_formed p" "term_formed c"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by auto
  show "(155,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_predecessor_report_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then rows
        else if i=4 then l else if i=5 then m else if i=6 then p else c"])
      (use parts formed in auto)
qed

end
