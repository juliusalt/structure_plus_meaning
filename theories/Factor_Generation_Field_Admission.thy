theory Factor_Generation_Field_Admission
  imports Factor_Generation_Source_Clauses RRA_Generation_Dependencies
begin

section \<open>The complete four-field record and predecessor socket graph\<close>

lemma generation_syntax_valuation:
  "(147,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      t=generation_syntax_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) \<and>
      (34,rooted_rows_argument (h 0) (h 1)
        (data_list_term [Pair_Term (h 7) (h 2),Pair_Term (h 8) (h 6),
          Pair_Term (h 9) (h 4),Pair_Term (h 10) (h 5)]))\<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument (h 0) (h 6) (h 3))\<in>positive_meaning family_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_syntax_schema_def schema_variables_def generation_source_call generation_source_components)

lemma generation_syntax_fields:
  "(147,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>a r l m p c pr s0 s1 s2 s3. t=generation_syntax_argument a r l m p c \<and>
      (34,rooted_rows_argument a r (data_list_term
        [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]))\<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument a pr m)\<in>positive_meaning family_admission_system)"
proof
  assume "(147,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>a r l m p c pr s0 s1 s2 s3. t=generation_syntax_argument a r l m p c \<and>
      (34,rooted_rows_argument a r (data_list_term
        [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]))\<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument a pr m)\<in>positive_meaning family_admission_system"
    by (simp only: generation_syntax_valuation) blast
next
  assume "\<exists>a r l m p c pr s0 s1 s2 s3. t=generation_syntax_argument a r l m p c \<and>
      (34,rooted_rows_argument a r (data_list_term
        [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]))\<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument a pr m)\<in>positive_meaning family_admission_system"
  then obtain a r l m p c pr s0 s1 s2 s3 where parts: "t=generation_syntax_argument a r l m p c"
    "(34,rooted_rows_argument a r (data_list_term
      [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]))\<in>positive_meaning record_admission_system"
    "(32,rooted_rows_argument a pr m)\<in>positive_meaning family_admission_system" by blast
  have formed: "term_formed a" "term_formed r" "term_formed l" "term_formed m" "term_formed p" "term_formed c"
    "term_formed pr" "term_formed s0" "term_formed s1" "term_formed s2" "term_formed s3"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
  show "(147,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_syntax_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then a else if i=1 then r else if i=2 then l else if i=3 then m
        else if i=4 then p else if i=5 then c else if i=6 then pr else if i=7 then s0
        else if i=8 then s1 else if i=9 then s2 else s3"])
      (use parts formed in auto)
qed

abbreviation generation_syntax_result :: "factor_term \<Rightarrow> bool" where
  "generation_syntax_result t \<equiv> \<exists>R a r l ms p c.
    t=generation_syntax_argument a (Payload_Term r) (Payload_Term l)
      (data_list_term (map address_pair_data ms)) (Payload_Term p) (Payload_Term c) \<and>
    artifact_value_presents R a \<and> distinct ms \<and> generation_syntax_at R r l (set ms) p c"

theorem generation_syntax_exact:
  "(147,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_syntax_result t"
proof
  assume holds: "(147,t)\<in>positive_meaning generation_source_system"
  obtain a k l m p c pr s0 s1 s2 s3 where fields: "t=generation_syntax_argument a k l m p c"
    "(34,rooted_rows_argument a k (data_list_term
      [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]))\<in>positive_meaning record_admission_system"
    "(32,rooted_rows_argument a pr m)\<in>positive_meaning family_admission_system"
    using holds by (simp only: generation_syntax_fields) blast
  obtain R a' r xs where raw_record:
    "rooted_rows_argument a k (data_list_term
      [Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]) =
      rooted_rows_argument a' (Payload_Term r) (data_list_term (map address_pair_data xs))"
    "artifact_value_presents R a'" "record_at R r (map fst xs) (map snd xs)"
    using record_admission_exact[THEN iffD1, OF fields(2)]
    by (elim exE conjE) (rule that, assumption+)
  have rec: "artifact_value_presents R a" "k=Payload_Term r"
    "map address_pair_data xs=[Pair_Term s0 l,Pair_Term s1 pr,Pair_Term s2 p,Pair_Term s3 c]"
    "record_at R r (map fst xs) (map snd xs)"
    using raw_record by (auto simp only: factor_term.inject data_list_term_injective)
  obtain q0 q1 q2 q3 lr pr' payr cr where decoded:
    "xs=[(q0,lr),(q1,pr'),(q2,payr),(q3,cr)]"
    "l=Payload_Term lr" "pr=Payload_Term pr'" "p=Payload_Term payr" "c=Payload_Term cr"
    using rec(3) by (auto simp: map_eq_Cons_conv address_pair_data_def split: prod.splits)
  obtain ms where family: "m=data_list_term (map address_pair_data ms)" "distinct ms" "family_at R pr' (set ms)"
    using fields(3) by (auto simp: family_admission_at_source[OF rec(1)] decoded(3))
  have syntax_read: "generation_syntax_at R r lr (set ms) payr cr"
    using rec(4) decoded(1) family(3) by (auto simp: generation_syntax_at_def)
  show "generation_syntax_result t" using fields(1) rec(1,2) decoded(2,4,5) family(1,2) syntax_read by blast
next
  assume "generation_syntax_result t"
  then obtain R a r l ms p c where parts:
    "t=generation_syntax_argument a (Payload_Term r) (Payload_Term l)
      (data_list_term (map address_pair_data ms)) (Payload_Term p) (Payload_Term c)"
    "artifact_value_presents R a" "distinct ms" "generation_syntax_at R r l (set ms) p c" by blast
  obtain ps pr where native: "record_at R r ps [l,pr,p,c]" "family_at R pr (set ms)"
    using parts(4) by (auto simp: generation_syntax_at_def)
  have length: "length ps=Suc (Suc (Suc (Suc 0)))"
    using record_at_preserves_socket_occurrences[OF native(1)] by simp
  obtain s0 s1 s2 s3 where sockets: "ps=[s0,s1,s2,s3]"
    using length by (auto simp only: length_Suc_conv length_0_conv)
  have rec: "(34,rooted_rows_argument a (Payload_Term r) (data_list_term
      [Pair_Term (Payload_Term s0) (Payload_Term l),Pair_Term (Payload_Term s1) (Payload_Term pr),
        Pair_Term (Payload_Term s2) (Payload_Term p),Pair_Term (Payload_Term s3) (Payload_Term c)]))
      \<in>positive_meaning record_admission_system"
    using record_admission_rows[OF parts(2), of r "[(s0,l),(s1,pr),(s2,p),(s3,c)]"] native(1)
    by (simp add: sockets address_pair_data_def)
  have family: "(32,rooted_rows_argument a (Payload_Term pr) (data_list_term (map address_pair_data ms)))
      \<in>positive_meaning family_admission_system"
    using parts(3) native(2) by (simp add: family_admission_rows[OF parts(2)])
  show "(147,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_syntax_fields,
      rule exI[of _ a], rule exI[of _ "Payload_Term r"], rule exI[of _ "Payload_Term l"],
      rule exI[of _ "data_list_term (map address_pair_data ms)"],
      rule exI[of _ "Payload_Term p"], rule exI[of _ "Payload_Term c"],
      rule exI[of _ "Payload_Term pr"], rule exI[of _ "Payload_Term s0"],
      rule exI[of _ "Payload_Term s1"], rule exI[of _ "Payload_Term s2"], rule exI[of _ "Payload_Term s3"])
      (use parts(1) rec family in simp)
qed

corollary generation_syntax_at_source:
  assumes source: "artifact_value_presents R a"
  shows "(147,generation_syntax_argument a k l m p c)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>r lr ms payr cr. k=Payload_Term r \<and> l=Payload_Term lr \<and>
      m=data_list_term (map address_pair_data ms) \<and> p=Payload_Term payr \<and> c=Payload_Term cr \<and>
      distinct ms \<and> generation_syntax_at R r lr (set ms) payr cr)"
proof -
  have recovery: "artifact_value_presents S a \<longleftrightarrow> S=R" for S
    using source artifact_value_presents_unique by blast
  show ?thesis by (auto simp: generation_syntax_exact recovery)
qed

corollary generation_syntax_on_rows:
  assumes source: "artifact_value_presents R a"
  shows "(147,generation_syntax_argument a (Payload_Term r) (Payload_Term l)
      (data_list_term (map address_pair_data ms)) (Payload_Term p) (Payload_Term c))
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    distinct ms \<and> generation_syntax_at R r l (set ms) p c"
  by (simp add: generation_syntax_at_source[OF source] data_list_term_injective
    injective_mapped_lists[OF address_pair_data_injective])

section \<open>All three targets are read in that same source environment\<close>

lemma generation_fields_valuation:
  "(148,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      t=generation_fields_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (147,generation_syntax_argument (h 7) (h 2) (h 8) (h 4) (h 9) (h 10))\<in>positive_meaning generation_source_system \<and>
      (43,citation_observation_argument (h 0) (h 1) (h 8) (h 3))\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument (h 0) (h 1) (h 9) (h 5))\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument (h 0) (h 1) (h 10) (h 6))\<in>positive_meaning anchored_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_fields_schema_def schema_variables_def generation_source_call generation_source_components)

lemma generation_fields_calls:
  "(148,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>e u r l m p c a lr payr cr. t=generation_fields_argument e u r l m p c \<and>
      (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
      (147,generation_syntax_argument a r lr m payr cr)\<in>positive_meaning generation_source_system \<and>
      (43,citation_observation_argument e u lr l)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u payr p)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u cr c)\<in>positive_meaning anchored_admission_system)"
proof
  assume "(148,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>e u r l m p c a lr payr cr. t=generation_fields_argument e u r l m p c \<and>
      (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
      (147,generation_syntax_argument a r lr m payr cr)\<in>positive_meaning generation_source_system \<and>
      (43,citation_observation_argument e u lr l)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u payr p)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u cr c)\<in>positive_meaning anchored_admission_system"
    by (simp only: generation_fields_valuation) blast
next
  assume "\<exists>e u r l m p c a lr payr cr. t=generation_fields_argument e u r l m p c \<and>
      (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
      (147,generation_syntax_argument a r lr m payr cr)\<in>positive_meaning generation_source_system \<and>
      (43,citation_observation_argument e u lr l)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u payr p)\<in>positive_meaning anchored_admission_system \<and>
      (43,citation_observation_argument e u cr c)\<in>positive_meaning anchored_admission_system"
  then obtain e u r l m p c a lr payr cr where parts: "t=generation_fields_argument e u r l m p c"
    "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    "(147,generation_syntax_argument a r lr m payr cr)\<in>positive_meaning generation_source_system"
    "(43,citation_observation_argument e u lr l)\<in>positive_meaning anchored_admission_system"
    "(43,citation_observation_argument e u payr p)\<in>positive_meaning anchored_admission_system"
    "(43,citation_observation_argument e u cr c)\<in>positive_meaning anchored_admission_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed l" "term_formed m" "term_formed p"
    "term_formed c" "term_formed a" "term_formed lr" "term_formed payr" "term_formed cr"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(5)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(6)]] by auto
  show "(148,t)\<in>positive_meaning generation_source_system"
    by (simp only: generation_fields_valuation, rule exI[of _
      "\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then l
        else if i=4 then m else if i=5 then p else if i=6 then c else if i=7 then a
        else if i=8 then lr else if i=9 then payr else cr"])
      (use parts formed in auto)
qed

abbreviation generation_fields_result :: "factor_term \<Rightarrow> bool" where
  "generation_fields_result t \<equiv> \<exists>E e u r l ms p c a b q.
    t=generation_fields_argument e (use_data_term u) (Payload_Term r) a
      (data_list_term (map address_pair_data ms)) b q \<and>
    environment_value_presents E e \<and> target_value_presents l a \<and>
    target_value_presents p b \<and> target_value_presents c q \<and>
    distinct ms \<and> generation_fields_at E u r l (set ms) p c"

theorem generation_fields_exact:
  "(148,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_fields_result t"
proof
  assume holds: "(148,t)\<in>positive_meaning generation_source_system"
  obtain e ut k a m b q art lr payr cr where calls: "t=generation_fields_argument e ut k a m b q"
    "(37,artifact_lookup_argument e ut art)\<in>positive_meaning artifact_lookup_system"
    "(147,generation_syntax_argument art k lr m payr cr)\<in>positive_meaning generation_source_system"
    "(43,citation_observation_argument e ut lr a)\<in>positive_meaning anchored_admission_system"
    "(43,citation_observation_argument e ut payr b)\<in>positive_meaning anchored_admission_system"
    "(43,citation_observation_argument e ut cr q)\<in>positive_meaning anchored_admission_system"
    using holds by (simp only: generation_fields_calls) blast
  obtain E u R where source: "environment_value_presents E e" "ut=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R art"
    using calls(2) by (auto simp: artifact_lookup_exact)
  obtain r lref ms pref cref where syntax_read: "k=Payload_Term r" "lr=Payload_Term lref"
    "m=data_list_term (map address_pair_data ms)" "payr=Payload_Term pref" "cr=Payload_Term cref"
    "distinct ms" "generation_syntax_at R r lref (set ms) pref cref"
    using calls(3) by (simp only: generation_syntax_at_source[OF source(4)]) blast
  obtain l where locus: "target_value_presents l a" "anchored_at E u lref l"
    using calls(4) by (auto simp: anchored_admission_at_source[OF source(1)] source(2) syntax_read(2)
      dest: injD[OF use_data_term_injective])
  obtain p where payload: "target_value_presents p b" "anchored_at E u pref p"
    using calls(5) by (auto simp: anchored_admission_at_source[OF source(1)] source(2) syntax_read(4)
      dest: injD[OF use_data_term_injective])
  obtain c where cause: "target_value_presents c q" "anchored_at E u cref c"
    using calls(6) by (auto simp: anchored_admission_at_source[OF source(1)] source(2) syntax_read(5)
      dest: injD[OF use_data_term_injective])
  have fields: "generation_fields_at E u r l (set ms) p c"
    using environment_value_presents_formed[OF source(1)] source(3) syntax_read(7) locus(2) payload(2) cause(2)
    by (auto simp: generation_fields_at_def generation_syntax_at_def; blast)
  show "generation_fields_result t"
    using calls(1) source(1,2) syntax_read(1,3,6) locus(1) payload(1) cause(1) fields by blast
next
  assume "generation_fields_result t"
  then obtain E e u r l ms p c a b q where parts:
    "t=generation_fields_argument e (use_data_term u) (Payload_Term r) a
      (data_list_term (map address_pair_data ms)) b q"
    "environment_value_presents E e" "target_value_presents l a" "target_value_presents p b"
    "target_value_presents c q" "distinct ms" "generation_fields_at E u r l (set ms) p c" by blast
  obtain R lr payr cr where native: "artifact_at E u R" "generation_syntax_at R r lr (set ms) payr cr"
    "anchored_at E u lr l" "anchored_at E u payr p" "anchored_at E u cr c"
    using generation_fields_syntax[OF parts(7)] by blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF parts(2)] by blast
  have rf: "exact_formed R" using ef native(1) by (auto simp: environment_formed_def)
  obtain art where presentation: "artifact_value_presents R art" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) art)\<in>positive_meaning artifact_lookup_system"
    using parts(2) native(1) presentation by (auto simp: artifact_lookup_exact)
  have syntax_read: "(147,generation_syntax_argument art (Payload_Term r) (Payload_Term lr)
      (data_list_term (map address_pair_data ms)) (Payload_Term payr) (Payload_Term cr))
      \<in>positive_meaning generation_source_system"
    using parts(6) native(2) by (simp add: generation_syntax_on_rows[OF presentation])
  have locus: "(43,citation_observation_argument e (use_data_term u) (Payload_Term lr) a)
      \<in>positive_meaning anchored_admission_system"
    using native(3) by (simp add: anchored_admission_on_values[OF parts(2,3)])
  have payload: "(43,citation_observation_argument e (use_data_term u) (Payload_Term payr) b)
      \<in>positive_meaning anchored_admission_system"
    using native(4) by (simp add: anchored_admission_on_values[OF parts(2,4)])
  have cause: "(43,citation_observation_argument e (use_data_term u) (Payload_Term cr) q)
      \<in>positive_meaning anchored_admission_system"
    using native(5) by (simp add: anchored_admission_on_values[OF parts(2,5)])
  show "(148,t)\<in>positive_meaning generation_source_system"
    using parts(1) lookup syntax_read locus payload cause by (auto simp: generation_fields_calls)
qed

corollary generation_fields_on_values:
  assumes source: "environment_value_presents E e"
    and "values": "target_value_presents l a" "target_value_presents p b" "target_value_presents c q"
  shows "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a m b q)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>ms. m=data_list_term (map address_pair_data ms) \<and> distinct ms \<and>
      generation_fields_at E u r l (set ms) p c)"
proof -
  have env: "environment_value_presents F e \<longleftrightarrow> F=E" for F
    using source environment_value_presents_unique by blast
  have locus: "target_value_presents T a \<longleftrightarrow> T=l" for T
    using "values"(1) target_value_presents_unique by blast
  have payload: "target_value_presents T b \<longleftrightarrow> T=p" for T
    using "values"(2) target_value_presents_unique by blast
  have cause: "target_value_presents T q \<longleftrightarrow> T=c" for T
    using "values"(3) target_value_presents_unique by blast
  show ?thesis
    by (auto simp: generation_fields_exact env locus payload cause inj_eq[OF use_data_term_injective])
qed

corollary generation_fields_on_rows:
  assumes "environment_value_presents E e" "target_value_presents l a"
    "target_value_presents p b" "target_value_presents c q"
  shows "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a
      (data_list_term (map address_pair_data ms)) b q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    distinct ms \<and> generation_fields_at E u r l (set ms) p c"
  by (simp add: generation_fields_on_values[OF assms] data_list_term_injective
    injective_mapped_lists[OF address_pair_data_injective])

text \<open>
  Each helper has an all-term contract for its independently defined grammar
  relation. The syntax result retains the three citation endpoints and the
  entire keyed predecessor graph. Its record sockets are checked through the
  existing complete record contract. The field reader recovers the three
  exact targets in the same supplied environment and retains that same graph.

  Source artifacts, environments, and target values can use any admitted
  presentation. Every distinct complete enumeration of the predecessor graph
  is accepted. These field contracts neither read predecessor generations nor
  validate the recorded cause; those are separate relations.
\<close>

end
