theory Factor_Admission_Request_Primitives
  imports Factor_Admission_Request_Clauses
begin

section \<open>The request predicates reuse the actual original operations\<close>

lemma admission_sequence_data_extension:
  "admission_extension data_append_system admission_sequence_system"
proof -
  have included: "system_definitions data_append_system\<subseteq>system_definitions admission_sequence_system"
    by auto
  have agreement: "systems_agree_on data_append_system admission_sequence_system
      (system_definitions data_append_system)"
    by (auto simp: systems_agree_on_def admission_sequence_system_def admission_plan_system_def
      admission_counter_system_def admission_counter_element_system_def)
  show ?thesis using included agreement
    by (simp only: admission_extension_def data_append_system_formed admission_sequence_system_formed; blast)
qed

lemma admission_sequence_data_meaning:
  assumes "d\<in>system_definitions data_append_system"
  shows "(d,t)\<in>positive_meaning admission_sequence_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_append_system"
  by (rule admission_extension_meaning[OF admission_sequence_data_extension assms])

lemma admission_request_components:
  "(5,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (5,z)\<in>positive_meaning bag_comparison_system"
  "(340,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow> (\<exists>n. z=admission_counter n)"
  "(46,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (46,z)\<in>positive_meaning data_append_system"
  "(361,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow> admission_sequence_result z"
  using admission_request_old_meaning[where d=5 and t=z and D=D]
    admission_request_old_meaning[where d=340 and t=z and D=D]
    admission_request_old_meaning[where d=46 and t=z and D=D]
    admission_request_old_meaning[where d=361 and t=z and D=D]
    admission_sequence_data_meaning[where d=5 and t=z] data_append_bag_meaning[where d=5 and t=z]
  by (auto simp: admission_sequence_components admission_sequence_exact)

section \<open>Supported sites are read from the fixed complete source term\<close>

lemma admission_supported_site_valuation:
  "(362,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> z=h 0 \<and>
      (5,Pair_Term (h 0) (Pair_Term (admission_source_data D) (h 1)))\<in>positive_meaning bag_comparison_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: admission_request_clauses admission_request_family_def admission_supported_site_schema_def
      schema_variables_def admission_request_call admission_request_components)

theorem admission_supported_site_exact:
  assumes finite: "finite D"
  shows "(362,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (\<exists>d\<in>D. z=admission_counter d)"
proof
  assume holds: "(362,z)\<in>positive_meaning (admission_request_system D)"
  then obtain r where selection:
    "(5,Pair_Term z (Pair_Term (admission_source_data D) r))\<in>positive_meaning bag_comparison_system"
    by (auto simp: admission_supported_site_valuation)
  have selected: "selected_data_member z (admission_source_data D)" using selection by blast
  show "\<exists>d\<in>D. z=admission_counter d"
    using selected by (simp only: admission_source_data_member[OF finite])
next
  assume "\<exists>d\<in>D. z=admission_counter d"
  then have selected: "selected_data_member z (admission_source_data D)"
    by (simp only: admission_source_data_member[OF finite])
  obtain r where selection:
    "(5,Pair_Term z (Pair_Term (admission_source_data D) r))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed z" "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF selection]] by auto
  show "(362,z)\<in>positive_meaning (admission_request_system D)"
    by (simp only: admission_supported_site_valuation;
      rule exI[of _ "\<lambda>i::nat. if i=0 then z else r"])
      (use formed selection in auto)
qed

corollary admission_supported_site_at_counter:
  assumes "finite D"
  shows "(362,admission_counter d)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow> d\<in>D"
  by (simp only: admission_supported_site_exact[OF assms] admission_counter_injective; auto)

section \<open>The counter must extend the actual source's entire occupied prefix\<close>

lemma admission_fresh_counter_valuation:
  "(365,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> z=h 0 \<and>
      (\<exists>m. h 1=admission_counter m) \<and>
      (46,collection_join_argument (admission_counter (admission_source_floor D)) (h 1) (h 0))
        \<in>positive_meaning data_append_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: admission_request_clauses admission_request_family_def admission_fresh_counter_schema_def
      schema_variables_def admission_request_call admission_request_components)

theorem admission_fresh_counter_exact:
  "(365,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (\<exists>n. admission_source_floor D\<le>n \<and> z=admission_counter n)"
proof
  assume holds: "(365,z)\<in>positive_meaning (admission_request_system D)"
  then obtain m where append:
    "(46,collection_join_argument (admission_counter (admission_source_floor D)) (admission_counter m) z)
      \<in>positive_meaning data_append_system"
    by (auto simp: admission_fresh_counter_valuation)
  have counter_value: "z=admission_counter (admission_source_floor D+m)"
    using append by (simp only: data_append_at_lists; simp add: replicate_add)
  show "\<exists>n. admission_source_floor D\<le>n \<and> z=admission_counter n"
    by (rule exI[of _ "admission_source_floor D+m"]) (simp add: counter_value)
next
  assume "\<exists>n. admission_source_floor D\<le>n \<and> z=admission_counter n"
  then obtain n where bound: "admission_source_floor D\<le>n" and counter_value: "z=admission_counter n" by blast
  let ?m="n-admission_source_floor D"
  have total: "admission_source_floor D+?m=n" using bound by arith
  have merged: "replicate n (Payload_Term [])=
    replicate (admission_source_floor D) (Payload_Term [])@replicate ?m (Payload_Term [])"
    using total by (metis replicate_add)
  have append:
    "(46,collection_join_argument (admission_counter (admission_source_floor D)) (admission_counter ?m)
      (admission_counter n))\<in>positive_meaning data_append_system"
    by (simp only: data_append_lists) (use merged in \<open>auto simp: octets_formed_def\<close>)
  show "(365,z)\<in>positive_meaning (admission_request_system D)"
    by (simp only: admission_fresh_counter_valuation;
      rule exI[of _ "\<lambda>i::nat. if i=0 then admission_counter n else admission_counter ?m"])
      (use counter_value append in auto)
qed

corollary admission_fresh_counter_at_counter:
  "(365,admission_counter n)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    admission_source_floor D\<le>n"
  by (simp only: admission_fresh_counter_exact admission_counter_injective; auto)

text \<open>
  Membership consumes the complete source term through the original native
  selection predicate. Counter admission consumes the original counter
  recognizer and native append relation. Their meanings are preserved through
  the actual program extensions; no independently supplied result flags stand
  in for either computation.
\<close>

end
