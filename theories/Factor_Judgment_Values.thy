theory Factor_Judgment_Values
  imports Factor_Environment_Values Factor_Complete_Data_Quotation
begin

section \<open>An exact environment with its program and call sites\<close>

definition judgment_value_presents ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "judgment_value_presents E pu pr au ar t \<longleftrightarrow>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    (\<exists>e. environment_value_presents E e \<and>
      t=Pair_Term e (Pair_Term (Pair_Term (use_data_term pu) (Payload_Term pr))
        (Pair_Term (use_data_term au) (Payload_Term ar))))"

theorem judgment_value_presents_unique:
  assumes first: "judgment_value_presents E pu pr au ar t"
    and second: "judgment_value_presents F qu qr bu br t"
  shows "E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain e where left: "environment_value_presents E e"
    "t=Pair_Term e (Pair_Term (Pair_Term (use_data_term pu) (Payload_Term pr))
      (Pair_Term (use_data_term au) (Payload_Term ar)))"
    using first unfolding judgment_value_presents_def by blast
  obtain f where right: "environment_value_presents F f"
    "t=Pair_Term f (Pair_Term (Pair_Term (use_data_term qu) (Payload_Term qr))
      (Pair_Term (use_data_term bu) (Payload_Term br)))"
    using second unfolding judgment_value_presents_def by blast
  have same: "e=f" and program: "use_data_term pu=use_data_term qu"
    and call: "use_data_term au=use_data_term bu" and positions: "pr=qr \<and> ar=br"
    using left(2) right(2) by simp_all
  have other: "environment_value_presents F e" using right(1) same by simp
  have env: "E=F" by (rule environment_value_presents_unique[OF left(1) other])
  have pu: "pu=qu" by (rule injD[OF use_data_term_injective program])
  have au: "au=bu" by (rule injD[OF use_data_term_injective call])
  show ?thesis using env pu au positions by blast
qed

lemma judgment_value_presents_formed:
  assumes present: "judgment_value_presents E pu pr au ar t"
  shows "environment_formed E \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain e where sites: "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    and body: "environment_value_presents E e"
    and encoded: "t=Pair_Term e (Pair_Term (Pair_Term (use_data_term pu) (Payload_Term pr))
      (Pair_Term (use_data_term au) (Payload_Term ar)))"
    using present unfolding judgment_value_presents_def by blast
  have ef: "environment_formed E" and formed: "term_formed e" and closed: "self_contained_term e"
    using environment_value_presents_formed[OF body] by auto
  have pr: "octets_formed pr" and ar: "octets_formed ar"
    using environment_position_address[OF ef sites(1)] environment_position_address[OF ef sites(2)] by simp_all
  show ?thesis using ef formed closed pr ar encoded by simp
qed

theorem judgment_value_presents_total:
  assumes ef: "environment_formed E"
    and program: "(pu,pr)\<in>environment_positions E" and app: "(au,ar)\<in>environment_positions E"
  shows "\<exists>t. judgment_value_presents E pu pr au ar t"
proof -
  obtain e where present: "environment_value_presents E e"
    using environment_value_presents_total[OF ef] by blast
  show ?thesis
    by (rule exI[of _ "Pair_Term e (Pair_Term (Pair_Term (use_data_term pu) (Payload_Term pr))
      (Pair_Term (use_data_term au) (Payload_Term ar)))"])
       (use program app present in \<open>auto simp: judgment_value_presents_def\<close>)
qed

section \<open>The recorded target contains its whole scope\<close>

definition judgment_value_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "judgment_value_quoted_at C r E pu pr au ar \<longleftrightarrow>
    (\<exists>t. judgment_value_presents E pu pr au ar t \<and> complete_data_quoted_at C r t)"

theorem judgment_value_quoted_unique:
  assumes first: "judgment_value_quoted_at C r E pu pr au ar"
    and second: "judgment_value_quoted_at C r F qu qr bu br"
  shows "E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain t where left: "judgment_value_presents E pu pr au ar t" "complete_data_quoted_at C r t"
    using first unfolding judgment_value_quoted_at_def by blast
  obtain v where right: "judgment_value_presents F qu qr bu br v" "complete_data_quoted_at C r v"
    using second unfolding judgment_value_quoted_at_def by blast
  have same: "t=v" by (rule complete_data_quotation_unique[OF left(2) right(2)])
  have other: "judgment_value_presents F qu qr bu br t" using right(1) same by simp
  show ?thesis by (rule judgment_value_presents_unique[OF left(1) other])
qed

lemma judgment_value_quoted_formed:
  assumes "judgment_value_quoted_at C r E pu pr au ar"
  shows "exact_formed C \<and> environment_formed E \<and>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E"
proof -
  obtain t where present: "judgment_value_presents E pu pr au ar t"
    and quote: "complete_data_quoted_at C r t"
    using assms unfolding judgment_value_quoted_at_def by blast
  show ?thesis using complete_data_quotation_formed[OF quote] judgment_value_presents_formed[OF present]
    present by (simp add: judgment_value_presents_def)
qed

lemma judgment_value_quoted_anchor:
  assumes "judgment_value_quoted_at C r E pu pr au ar"
  shows "anchor_formed (C,r)"
proof -
  obtain t where quoted: "complete_data_quoted_at C r t"
    using assms unfolding judgment_value_quoted_at_def by blast
  show ?thesis by (rule complete_data_quotation_anchor[OF quoted])
qed

theorem judgment_value_quoted_total:
  assumes ef: "environment_formed E"
    and program: "(pu,pr)\<in>environment_positions E" and app: "(au,ar)\<in>environment_positions E"
  shows "\<exists>C. exact_formed C \<and> judgment_value_quoted_at C [] E pu pr au ar"
proof -
  obtain t where present: "judgment_value_presents E pu pr au ar t"
    using judgment_value_presents_total[OF ef program app] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using judgment_value_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have cf: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  show ?thesis by (rule exI[of _ "term_syntax t"])
    (use present quote cf in \<open>auto simp: judgment_value_quoted_at_def\<close>)
qed

theorem judgment_value_quoted_in_environment:
  assumes quote: "judgment_value_quoted_at C r E pu pr au ar"
    and ff: "environment_formed F" and source: "artifact_at F u C"
  shows "\<exists>t. judgment_value_presents E pu pr au ar t \<and>
    term_quoted_at F u r t (rra_carrier (object_structure C)) {}"
proof -
  obtain t where present: "judgment_value_presents E pu pr au ar t"
    and full: "complete_data_quoted_at C r t"
    using quote unfolding judgment_value_quoted_at_def by blast
  have native: "term_quoted_at F u r t (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF full] ff source])
  show ?thesis using present native by blast
qed

text \<open>
  The value contains one complete environment and two actual sites: the program
  root and the call root. The whole standalone quotation is a complete
  readdressed copy of its data syntax. Its exact artifact and root determine
  every represented value and coordinate, independently of outer bindings.

  This is inspectable scope data. The program and application still need their
  native grammar checks, and minimal reference closure is checked separately.
  No truth value, derivation, publication, or authority field is stored here.
\<close>

end
