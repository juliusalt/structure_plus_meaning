theory Factor_Current_Entries
  imports Factor_Current_Programs
begin

section \<open>An adopted purpose selects one exact entry in the recovered scope\<close>

definition purpose_entry :: "exact_target \<Rightarrow> local_address option definition_site \<Rightarrow> bool" where
  "purpose_entry p d \<longleftrightarrow>
    (\<exists>C q. p=Whole_Artifact C \<and> complete_data_quoted_at C q (site_data_term (fst d) (snd d)))"

lemma purpose_entry_unique:
  assumes first: "purpose_entry p d" and second: "purpose_entry p e"
  shows "d=e"
proof -
  obtain C q where left: "p=Whole_Artifact C"
    "complete_data_quoted_at C q (site_data_term (fst d) (snd d))"
    using first unfolding purpose_entry_def by blast
  obtain D r where right: "p=Whole_Artifact D"
    "complete_data_quoted_at D r (site_data_term (fst e) (snd e))"
    using second unfolding purpose_entry_def by blast
  have same: "D=C" using left(1) right(1) by simp
  have other: "complete_data_quoted_at C r (site_data_term (fst e) (snd e))"
    using right(2) same by simp
  have sites: "site_data_term (fst d) (snd d)=site_data_term (fst e) (snd e)"
    using complete_data_quotation_whole_unique[OF left(2) other] by blast
  show ?thesis using sites by (simp add: prod_eq_iff)
qed

lemma purpose_entry_formed:
  assumes entry: "purpose_entry p d"
  shows "target_formed p \<and> octets_formed (snd d)"
  using entry complete_data_quotation_formed
  unfolding purpose_entry_def by fastforce

theorem purpose_entry_total:
  assumes formed: "octets_formed (snd d)"
  shows "\<exists>p. purpose_entry p d"
proof -
  have tf: "term_formed (site_data_term (fst d) (snd d))" using formed by simp
  have quote: "complete_data_quoted_at (term_syntax (site_data_term (fst d) (snd d))) []
      (site_data_term (fst d) (snd d))"
    by (rule complete_data_quotation_total[OF tf]) simp
  show ?thesis using quote unfolding purpose_entry_def by blast
qed

definition current_entry_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_target \<Rightarrow> exact_target \<Rightarrow>
    generation_core \<Rightarrow> exact_target \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option native_system \<Rightarrow>
    local_address option definition_site \<Rightarrow> bool" where
  "current_entry_scope_quoted_at C q A l G p E u r P d \<longleftrightarrow>
    current_program_scope_quoted_at C q A l G p E u r P \<and>
    purpose_entry p d \<and> d\<in>system_definitions P"

theorem current_entry_scope_unique:
  assumes first: "current_entry_scope_quoted_at C q A l G p E u r P d"
    and second: "current_entry_scope_quoted_at C q B m H z F v s Q e"
  shows "A=B \<and> l=m \<and> G=H \<and> p=z \<and> E=F \<and> u=v \<and> r=s \<and> P=Q \<and> d=e"
proof -
  have left: "current_program_scope_quoted_at C q A l G p E u r P" "purpose_entry p d"
    using first by (auto simp: current_entry_scope_quoted_at_def)
  have right: "current_program_scope_quoted_at C q B m H z F v s Q" "purpose_entry z e"
    using second by (auto simp: current_entry_scope_quoted_at_def)
  have fields: "A=B \<and> l=m \<and> G=H \<and> p=z \<and> E=F \<and> u=v \<and> r=s \<and> P=Q"
    by (rule current_program_scope_unique[OF left(1) right(1)])
  have other: "purpose_entry p e" using right(2) fields by simp
  show ?thesis using fields purpose_entry_unique[OF left(2) other] by blast
qed

lemma current_entry_scope_closed:
  assumes current: "current_entry_scope_quoted_at C q A l G p E u r P d"
  shows "closed_native_package_at E u r P \<and> native_package_environment E u r=E \<and>
    d\<in>system_definitions P"
  using current generation_program_scope_closed
  unfolding current_entry_scope_quoted_at_def current_program_scope_quoted_at_def by blast

lemma current_entry_scope_frame:
  assumes current: "current_entry_scope_quoted_at C q A l G p E u r P d"
  shows "\<exists>H pu pr au ar F v root.
    current_scope_quoted_at C q H pu pr au ar A F v root l G p"
  using current unfolding current_entry_scope_quoted_at_def current_program_scope_quoted_at_def by blast

theorem current_entry_scope_quoted_total:
  fixes H F :: "local_address option artifact_environment"
  assumes current: "native_current H pu pr au ar A F v root l G p"
    and scope: "generation_program_scope G E u r P"
    and entry: "purpose_entry p d" and member: "d\<in>system_definitions P"
  shows "\<exists>C. current_entry_scope_quoted_at C [] A l G p E u r P d"
  using current_program_scope_quoted_total[OF current scope] entry member
  unfolding current_entry_scope_quoted_at_def by blast

theorem current_entry_scope_future_application:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "native_package_at F pu pr P"
    and "native_package_environment F pu pr=E"
    and "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    and "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof -
  have program: "current_program_scope_quoted_at C q A l G p E pu pr P"
    using current by (simp add: current_entry_scope_quoted_at_def)
  show "native_package_at F pu pr P" "native_package_environment F pu pr=E"
    "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule current_program_scope_future_application[OF program formed included app])+
qed

text \<open>
  This purpose profile designates an exact use and address within the program
  scope already retained by the adopted generation. The complete purpose
  quotation determines its own root. No root marker, program copy, or second
  authority field is stored. The actual currentness frame determines both the
  program and the entry; an auxiliary definition cannot replace that entry.

  Purpose targets outside this profile retain their existing ordinary meaning.
  The adoption policy remains explicit, and its program may differ from the
  program selected by the generation. This profile neither validates a cause
  nor supplies the remaining amendment certificate and succession conditions.
\<close>

end
