theory Factor_Current_Site_Certificates
  imports Factor_Current_Site_Permission Factor_Replay_Scopes
begin

section \<open>Closed proof records retain their exact permitted site\<close>

definition current_site_permission_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_site_permission_certificate C q R s N u r \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F au ar root.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      replay_scope_quoted_at R s F pu pr au ar root {} \<and> current_permits_site_at C q F au ar N u r)"

theorem current_site_permission_certificate_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "current_site_permission_certificate C q R s N u r\<longleftrightarrow>
    current_permits_site_at C q F au ar N u r"
proof
  assume "current_site_permission_certificate C q R s N u r"
  then obtain M qu qr bu br other where recorded: "replay_scope_quoted_at R s M qu qr bu br other {}"
    "current_permits_site_at C q M bu br N u r"
    unfolding current_site_permission_certificate_def by blast
  have same: "M=F \<and> bu=au \<and> br=ar" using replay_scope_whole_unique[OF recorded(1) scope] by blast
  show "current_permits_site_at C q F au ar N u r" using recorded(2) same by simp
next
  assume "current_permits_site_at C q F au ar N u r"
  then show "current_site_permission_certificate C q R s N u r"
    using current scope unfolding current_site_permission_certificate_def by blast
qed

theorem current_site_permission_certificate_subject_unique:
  assumes first: "current_site_permission_certificate C q R s N u r"
    and second: "current_site_permission_certificate D a R b M v c"
  shows "s=b \<and> N=M \<and> u=v \<and> r=c"
proof -
  obtain F pu pr au ar root where left: "replay_scope_quoted_at R s F pu pr au ar root {}"
    "current_permits_site_at C q F au ar N u r"
    using first unfolding current_site_permission_certificate_def by blast
  obtain L qu qr bu br other where right: "replay_scope_quoted_at R b L qu qr bu br other {}"
    "current_permits_site_at D a L bu br M v c"
    using second unfolding current_site_permission_certificate_def by blast
  have same: "s=b \<and> F=L \<and> au=bu \<and> ar=br" using replay_scope_whole_unique[OF left(1) right(1)] by blast
  have actual: "current_permits_site_at D a F au ar M v c" using right(2) same by simp
  show ?thesis using same current_site_permission_subject_unique[OF left(2) actual] by blast
qed

theorem current_site_permission_certificate_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "current_site_permission_certificate C q R s N u r"
  shows "\<exists>F au ar root t I K.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu pr P \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au ar d t I K \<and>
    current_permits_site_at C q F au ar N u r \<and>
    site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P"
proof -
  obtain A' l' G' p' E' qu qr Q e F au ar root where recorded:
    "current_entry_scope_quoted_at C q A' l' G' p' E' qu qr Q e"
    "replay_scope_quoted_at R s F qu qr au ar root {}" "current_permits_site_at C q F au ar N u r"
    using certificate unfolding current_site_permission_certificate_def by blast
  have roots: "pu=qu \<and> pr=qr" using current_entry_scope_unique[OF current recorded(1)] by blast
  have scope: "replay_scope_quoted_at R s F pu pr au ar root {}" using recorded(2) roots by simp
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E"
    using current_site_permission_program_scope[OF current recorded(3)] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_site_permission_at_scope[OF current] recorded(3) by blast
  have fields: "site_permission_invariant P d" "site_value_presents N u r t" "(d,t)\<in>positive_meaning P"
    using current_site_permission_with_reads[OF current program(1,2) app] recorded(3) by blast+
  show ?thesis using scope program app recorded(3) fields by blast
qed

theorem current_site_permission_certificate_permits:
  assumes "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    "current_site_permission_certificate C q R s N u r"
  shows "factor_permits_site P d N u r"
  using current_site_permission_certificate_program[OF assms] unfolding factor_permits_site_def by blast

lemma current_site_permission_certificate_formed:
  assumes certificate: "current_site_permission_certificate C q R s N u r"
  shows "exact_formed C \<and> exact_formed R \<and> environment_formed N \<and> (u,r)\<in>environment_positions N"
proof -
  obtain A l G p E pu pr P d where current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    using certificate unfolding current_site_permission_certificate_def by blast
  obtain F au ar root where scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
    using current_site_permission_certificate_program[OF current certificate] by blast
  show ?thesis using current_entry_scope_formed[OF current] replay_scope_formed[OF scope]
    factor_site_permission_formed[OF current_site_permission_certificate_permits[OF current certificate]] by blast
qed

theorem current_site_permission_certificate_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "current_site_permission_certificate C q R s N u r"
  shows "\<exists>F au ar root t I K J.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar d t I K \<and>
    native_schema_graph_at F root J \<and> schema_graph_derives (positioned_program P) J root d t {} \<and>
    site_permission_invariant P d \<and> site_value_presents N u r t"
proof -
  obtain F au ar root t I K where recorded: "replay_scope_quoted_at R s F pu pr au ar root {}"
    "native_package_at F pu pr P" "native_package_environment F pu pr=E" "native_application_at F au ar d t I K"
    "site_permission_invariant P d" "site_value_presents N u r t"
    using current_site_permission_certificate_program[OF current certificate] by blast
  have replay: "native_replay_at F pu pr au ar root {}" using recorded(1) by (simp add: replay_scope_quoted_at_def)
  obtain J where graph: "native_schema_graph_at F root J" using replay unfolding native_replay_at_def by blast
  have derived: "schema_graph_derives (positioned_program P) J root d t {}"
    using native_replay_with_reads[OF recorded(2,4) graph] replay by blast
  show ?thesis using recorded graph derived by blast
qed

theorem current_site_permission_certificate_changed_subject:
  assumes first: "current_site_permission_certificate C q R s N u r"
    and changed: "N\<noteq>M \<or> u\<noteq>v \<or> r\<noteq>c"
  shows "\<not>current_site_permission_certificate D a R b M v c"
  using current_site_permission_certificate_subject_unique[OF first] changed by blast

section \<open>Every permission retains its original program and minimal call scope\<close>

theorem current_site_permission_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_permits_site_at C q F au ar N u r"
  shows "\<exists>R M root. current_site_permission_certificate C q R [] N u r \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and> native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_positive_holds F pu pr au ar"
    using current_site_permission_program_scope[OF current permitted] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_site_permission_at_scope[OF current] permitted by blast
  obtain R M root where recorded: "replay_scope_quoted_at R [] M pu pr au ar root {}"
    and reads: "native_package_at M pu pr P" "native_application_at M au ar d t I K"
    and exact: "native_package_environment M pu pr=native_package_environment F pu pr"
      "native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
    using positive_judgment_has_recorded_replay[OF program(3) app program(5)] by blast
  have mf: "environment_formed M" using replay_scope_formed[OF recorded] by blast
  have canonical: "native_package_environment M pu pr=E" using exact(1) program(4) by simp
  have included: "environment_included E M"
    using native_package_environment_included[of M pu pr] canonical by simp
  have retained: "current_permits_site_at C q M au ar N u r"
    using permitted by (simp only: current_site_permission_with_reads[OF current program(1,2) app]
      current_site_permission_with_reads[OF current mf included reads(2)])
  have certificate: "current_site_permission_certificate C q R [] N u r"
    using current_site_permission_certificate_with_scope[OF current recorded] retained by blast
  show ?thesis using certificate recorded canonical exact(2) by blast
qed

theorem current_site_permission_certificate_presentation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_permits_site P d N u r" and present: "site_value_presents N u r t"
  shows "\<exists>R F au root I K. current_site_permission_certificate C q R [] N u r \<and>
    replay_scope_quoted_at R [] F pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au [] d t I K"
proof -
  obtain M au I K where app: "native_application_at M au [] d t I K"
    and allowed: "current_permits_site_at C q M au [] N u r"
    using current_site_permission_application_total[OF current permitted present] by blast
  obtain R F root where certificate: "current_site_permission_certificate C q R [] N u r"
    "replay_scope_quoted_at R [] F pu pr au [] root {}" "native_package_environment F pu pr=E"
    "native_judgment_environment F pu pr au []=native_judgment_environment M pu pr au []"
    using current_site_permission_certification_total[OF current allowed] by blast
  have package: "native_package_at M pu pr P" using current_site_permission_program_scope[OF current allowed] by blast
  have original: "native_application_at (native_judgment_environment M pu pr au []) au [] d t I K"
    by (rule native_judgment_environment_recovers(2)[OF package app])
  have kept: "native_application_at (native_judgment_environment F pu pr au []) au [] d t I K"
    using original certificate(4) by simp
  have ff: "environment_formed F" using replay_scope_formed[OF certificate(2)] by blast
  have call: "native_application_at F au [] d t I K"
    by (rule native_application_included[OF kept native_judgment_environment_included ff])
  show ?thesis using certificate(1-3) call by blast
qed

theorem current_site_permission_certificate_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_permits_site P d N u r"
  shows "\<exists>R. current_site_permission_certificate C q R [] N u r"
proof -
  obtain t where present: "site_value_presents N u r t" using permitted unfolding factor_permits_site_def by blast
  show ?thesis using current_site_permission_certificate_presentation_total[OF current permitted present] by blast
qed

text \<open>
  A whole proof record uniquely fixes the complete permitted environment and
  actual site, even across different current frames. Changed bindings or a
  different site cannot be substituted into that same record. The proof uses
  the current frame's exact program site and selected permission entry.

  The closed native graph derives an ordinary permission call on complete
  site data. Every permitted presentation has such a record, and certification
  retains the original program and complete minimal call scope. This record
  establishes neither all truths at the submitted site nor adequate checking
  of an amendment's complete dependency obligations.
\<close>

end
