theory Factor_Site_Permission
  imports Factor_Site_Values Factor_Native_Meaning
begin

section \<open>Ordinary permission on one exact environment and site\<close>

definition site_permission_invariant ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "site_permission_invariant P d \<longleftrightarrow>
    (\<forall>N u r t v. site_value_presents N u r t \<longrightarrow> site_value_presents N u r v \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P))"

lemma site_permission_invariantD:
  assumes invariant: "site_permission_invariant P d"
    and first: "site_value_presents N u r t" and second: "site_value_presents N u r v"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P"
  using invariant[unfolded site_permission_invariant_def, rule_format, OF first second] by auto

lemma site_permission_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
  shows "site_permission_invariant Q e\<longleftrightarrow>site_permission_invariant P d"
  by (simp add: site_permission_invariant_def boundary meaning)

definition factor_permits_site ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "factor_permits_site P d N u r \<longleftrightarrow> site_permission_invariant P d \<and>
    (\<exists>t. site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P)"

lemma factor_site_permission_formed:
  assumes permitted: "factor_permits_site P d N u r"
  shows "schema_system_formed P \<and> environment_formed N \<and> (u,r)\<in>environment_positions N"
proof -
  obtain t where present: "site_value_presents N u r t" and truth: "(d,t)\<in>positive_meaning P"
    using permitted unfolding factor_permits_site_def by blast
  have program: "schema_system_formed P" using positive_meaning_formed[OF truth]
    by (simp add: schema_call_formed_def)
  have site: "(u,r)\<in>environment_positions N" using present by (simp add: site_value_presents_def)
  show ?thesis using program site site_value_presents_formed[OF present] by blast
qed

theorem factor_site_permission_at_presentation:
  assumes invariant: "site_permission_invariant P d" and present: "site_value_presents N u r t"
  shows "factor_permits_site P d N u r\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof
  assume "factor_permits_site P d N u r"
  then obtain v where other: "site_value_presents N u r v" "(d,v)\<in>positive_meaning P"
    unfolding factor_permits_site_def by blast
  show "(d,t)\<in>positive_meaning P" using site_permission_invariantD(2)[OF invariant other(1) present] other(2) by blast
next
  assume "(d,t)\<in>positive_meaning P"
  then show "factor_permits_site P d N u r" using invariant present unfolding factor_permits_site_def by blast
qed

theorem factor_site_permission_every_presentation:
  "factor_permits_site P d N u r\<longleftrightarrow>
    environment_formed N \<and> (u,r)\<in>environment_positions N \<and> site_permission_invariant P d \<and>
    (\<forall>t. site_value_presents N u r t \<longrightarrow> (d,t)\<in>positive_meaning P)"
proof
  assume permitted: "factor_permits_site P d N u r"
  have invariant: "site_permission_invariant P d" using permitted by (simp add: factor_permits_site_def)
  show "environment_formed N \<and> (u,r)\<in>environment_positions N \<and> site_permission_invariant P d \<and>
    (\<forall>t. site_value_presents N u r t \<longrightarrow> (d,t)\<in>positive_meaning P)"
    using factor_site_permission_formed[OF permitted] invariant
      factor_site_permission_at_presentation[OF invariant] permitted by blast
next
  assume fields: "environment_formed N \<and> (u,r)\<in>environment_positions N \<and> site_permission_invariant P d \<and>
    (\<forall>t. site_value_presents N u r t \<longrightarrow> (d,t)\<in>positive_meaning P)"
  obtain t where present: "site_value_presents N u r t"
    using site_value_presents_total fields by blast
  show "factor_permits_site P d N u r" using fields present unfolding factor_permits_site_def by blast
qed

section \<open>The submitted scope is data for an actual native permission call\<close>

definition native_site_permission_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "native_site_permission_at F pu pr au ar N u r \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
      site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P)"

theorem native_site_permission_with_reads:
  assumes package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "native_site_permission_at F pu pr au ar N u r\<longleftrightarrow>
    site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P"
proof
  assume "native_site_permission_at F pu pr au ar N u r"
  then obtain Q e v J L where other: "native_package_at F pu pr Q" "native_application_at F au ar e v J L"
    "site_permission_invariant Q e" "site_value_presents N u r v" "(e,v)\<in>positive_meaning Q"
    unfolding native_site_permission_at_def by blast
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P"
    using other(3-5) programs calls by simp
next
  assume "site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P"
  then show "native_site_permission_at F pu pr au ar N u r"
    using package app unfolding native_site_permission_at_def by blast
qed

lemma native_site_permission_truth:
  assumes "native_site_permission_at F pu pr au ar N u r"
  shows "native_positive_holds F pu pr au ar"
  using assms unfolding native_site_permission_at_def native_positive_holds_def by blast

theorem native_site_permission_at_presentation:
  assumes package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    and invariant: "site_permission_invariant P d" and present: "site_value_presents N u r t"
  shows "native_site_permission_at F pu pr au ar N u r\<longleftrightarrow>factor_permits_site P d N u r"
  by (simp only: native_site_permission_with_reads[OF package app] invariant present
    factor_site_permission_at_presentation[OF invariant present] simp_thms)

theorem native_site_permission_subject_unique:
  assumes first: "native_site_permission_at F pu pr au ar N u r"
    and second: "native_site_permission_at F qu qr au ar M v s"
  shows "N=M \<and> u=v \<and> r=s"
proof -
  obtain d t I K where left: "native_application_at F au ar d t I K" "site_value_presents N u r t"
    using first unfolding native_site_permission_at_def by blast
  obtain e w J L where right: "native_application_at F au ar e w J L" "site_value_presents M v s w"
    using second unfolding native_site_permission_at_def by blast
  have same: "t=w" using native_application_unique[OF left(1) right(1)] by blast
  have other: "site_value_presents M v s t" using right(2) same by simp
  show ?thesis by (rule site_value_presents_unique[OF left(2) other])
qed

theorem native_site_permission_presentations_agree:
  assumes first: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and second: "native_package_at M qu qr P" "native_application_at M bu br d v J L"
    and invariant: "site_permission_invariant P d"
    and left: "site_value_presents N u r t" and right: "site_value_presents N u r v"
  shows "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M qu qr bu br"
    and "native_site_permission_at F pu pr au ar N u r\<longleftrightarrow>native_site_permission_at M qu qr bu br N u r"
proof -
  show "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M qu qr bu br"
    using native_application_formed_with_reads[OF first] native_application_formed_with_reads[OF second]
      site_permission_invariantD(1)[OF invariant left right] by blast
  show "native_site_permission_at F pu pr au ar N u r\<longleftrightarrow>native_site_permission_at M qu qr bu br N u r"
    by (simp only: native_site_permission_at_presentation[OF first invariant left]
      native_site_permission_at_presentation[OF second invariant right])
qed

text \<open>
  The complete environment and actual site are ordinary arguments to a
  supplied positive definition. The policy's formation and truth must agree
  across every complete presentation of that subject. The native call fixes
  the whole subject and invokes only its own program's clauses.

  Permission supplies no meaning to the submitted site and proves no arbitrary
  application at it. A later dependency profile must independently establish
  that the site is a required definition of an actual closed program. A
  concrete policy must state what it checks before giving this permission;
  its adequacy does not follow from the name of this relation.
\<close>

end
