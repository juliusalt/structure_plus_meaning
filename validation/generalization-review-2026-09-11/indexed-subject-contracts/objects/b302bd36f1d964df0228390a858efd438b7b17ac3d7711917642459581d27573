theory Factor_Continuation
  imports Factor_Continuation_Values Factor_Native_Meaning
begin

section \<open>Continuation permission by an ordinary positive definition\<close>

definition continuation_permission_invariant ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "continuation_permission_invariant P d \<longleftrightarrow>
    (\<forall>S T U C cu cr t v. continuation_value_presents S T U C cu cr t \<longrightarrow>
      continuation_value_presents S T U C cu cr v \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P))"

lemma continuation_permission_invariantD:
  assumes invariant: "continuation_permission_invariant P d"
    and first: "continuation_value_presents S T U C cu cr t"
    and second: "continuation_value_presents S T U C cu cr v"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P"
  using invariant[unfolded continuation_permission_invariant_def, rule_format, OF first second] by auto

lemma continuation_permission_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
  shows "continuation_permission_invariant Q e\<longleftrightarrow>continuation_permission_invariant P d"
  by (simp add: continuation_permission_invariant_def boundary meaning)

theorem continuation_permission_factors_through_subject:
  "continuation_permission_invariant P d \<longleftrightarrow>
    (\<exists>B M. \<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B S T U C cu cr) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M S T U C cu cr))"
proof
  assume invariant: "continuation_permission_invariant P d"
  let ?B="\<lambda>S T U C cu cr. \<exists>v. continuation_value_presents S T U C cu cr v \<and> schema_call_formed P d v"
  let ?M="\<lambda>S T U C cu cr. \<exists>v. continuation_value_presents S T U C cu cr v \<and> (d,v)\<in>positive_meaning P"
  show "\<exists>B M. \<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B S T U C cu cr) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M S T U C cu cr)"
  proof (rule exI[of _ ?B], rule exI[of _ ?M], intro allI impI)
    fix S T U C cu cr t assume present: "continuation_value_presents S T U C cu cr t"
    have boundary: "\<And>v. continuation_value_presents S T U C cu cr v \<Longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v)"
      by (rule continuation_permission_invariantD(1)[OF invariant present])
    have meaning: "\<And>v. continuation_value_presents S T U C cu cr v \<Longrightarrow>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
      by (rule continuation_permission_invariantD(2)[OF invariant present])
    show "(schema_call_formed P d t\<longleftrightarrow>?B S T U C cu cr) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>?M S T U C cu cr)"
      using present boundary meaning by blast
  qed
next
  assume "\<exists>B M. \<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B S T U C cu cr) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M S T U C cu cr)"
  then obtain B M where factors: "\<And>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<Longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B S T U C cu cr) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M S T U C cu cr)" by blast
  show "continuation_permission_invariant P d" unfolding continuation_permission_invariant_def
  proof (intro allI impI)
    fix S T U C cu cr t v assume first: "continuation_value_presents S T U C cu cr t"
      and second: "continuation_value_presents S T U C cu cr v"
    show "(schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
      using factors[OF first] factors[OF second] by blast
  qed
qed

definition factor_continues ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow>
    selection_snapshot \<Rightarrow> local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> bool" where
  "factor_continues P d S T U C cu cr \<longleftrightarrow> continuation_permission_invariant P d \<and>
    (\<exists>t. continuation_value_presents S T U C cu cr t \<and> (d,t)\<in>positive_meaning P)"

lemma factor_continuation_formed:
  assumes permitted: "factor_continues P d S T U C cu cr"
  shows "schema_system_formed P \<and> snapshot_formed S \<and> transaction_formed T \<and> snapshot_formed U \<and>
    environment_formed C \<and> (cu,cr)\<in>environment_positions C"
proof -
  obtain t where present: "continuation_value_presents S T U C cu cr t" and truth: "(d,t)\<in>positive_meaning P"
    using permitted unfolding factor_continues_def by blast
  have program: "schema_system_formed P"
    using positive_meaning_formed[OF truth] by (simp add: schema_call_formed_def)
  show ?thesis using program continuation_value_presents_formed[OF present] by blast
qed

theorem factor_continuation_at_presentation:
  assumes invariant: "continuation_permission_invariant P d"
    and present: "continuation_value_presents S T U C cu cr t"
  shows "factor_continues P d S T U C cu cr\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof
  assume "factor_continues P d S T U C cu cr"
  then obtain v where other: "continuation_value_presents S T U C cu cr v" "(d,v)\<in>positive_meaning P"
    by (auto simp: factor_continues_def)
  show "(d,t)\<in>positive_meaning P"
    using continuation_permission_invariantD(2)[OF invariant other(1) present] other(2) by blast
next
  assume "(d,t)\<in>positive_meaning P"
  then show "factor_continues P d S T U C cu cr" using invariant present unfolding factor_continues_def by blast
qed

theorem factor_continuation_every_presentation:
  "factor_continues P d S T U C cu cr\<longleftrightarrow>
    snapshot_formed S \<and> transaction_formed T \<and> snapshot_formed U \<and>
    environment_formed C \<and> (cu,cr)\<in>environment_positions C \<and> continuation_permission_invariant P d \<and>
    (\<forall>t. continuation_value_presents S T U C cu cr t \<longrightarrow> (d,t)\<in>positive_meaning P)"
proof
  assume permitted: "factor_continues P d S T U C cu cr"
  have invariant: "continuation_permission_invariant P d" using permitted by (simp add: factor_continues_def)
  have every: "\<forall>t. continuation_value_presents S T U C cu cr t \<longrightarrow> (d,t)\<in>positive_meaning P"
    using permitted factor_continuation_at_presentation[OF invariant] by blast
  show "snapshot_formed S \<and> transaction_formed T \<and> snapshot_formed U \<and>
    environment_formed C \<and> (cu,cr)\<in>environment_positions C \<and> continuation_permission_invariant P d \<and>
    (\<forall>t. continuation_value_presents S T U C cu cr t \<longrightarrow> (d,t)\<in>positive_meaning P)"
    using factor_continuation_formed[OF permitted] invariant every by blast
next
  assume parts: "snapshot_formed S \<and> transaction_formed T \<and> snapshot_formed U \<and>
    environment_formed C \<and> (cu,cr)\<in>environment_positions C \<and> continuation_permission_invariant P d \<and>
    (\<forall>t. continuation_value_presents S T U C cu cr t \<longrightarrow> (d,t)\<in>positive_meaning P)"
  obtain t where present: "continuation_value_presents S T U C cu cr t"
    using continuation_value_presents_total parts by blast
  show "factor_continues P d S T U C cu cr" using parts present unfolding factor_continues_def by blast
qed

section \<open>Native continuation keeps its actual semantic dependency boundary\<close>

definition native_continuation_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "native_continuation_at E pu pr au ar S T U C cu cr \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
      (d,t)\<in>positive_meaning P)"

lemma native_continuation_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>
    continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
    (d,t)\<in>positive_meaning P"
proof
  assume "native_continuation_at E pu pr au ar S T U C cu cr"
  then obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "continuation_permission_invariant Q e" "continuation_value_presents S T U C cu cr v"
    "(e,v)\<in>positive_meaning Q" unfolding native_continuation_at_def by blast
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
    (d,t)\<in>positive_meaning P" using other(3-5) programs calls by simp
next
  assume "continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
    (d,t)\<in>positive_meaning P"
  then show "native_continuation_at E pu pr au ar S T U C cu cr"
    using package app unfolding native_continuation_at_def by blast
qed

lemma native_continuation_truth:
  assumes "native_continuation_at E pu pr au ar S T U C cu cr"
  shows "native_positive_holds E pu pr au ar"
  using assms unfolding native_continuation_at_def native_positive_holds_def by blast

theorem native_continuation_at_presentation:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and invariant: "continuation_permission_invariant P d"
    and present: "continuation_value_presents S T U C cu cr t"
  shows "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>factor_continues P d S T U C cu cr"
  by (simp only: native_continuation_with_reads[OF package app]
      factor_continuation_at_presentation[OF invariant present] invariant present simp_thms)

theorem native_continuation_subject_unique:
  assumes first: "native_continuation_at E pu pr au ar S T U C cu cr"
    and second: "native_continuation_at E qu qr au ar V W X D du dr"
  shows "S=V \<and> T=W \<and> U=X \<and> C=D \<and> cu=du \<and> cr=dr"
proof -
  obtain d t I K where left: "native_application_at E au ar d t I K"
    "continuation_value_presents S T U C cu cr t" using first unfolding native_continuation_at_def by blast
  obtain e v J L where right: "native_application_at E au ar e v J L"
    "continuation_value_presents V W X D du dr v" using second unfolding native_continuation_at_def by blast
  have same: "t=v" using native_application_unique[OF left(1) right(1)] by blast
  have other: "continuation_value_presents V W X D du dr t" using right(2) same by simp
  show ?thesis by (rule continuation_value_presents_unique[OF left(2) other])
qed

theorem native_continuation_presentations_agree:
  assumes first: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and second: "native_package_at F qu qr P" "native_application_at F bu br d v J L"
    and invariant: "continuation_permission_invariant P d"
    and left: "continuation_value_presents S T U C cu cr t"
    and right: "continuation_value_presents S T U C cu cr v"
  shows "native_application_formed E pu pr au ar\<longleftrightarrow>native_application_formed F qu qr bu br"
    and "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>
      native_continuation_at F qu qr bu br S T U C cu cr"
proof -
  show "native_application_formed E pu pr au ar\<longleftrightarrow>native_application_formed F qu qr bu br"
    using native_application_formed_with_reads[OF first] native_application_formed_with_reads[OF second]
      continuation_permission_invariantD(1)[OF invariant left right] by blast
  show "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>
      native_continuation_at F qu qr bu br S T U C cu cr"
    by (simp only: native_continuation_at_presentation[OF first invariant left]
        native_continuation_at_presentation[OF second invariant right])
qed

theorem native_continuation_dependency_locality:
  assumes package: "native_package_at E pu pr P" and formed: "environment_formed F"
    and included: "environment_included (native_package_environment E pu pr) F"
    and first: "native_application_at E au ar d t I K" and second: "native_application_at F bu br d t J L"
  shows "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>
    native_continuation_at F pu pr bu br S T U C cu cr"
proof -
  have copied: "native_package_at F pu pr P" by (rule native_package_dependency_locality[OF package formed included])
  show ?thesis by (simp only: native_continuation_with_reads[OF package first]
      native_continuation_with_reads[OF copied second])
qed

theorem native_continuation_missing_program_material:
  assumes package: "native_package_at E pu pr P" and smaller: "environment_included F E"
    and missing: "\<not>environment_included (native_package_environment E pu pr) F"
  shows "\<not>native_continuation_at F pu pr au ar S T U C cu cr"
proof
  assume "native_continuation_at F pu pr au ar S T U C cu cr"
  then obtain Q where read: "native_package_at F pu pr Q" unfolding native_continuation_at_def by blast
  have "environment_included (native_package_environment E pu pr) F"
    by (rule native_package_dependency_material_required[OF package read smaller])
  then show False using missing by blast
qed

section \<open>Advancement joins structural success and continuation permission\<close>

definition factor_advances ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow>
    selection_snapshot \<Rightarrow> local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> bool" where
  "factor_advances P d S T U C cu cr \<longleftrightarrow>
    transact S T (Applied U) \<and> factor_continues P d S T U C cu cr"

definition native_advance_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "native_advance_at E pu pr au ar S T U C cu cr \<longleftrightarrow>
    transact S T (Applied U) \<and> native_continuation_at E pu pr au ar S T U C cu cr"

theorem native_advance_at_presentation:
  assumes "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "continuation_permission_invariant P d" "continuation_value_presents S T U C cu cr t"
  shows "native_advance_at E pu pr au ar S T U C cu cr\<longleftrightarrow>factor_advances P d S T U C cu cr"
  by (simp only: native_advance_at_def factor_advances_def native_continuation_at_presentation[OF assms])

lemma native_advance_output_unique:
  assumes "native_advance_at E pu pr au ar S T U C cu cr"
    "native_advance_at F qu qr bu br S T V D du dr"
  shows "U=V"
  using assms by (auto simp: native_advance_at_def transact_applied_iff)

lemma native_advance_conflict_rejected:
  assumes "transact S T (Conflict observations)"
  shows "\<not>native_advance_at E pu pr au ar S T U C cu cr"
  using assms by (auto simp: native_advance_at_def transact_conflict_iff transact_applied_iff)

lemma native_advance_no_extra_change:
  assumes advance: "native_advance_at E pu pr au ar S T U C cu cr" and outside: "l\<notin>changed_loci T"
  shows "snapshot_lookup U l=snapshot_lookup S l"
proof -
  have trans: "transact S T (Applied U)" using advance by (simp add: native_advance_at_def)
  show ?thesis by (rule successful_transaction_no_extra_change[OF trans outside])
qed

text \<open>
  Continuation is the truth of a supplied ordinary program on the complete
  argument. Its admission requires formation and truth invariance over every
  presentation of that argument. The exact native application determines its
  whole subject, and the program's actual dependency environment determines
  its meaning. A subenvironment missing required program material cannot
  acquire continuation permission from any supplied history or other data.

  Advancement additionally checks the independently supplied after snapshot
  against structural comparison and replacement. No historical predecessor,
  semantic dependency, construction input, or authority boundary is equated
  with another. A particular policy can state relationships between them.
  This raw join supplies no adoption, cause validity, or evidence predicate.
\<close>

end
