theory Factor_Authority
  imports Factor_Adoption_Values Factor_Native_Meaning RRA_Publication_Dependencies
begin

section \<open>Raw adoption by an explicit ordinary definition\<close>

definition adoption_permission_invariant ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "adoption_permission_invariant P d \<longleftrightarrow>
    (\<forall>A G purpose t v. adoption_value_presents A G purpose t \<longrightarrow>
      adoption_value_presents A G purpose v \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P))"

lemma adoption_permission_invariantD:
  assumes invariant: "adoption_permission_invariant P d"
    and first: "adoption_value_presents A G purpose t" and second: "adoption_value_presents A G purpose v"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P"
  using invariant[unfolded adoption_permission_invariant_def, rule_format, OF first second] by auto

lemma adoption_permission_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
  shows "adoption_permission_invariant Q e\<longleftrightarrow>adoption_permission_invariant P d"
  by (simp add: adoption_permission_invariant_def boundary meaning)

theorem adoption_permission_factors_through_subject:
  "adoption_permission_invariant P d \<longleftrightarrow>
    (\<exists>B M. \<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B A G purpose) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M A G purpose))"
proof
  assume invariant: "adoption_permission_invariant P d"
  let ?B="\<lambda>A G p. \<exists>v. adoption_value_presents A G p v \<and> schema_call_formed P d v"
  let ?M="\<lambda>A G p. \<exists>v. adoption_value_presents A G p v \<and> (d,v)\<in>positive_meaning P"
  show "\<exists>B M. \<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B A G purpose) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M A G purpose)"
  proof (rule exI[of _ ?B], rule exI[of _ ?M], intro allI impI)
    fix A G p t assume present: "adoption_value_presents A G p t"
    have boundary: "\<And>v. adoption_value_presents A G p v \<Longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v)"
      by (rule adoption_permission_invariantD(1)[OF invariant present])
    have meaning: "\<And>v. adoption_value_presents A G p v \<Longrightarrow>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
      by (rule adoption_permission_invariantD(2)[OF invariant present])
    show "(schema_call_formed P d t\<longleftrightarrow>?B A G p) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>?M A G p)"
      using present boundary meaning by blast
  qed
next
  assume "\<exists>B M. \<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B A G purpose) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M A G purpose)"
  then obtain B M where factors: "\<And>A G purpose t. adoption_value_presents A G purpose t \<Longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>B A G purpose) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>M A G purpose)" by blast
  show "adoption_permission_invariant P d" unfolding adoption_permission_invariant_def
  proof (intro allI impI)
    fix A G p t v assume first: "adoption_value_presents A G p t" and second: "adoption_value_presents A G p v"
    show "(schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
      using factors[OF first] factors[OF second] by blast
  qed
qed

definition factor_adopts ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> exact_target \<Rightarrow> generation_core \<Rightarrow>
    exact_target \<Rightarrow> bool" where
  "factor_adopts P d A G purpose \<longleftrightarrow> adoption_permission_invariant P d \<and>
    (\<exists>t. adoption_value_presents A G purpose t \<and> (d,t)\<in>positive_meaning P)"

lemma factor_adoption_formed:
  assumes adopted: "factor_adopts P d A G purpose"
  shows "schema_system_formed P \<and> target_formed A \<and> generation_formed G \<and> target_formed purpose"
proof -
  obtain t where present: "adoption_value_presents A G purpose t" and truth: "(d,t)\<in>positive_meaning P"
    using adopted unfolding factor_adopts_def by blast
  have program: "schema_system_formed P"
    using positive_meaning_formed[OF truth] by (simp add: schema_call_formed_def)
  show ?thesis using program adoption_value_presents_formed[OF present] by blast
qed

theorem factor_adoption_at_presentation:
  assumes invariant: "adoption_permission_invariant P d" and present: "adoption_value_presents A G purpose t"
  shows "factor_adopts P d A G purpose\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof
  assume "factor_adopts P d A G purpose"
  then obtain v where other: "adoption_value_presents A G purpose v" "(d,v)\<in>positive_meaning P"
    by (auto simp: factor_adopts_def)
  show "(d,t)\<in>positive_meaning P"
    using adoption_permission_invariantD(2)[OF invariant other(1) present] other(2) by blast
next
  assume "(d,t)\<in>positive_meaning P"
  then show "factor_adopts P d A G purpose" using invariant present unfolding factor_adopts_def by blast
qed

theorem factor_adoption_every_presentation:
  "factor_adopts P d A G purpose\<longleftrightarrow>
    target_formed A \<and> generation_formed G \<and> target_formed purpose \<and> adoption_permission_invariant P d \<and>
    (\<forall>t. adoption_value_presents A G purpose t \<longrightarrow> (d,t)\<in>positive_meaning P)"
proof
  assume adopted: "factor_adopts P d A G purpose"
  have invariant: "adoption_permission_invariant P d" using adopted by (simp add: factor_adopts_def)
  have every: "\<forall>t. adoption_value_presents A G purpose t \<longrightarrow> (d,t)\<in>positive_meaning P"
    using adopted factor_adoption_at_presentation[OF invariant] by blast
  show "target_formed A \<and> generation_formed G \<and> target_formed purpose \<and> adoption_permission_invariant P d \<and>
    (\<forall>t. adoption_value_presents A G purpose t \<longrightarrow> (d,t)\<in>positive_meaning P)"
    using factor_adoption_formed[OF adopted] invariant every by blast
next
  assume parts: "target_formed A \<and> generation_formed G \<and> target_formed purpose \<and> adoption_permission_invariant P d \<and>
    (\<forall>t. adoption_value_presents A G purpose t \<longrightarrow> (d,t)\<in>positive_meaning P)"
  obtain t where present: "adoption_value_presents A G purpose t"
    using adoption_value_presents_total parts by blast
  show "factor_adopts P d A G purpose" using parts present unfolding factor_adopts_def by blast
qed

section \<open>Native adoption retains its actual program and application\<close>

definition native_adoption_judgment_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "native_adoption_judgment_at E pu pr au ar A G purpose \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      adoption_permission_invariant P d \<and> adoption_value_presents A G purpose t \<and>
      (d,t)\<in>positive_meaning P)"

lemma native_adoption_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_adoption_judgment_at E pu pr au ar A G purpose \<longleftrightarrow>
    adoption_permission_invariant P d \<and> adoption_value_presents A G purpose t \<and> (d,t)\<in>positive_meaning P"
proof
  assume "native_adoption_judgment_at E pu pr au ar A G purpose"
  then obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "adoption_permission_invariant Q e" "adoption_value_presents A G purpose v" "(e,v)\<in>positive_meaning Q"
    unfolding native_adoption_judgment_at_def by blast
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "adoption_permission_invariant P d \<and> adoption_value_presents A G purpose t \<and> (d,t)\<in>positive_meaning P"
    using other(3-5) programs calls by simp
next
  assume "adoption_permission_invariant P d \<and> adoption_value_presents A G purpose t \<and> (d,t)\<in>positive_meaning P"
  then show "native_adoption_judgment_at E pu pr au ar A G purpose"
    using package app unfolding native_adoption_judgment_at_def by blast
qed

lemma native_adoption_truth:
  assumes "native_adoption_judgment_at E pu pr au ar A G purpose"
  shows "native_positive_holds E pu pr au ar"
  using assms unfolding native_adoption_judgment_at_def native_positive_holds_def by blast

lemma native_adoption_formed:
  assumes adopted: "native_adoption_judgment_at E pu pr au ar A G purpose"
  shows "target_formed A \<and> generation_formed G \<and> target_formed purpose"
proof -
  obtain t where present: "adoption_value_presents A G purpose t"
    using adopted unfolding native_adoption_judgment_at_def by blast
  show ?thesis using adoption_value_presents_formed[OF present] by blast
qed

theorem native_adoption_at_presentation:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and invariant: "adoption_permission_invariant P d" and present: "adoption_value_presents A G purpose t"
  shows "native_adoption_judgment_at E pu pr au ar A G purpose\<longleftrightarrow>factor_adopts P d A G purpose"
  by (simp only: native_adoption_with_reads[OF package app]
      factor_adoption_at_presentation[OF invariant present] invariant present simp_thms)

theorem native_adoption_subject_unique:
  assumes first: "native_adoption_judgment_at E pu pr au ar A G purpose"
    and second: "native_adoption_judgment_at E qu qr au ar B H other"
  shows "A=B \<and> G=H \<and> purpose=other"
proof -
  obtain d t I K where left: "native_application_at E au ar d t I K" "adoption_value_presents A G purpose t"
    using first unfolding native_adoption_judgment_at_def by blast
  obtain e v J L where right: "native_application_at E au ar e v J L" "adoption_value_presents B H other v"
    using second unfolding native_adoption_judgment_at_def by blast
  have same: "t=v" using native_application_unique[OF left(1) right(1)] by blast
  have other: "adoption_value_presents B H other t" using right(2) same by simp
  show ?thesis by (rule adoption_value_presents_unique[OF left(2) other])
qed

theorem native_adoption_presentations_agree:
  assumes first: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and second: "native_package_at F qu qr P" "native_application_at F bu br d v J L"
    and invariant: "adoption_permission_invariant P d"
    and left: "adoption_value_presents A G purpose t" and right: "adoption_value_presents A G purpose v"
  shows "native_application_formed E pu pr au ar\<longleftrightarrow>native_application_formed F qu qr bu br"
    and "native_adoption_judgment_at E pu pr au ar A G purpose\<longleftrightarrow>
      native_adoption_judgment_at F qu qr bu br A G purpose"
proof -
  show "native_application_formed E pu pr au ar\<longleftrightarrow>native_application_formed F qu qr bu br"
    using native_application_formed_with_reads[OF first] native_application_formed_with_reads[OF second]
      adoption_permission_invariantD(1)[OF invariant left right] by blast
  show "native_adoption_judgment_at E pu pr au ar A G purpose\<longleftrightarrow>
      native_adoption_judgment_at F qu qr bu br A G purpose"
    by (simp only: native_adoption_at_presentation[OF first invariant left]
        native_adoption_at_presentation[OF second invariant right])
qed

theorem native_adoption_dependency_locality:
  assumes package: "native_package_at E pu pr P" and formed: "environment_formed F"
    and included: "environment_included (native_package_environment E pu pr) F"
    and first: "native_application_at E au ar d t I K" and second: "native_application_at F bu br d t J L"
  shows "native_adoption_judgment_at E pu pr au ar A G purpose\<longleftrightarrow>
    native_adoption_judgment_at F pu pr bu br A G purpose"
proof -
  have copied: "native_package_at F pu pr P" by (rule native_package_dependency_locality[OF package formed included])
  show ?thesis by (simp only: native_adoption_with_reads[OF package first]
      native_adoption_with_reads[OF copied second])
qed

section \<open>Currentness is relative to an exact publication scope\<close>

definition native_current ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> 'v artifact_environment \<Rightarrow> 'v \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "native_current E pu pr au ar A F v root l G purpose \<longleftrightarrow>
    native_adoption_judgment_at E pu pr au ar A G purpose \<and>
    (\<exists>P. publication_environment_closed F v root P \<and> snapshot_lookup (publication_snapshot P) l=Some G)"

lemma native_current_with_publication:
  assumes pub: "publication_environment_closed F v root P"
  shows "native_current E pu pr au ar A F v root l G purpose \<longleftrightarrow>
    native_adoption_judgment_at E pu pr au ar A G purpose \<and> snapshot_lookup (publication_snapshot P) l=Some G"
proof -
  have reading: "publication_at F v root P" using pub by (simp add: publication_environment_closed_def)
  have unique: "\<And>Q. publication_environment_closed F v root Q \<Longrightarrow> Q=P"
  proof -
    fix Q assume "publication_environment_closed F v root Q"
    then have other: "publication_at F v root Q" by (simp add: publication_environment_closed_def)
    show "Q=P" by (rule publication_at_unique[OF other reading])
  qed
  show ?thesis using pub unique unfolding native_current_def by blast
qed

lemma native_current_selected:
  assumes current: "native_current E pu pr au ar A F v root l G purpose"
    and pub: "publication_at F v root P"
  shows "G\<in>fset (publication_snapshot P) \<and> generation_locus G=l"
proof -
  obtain Q where closed: "publication_environment_closed F v root Q"
    and selected: "snapshot_lookup (publication_snapshot Q) l=Some G"
    using current unfolding native_current_def by blast
  have other: "publication_at F v root Q" using closed by (simp add: publication_environment_closed_def)
  have same: "Q=P" by (rule publication_at_unique[OF other pub])
  have formed: "snapshot_formed (publication_snapshot P)"
    using publication_at_formed[OF pub] by (simp add: publication_formed_def)
  show ?thesis using selected same snapshot_lookup_some[OF formed, of l G] by simp
qed

lemma native_current_locus:
  assumes current: "native_current E pu pr au ar A F v root l G purpose"
  shows "generation_locus G=l"
proof -
  obtain P where closed: "publication_environment_closed F v root P" using current unfolding native_current_def by blast
  have pub: "publication_at F v root P" using closed by (simp add: publication_environment_closed_def)
  show ?thesis using native_current_selected[OF current pub] by blast
qed

theorem native_current_generation_unique:
  assumes first: "native_current E pu pr au ar A F v root l G purpose"
    and second: "native_current H qu qr bu br B F v root l K other"
  shows "G=K"
proof -
  obtain P where pub: "publication_environment_closed F v root P" using first unfolding native_current_def by blast
  have left: "snapshot_lookup (publication_snapshot P) l=Some G"
    using first by (simp only: native_current_with_publication[OF pub])
  have right: "snapshot_lookup (publication_snapshot P) l=Some K"
    using second by (simp only: native_current_with_publication[OF pub])
  show ?thesis using left right by simp
qed

theorem native_current_program_locality:
  assumes package: "native_package_at E pu pr P" and formed: "environment_formed H"
    and included: "environment_included (native_package_environment E pu pr) H"
    and first: "native_application_at E au ar d t I K" and second: "native_application_at H bu br d t J L"
  shows "native_current E pu pr au ar A F v root l G purpose\<longleftrightarrow>
    native_current H pu pr bu br A F v root l G purpose"
  by (simp only: native_current_def native_adoption_dependency_locality[OF package formed included first second])

text \<open>
  Raw adoption is an ordinary application of a supplied positive definition
  to the complete authority, generation, and purpose data. The definition
  itself determines permission. Admission as a policy on these data requires
  formation and truth invariance across all their complete presentations.
  No generation-cause validity or proof predicate occurs in this layer.

  Currentness additionally uses an exact closed publication scope and the
  generation selected at the supplied locus. It is relative to the actual
  program and call, authority, publication scope and site, locus, generation,
  and purpose. The locus is recovered from the selected core. Currentness is
  not a field of a generation, and an adoption need not be published anywhere.
  Retaining the program's complete dependency environment preserves adoption
  and currentness. Checking policy-admission evidence is a higher obligation.
\<close>

end
