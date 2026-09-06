theory Factor_Transition_Dependencies
  imports Factor_Transition_Accounts Factor_Dependency_Evidence
begin

section \<open>The accepted account material contains the complete dependency evidence\<close>

definition transition_dependency_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "transition_dependency_certificate C q K H X \<longleftrightarrow>
    transition_account_certificate C q K H X \<and>
    (\<exists>S T U B bu br M mu mr D R N nu nr.
      continuation_envelope C q K S T U B bu br \<and> successor_material_at B bu br X M mu mr \<and>
      assembly_support_at M mu mr D R N nu nr \<and> amendment_dependency_evidence_at C q H N nu nr)"

lemma transition_dependency_account:
  assumes "transition_dependency_certificate C q K H X"
  shows "transition_account_certificate C q K H X"
  using assms by (simp add: transition_dependency_certificate_def)

theorem transition_dependency_with_material:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
  shows "transition_dependency_certificate C q K H X\<longleftrightarrow>
    transition_account_certificate C q K H X \<and> amendment_dependency_evidence_at C q H N nu nr"
proof
  assume certificate: "transition_dependency_certificate C q K H X"
  then obtain S' T' U' B' bu' br' M' mu' mr' D' R' N' nu' nr' where other:
    "continuation_envelope C q K S' T' U' B' bu' br'"
    "successor_material_at B' bu' br' X M' mu' mr'" "assembly_support_at M' mu' mr' D' R' N' nu' nr'"
    "amendment_dependency_evidence_at C q H N' nu' nr'"
    unfolding transition_dependency_certificate_def by blast
  have same: "N=N' \<and> nu=nu' \<and> nr=nr'"
    using transition_account_material_unique[OF envelope body support other(1-3)] by blast
  show "transition_account_certificate C q K H X \<and> amendment_dependency_evidence_at C q H N nu nr"
    using transition_dependency_account[OF certificate] other(4) same by simp
next
  assume parts: "transition_account_certificate C q K H X \<and> amendment_dependency_evidence_at C q H N nu nr"
  then have account: "transition_account_certificate C q K H X"
    and evidence: "amendment_dependency_evidence_at C q H N nu nr" by auto
  show "transition_dependency_certificate C q K H X" unfolding transition_dependency_certificate_def
    by (rule conjI[OF account], rule exI[of _ S], rule exI[of _ T], rule exI[of _ U], rule exI[of _ B],
        rule exI[of _ bu], rule exI[of _ br], rule exI[of _ M], rule exI[of _ mu], rule exI[of _ mr],
        rule exI[of _ D], rule exI[of _ R], rule exI[of _ N], rule exI[of _ nu], rule exI[of _ nr])
       (use envelope body support evidence in blast)
qed

theorem transition_dependency_with_collection:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
    and collection: "dependency_support_at N nu nr E Rs L lu lr"
  shows "transition_dependency_certificate C q K H X\<longleftrightarrow>
    transition_account_certificate C q K H X \<and> (\<exists>r. amendment_dependency_evidence C q H E r Rs)"
  by (simp only: transition_dependency_with_material[OF envelope body support]
    amendment_dependency_evidence_at_with_support[OF collection])

theorem transition_dependency_material_unique:
  assumes left: "continuation_envelope C q K S T U B bu br"
    "successor_material_at B bu br X M mu mr" "assembly_support_at M mu mr D R N nu nr"
    "dependency_support_at N nu nr E Rs L lu lr"
    and right: "continuation_envelope C' q' K S' T' U' B' bu' br'"
    "successor_material_at B' bu' br' X' M' mu' mr'" "assembly_support_at M' mu' mr' D' R' N' nu' nr'"
    "dependency_support_at N' nu' nr' E' Rs' L' lu' lr'"
  shows "X=X' \<and> E=E' \<and> Rs=Rs' \<and> L=L' \<and> lu=lu' \<and> lr=lr'"
proof -
  have same: "X=X' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
    using transition_account_material_unique[OF left(1-3) right(1-3)] by blast
  have other: "dependency_support_at N nu nr E' Rs' L' lu' lr'" using right(4) same by simp
  show ?thesis using same dependency_support_at_unique[OF left(4) other] by blast
qed

theorem transition_dependency_coverage:
  assumes subjects: "amendment_dependency_subjects C q H V"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
    and collection: "dependency_support_at N nu nr E Rs L lu lr"
    and certificate: "transition_dependency_certificate C q K H X"
  shows "finite Rs \<and> Rs\<noteq>{} \<and>
    (\<exists>r. amendment_dependency_evidence C q H E r Rs \<and>
      current_companion C q E r \<and> site_evidence_covers E r V Rs)"
proof -
  obtain r where evidence: "amendment_dependency_evidence C q H E r Rs"
    using certificate by (simp only: transition_dependency_with_collection[OF envelope body support collection]; blast)
  have scope: "current_companion C q E r \<and> site_evidence_covers E r V Rs"
    using evidence by (simp only: amendment_dependency_evidence_with_subjects[OF subjects])
  show ?thesis using evidence scope amendment_dependency_evidence_formed[OF evidence] by blast
qed

theorem transition_dependency_empty_collection_rejected:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
    and collection: "dependency_support_at N nu nr E {} L lu lr"
  shows "\<not>transition_dependency_certificate C q K H X"
  by (simp only: transition_dependency_with_collection[OF assms]
    amendment_dependency_empty_evidence_rejected; blast)

theorem transition_dependency_extra_subject_rejected:
  assumes subjects: "amendment_dependency_subjects C q H V" and outside: "x\<notin>V" and member: "Q\<in>Rs"
    and wrong: "current_site_permission_certificate D0 r0 Q s0 (fst x) (fst (snd x)) (snd (snd x))"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
    and collection: "dependency_support_at N nu nr E Rs L lu lr"
  shows "\<not>transition_dependency_certificate C q K H X"
proof
  assume certificate: "transition_dependency_certificate C q K H X"
  obtain r where covered: "site_evidence_covers E r V Rs"
    using transition_dependency_coverage[OF subjects envelope body support collection certificate] by blast
  obtain y s where other: "y\<in>V"
    "current_site_permission_certificate E r Q s (fst y) (fst (snd y)) (snd (snd y))"
    using site_evidence_covers_record[OF covered member] by blast
  have same: "x=y" by (rule site_permission_record_subject_unique[OF wrong other(2)])
  show False using outside other(1) same by simp
qed

section \<open>Actual acceptance and its separate replay retain this complete collection\<close>

definition current_transition_dependencies_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_transition_dependencies_at C q F au ar H K X \<longleftrightarrow>
    current_accepts_at C q F au ar H (Whole_Artifact K) \<and> transition_dependency_certificate C q K H X"

theorem current_transition_dependencies_account:
  assumes "current_transition_dependencies_at C q F au ar H K X"
  shows "current_transition_account_at C q F au ar H K X"
  using assms transition_dependency_account
  unfolding current_transition_dependencies_at_def current_transition_account_at_def by blast

theorem current_transition_dependencies_subject_unique:
  assumes "current_transition_dependencies_at C q F au ar G K X" "current_transition_dependencies_at D r F au ar H L Y"
  shows "G=H \<and> K=L \<and> X=Y"
  by (rule current_transition_account_subject_unique[OF current_transition_dependencies_account[OF assms(1)]
    current_transition_dependencies_account[OF assms(2)]])

definition certified_transition_dependencies ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_transition_dependencies C q R s H K X \<longleftrightarrow>
    current_acceptance_certificate C q R s H (Whole_Artifact K) \<and> transition_dependency_certificate C q K H X"

theorem certified_transition_dependencies_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "certified_transition_dependencies C q R s H K X\<longleftrightarrow>
    current_transition_dependencies_at C q F au ar H K X"
  by (simp only: certified_transition_dependencies_def current_transition_dependencies_at_def
    current_acceptance_certificate_with_scope[OF current scope])

theorem certified_transition_dependencies_account:
  assumes "certified_transition_dependencies C q R s H K X"
  shows "certified_transition_account C q R s H K X"
  using assms transition_dependency_account
  unfolding certified_transition_dependencies_def certified_transition_account_def by blast

theorem certified_transition_dependencies_sound:
  assumes "certified_transition_dependencies C q R s H K X"
  shows "\<exists>F au ar. current_transition_dependencies_at C q F au ar H K X"
  using assms unfolding certified_transition_dependencies_def current_acceptance_certificate_def
    current_transition_dependencies_at_def by blast

theorem current_transition_dependencies_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_dependencies_at C q F au ar H K X"
  shows "\<exists>R M root. certified_transition_dependencies C q R [] H K X \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and> native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have accepted: "current_accepts_at C q F au ar H (Whole_Artifact K)"
    and evidence: "transition_dependency_certificate C q K H X"
    using transition by (auto simp: current_transition_dependencies_at_def)
  show ?thesis using current_acceptance_certification_total[OF current accepted] evidence
    unfolding certified_transition_dependencies_def by blast
qed

theorem certified_transition_dependencies_subject_unique:
  assumes "certified_transition_dependencies C q R s G K X" "certified_transition_dependencies D r R a H L Y"
  shows "s=a \<and> G=H \<and> K=L \<and> X=Y"
  by (rule certified_transition_account_subject_unique[OF certified_transition_dependencies_account[OF assms(1)]
    certified_transition_dependencies_account[OF assms(2)]])

text \<open>
  The dependency frame, complete proof collection, and remaining scope occur
  inside the same accepted continuation material as the assembly account.
  Whole-value recovery prevents substituting a different collection while
  retaining that accepted envelope. Every required old or candidate definition
  has predecessor permission evidence, and every supplied proof has a required
  subject. Empty collections and proofs of unrelated subjects are rejected.

  The actual successor frame, successful publication, historical edge,
  construction account, and all original acceptance-scope bindings remain
  the requirements of the earlier account component. Acceptance certification
  retains that same candidate, collection, and complete minimal call scope.

  The remaining scope still needs comparison, migration, and exact
  cross-version interpretation. The dependency permission profile is an
  explicit component of the proposed protocol; an internal definition and
  adequacy theorem for the whole mechanism remain necessary.
\<close>

end
