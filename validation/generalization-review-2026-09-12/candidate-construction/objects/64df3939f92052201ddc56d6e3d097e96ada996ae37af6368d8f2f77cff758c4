theory Factor_Dependency_Evidence
  imports Factor_Current_Site_Certificates Factor_Current_Companions Factor_Amendment_Dependencies
    Factor_Dependency_Support
begin

section \<open>Every record has a required subject and every required subject has a record\<close>

definition site_evidence_covers ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow>
    (local_address option artifact_environment\<times>local_address option definition_site) set \<Rightarrow>
    exact_artifact set \<Rightarrow> bool" where
  "site_evidence_covers D r U Rs \<longleftrightarrow> finite Rs \<and>
    (\<forall>R\<in>Rs. \<exists>x\<in>U. \<exists>s. current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))) \<and>
    (\<forall>x\<in>U. \<exists>R\<in>Rs. \<exists>s. current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x)))"

lemma site_permission_record_subject_unique:
  assumes first: "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    and second: "current_site_permission_certificate E a R b (fst y) (fst (snd y)) (snd (snd y))"
  shows "x=y"
  using current_site_permission_certificate_subject_unique[OF first second] by (metis prod_eqI)

lemma site_evidence_covers_empty:
  "site_evidence_covers D r U {}\<longleftrightarrow>U={}"
  by (auto simp: site_evidence_covers_def)

lemma site_evidence_covers_required:
  assumes "site_evidence_covers D r U Rs" "x\<in>U"
  shows "\<exists>R\<in>Rs. \<exists>s. current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  using assms unfolding site_evidence_covers_def by blast

lemma site_evidence_covers_record:
  assumes "site_evidence_covers D r U Rs" "R\<in>Rs"
  shows "\<exists>x\<in>U. \<exists>s. current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  using assms unfolding site_evidence_covers_def by blast

theorem site_evidence_covers_unique:
  assumes first: "site_evidence_covers D r U Rs" and second: "site_evidence_covers E a V Rs"
  shows "U=V"
proof
  show "U\<subseteq>V"
  proof
    fix x assume member: "x\<in>U"
    obtain R s where evidence: "R\<in>Rs"
      "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
      using site_evidence_covers_required[OF first member] by blast
    obtain y b where subject: "y\<in>V"
      "current_site_permission_certificate E a R b (fst y) (fst (snd y)) (snd (snd y))"
      using site_evidence_covers_record[OF second evidence(1)] by blast
    have same: "x=y" by (rule site_permission_record_subject_unique[OF evidence(2) subject(2)])
    show "x\<in>V" using subject(1) same by simp
  qed
  show "V\<subseteq>U"
  proof
    fix y assume member: "y\<in>V"
    obtain R b where evidence: "R\<in>Rs"
      "current_site_permission_certificate E a R b (fst y) (fst (snd y)) (snd (snd y))"
      using site_evidence_covers_required[OF second member] by blast
    obtain x s where subject: "x\<in>U"
      "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
      using site_evidence_covers_record[OF first evidence(1)] by blast
    have same: "y=x" by (rule site_permission_record_subject_unique[OF evidence(2) subject(2)])
    show "y\<in>U" using subject(1) same by simp
  qed
qed

theorem site_evidence_missing_subject:
  assumes required: "x\<in>U"
    and missing: "\<And>R s. R\<in>Rs \<Longrightarrow>
      \<not>current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  shows "\<not>site_evidence_covers D r U Rs"
  using site_evidence_covers_required[OF _ required] missing by blast

theorem site_evidence_remove_sole_record:
  assumes covered: "site_evidence_covers D r U Rs" and required: "x\<in>U"
    and sole: "\<And>R s. R\<in>Rs \<Longrightarrow>
      current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x)) \<Longrightarrow> R=R0"
  shows "R0\<in>Rs" "\<not>site_evidence_covers D r U (Rs-{R0})"
proof -
  obtain R s where found: "R\<in>Rs"
    "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    using site_evidence_covers_required[OF covered required] by blast
  show "R0\<in>Rs" using sole[OF found] found(1) by simp
  show "\<not>site_evidence_covers D r U (Rs-{R0})"
    by (rule site_evidence_missing_subject[OF required]) (use sole in blast)
qed

theorem site_evidence_insert_required_record:
  assumes covered: "site_evidence_covers D r U Rs" and required: "x\<in>U"
    and certificate: "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  shows "site_evidence_covers D r U (insert R Rs)"
  using assms unfolding site_evidence_covers_def by auto

theorem site_evidence_extra_subject:
  assumes outside: "x\<notin>U"
    and certificate: "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  shows "\<not>site_evidence_covers D r U (insert R Rs)"
proof
  assume covered: "site_evidence_covers D r U (insert R Rs)"
  have member: "R\<in>insert R Rs" by simp
  obtain y a where other: "y\<in>U"
    "current_site_permission_certificate D r R a (fst y) (fst (snd y)) (snd (snd y))"
    using site_evidence_covers_record[OF covered member] by blast
  have same: "x=y" by (rule site_permission_record_subject_unique[OF certificate other(2)])
  show False using outside other(1) same by simp
qed

theorem site_evidence_covers_total:
  assumes current: "current_entry_scope_quoted_at D r A l G p E pu pr P d"
    and finite: "finite U"
    and permitted: "\<And>x. x\<in>U \<Longrightarrow> factor_permits_site P d (fst x) (fst (snd x)) (snd (snd x))"
  shows "\<exists>Rs. site_evidence_covers D r U Rs \<and>
    (\<forall>R\<in>Rs. \<not>site_evidence_covers D r U (Rs-{R}))"
proof -
  have each: "\<forall>x\<in>U. \<exists>R. current_site_permission_certificate D r R [] (fst x) (fst (snd x)) (snd (snd x))"
    using current_site_permission_certificate_total[OF current] permitted by blast
  obtain f where chosen: "\<forall>x\<in>U.
    current_site_permission_certificate D r (f x) [] (fst x) (fst (snd x)) (snd (snd x))"
    using bchoice[OF each] by blast
  have records: "\<forall>R\<in>image f U. \<exists>x\<in>U. \<exists>s.
    current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    using chosen by blast
  have required: "\<forall>x\<in>U. \<exists>R\<in>image f U. \<exists>s.
    current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  proof (intro ballI)
    fix x assume member: "x\<in>U"
    have proof_record: "current_site_permission_certificate D r (f x) [] (fst x) (fst (snd x)) (snd (snd x))"
      using chosen member by blast
    show "\<exists>R\<in>image f U. \<exists>s.
      current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
      by (rule bexI[of _ "f x"]) (use proof_record member in auto)
  qed
  have finite_records: "finite (image f U)" using finite by simp
  have covered: "site_evidence_covers D r U (image f U)"
    using finite_records records required by (simp add: site_evidence_covers_def)
  have needed: "\<forall>R\<in>image f U. \<not>site_evidence_covers D r U (image f U-{R})"
  proof (intro ballI)
    fix R assume member: "R\<in>image f U"
    then obtain x where subject: "x\<in>U" "R=f x" by blast
    have sole: "\<And>S s. S\<in>image f U \<Longrightarrow>
      current_site_permission_certificate D r S s (fst x) (fst (snd x)) (snd (snd x)) \<Longrightarrow> S=R"
    proof -
      fix S s assume inside: "S\<in>image f U"
        and proof_record: "current_site_permission_certificate D r S s (fst x) (fst (snd x)) (snd (snd x))"
      obtain y where other: "y\<in>U" "S=f y" using inside by blast
      have recorded: "current_site_permission_certificate D r S [] (fst y) (fst (snd y)) (snd (snd y))"
        using chosen other by blast
      have same: "x=y" by (rule site_permission_record_subject_unique[OF proof_record recorded])
      show "S=R" using subject(2) other(2) same by simp
    qed
    show "\<not>site_evidence_covers D r U (image f U-{R})"
      by (rule site_evidence_remove_sole_record(2)[OF covered subject(1) sole])
  qed
  show ?thesis using covered needed by blast
qed

section \<open>The predecessor selects the policy and both programs fix its obligations\<close>

definition amendment_dependency_evidence ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact set \<Rightarrow> bool" where
  "amendment_dependency_evidence C q H D r Rs \<longleftrightarrow>
    current_companion C q D r \<and>
    (\<exists>U. amendment_dependency_subjects C q H U \<and> site_evidence_covers D r U Rs)"

theorem amendment_dependency_evidence_with_subjects:
  assumes subjects: "amendment_dependency_subjects C q H U"
  shows "amendment_dependency_evidence C q H D r Rs\<longleftrightarrow>
    current_companion C q D r \<and> site_evidence_covers D r U Rs"
proof
  assume evidence: "amendment_dependency_evidence C q H D r Rs"
  obtain V where other: "amendment_dependency_subjects C q H V" "site_evidence_covers D r V Rs"
    using evidence unfolding amendment_dependency_evidence_def by blast
  have same: "U=V" by (rule amendment_dependency_subjects_unique[OF subjects other(1)])
  show "current_companion C q D r \<and> site_evidence_covers D r U Rs"
    using evidence other(2) same by (simp add: amendment_dependency_evidence_def)
next
  assume "current_companion C q D r \<and> site_evidence_covers D r U Rs"
  then show "amendment_dependency_evidence C q H D r Rs"
    using subjects unfolding amendment_dependency_evidence_def by blast
qed

lemma amendment_dependency_evidence_formed:
  assumes evidence: "amendment_dependency_evidence C q H D r Rs"
  shows "finite Rs \<and> Rs\<noteq>{} \<and> exact_formed D \<and> (\<forall>R\<in>Rs. exact_formed R)"
proof -
  obtain U where subjects: "amendment_dependency_subjects C q H U" and covered: "site_evidence_covers D r U Rs"
    using evidence unfolding amendment_dependency_evidence_def by blast
  have finite: "finite Rs" using covered by (simp add: site_evidence_covers_def)
  obtain x where member: "x\<in>U" using amendment_dependency_subjects_boundary(2)[OF subjects] by blast
  obtain R s where certificate: "R\<in>Rs"
    "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    using site_evidence_covers_required[OF covered member] by blast
  have every: "\<forall>R\<in>Rs. exact_formed R"
  proof (intro ballI)
    fix R assume in_set: "R\<in>Rs"
    obtain y a where valid: "current_site_permission_certificate D r R a (fst y) (fst (snd y)) (snd (snd y))"
      using site_evidence_covers_record[OF covered in_set] by blast
    show "exact_formed R" using current_site_permission_certificate_formed[OF valid] by blast
  qed
  show ?thesis using finite certificate(1) every current_site_permission_certificate_formed[OF certificate(2)] by blast
qed

theorem amendment_dependency_evidence_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and evidence: "amendment_dependency_evidence C q H D r Rs"
  shows "\<exists>z e. current_entry_scope_quoted_at D r A l G z E pu pr P e"
proof -
  obtain U where subjects: "amendment_dependency_subjects C q H U" and covered: "site_evidence_covers D r U Rs"
    and companion: "current_companion C q D r"
    using evidence unfolding amendment_dependency_evidence_def by blast
  obtain x where member: "x\<in>U" using amendment_dependency_subjects_boundary(2)[OF subjects] by blast
  obtain R s where certificate: "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    using site_evidence_covers_required[OF covered member] by blast
  obtain A' l' G' z E' qu qr Q e where selected: "current_entry_scope_quoted_at D r A' l' G' z E' qu qr Q e"
    using certificate unfolding current_site_permission_certificate_def by blast
  have same: "A=A' \<and> l=l' \<and> G=G' \<and> E=E' \<and> pu=qu \<and> pr=qr \<and> P=Q"
    by (rule current_companion_program[OF companion current selected])
  show ?thesis using selected same by blast
qed

theorem amendment_dependency_evidence_permits:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and subjects: "amendment_dependency_subjects C q H U"
    and evidence: "amendment_dependency_evidence C q H D r Rs"
  shows "\<exists>z e. current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    (\<forall>x\<in>U. factor_permits_site P e (fst x) (fst (snd x)) (snd (snd x)))"
proof -
  obtain z e where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    using amendment_dependency_evidence_entry[OF current evidence] by blast
  have covered: "site_evidence_covers D r U Rs"
    using evidence by (simp only: amendment_dependency_evidence_with_subjects[OF subjects]; blast)
  have every: "\<forall>x\<in>U. factor_permits_site P e (fst x) (fst (snd x)) (snd (snd x))"
  proof (intro ballI)
    fix x assume member: "x\<in>U"
    obtain R s where certificate: "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
      using site_evidence_covers_required[OF covered member] by blast
    show "factor_permits_site P e (fst x) (fst (snd x)) (snd (snd x))"
      by (rule current_site_permission_certificate_permits[OF selected certificate])
  qed
  show ?thesis using selected every by blast
qed

theorem amendment_dependency_recorded_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and subjects: "amendment_dependency_subjects C q H U"
    and evidence: "amendment_dependency_evidence C q H D r Rs" and member: "R\<in>Rs"
  shows "\<exists>z e x s F au ar root t I K J.
    x\<in>U \<and> current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x)) \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar e t I K \<and>
    native_schema_graph_at F root J \<and> schema_graph_derives (positioned_program P) J root e t {} \<and>
    site_permission_invariant P e \<and> site_value_presents (fst x) (fst (snd x)) (snd (snd x)) t"
proof -
  obtain z e where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    using amendment_dependency_evidence_entry[OF current evidence] by blast
  have covered: "site_evidence_covers D r U Rs"
    using evidence by (simp only: amendment_dependency_evidence_with_subjects[OF subjects]; blast)
  obtain x s where subject: "x\<in>U"
    "current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
    using site_evidence_covers_record[OF covered member] by blast
  show ?thesis using selected subject current_site_permission_certificate_derivation[OF selected subject(2)] by blast
qed

theorem amendment_dependency_empty_evidence_rejected:
  "\<not>amendment_dependency_evidence C q H D r {}"
  using amendment_dependency_evidence_formed by blast

theorem amendment_dependency_missing_subject:
  assumes subjects: "amendment_dependency_subjects C q H U" and required: "x\<in>U"
    and missing: "\<And>R s. R\<in>Rs \<Longrightarrow>
      \<not>current_site_permission_certificate D r R s (fst x) (fst (snd x)) (snd (snd x))"
  shows "\<not>amendment_dependency_evidence C q H D r Rs"
  using site_evidence_missing_subject[OF required missing]
  by (simp only: amendment_dependency_evidence_with_subjects[OF subjects]; blast)

theorem amendment_dependency_evidence_total:
  assumes subjects: "amendment_dependency_subjects C q H U" and companion: "current_companion C q D r"
    and selected: "current_entry_scope_quoted_at D r A l G p E pu pr P d"
    and permitted: "\<And>x. x\<in>U \<Longrightarrow> factor_permits_site P d (fst x) (fst (snd x)) (snd (snd x))"
  shows "\<exists>Rs. amendment_dependency_evidence C q H D r Rs \<and>
    (\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C q H D r (Rs-{R}))"
proof -
  have finite: "finite U" by (rule amendment_dependency_subjects_boundary(1)[OF subjects])
  obtain Rs where covered: "site_evidence_covers D r U Rs"
    and needed: "\<forall>R\<in>Rs. \<not>site_evidence_covers D r U (Rs-{R})"
    using site_evidence_covers_total[OF selected finite permitted] by blast
  show ?thesis by (rule exI[of _ Rs])
    (use companion covered needed in \<open>simp only: amendment_dependency_evidence_with_subjects[OF subjects]; blast\<close>)
qed

section \<open>The complete proof family is read inside the submitted scope\<close>

definition amendment_dependency_evidence_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "amendment_dependency_evidence_at C q H M mu mr \<longleftrightarrow>
    (\<exists>D r Rs N nu nr. dependency_support_at M mu mr D Rs N nu nr \<and>
      amendment_dependency_evidence C q H D r Rs)"

theorem amendment_dependency_evidence_at_with_support:
  assumes support: "dependency_support_at M mu mr D Rs N nu nr"
  shows "amendment_dependency_evidence_at C q H M mu mr\<longleftrightarrow>
    (\<exists>r. amendment_dependency_evidence C q H D r Rs)"
proof
  assume "amendment_dependency_evidence_at C q H M mu mr"
  then obtain D' r Rs' N' nu' nr' where other: "dependency_support_at M mu mr D' Rs' N' nu' nr'"
    "amendment_dependency_evidence C q H D' r Rs'"
    unfolding amendment_dependency_evidence_at_def by blast
  have same: "D=D' \<and> Rs=Rs'" using dependency_support_at_unique[OF support other(1)] by blast
  show "\<exists>r. amendment_dependency_evidence C q H D r Rs" using other(2) same by blast
next
  assume "\<exists>r. amendment_dependency_evidence C q H D r Rs"
  then show "amendment_dependency_evidence_at C q H M mu mr"
    using support unfolding amendment_dependency_evidence_at_def by blast
qed

lemma amendment_dependency_evidence_at_formed:
  assumes "amendment_dependency_evidence_at C q H M mu mr"
  shows "environment_formed M \<and> (mu,mr)\<in>environment_positions M"
  using assms dependency_support_at_formed unfolding amendment_dependency_evidence_at_def by blast

theorem amendment_dependency_material_total:
  assumes evidence: "amendment_dependency_evidence C q H D r Rs"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. dependency_support_at M None [] D Rs N nu nr \<and>
    amendment_dependency_evidence_at C q H M None []"
proof -
  have fields: "exact_formed D" "finite Rs" "\<forall>R\<in>Rs. exact_formed R"
    using amendment_dependency_evidence_formed[OF evidence] by auto
  obtain M where support: "dependency_support_at M None [] D Rs N nu nr"
    using dependency_support_total[OF fields remainder] by blast
  have valid: "amendment_dependency_evidence_at C q H M None []"
    using support evidence unfolding amendment_dependency_evidence_at_def by blast
  show ?thesis using support valid by blast
qed

text \<open>
  Each required subject has a closed proof of permission at one actual
  companion entry of the predecessor program. Every supplied record must
  prove a required subject. Different proofs of that same permission may
  accumulate, while deleting its sole record or adding an unrelated subject
  fails coverage. A whole record cannot be reassigned to a different subject.
  Every permitted finite requirement has a complete collection in which each
  record is needed, without prohibiting additional valid evidence later.

  The actual old and candidate program scopes fix the entire required domain.
  It includes retained definitions as well as changed ones, and it is never
  empty at an actual current frame. The policy frame is selected under the
  predecessor's original adoption policy; its proof uses the exact old
  program, not the submitted dependency's clauses.

  The complete finite collection is ordinary submitted data. Its subject keys
  and quotation roots are recovered from the records instead of being stored
  again. Its remaining scope is preserved exactly for the later comparison
  and interpretation checks. Empty collections are formed data but cannot
  meet these actual amendment obligations.

  This profile interprets dependency evidence as predecessor permission for
  each exact definition site in its complete program scope. It does not prove
  every application at that site, nor does it establish that the selected
  policy implements adequate dependency checking. Native checking of the full
  protocol and its genesis adequacy remain separate obligations.
\<close>

end
