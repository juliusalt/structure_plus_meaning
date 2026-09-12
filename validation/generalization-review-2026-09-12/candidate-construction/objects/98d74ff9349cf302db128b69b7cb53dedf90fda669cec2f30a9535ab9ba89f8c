theory Factor_Current_Construction_Certificates
  imports Factor_Current_Construction Factor_Replay_Scopes Factor_Certified_Construction
begin

section \<open>A closed replay of the actual current construction call\<close>

definition current_construction_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_construction_certificate C q R s xs B W Z \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F au ar root.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      replay_scope_quoted_at R s F pu pr au ar root {} \<and>
      current_constructs_at C q F au ar xs B W Z)"

theorem current_construction_certificate_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "current_construction_certificate C q R s xs B W Z \<longleftrightarrow>
    current_constructs_at C q F au ar xs B W Z"
proof
  assume "current_construction_certificate C q R s xs B W Z"
  then obtain M qu qr bu br other where recorded:
    "replay_scope_quoted_at R s M qu qr bu br other {}"
    "current_constructs_at C q M bu br xs B W Z"
    unfolding current_construction_certificate_def by blast
  have same: "M=F \<and> bu=au \<and> br=ar" using replay_scope_whole_unique[OF recorded(1) scope] by blast
  show "current_constructs_at C q F au ar xs B W Z" using recorded(2) same by simp
next
  assume "current_constructs_at C q F au ar xs B W Z"
  then show "current_construction_certificate C q R s xs B W Z"
    using current scope unfolding current_construction_certificate_def by blast
qed

theorem current_construction_certificate_account_unique:
  assumes first: "current_construction_certificate C q R s xs B W Z"
    and second: "current_construction_certificate D r R a ys B' W' Z'"
  shows "s=a \<and> xs=ys \<and> B=B' \<and> W=W' \<and> Z=Z'"
proof -
  obtain F pu pr au ar root where left: "replay_scope_quoted_at R s F pu pr au ar root {}"
    "current_constructs_at C q F au ar xs B W Z"
    using first unfolding current_construction_certificate_def by blast
  obtain M qu qr bu br other where right: "replay_scope_quoted_at R a M qu qr bu br other {}"
    "current_constructs_at D r M bu br ys B' W' Z'"
    using second unfolding current_construction_certificate_def by blast
  have same: "s=a \<and> F=M \<and> au=bu \<and> ar=br" using replay_scope_whole_unique[OF left(1) right(1)] by blast
  have other: "current_constructs_at D r F au ar ys B' W' Z'" using right(2) same by simp
  show ?thesis using same current_construction_account_unique[OF left(2) other] by blast
qed

theorem current_construction_certificate_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "current_construction_certificate C q R s xs B W Z"
  shows "\<exists>F au ar root t I K.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu pr P \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au ar d t I K \<and>
    current_constructs_at C q F au ar xs B W Z \<and>
    certified_construction_at F pu pr au ar root xs B W Z"
proof -
  obtain A' l' G' p' E' qu qr Q e F au ar root where recorded:
    "current_entry_scope_quoted_at C q A' l' G' p' E' qu qr Q e"
    "replay_scope_quoted_at R s F qu qr au ar root {}"
    "current_constructs_at C q F au ar xs B W Z"
    using certificate unfolding current_construction_certificate_def by blast
  have roots: "pu=qu \<and> pr=qr" using current_entry_scope_unique[OF current recorded(1)] by blast
  have scope: "replay_scope_quoted_at R s F pu pr au ar root {}" using recorded(2) roots by simp
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "construction_judgment_at F pu pr au ar xs B W Z"
    using current_construction_program_scope[OF current recorded(3)] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_construction_at_scope[OF current] recorded(3) by blast
  have replay: "native_replay_at F pu pr au ar root {}" using scope by (simp add: replay_scope_quoted_at_def)
  have claim: "construction_claim_presents xs B W Z t" "factor_constructs P d xs B W Z"
    using construction_judgment_with_reads[OF program(3) app] program(5) by blast+
  have proved: "certified_construction_at F pu pr au ar root xs B W Z"
    using claim replay by (simp only: certified_construction_exact_join[OF program(3) app])
  show ?thesis using scope program(1-4) app recorded(3) proved by blast
qed

theorem current_construction_certificate_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "current_construction_certificate C q R s xs B W Z"
  shows "\<exists>F au ar root t I K J.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar d t I K \<and>
    native_schema_graph_at F root J \<and> schema_graph_derives (positioned_program P) J root d t {} \<and>
    construction_claim_presents xs B W Z t \<and> construction_permission_invariant P d \<and>
    source_constructs xs B W Z \<and> construction_coordinates_formed B W"
proof -
  obtain F au ar root t I K where recorded:
    "replay_scope_quoted_at R s F pu pr au ar root {}"
    "native_package_at F pu pr P" "native_package_environment F pu pr=E"
    "native_application_at F au ar d t I K" "certified_construction_at F pu pr au ar root xs B W Z"
    using current_construction_certificate_program[OF current certificate] by blast
  have replay: "native_replay_at F pu pr au ar root {}"
    using recorded(1) by (simp add: replay_scope_quoted_at_def)
  obtain J where graph: "native_schema_graph_at F root J" using replay unfolding native_replay_at_def by blast
  have derived: "schema_graph_derives (positioned_program P) J root d t {}"
    using native_replay_with_reads[OF recorded(2,4) graph] replay by blast
  have fields: "construction_claim_presents xs B W Z t" "construction_permission_invariant P d"
    "source_constructs xs B W Z" "construction_coordinates_formed B W"
    using certified_construction_with_reads[OF recorded(2,4)] recorded(5) by blast+
  show ?thesis using recorded(1-4) graph derived fields by blast
qed

section \<open>The exact minimal construction scope survives certification\<close>

theorem current_construction_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_constructs_at C q F au ar xs B W Z"
  shows "\<exists>R M root. current_construction_certificate C q R [] xs B W Z \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and>
    native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_positive_holds F pu pr au ar"
    using current_construction_program_scope[OF current permitted] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_construction_at_scope[OF current] permitted by blast
  obtain R M root where recorded: "replay_scope_quoted_at R [] M pu pr au ar root {}"
    and reads: "native_package_at M pu pr P" "native_application_at M au ar d t I K"
    and exact: "native_package_environment M pu pr=native_package_environment F pu pr"
      "native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
    using positive_judgment_has_recorded_replay[OF program(3) app program(5)] by blast
  have mf: "environment_formed M" using replay_scope_formed[OF recorded] by blast
  have canonical: "native_package_environment M pu pr=E" using exact(1) program(4) by simp
  have included: "environment_included E M"
    using native_package_environment_included[of M pu pr] canonical by simp
  have retained: "current_constructs_at C q M au ar xs B W Z"
    using permitted by (simp only: current_construction_with_reads[OF current program(1,2) app]
      current_construction_with_reads[OF current mf included reads(2)])
  have certificate: "current_construction_certificate C q R [] xs B W Z"
    using current_construction_certificate_with_scope[OF current recorded] retained by blast
  show ?thesis using certificate recorded canonical exact(2) by blast
qed

theorem current_construction_certificate_presentation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_constructs P d xs B W Z"
    and present: "construction_claim_presents xs B W Z t"
  shows "\<exists>R F au root I K. current_construction_certificate C q R [] xs B W Z \<and>
    replay_scope_quoted_at R [] F pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au [] d t I K"
proof -
  obtain M au I K where app: "native_application_at M au [] d t I K"
    and allowed: "current_constructs_at C q M au [] xs B W Z"
    using current_construction_application_total[OF current permitted present] by blast
  obtain R F root where certificate: "current_construction_certificate C q R [] xs B W Z"
    "replay_scope_quoted_at R [] F pu pr au [] root {}" "native_package_environment F pu pr=E"
    "native_judgment_environment F pu pr au []=native_judgment_environment M pu pr au []"
    using current_construction_certification_total[OF current allowed] by blast
  have package: "native_package_at M pu pr P" using current_construction_program_scope[OF current allowed] by blast
  have original: "native_application_at (native_judgment_environment M pu pr au []) au [] d t I K"
    by (rule native_judgment_environment_recovers(2)[OF package app])
  have kept: "native_application_at (native_judgment_environment F pu pr au []) au [] d t I K"
    using original certificate(4) by simp
  have ff: "environment_formed F" using replay_scope_formed[OF certificate(2)] by blast
  have call: "native_application_at F au [] d t I K"
    by (rule native_application_included[OF kept native_judgment_environment_included ff])
  show ?thesis using certificate(1-3) call by blast
qed

text \<open>
  The complete replay record fixes the program site, actual selected call,
  and full construction account. The finite closed graph derives that call
  under the current program. Its separate construction admission condition
  includes structural validity and invariance over every complete account
  presentation; a proof of one call does not establish that condition.

  Certification preserves the exact minimal program-and-call environment.
  Every permitted complete presentation receives an actual recorded call.
  The construction output does not determine a generation's locus, history,
  cause quotation, authority, or publication. Those remain later joins.
\<close>

end
