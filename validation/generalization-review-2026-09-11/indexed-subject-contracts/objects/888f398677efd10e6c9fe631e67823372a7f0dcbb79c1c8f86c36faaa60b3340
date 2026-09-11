theory Factor_Certified_Construction
  imports Factor_Replay Factor_Native_Construction
begin

section \<open>Construction permission has a finite derivation\<close>

theorem factor_construction_derivation:
  "factor_constructs P d xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<exists>t tree. construction_claim_presents xs B W R t \<and> checks_schema_proof P tree d t)"
  by (simp add: factor_constructs_def schema_proof_adequate)

section \<open>Construction certification adds its own complete account\<close>

definition certified_construction_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_construction_at E pu pr au ar root xs B W R \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
      construction_claim_presents xs B W R t \<and> construction_permission_invariant P d \<and>
      native_replay_at E pu pr au ar root {})"

lemma certified_construction_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "certified_construction_at E pu pr au ar root xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_claim_presents xs B W R t \<and> construction_permission_invariant P d \<and>
    native_replay_at E pu pr au ar root {}"
proof
  assume certified: "certified_construction_at E pu pr au ar root xs B W R"
  obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "source_constructs xs B W R" "construction_coordinates_formed B W"
    "construction_claim_presents xs B W R v" "construction_permission_invariant Q e"
    "native_replay_at E pu pr au ar root {}"
    using certified by (auto simp: certified_construction_at_def)
  have program: "Q=P" by (rule native_package_unique[OF other(1) package])
  have call: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_claim_presents xs B W R t \<and> construction_permission_invariant P d \<and>
    native_replay_at E pu pr au ar root {}" using other(3-7) program call by simp
next
  assume "source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_claim_presents xs B W R t \<and> construction_permission_invariant P d \<and>
    native_replay_at E pu pr au ar root {}"
  then show "certified_construction_at E pu pr au ar root xs B W R"
    using package app unfolding certified_construction_at_def by blast
qed

theorem certified_construction_permission:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and certified: "certified_construction_at E pu pr au ar root xs B W R"
  shows "factor_constructs P d xs B W R"
proof -
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and present: "construction_claim_presents xs B W R t"
    and invariant: "construction_permission_invariant P d"
    and replay: "native_replay_at E pu pr au ar root {}"
    using certified_construction_with_reads[OF package app] certified by blast+
  have positive: "native_positive_holds E pu pr au ar" by (rule native_replay_closed_sound[OF replay])
  have meaning: "(d,t)\<in>positive_meaning P" using native_positive_holds_with_reads[OF package app] positive by blast
  show ?thesis using factor_construction_at_presentation[OF built coords invariant present] meaning by blast
qed

theorem certified_construction_exact_join:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "certified_construction_at E pu pr au ar root xs B W R \<longleftrightarrow>
    factor_constructs P d xs B W R \<and> construction_claim_presents xs B W R t \<and>
    native_replay_at E pu pr au ar root {}"
proof
  assume certified: "certified_construction_at E pu pr au ar root xs B W R"
  have permission: "factor_constructs P d xs B W R"
    by (rule certified_construction_permission[OF package app certified])
  have rest: "construction_claim_presents xs B W R t \<and> native_replay_at E pu pr au ar root {}"
    using certified_construction_with_reads[OF package app, where root=root and xs=xs and B=B and W=W and R=R]
      certified by blast
  show "factor_constructs P d xs B W R \<and> construction_claim_presents xs B W R t \<and>
    native_replay_at E pu pr au ar root {}" using permission rest by blast
next
  assume parts: "factor_constructs P d xs B W R \<and> construction_claim_presents xs B W R t \<and>
    native_replay_at E pu pr au ar root {}"
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using parts by (auto simp: factor_constructs_def)
  show "certified_construction_at E pu pr au ar root xs B W R"
    using certified_construction_with_reads[OF package app, where root=root and xs=xs and B=B and W=W and R=R]
      built coords invariant parts by blast
qed

theorem certified_construction_requires_admission:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and inadmissible: "\<not>construction_permission_invariant P d"
  shows "\<not>certified_construction_at E pu pr au ar root xs B W R"
  using certified_construction_with_reads[OF package app] inadmissible by blast

theorem certified_construction_account_unique:
  assumes first: "certified_construction_at E pu pr au ar root xs B W R"
    and second: "certified_construction_at E pu pr au ar other ys C X S"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof -
  obtain P d t I K where read: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using first by (auto simp: certified_construction_at_def)
  have left: "construction_claim_presents xs B W R t"
    and right: "construction_claim_presents ys C X S t"
    using certified_construction_with_reads[OF read] first second by blast+
  show ?thesis by (rule construction_claim_presents_unique[OF left right])
qed

section \<open>Every permitted presentation receives a retained certificate\<close>

theorem certified_construction_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and allowed: "factor_constructs P d xs B W R"
    and present: "construction_claim_presents xs B W R t"
  shows "\<exists>F au root I K. certified_construction_at F pu pr au [] root xs B W R \<and>
    native_application_at F au [] d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using allowed by (auto simp: factor_constructs_def)
  have meaning: "(d,t)\<in>positive_meaning P"
    using factor_construction_at_presentation[OF built coords invariant present] allowed by blast
  have member: "d\<in>system_definitions P" using schema_call_formed_target[OF positive_meaning_formed[OF meaning]] by blast
  obtain F au I K where call: "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "native_positive_holds F pu pr au []"
    using native_construction_application_total[OF package member built coords invariant present] allowed by blast
  obtain A Q e v J L root where retained: "native_replay_at A pu pr au [] root {}"
    "native_package_at F pu pr Q" "native_application_at F au [] e v J L"
    "native_package_at A pu pr Q" "native_application_at A au [] e v J L"
    "native_package_environment A pu pr=native_package_environment F pu pr"
    using native_positive_replay_total[OF call(4)] by blast
  have program: "Q=P" by (rule native_package_unique[OF retained(2) call(1)])
  have argument: "e=d \<and> v=t" using native_application_unique[OF retained(3) call(2)] by blast
  have final_package: "native_package_at A pu pr P" using retained(4) program by simp
  have final_call: "native_application_at A au [] d t J L" using retained(5) argument by simp
  have certified: "certified_construction_at A pu pr au [] root xs B W R"
    using certified_construction_with_reads[OF final_package final_call]
      built coords present invariant retained(1) by blast
  have canonical: "native_package_environment A pu pr=native_package_environment E pu pr"
    using retained(6) call(3) by simp
  show ?thesis
    by (rule exI[of _ A], rule exI[of _ au], rule exI[of _ root], rule exI[of _ J], rule exI[of _ L])
       (use certified final_call canonical in blast)
qed

text \<open>
  Generic replay acquires no construction fields. This separate join recovers
  the complete account from its actual argument and requires the program's
  independent unordered-permission admission condition. Its permission follows
  from replay soundness. Different proof roots do not change account identity.
  Every admitted presentation has a retained certificate with the same program
  environment. Native checking of admission evidence remains a separate open
  obligation; a replay of one serialized call cannot replace it.
\<close>

end
