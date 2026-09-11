theory Factor_Cause
  imports Factor_Construction_Presentations Factor_Native_Meaning RRA_Generation_Dependencies
begin

section \<open>Construction validity is a separate judgment\<close>

definition construction_judgment_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> exact_artifact list \<Rightarrow>
    (local_address\<times>exact_artifact) set \<Rightarrow> addressed_construction \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "construction_judgment_at E pu pr au ar xs B W R \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R)"

lemma construction_judgment_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "construction_judgment_at E pu pr au ar xs B W R \<longleftrightarrow>
    construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
proof
  assume judged: "construction_judgment_at E pu pr au ar xs B W R"
  obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "construction_claim_presents xs B W R v" "factor_constructs Q e xs B W R"
    using judged unfolding construction_judgment_at_def by blast
  have program: "Q=P" by (rule native_package_unique[OF other(1) package])
  have call: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
    using other(3,4) program call by simp
next
  assume "construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
  then show "construction_judgment_at E pu pr au ar xs B W R"
    using package app unfolding construction_judgment_at_def by blast
qed

lemma construction_judgment_account_unique:
  assumes first: "construction_judgment_at E pu pr au ar xs B W R"
    and second: "construction_judgment_at E qu qr au ar ys C X S"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof -
  obtain d t I K where left: "native_application_at E au ar d t I K"
    "construction_claim_presents xs B W R t"
    using first unfolding construction_judgment_at_def by blast
  obtain e v J L where right: "native_application_at E au ar e v J L"
    "construction_claim_presents ys C X S v"
    using second unfolding construction_judgment_at_def by blast
  have same: "t=v" using native_application_unique[OF left(1) right(1)] by blast
  have other: "construction_claim_presents ys C X S t" using right(2) same by simp
  show ?thesis by (rule construction_claim_presents_unique[OF left(2) other])
qed


lemma construction_judgment_truth:
  assumes judged: "construction_judgment_at E pu pr au ar xs B W R"
  shows "native_positive_holds E pu pr au ar"
proof -
  obtain P d t I K where package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K"
    and present: "construction_claim_presents xs B W R t" and allowed: "factor_constructs P d xs B W R"
    using judged unfolding construction_judgment_at_def by blast
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using allowed by (auto simp: factor_constructs_def)
  have truth: "(d,t)\<in>positive_meaning P"
    using factor_construction_at_presentation[OF built coords invariant present] allowed by blast
  show ?thesis using native_positive_holds_with_reads[OF package app] truth by blast
qed


definition construction_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "construction_cause_at E gu gr G pu pr xs B W R \<longleftrightarrow>
    generation_at E gu gr G \<and> generation_payload G=Whole_Artifact R \<and>
    (\<exists>cu cr. generation_cause_location E gu gr cu cr \<and>
      construction_judgment_at E pu pr cu cr xs B W R)"

theorem construction_cause_with_reads:
  assumes gen: "generation_at E gu gr G"
    and site: "generation_cause_location E gu gr cu cr"
    and package: "native_package_at E pu pr P"
    and app: "native_application_at E cu cr d t I K"
  shows "construction_cause_at E gu gr G pu pr xs B W R \<longleftrightarrow>
    generation_payload G=Whole_Artifact R \<and>
    construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
proof
  assume valid: "construction_cause_at E gu gr G pu pr xs B W R"
  obtain vu vr Q e x J L where other: "generation_payload G=Whole_Artifact R"
    "generation_cause_location E gu gr vu vr" "native_package_at E pu pr Q"
    "native_application_at E vu vr e x J L"
    "construction_claim_presents xs B W R x" "factor_constructs Q e xs B W R"
    using valid unfolding construction_cause_at_def construction_judgment_at_def by blast
  have location: "vu=cu \<and> vr=cr"
    by (rule generation_cause_location_unique[OF other(2) site])
  have program: "Q=P" by (rule native_package_unique[OF other(3) package])
  have same_app: "native_application_at E cu cr e x J L" using other(4) location by simp
  have call: "e=d \<and> x=t" using native_application_unique[OF same_app app] by blast
  show "generation_payload G=Whole_Artifact R \<and>
    construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
    using other(1,5,6) program call by simp
next
  assume "generation_payload G=Whole_Artifact R \<and>
    construction_claim_presents xs B W R t \<and> factor_constructs P d xs B W R"
  then show "construction_cause_at E gu gr G pu pr xs B W R"
    using gen site package app unfolding construction_cause_at_def construction_judgment_at_def by blast
qed

theorem construction_cause_accounts_for_payload:
  assumes valid: "construction_cause_at E gu gr G pu pr xs B W R"
  shows "source_constructs xs B W R"
    "construction_coordinates_formed B W"
    "generation_payload G=Whole_Artifact R"
    "K2 (construction_assembly xs B W) \<and> R=assembly_output (construction_assembly xs B W)"
proof -
  show built: "source_constructs xs B W R"
    using valid by (auto simp: construction_cause_at_def construction_judgment_at_def factor_constructs_def)
  show "construction_coordinates_formed B W"
    using valid by (auto simp: construction_cause_at_def construction_judgment_at_def factor_constructs_def)
  show "generation_payload G=Whole_Artifact R"
    using valid by (simp add: construction_cause_at_def construction_judgment_at_def)
  show "K2 (construction_assembly xs B W) \<and> R=assembly_output (construction_assembly xs B W)"
    using built by (simp add: source_constructs_iff_K2)
qed

theorem construction_cause_account_unique:
  assumes first: "construction_cause_at E gu gr G pu pr xs B W R"
    and second: "construction_cause_at E gu gr H qu qr ys C X S"
  shows "G=H \<and> xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof -
  obtain cu cr d t I K where left: "generation_at E gu gr G"
    "generation_cause_location E gu gr cu cr" "native_application_at E cu cr d t I K"
    "construction_claim_presents xs B W R t"
    using first unfolding construction_cause_at_def construction_judgment_at_def by blast
  obtain vu vr e x J L where right: "generation_at E gu gr H"
    "generation_cause_location E gu gr vu vr" "native_application_at E vu vr e x J L"
    "construction_claim_presents ys C X S x"
    using second unfolding construction_cause_at_def construction_judgment_at_def by blast
  have core: "G=H" by (rule generation_at_unique[OF left(1) right(1)])
  have location: "vu=cu \<and> vr=cr"
    by (rule generation_cause_location_unique[OF right(2) left(2)])
  have app: "native_application_at E cu cr e x J L" using right(3) location by simp
  have same_term: "t=x" using native_application_unique[OF left(3) app] by blast
  have present: "construction_claim_presents ys C X S t" using right(4) same_term by simp
  show ?thesis using core construction_claim_presents_unique[OF left(4) present] by blast
qed

theorem construction_cause_native_truth:
  assumes gen: "generation_at E gu gr G"
    and site: "generation_cause_location E gu gr cu cr"
    and package: "native_package_at E pu pr P"
    and app: "native_application_at E cu cr d t I K"
    and valid: "construction_cause_at E gu gr G pu pr xs B W R"
  shows "native_positive_holds E pu pr cu cr"
proof -
  have allowed: "factor_constructs P d xs B W R"
    and present: "construction_claim_presents xs B W R t"
    using construction_cause_with_reads[OF gen site package app] valid by blast+
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using allowed by (auto simp: factor_constructs_def)
  have truth: "(d,t)\<in>positive_meaning P"
    using factor_construction_at_presentation[OF built coords invariant present] allowed by blast
  show ?thesis using native_positive_holds_with_reads[OF package app] truth by blast
qed

lemma construction_cause_is_an_occurrence:
  assumes valid: "construction_cause_at E gu gr G pu pr xs B W R"
  shows "\<exists>C a. generation_cause G=Occurrence_Anchor (C,a)"
proof -
  obtain cu cr where gen: "generation_at E gu gr G"
    and site: "generation_cause_location E gu gr cu cr"
    using valid unfolding construction_cause_at_def construction_judgment_at_def by blast
  obtain C where art: "artifact_at E cu C"
    using generation_cause_location_artifact[OF site] by blast
  show ?thesis using generation_cause_location_target[OF gen site art] by blast
qed

theorem generation_formation_does_not_validate_construction:
  "\<exists>E :: bool artifact_environment. \<exists>G.
    environment_closed E {False} {(False,[9])} \<and> generation_at E False [] G \<and>
    (\<forall>pu pr xs B W R. \<not>construction_cause_at E False [] G pu pr xs B W R)"
proof -
  let ?E = "one_binding_environment base_generation_artifact [9] empty_artifact"
  let ?T = "Whole_Artifact empty_artifact"
  let ?G = "Generation ?T {||} ?T ?T"
  have read: "environment_closed ?E {False} {(False,[9])}"
    "generation_at ?E False [] ?G"
    using closed_base_generation[OF empty_artifact_formed] by auto
  have invalid: "\<forall>pu pr xs B W R. \<not>construction_cause_at ?E False [] ?G pu pr xs B W R"
  proof (intro allI notI)
    fix pu pr xs B W R
    assume valid: "construction_cause_at ?E False [] ?G pu pr xs B W R"
    show False using construction_cause_is_an_occurrence[OF valid] by simp
  qed
  show ?thesis by (rule exI[of _ ?E], rule exI[of _ ?G]) (use read invalid in blast)
qed

text \<open>
  The selected cause is an actual application read through the generation's
  own citation. Its complete argument determines the inputs, base entries,
  selections, origins, and output. Construction permission supplies structural
  validity, presentation invariance, and truth. The payload must be that exact
  output. Neither generation formation nor a whole-artifact cause declaration
  establishes this construction judgment.

  These are judgments relative to an explicit environment and native package.
  Uniqueness at that boundary does not assert that an artifact-and-address
  target determines its outgoing reference bindings. Identity of a resolved
  cause across different environments requires a further scope account.
  Base admission, continuation, proof certification, and adoption are separate.
\<close>

end
