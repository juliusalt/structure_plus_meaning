theory Factor_Construction_Cause_Material
  imports Factor_Construction_Cause_Readings Factor_Generation_Construction Factor_Construction_Permission_Coverage
begin

section \<open>Future calls first retain a compatible reference and candidate\<close>

theorem related_test_profile_application_total:
  assumes package: "native_package_at E pu pr P" and profile: "native_related_test_package C k E pu pr d"
    and argument: "term_formed t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_application_at F au [] d t I K \<and>
    native_related_test_package C k F pu pr d"
proof -
  obtain H test where parts: "d\<in>system_definitions P" "environment_formed H"
    "environment_included C H" "environment_included E H" "native_related_test_at H (fst d) (snd d) k test"
    using native_related_test_package_witnesses[OF profile package] by blast
  have reference_formed: "environment_formed C" using profile by (simp add: native_related_test_package_def)
  have original: "native_package_at H pu pr P" by (rule native_package_included[OF package parts(4,2)])
  obtain F au I K where formed: "environment_formed F" and extension: "environment_included H F"
    and kept: "native_package_at F pu pr P" and app: "native_application_at F au [] d t I K"
    using native_application_extension_total[OF original parts(1) argument] by blast
  have first: "environment_included C F" by (rule environment_included_trans[OF parts(3) extension])
  have second: "environment_included E F" by (rule environment_included_trans[OF parts(4) extension])
  have clause: "native_related_test_at F (fst d) (snd d) k test"
    by (rule native_related_test_included[OF parts(5) extension formed])
  have retained: "native_related_test_package C k F pu pr d"
    unfolding native_related_test_package_def
    using reference_formed kept parts(1) formed first environment_included_refl clause by blast
  show ?thesis using formed second kept app retained by blast
qed

section \<open>The exact original program and call receive an actual recorded generation\<close>

context construction_permission_admission
begin

theorem profile_recording_total:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and profile: "native_related_test_package C k E pu pr d"
    and account: "construction_account_presents a t" and truth: "(d,t)\<in>positive_meaning P"
    and locus: "target_formed l" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>F D A u. F=native_judgment_environment E pu pr au ar \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    F=native_judgment_environment F pu pr au ar \<and> judgment_value_quoted_at D [] F pu pr au ar \<and>
    generation_at A u [] (Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) \<and>
    generation_source_environment A u []=A \<and>
    recorded_construction_profile C k ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) a \<and>
    (\<forall>p q. generation_source_presents ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) p \<longrightarrow>
      construction_account_presents a q \<longrightarrow> recorded_construction_reading c (definition_site_value k) p q)"
proof -
  let ?F="native_judgment_environment E pu pr au ar"
  have kept: "native_package_at ?F pu pr P" "native_application_at ?F au ar d t I K" "environment_formed ?F"
    by (rule native_judgment_environment_recovers[OF package app])+
  have fixed: "?F=native_judgment_environment ?F pu pr au ar"
    by (simp only: native_judgment_environment_idempotent[OF package app])
  have retained: "native_related_test_package C k ?F pu pr d"
    by (rule native_related_test_package_restriction[OF profile package kept(1) native_judgment_environment_included])
  have relation: "construction_profile_context C k (?F,((pu,pr),(au,ar))) a"
    by (simp only: profile_context_at_reads[OF kept(1,2)]) (use retained account truth in blast)
  have judged: "construction_judgment_at ?F pu pr au ar (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    using relation by (simp only: construction_profile_context_def fst_conv snd_conv; blast)
  have positions: "(pu,pr)\<in>environment_positions ?F" "(au,ar)\<in>environment_positions ?F"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain D where quote: "judgment_value_quoted_at D [] ?F pu pr au ar"
    using judgment_value_quoted_total[OF kept(3) positions] by blast
  let ?G="Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)"
  obtain A :: "local_address option artifact_environment" and u
    where gen: "generation_at A u [] ?G" and closed: "generation_environment_closed A {(u,[])}"
    using recorded_generation_presentation_total[OF quote fixed judged locus predecessors] by blast
  have outer: "generation_source_environment A u []=A" by (rule generation_source_environment_fixed[OF closed])
  have scope: "generation_recorded_scope ((A,(u,[])),?G) (?F,((pu,pr),(au,ar)))"
    using gen quote by (auto simp: generation_recorded_scope_def generation_judgment_scope_at_def)
  have recorded: "recorded_construction_profile C k ((A,(u,[])),?G) a"
    by (simp only: recorded_construction_profile_at_scope[OF scope] fst_conv snd_conv)
      (use fixed relation in simp)
  have readings: "recorded_construction_reading c (definition_site_value k) p q"
    if "generation_source_presents ((A,(u,[])),?G) p" "construction_account_presents a q" for p q
    by (simp only: recorded_construction_reading_at_source[OF that(1)],
      rule exI[of _ a], rule conjI[OF recorded that(2)])
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ D], rule exI[of _ A], rule exI[of _ u])
    (use kept(1,2) fixed quote gen outer recorded readings in blast)
qed

end

section \<open>One native policy covers every complete construction account\<close>

context construction_permission_completion
begin

theorem complete_account_policy_total:
  "\<exists>E pu P d. closed_native_package_at E pu [] P \<and> d\<in>system_definitions P \<and>
    native_related_test_package C k E pu [] d \<and> construction_permission_invariant P d \<and>
    (\<forall>t. schema_call_formed P d t \<longleftrightarrow> term_formed t) \<and>
    (\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. construction_account_presents a t))"
proof -
  have member: "250\<in>system_definitions construction_admission_system" by simp
  obtain E pu P d where built: "closed_native_package_at E pu [] P" "d\<in>system_definitions P"
    "native_related_test_package C k E pu [] d" "construction_permission_invariant P d"
    "\<forall>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
    "(\<lambda>t. (d,t)\<in>positive_meaning P)=
      saturate_observation construction_account_presents (\<lambda>t. (250,t)\<in>positive_meaning construction_admission_system)"
    using program_completion[OF construction_admission_system_formed member]
    by (elim exE conjE) (rule that; assumption)
  have equation: "(d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. construction_account_presents a t)" for t
    using fun_cong[OF built(6), of t]
    by (auto simp: construction_admission_exact saturate_observation_def presentation_transport_def)
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ P], rule exI[of _ d])
    (use built(1-5) equation in blast)
qed

theorem all_accounts_have_profiled_recordings:
  "\<exists>E pu P d. closed_native_package_at E pu [] P \<and> native_related_test_package C k E pu [] d \<and>
    (\<forall>a l V. construction_account_domain a \<longrightarrow> target_formed l \<longrightarrow>
      (\<forall>H\<in>fset V. generation_formed H) \<longrightarrow>
      (\<exists>A u D. generation_at A u [] (Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) \<and>
        generation_source_environment A u []=A \<and>
        recorded_construction_profile C k ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) a \<and>
        (\<forall>p q. generation_source_presents ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) p \<longrightarrow>
          construction_account_presents a q \<longrightarrow> recorded_construction_reading c (definition_site_value k) p q)))"
proof -
  obtain E pu P d where package: "closed_native_package_at E pu [] P" and profile: "native_related_test_package C k E pu [] d"
    and truth: "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. construction_account_presents a t)"
    using complete_account_policy_total by (elim exE conjE) (rule that; assumption)
  have native: "native_package_at E pu [] P" using package by (simp add: closed_native_package_at_def)
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ P], rule exI[of _ d], intro conjI allI impI)
    show "closed_native_package_at E pu [] P" by (rule package)
    show "native_related_test_package C k E pu [] d" by (rule profile)
  next
    fix a l V assume domain: "construction_account_domain a" and locus: "target_formed l"
      and predecessors: "\<forall>H\<in>fset V. generation_formed H"
    obtain t where account: "construction_account_presents a t" using construction_accounts.total[OF domain] by blast
    have formed: "term_formed t" by (rule construction_account_formed[OF account])
    obtain F au I K where kept: "native_package_at F pu [] P" and app: "native_application_at F au [] d t I K"
      and retained: "native_related_test_package C k F pu [] d"
      using related_test_profile_application_total[OF native profile formed] by blast
    have holds: "(d,t)\<in>positive_meaning P" using truth account by blast
    show "\<exists>A u D. generation_at A u [] (Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) \<and>
      generation_source_environment A u []=A \<and>
      recorded_construction_profile C k ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) a \<and>
      (\<forall>p q. generation_source_presents ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) p \<longrightarrow>
        construction_account_presents a q \<longrightarrow> recorded_construction_reading c (definition_site_value k) p q)"
      using profile_recording_total[OF kept app retained account holds locus predecessors]
      by (elim exE conjE) (intro exI conjI; assumption)
  qed
qed

end

text \<open>
  An actual profiled construction call has a complete least judgment scope
  and a closed generation recording it. The retained package is the original
  program and the retained application has the original entry, operand, and
  material boundaries. Every complete outer source and every presentation of
  that account satisfy the independently proved reader join.

  The reference-compatible environment is chosen before a future application
  is installed. Its compatibility is an explicit witness; arbitrary extensions
  need not preserve the permission profile. Restriction to the actual program
  and call does preserve it. No recorded policy is replaced in this process.

  A single constructed native policy accepts exactly all complete accounts.
  It gives actual recordings for each such account, every formed locus, and
  every finite formed predecessor family. This establishes coverage without
  imposing history, authority, adoption, or a preferred table ordering. The
  combined ordinary implementation and its native recording contracts are
  supplied by Factor_Construction_Cause_Contracts.
\<close>

end
