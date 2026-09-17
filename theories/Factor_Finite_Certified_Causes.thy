theory Factor_Finite_Certified_Causes
  imports Factor_Finite_Judgment_Scope_Readings Factor_Finite_Literal_Replay
    Factor_Certified_Base_Cause RRA_Finite_Inclusion
begin

definition finite_certified_judgment_context where
  "finite_certified_judgment_context F pu pr au ar G H root R=(
    F=finite_native_judgment_environment F pu pr au ar \<and>
    generation_payload G=Finite_Whole R \<and> finite_native_judgment_ready F pu pr au ar \<and>
    finite_literal_application_ready F au ar R \<and> finite_environment_included F H \<and>
    finite_native_replay_proves H pu pr au ar root)"

lemma finite_certified_judgment_context_exact:
  "finite_certified_judgment_context F pu pr au ar G H root R \<longleftrightarrow>
    decode_finite_environment F=native_judgment_environment (decode_finite_environment F) pu pr au ar \<and>
    generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R) \<and>
    (\<exists>P d I K. native_package_at (decode_finite_environment F) pu pr P \<and>
      native_application_at (decode_finite_environment F) au ar d
        (Target_Term (Whole_Artifact (decode_finite_object R))) I K) \<and>
    environment_included (decode_finite_environment F) (decode_finite_environment H) \<and>
    native_replay_at (decode_finite_environment H) pu pr au ar root {}"
proof -
  have minimal: "F=finite_native_judgment_environment F pu pr au ar \<longleftrightarrow>
    decode_finite_environment F=native_judgment_environment (decode_finite_environment F) pu pr au ar"
    by (simp only: decode_finite_environment_injective[symmetric] finite_native_judgment_environment_correct)
  have payload: "generation_payload G=Finite_Whole R \<longleftrightarrow>
    generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R)"
    by (simp only: decode_finite_generation_selectors decode_finite_target_injective[symmetric]
      decode_finite_target.simps)
  show ?thesis
    by (simp only: finite_certified_judgment_context_def minimal payload finite_native_judgment_ready_correct
      finite_literal_application_ready_at finite_environment_included_correct finite_native_replay_proves_correct; blast)
qed

definition finite_certified_base_cause where
  "finite_certified_base_cause E gu gr G H root R=fBex (finite_generation_judgment_readings E gu gr G)
    (\<lambda>(F,pu,pr,au,ar). finite_certified_judgment_context F pu pr au ar G H root R)"

theorem finite_certified_base_cause_exact:
  "finite_certified_base_cause E gu gr G H root R \<longleftrightarrow>
    certified_base_cause_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R)"
proof
  assume checked: "finite_certified_base_cause E gu gr G H root R"
  obtain F pu pr au ar where member: "(F,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G"
    and held: "finite_certified_judgment_context F pu pr au ar G H root R"
    using checked by (auto simp: finite_certified_base_cause_def Bex_def split_paired_Ex)
  show "certified_base_cause_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R)"
    using member held by (simp only: finite_generation_judgment_readings_exact
      finite_certified_judgment_context_exact certified_base_cause_at_def; blast)
next
  assume certified: "certified_base_cause_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R)"
  obtain F pu pr au ar P d I K where scope: "generation_judgment_scope_at (decode_finite_environment E)
      gu gr (decode_finite_generation G) F pu pr au ar"
    and facts: "F=native_judgment_environment F pu pr au ar"
      "generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R)"
      "native_package_at F pu pr P"
      "native_application_at F au ar d (Target_Term (Whole_Artifact (decode_finite_object R))) I K"
      "environment_included F (decode_finite_environment H)"
      "native_replay_at (decode_finite_environment H) pu pr au ar root {}"
    using certified unfolding certified_base_cause_at_def by blast
  obtain Q where member: "(Q,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G"
    and decode: "decode_finite_environment Q=F"
    using finite_generation_judgment_readings_complete[OF scope] by blast
  have held: "finite_certified_judgment_context Q pu pr au ar G H root R"
    using facts by (simp only: finite_certified_judgment_context_exact decode; blast)
  show "finite_certified_base_cause E gu gr G H root R"
    unfolding finite_certified_base_cause_def Bex_def
    by (rule exI[of _ "(Q,pu,pr,au,ar)"]) (use member held in auto)
qed

corollary finite_certified_base_cause_sound:
  "finite_certified_base_cause E gu gr G H root R \<Longrightarrow>
    recorded_base_cause_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_object R)"
  by (simp only: finite_certified_base_cause_exact; rule certified_base_cause_sound)

text \<open>
  Admission reads the original generation and its actual complete recorded cause.
  That cause must recover the least judgment environment, preserve its whole
  literal payload and be supported by an actual closed replay in the supplied
  retained environment. The Boolean is equivalent to the original certified
  relation on every input. Historical permission and policy adequacy remain
  independently required; formation or a supplied validity flag cannot replace
  the checked cause.
\<close>

end
