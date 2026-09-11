theory Factor_Transition_Interpretations
  imports Factor_Transition_Comparisons Factor_Amendment_Interpretations
begin

section \<open>The accepted comparison material retains the historical entry selection\<close>

definition transition_interpretation_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "transition_interpretation_certificate C q K H X \<longleftrightarrow>
    transition_comparison_certificate C q K H X \<and>
    (\<exists>S T U B bu br M mu mr D R N nu nr E Rs L lu lr W F fu fr b J ju jr.
      continuation_envelope C q K S T U B bu br \<and> successor_material_at B bu br X M mu mr \<and>
      assembly_support_at M mu mr D R N nu nr \<and> dependency_support_at N nu nr E Rs L lu lr \<and>
      comparison_support_at L lu lr W F fu fr b J ju jr \<and> amendment_interpretation_at C q H J ju jr)"

lemma transition_interpretation_comparison:
  assumes "transition_interpretation_certificate C q K H X"
  shows "transition_comparison_certificate C q K H X"
  using assms by (simp add: transition_interpretation_certificate_def)

theorem transition_interpretation_with_material:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E Rs L lu lr"
    and comparison: "comparison_support_at L lu lr W F fu fr b J ju jr"
  shows "transition_interpretation_certificate C q K H X \<longleftrightarrow>
    transition_comparison_certificate C q K H X \<and> amendment_interpretation_at C q H J ju jr"
proof
  assume certificate: "transition_interpretation_certificate C q K H X"
  obtain S' T' U' B' bu' br' M' mu' mr' D' R' N' nu' nr' E' Rs' L' lu' lr' W' F' fu' fr' b' J' ju' jr' where other:
    "continuation_envelope C q K S' T' U' B' bu' br'" "successor_material_at B' bu' br' X M' mu' mr'"
    "assembly_support_at M' mu' mr' D' R' N' nu' nr'" "dependency_support_at N' nu' nr' E' Rs' L' lu' lr'"
    "comparison_support_at L' lu' lr' W' F' fu' fr' b' J' ju' jr'"
    "amendment_interpretation_at C q H J' ju' jr'"
    using certificate[unfolded transition_interpretation_certificate_def, THEN conjunct2]
    by (atomize_elim) assumption
  have same: "J=J' \<and> ju=ju' \<and> jr=jr'"
    using transition_comparison_material_unique[OF envelope body assembly dependencies comparison other(1-5)] by blast
  show "transition_comparison_certificate C q K H X \<and> amendment_interpretation_at C q H J ju jr"
    using transition_interpretation_comparison[OF certificate] other(6) same by simp
next
  assume parts: "transition_comparison_certificate C q K H X \<and> amendment_interpretation_at C q H J ju jr"
  have prior: "transition_comparison_certificate C q K H X"
    and interpreted: "amendment_interpretation_at C q H J ju jr" using parts by auto
  show "transition_interpretation_certificate C q K H X" unfolding transition_interpretation_certificate_def
    by (rule conjI[OF prior], rule exI[of _ S], rule exI[of _ T], rule exI[of _ U],
        rule exI[of _ B], rule exI[of _ bu], rule exI[of _ br], rule exI[of _ M], rule exI[of _ mu],
        rule exI[of _ mr], rule exI[of _ D], rule exI[of _ R], rule exI[of _ N], rule exI[of _ nu],
        rule exI[of _ nr], rule exI[of _ E], rule exI[of _ Rs], rule exI[of _ L], rule exI[of _ lu],
        rule exI[of _ lr], rule exI[of _ W], rule exI[of _ F], rule exI[of _ fu], rule exI[of _ fr],
        rule exI[of _ b], rule exI[of _ J], rule exI[of _ ju], rule exI[of _ jr])
       (use envelope body assembly dependencies comparison interpreted in blast)
qed

theorem transition_interpretation_with_entries:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H E' qu qr Q"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E0 Rs L lu lr"
    and comparison: "comparison_support_at L lu lr W F fu fr c J ju jr"
    and bridge_value: "interpretation_support_at J ju jr a b V vu vr"
  shows "transition_interpretation_certificate C q K H X \<longleftrightarrow>
    transition_comparison_certificate C q K H X \<and> program_interpretation P Q a b"
  by (simp only: transition_interpretation_with_material[OF envelope body assembly dependencies comparison]
    amendment_interpretation_with_scopes[OF current candidate bridge_value])

theorem transition_interpretation_material_unique:
  assumes left: "continuation_envelope C q K S T U B bu br" "successor_material_at B bu br X M mu mr"
    "assembly_support_at M mu mr D R N nu nr" "dependency_support_at N nu nr E Rs L lu lr"
    "comparison_support_at L lu lr W F fu fr c J ju jr" "interpretation_support_at J ju jr a b V vu vr"
    and right: "continuation_envelope C' q' K S' T' U' B' bu' br'" "successor_material_at B' bu' br' X' M' mu' mr'"
    "assembly_support_at M' mu' mr' D' R' N' nu' nr'" "dependency_support_at N' nu' nr' E' Rs' L' lu' lr'"
    "comparison_support_at L' lu' lr' W' F' fu' fr' c' J' ju' jr'"
    "interpretation_support_at J' ju' jr' a' b' V' vu' vr'"
  shows "X=X' \<and> a=a' \<and> b=b' \<and> V=V' \<and> vu=vu' \<and> vr=vr'"
proof -
  have same: "X=X' \<and> J=J' \<and> ju=ju' \<and> jr=jr'"
    using transition_comparison_material_unique[OF left(1-5) right(1-5)] by blast
  have other: "interpretation_support_at J ju jr a' b' V' vu' vr'" using right(6) same by simp
  show ?thesis using same interpretation_support_at_unique[OF left(6) other] by blast
qed

theorem transition_interpretation_all_calls:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H E' qu qr Q"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E0 Rs L lu lr"
    and comparison: "comparison_support_at L lu lr W F fu fr c J ju jr"
    and bridge_value: "interpretation_support_at J ju jr a b V vu vr"
    and certificate: "transition_interpretation_certificate C q K H X"
  shows "(a,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      schema_call_formed P e t"
    and "(b,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      (e,t)\<in>positive_meaning P"
    and "{z. (a,z)\<in>positive_meaning Q} =
      (\<lambda>(e,t). Pair_Term (site_data_term (fst e) (snd e)) t) ` {(e,t). schema_call_formed P e t}"
    and "{z. (b,z)\<in>positive_meaning Q} =
      (\<lambda>(e,t). Pair_Term (site_data_term (fst e) (snd e)) t) ` positive_meaning P"
proof -
  have bridge: "program_interpretation P Q a b"
    using certificate by (simp only: transition_interpretation_with_entries[
      OF current candidate envelope body assembly dependencies comparison bridge_value]; blast)
  show "(a,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      schema_call_formed P e t"
    "(b,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      (e,t)\<in>positive_meaning P"
    by (rule program_interpretation_at_call[OF bridge])+
  show "{z. (a,z)\<in>positive_meaning Q} =
      (\<lambda>(e,t). Pair_Term (site_data_term (fst e) (snd e)) t) ` {(e,t). schema_call_formed P e t}"
    "{z. (b,z)\<in>positive_meaning Q} =
      (\<lambda>(e,t). Pair_Term (site_data_term (fst e) (snd e)) t) ` positive_meaning P"
    by (rule program_interpretation_no_extra[OF bridge])+
qed

section \<open>Original acceptance and its closed proof retain the interpreter\<close>

definition current_transition_interpretation_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_transition_interpretation_at C q F au ar H K X \<longleftrightarrow>
    current_accepts_at C q F au ar H (Whole_Artifact K) \<and> transition_interpretation_certificate C q K H X"

theorem current_transition_interpretation_comparison:
  assumes "current_transition_interpretation_at C q F au ar H K X"
  shows "current_transition_comparison_at C q F au ar H K X"
  using assms transition_interpretation_comparison
  unfolding current_transition_interpretation_at_def current_transition_comparison_at_def by blast

theorem current_transition_interpretation_subject_unique:
  assumes "current_transition_interpretation_at C q F au ar G K X"
    "current_transition_interpretation_at D r F au ar H L Y"
  shows "G=H \<and> K=L \<and> X=Y"
  by (rule current_transition_comparison_subject_unique[OF current_transition_interpretation_comparison[OF assms(1)]
    current_transition_interpretation_comparison[OF assms(2)]])

definition certified_transition_interpretation ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_transition_interpretation C q R s H K X \<longleftrightarrow>
    current_acceptance_certificate C q R s H (Whole_Artifact K) \<and> transition_interpretation_certificate C q K H X"

theorem certified_transition_interpretation_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "certified_transition_interpretation C q R s H K X \<longleftrightarrow>
    current_transition_interpretation_at C q F au ar H K X"
  by (simp only: certified_transition_interpretation_def current_transition_interpretation_at_def
    current_acceptance_certificate_with_scope[OF current scope])

theorem certified_transition_interpretation_comparison:
  assumes "certified_transition_interpretation C q R s H K X"
  shows "certified_transition_comparison C q R s H K X"
  using assms transition_interpretation_comparison
  unfolding certified_transition_interpretation_def certified_transition_comparison_def by blast

theorem certified_transition_interpretation_sound:
  assumes "certified_transition_interpretation C q R s H K X"
  shows "\<exists>F au ar. current_transition_interpretation_at C q F au ar H K X"
  using assms unfolding certified_transition_interpretation_def current_acceptance_certificate_def
    current_transition_interpretation_at_def by blast

theorem current_transition_interpretation_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_interpretation_at C q F au ar H K X"
  shows "\<exists>R M root. certified_transition_interpretation C q R [] H K X \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and> native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have accepted: "current_accepts_at C q F au ar H (Whole_Artifact K)"
    and evidence: "transition_interpretation_certificate C q K H X"
    using transition by (auto simp: current_transition_interpretation_at_def)
  show ?thesis using current_acceptance_certification_total[OF current accepted] evidence
    unfolding certified_transition_interpretation_def by blast
qed

theorem certified_transition_interpretation_subject_unique:
  assumes "certified_transition_interpretation C q R s G K X"
    "certified_transition_interpretation D r R a H L Y"
  shows "s=a \<and> G=H \<and> K=L \<and> X=Y"
  by (rule certified_transition_comparison_subject_unique[OF certified_transition_interpretation_comparison[OF assms(1)]
    certified_transition_interpretation_comparison[OF assms(2)]])

text \<open>
  The interpreter occupies the remaining material of the same comparison
  value already bound by the accepted envelope. Whole-value recovery fixes
  both entry roles and every field of the remaining scope. The current frame
  and candidate payload retain the exact contexts of all old and new sites.

  All earlier selection, account, dependency, and comparison components remain
  required. The retained interpreter recovers old formation and truth on every
  call and has no additional positive outputs. Acceptance and its closed proof
  retain that same whole subject, exact predecessor program, and minimal call
  environment. The candidate's interpreter clauses do not authorize adoption.

  Native checking of these mathematical components, including the submitted
  bridge's finite correctness certificate, migration, and full genesis
  adequacy remain necessary.
\<close>

end
