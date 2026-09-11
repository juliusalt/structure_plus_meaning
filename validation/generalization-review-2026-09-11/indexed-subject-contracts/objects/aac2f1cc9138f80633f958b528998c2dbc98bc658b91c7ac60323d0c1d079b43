theory Factor_Transition_Comparisons
  imports Factor_Transition_Dependencies Factor_Amendment_Comparisons
begin

section \<open>Accepted dependency material retains the complete comparison value\<close>

definition transition_comparison_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "transition_comparison_certificate C q K H X \<longleftrightarrow>
    transition_dependency_certificate C q K H X \<and>
    (\<exists>S T U B bu br M mu mr D R N nu nr E Rs L lu lr.
      continuation_envelope C q K S T U B bu br \<and> successor_material_at B bu br X M mu mr \<and>
      assembly_support_at M mu mr D R N nu nr \<and> dependency_support_at N nu nr E Rs L lu lr \<and>
      amendment_comparison_at C q H L lu lr)"

lemma transition_comparison_dependencies:
  assumes "transition_comparison_certificate C q K H X"
  shows "transition_dependency_certificate C q K H X"
  using assms by (simp add: transition_comparison_certificate_def)

theorem transition_comparison_with_material:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E Rs L lu lr"
  shows "transition_comparison_certificate C q K H X \<longleftrightarrow>
    transition_dependency_certificate C q K H X \<and> amendment_comparison_at C q H L lu lr"
proof
  assume certificate: "transition_comparison_certificate C q K H X"
  then obtain S' T' U' B' bu' br' M' mu' mr' D' R' N' nu' nr' E' Rs' L' lu' lr' where other:
    "continuation_envelope C q K S' T' U' B' bu' br'" "successor_material_at B' bu' br' X M' mu' mr'"
    "assembly_support_at M' mu' mr' D' R' N' nu' nr'" "dependency_support_at N' nu' nr' E' Rs' L' lu' lr'"
    "amendment_comparison_at C q H L' lu' lr'"
    unfolding transition_comparison_certificate_def by blast
  have same: "L=L' \<and> lu=lu' \<and> lr=lr'"
    using transition_dependency_material_unique[OF envelope body assembly dependencies other(1-4)] by blast
  show "transition_dependency_certificate C q K H X \<and> amendment_comparison_at C q H L lu lr"
    using transition_comparison_dependencies[OF certificate] other(5) same by simp
next
  assume parts: "transition_dependency_certificate C q K H X \<and> amendment_comparison_at C q H L lu lr"
  then have prior: "transition_dependency_certificate C q K H X"
    and comparison: "amendment_comparison_at C q H L lu lr" by auto
  show "transition_comparison_certificate C q K H X" unfolding transition_comparison_certificate_def
    by (rule conjI[OF prior], rule exI[of _ S], rule exI[of _ T], rule exI[of _ U],
        rule exI[of _ B], rule exI[of _ bu], rule exI[of _ br], rule exI[of _ M], rule exI[of _ mu],
        rule exI[of _ mr], rule exI[of _ D], rule exI[of _ R], rule exI[of _ N], rule exI[of _ nu],
        rule exI[of _ nr], rule exI[of _ E], rule exI[of _ Rs], rule exI[of _ L],
        rule exI[of _ lu], rule exI[of _ lr])
       (use envelope body assembly dependencies comparison in blast)
qed

theorem transition_comparison_with_reporter:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E Rs L lu lr"
    and comparison: "comparison_support_at L lu lr W F fu fr b J ju jr"
  shows "transition_comparison_certificate C q K H X \<longleftrightarrow>
    transition_dependency_certificate C q K H X \<and> amendment_reports_at C q H W F fu fr b"
  by (simp only: transition_comparison_with_material[OF envelope body assembly dependencies]
    amendment_comparison_with_support[OF comparison])

theorem transition_comparison_material_unique:
  assumes left: "continuation_envelope C q K S T U B bu br" "successor_material_at B bu br X M mu mr"
    "assembly_support_at M mu mr D R N nu nr" "dependency_support_at N nu nr E Rs L lu lr"
    "comparison_support_at L lu lr W F fu fr b J ju jr"
    and right: "continuation_envelope C' q' K S' T' U' B' bu' br'" "successor_material_at B' bu' br' X' M' mu' mr'"
    "assembly_support_at M' mu' mr' D' R' N' nu' nr'" "dependency_support_at N' nu' nr' E' Rs' L' lu' lr'"
    "comparison_support_at L' lu' lr' W' F' fu' fr' b' J' ju' jr'"
  shows "X=X' \<and> W=W' \<and> F=F' \<and> fu=fu' \<and> fr=fr' \<and> b=b' \<and> J=J' \<and> ju=ju' \<and> jr=jr'"
proof -
  have same: "X=X' \<and> L=L' \<and> lu=lu' \<and> lr=lr'"
    using transition_dependency_material_unique[OF left(1-4) right(1-4)] by blast
  have other: "comparison_support_at L lu lr W' F' fu' fr' b' J' ju' jr'" using right(5) same by simp
  show ?thesis using same comparison_support_at_unique[OF left(5) other] by blast
qed

theorem transition_comparison_complete_calls:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H Qs qu qr Q"
    and reporter: "closed_native_package_at F fu fr V"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E0 Rs L lu lr"
    and comparison: "comparison_support_at L lu lr W F fu fr b J ju jr"
    and certificate: "transition_comparison_certificate C q K H X"
  shows "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports V b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    and "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports V b} =
      system_comparison_calls Q P (native_package_roots Qs qu qr)"
    and "program_reports_only V b \<and> system_report_sound P Q (program_judgment_reports V b)"
proof -
  have accepted: "amendment_comparison_at C q H L lu lr"
    using certificate by (simp only: transition_comparison_with_material[OF envelope body assembly dependencies]; blast)
  show "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports V b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports V b} =
      system_comparison_calls Q P (native_package_roots Qs qu qr)"
    by (rule amendment_comparison_complete_calls[OF current candidate reporter comparison accepted])+
  have minimal: "native_package_environment F fu fr=F" by (rule native_package_closed_environment_fixed[OF reporter])
  have reports: "amendment_reports_at C q H W F fu fr b"
    using accepted by (simp only: amendment_comparison_with_support[OF comparison])
  show "program_reports_only V b \<and> system_report_sound P Q (program_judgment_reports V b)"
    using reports by (simp only: amendment_reports_with_scopes[OF current candidate reporter minimal]; blast)
qed

theorem transition_comparison_empty_rejected:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and assembly: "assembly_support_at M mu mr D R N nu nr"
    and dependencies: "dependency_support_at N nu nr E Rs L lu lr"
    and comparison: "comparison_support_at L lu lr {} F fu fr b J ju jr"
  shows "\<not>transition_comparison_certificate C q K H X"
  by (simp only: transition_comparison_with_material[OF envelope body assembly dependencies]
    amendment_comparison_empty_rejected[OF comparison]; blast)

section \<open>Actual acceptance and its closed record bind the same comparison\<close>

definition current_transition_comparison_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_transition_comparison_at C q F au ar H K X \<longleftrightarrow>
    current_accepts_at C q F au ar H (Whole_Artifact K) \<and> transition_comparison_certificate C q K H X"

theorem current_transition_comparison_dependencies:
  assumes "current_transition_comparison_at C q F au ar H K X"
  shows "current_transition_dependencies_at C q F au ar H K X"
  using assms transition_comparison_dependencies
  unfolding current_transition_comparison_at_def current_transition_dependencies_at_def by blast

theorem current_transition_comparison_subject_unique:
  assumes "current_transition_comparison_at C q F au ar G K X" "current_transition_comparison_at D r F au ar H L Y"
  shows "G=H \<and> K=L \<and> X=Y"
  by (rule current_transition_dependencies_subject_unique[OF current_transition_comparison_dependencies[OF assms(1)]
    current_transition_comparison_dependencies[OF assms(2)]])

definition certified_transition_comparison ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_transition_comparison C q R s H K X \<longleftrightarrow>
    current_acceptance_certificate C q R s H (Whole_Artifact K) \<and> transition_comparison_certificate C q K H X"

theorem certified_transition_comparison_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "certified_transition_comparison C q R s H K X \<longleftrightarrow>
    current_transition_comparison_at C q F au ar H K X"
  by (simp only: certified_transition_comparison_def current_transition_comparison_at_def
    current_acceptance_certificate_with_scope[OF current scope])

theorem certified_transition_comparison_dependencies:
  assumes "certified_transition_comparison C q R s H K X"
  shows "certified_transition_dependencies C q R s H K X"
  using assms transition_comparison_dependencies
  unfolding certified_transition_comparison_def certified_transition_dependencies_def by blast

theorem certified_transition_comparison_sound:
  assumes "certified_transition_comparison C q R s H K X"
  shows "\<exists>F au ar. current_transition_comparison_at C q F au ar H K X"
  using assms unfolding certified_transition_comparison_def current_acceptance_certificate_def
    current_transition_comparison_at_def by blast

theorem current_transition_comparison_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_comparison_at C q F au ar H K X"
  shows "\<exists>R M root. certified_transition_comparison C q R [] H K X \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and> native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have accepted: "current_accepts_at C q F au ar H (Whole_Artifact K)"
    and evidence: "transition_comparison_certificate C q K H X"
    using transition by (auto simp: current_transition_comparison_at_def)
  show ?thesis using current_acceptance_certification_total[OF current accepted] evidence
    unfolding certified_transition_comparison_def by blast
qed

theorem certified_transition_comparison_subject_unique:
  assumes "certified_transition_comparison C q R s G K X" "certified_transition_comparison D r R a H L Y"
  shows "s=a \<and> G=H \<and> K=L \<and> X=Y"
  by (rule certified_transition_dependencies_subject_unique[OF certified_transition_comparison_dependencies[OF assms(1)]
    certified_transition_comparison_dependencies[OF assms(2)]])

text \<open>
  The same accepted envelope contains construction evidence, the complete
  dependency collection, and this comparison value. Its whole structure fixes
  the structural rows, reporter scope and entry, and remaining material.
  Substitution of another value changes that accepted subject.

  Complete coverage and preservation soundness use the actual old and
  candidate programs. Both full call domains are recovered from the retained
  reporter, and empty structural reports fail. The reporter's clauses remain
  ordinary argument data for predecessor acceptance. The acceptance record
  preserves the exact old program and complete minimal judgment environment.

  These are explicit mathematical components of succession. Native admission
  of their whole grammar and semantic obligations, migration evidence, and
  exact cross-version interpretation remain to be constructed in the
  predecessor's ordinary protocol.
\<close>

end
