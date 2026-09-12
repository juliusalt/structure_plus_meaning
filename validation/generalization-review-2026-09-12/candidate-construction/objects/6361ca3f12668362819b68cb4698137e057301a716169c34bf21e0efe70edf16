theory Factor_Amendment_Dependencies
  imports Factor_Current_Entries
begin

section \<open>Both actual program scopes determine every required definition subject\<close>

lemma native_package_definition_subjects:
  assumes package: "native_package_at E pu pr P"
  shows "finite (system_definitions P) \<and> environment_formed E \<and>
    (\<forall>d\<in>system_definitions P. d\<in>environment_positions E \<and>
      (\<exists>p C. native_definition_at E (fst d) (snd d) p C))"
proof -
  have formed: "native_package_formed E (native_package_roots E pu pr)"
    by (rule native_package_projection(1)[OF package])
  have sites: "system_definitions P=native_definition_sites E (native_package_roots E pu pr)"
    using native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  show ?thesis using formed sites native_package_sites[OF formed]
    by (auto simp: native_package_formed_def)
qed

definition amendment_dependency_subjects ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    (local_address option artifact_environment\<times>local_address option definition_site) set \<Rightarrow> bool" where
  "amendment_dependency_subjects C q H U \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F qu qr Q.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and> generation_program_scope H F qu qr Q \<and>
      U=({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q))"

theorem amendment_dependency_subjects_with_scopes:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
  shows "amendment_dependency_subjects C q H U\<longleftrightarrow>
    U=({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q)"
proof
  assume "amendment_dependency_subjects C q H U"
  then obtain A' l' G' p' E' pu' pr' P' d' F' qu' qr' Q' where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' P' d'"
    "generation_program_scope H F' qu' qr' Q'"
    "U=({E'}\<times>system_definitions P')\<union>({F'}\<times>system_definitions Q')"
    unfolding amendment_dependency_subjects_def by blast
  have before: "E=E' \<and> P=P'" using current_entry_scope_unique[OF current other(1)] by blast
  have after: "F=F' \<and> Q=Q'" using generation_program_scope_unique[OF candidate other(2) refl] by blast
  show "U=({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q)" using other(3) before after by simp
next
  assume "U=({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q)"
  then show "amendment_dependency_subjects C q H U"
    using current candidate unfolding amendment_dependency_subjects_def by blast
qed

theorem amendment_dependency_subjects_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
  shows "\<exists>U. amendment_dependency_subjects C q H U"
  by (rule exI[of _ "({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q)"])
     (simp only: amendment_dependency_subjects_with_scopes[OF current candidate] refl)

theorem amendment_dependency_subjects_unique:
  assumes first: "amendment_dependency_subjects C q H U"
    and second: "amendment_dependency_subjects C q H V"
  shows "U=V"
proof -
  obtain A l G p E pu pr P d F qu qr Q where scopes:
    "current_entry_scope_quoted_at C q A l G p E pu pr P d" "generation_program_scope H F qu qr Q"
    using first unfolding amendment_dependency_subjects_def by blast
  show ?thesis using first second by (simp only: amendment_dependency_subjects_with_scopes[OF scopes]; blast)
qed

theorem amendment_dependency_subjects_boundary:
  assumes subjects: "amendment_dependency_subjects C q H U"
  shows "finite U" "U\<noteq>{}"
    "\<forall>N d. (N,d)\<in>U \<longrightarrow> environment_formed N \<and> d\<in>environment_positions N \<and>
      (\<exists>p B. native_definition_at N (fst d) (snd d) p B)"
proof -
  obtain A l G p E pu pr P d F qu qr Q where scopes:
    "current_entry_scope_quoted_at C q A l G p E pu pr P d" "generation_program_scope H F qu qr Q"
    and exact: "U=({E}\<times>system_definitions P)\<union>({F}\<times>system_definitions Q)"
    using subjects unfolding amendment_dependency_subjects_def by blast
  have packages: "native_package_at E pu pr P" "native_package_at F qu qr Q"
    using current_entry_scope_closed[OF scopes(1)] generation_program_scope_closed[OF scopes(2)]
    by (auto simp: closed_native_package_at_def)
  have old: "finite (system_definitions P)" "environment_formed E"
    "\<forall>d\<in>system_definitions P. d\<in>environment_positions E \<and>
      (\<exists>p C. native_definition_at E (fst d) (snd d) p C)"
    using native_package_definition_subjects[OF packages(1)] by auto
  have candidate: "finite (system_definitions Q)" "environment_formed F"
    "\<forall>d\<in>system_definitions Q. d\<in>environment_positions F \<and>
      (\<exists>p C. native_definition_at F (fst d) (snd d) p C)"
    using native_package_definition_subjects[OF packages(2)] by auto
  show "finite U" using old(1) candidate(1) exact by simp
  have member: "d\<in>system_definitions P" using current_entry_scope_closed[OF scopes(1)] by blast
  show "U\<noteq>{}" using member exact by auto
  show "\<forall>N d. (N,d)\<in>U \<longrightarrow> environment_formed N \<and> d\<in>environment_positions N \<and>
      (\<exists>p B. native_definition_at N (fst d) (snd d) p B)"
    using old(2,3) candidate(2,3) exact by auto
qed

theorem amendment_dependency_membership:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and subjects: "amendment_dependency_subjects C q H U"
  shows "(N,e)\<in>U\<longleftrightarrow>
    (N=E \<and> e\<in>system_definitions P) \<or> (N=F \<and> e\<in>system_definitions Q)"
  using subjects by (simp only: amendment_dependency_subjects_with_scopes[OF current candidate]; auto)

theorem amendment_dependency_same_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H E pu pr P"
  shows "amendment_dependency_subjects C q H U\<longleftrightarrow>U={E}\<times>system_definitions P"
  by (simp only: amendment_dependency_subjects_with_scopes[OF current candidate] Un_absorb)

text \<open>
  The required boundary contains every definition in both complete closed
  program packages. It includes their root definitions and all prospective
  dependencies, regardless of whether a definition is changed or lies on a
  public comparison boundary. No submitted proof chooses a smaller domain.

  Each subject retains its exact canonical program environment and actual
  definition site. Coincident coordinates in different scopes do not identify
  their subjects. Identical scope-and-site pairs occur once, including when
  the candidate retains the predecessor's whole program scope.

  The boundary is finite and nonempty for every actual current frame and
  program candidate. Its sites have actual native definition readings before
  evidence is considered. These facts provide no permission or proof for
  any required dependency.
\<close>

end
