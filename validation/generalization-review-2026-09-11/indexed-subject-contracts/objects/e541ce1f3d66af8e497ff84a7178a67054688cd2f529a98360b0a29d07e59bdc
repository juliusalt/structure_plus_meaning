theory Factor_Amendment_Domains
  imports Factor_Program_Changes Factor_Current_Entries
begin

section \<open>Public roots are recovered from the actual native package\<close>

lemma native_package_roots_inside:
  assumes package: "native_package_at E u r P"
  shows "native_package_roots E u r\<subseteq>system_definitions P"
  using native_definition_roots[of "native_package_roots E u r" E]
    native_package_projection(3)[OF package] by (simp add: native_package_sites_def)

lemma native_package_roots_empty:
  assumes package: "native_package_at E u r P"
  shows "native_package_roots E u r={}\<longleftrightarrow>system_definitions P={}"
proof
  assume empty: "native_package_roots E u r={}"
  show "system_definitions P={}" using native_package_projection(3)[OF package] empty
    by (simp add: native_package_sites_def native_definition_sites_def)
next
  assume "system_definitions P={}"
  then show "native_package_roots E u r={}" using native_package_roots_inside[OF package] by blast
qed

definition amendment_definition_domains ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option definition_site set \<Rightarrow> local_address option definition_site set \<Rightarrow> bool" where
  "amendment_definition_domains C q H U V \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F qu qr Q.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      generation_program_scope H F qu qr Q \<and>
      U=system_comparison_definitions P Q (native_package_roots E pu pr) \<and>
      V=system_comparison_definitions Q P (native_package_roots F qu qr))"

theorem amendment_definition_domains_with_scopes:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
  shows "amendment_definition_domains C q H U V\<longleftrightarrow>
    U=system_comparison_definitions P Q (native_package_roots E pu pr) \<and>
    V=system_comparison_definitions Q P (native_package_roots F qu qr)"
proof
  assume domains: "amendment_definition_domains C q H U V"
  obtain A' l' G' p' E' pu' pr' P' d' F' qu' qr' Q' where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' P' d'"
    "generation_program_scope H F' qu' qr' Q'"
    "U=system_comparison_definitions P' Q' (native_package_roots E' pu' pr')"
    "V=system_comparison_definitions Q' P' (native_package_roots F' qu' qr')"
    using domains unfolding amendment_definition_domains_def by blast
  have before: "E=E' \<and> pu=pu' \<and> pr=pr' \<and> P=P'"
    using current_entry_scope_unique[OF current other(1)] by blast
  have after: "F=F' \<and> qu=qu' \<and> qr=qr' \<and> Q=Q'"
    by (rule generation_program_scope_unique[OF candidate other(2) refl])
  show "U=system_comparison_definitions P Q (native_package_roots E pu pr) \<and>
    V=system_comparison_definitions Q P (native_package_roots F qu qr)"
    using other(3,4) before after by simp
next
  assume "U=system_comparison_definitions P Q (native_package_roots E pu pr) \<and>
    V=system_comparison_definitions Q P (native_package_roots F qu qr)"
  then show "amendment_definition_domains C q H U V"
    using current candidate unfolding amendment_definition_domains_def by blast
qed

theorem amendment_definition_domains_total:
  assumes "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    "generation_program_scope H F qu qr Q"
  shows "\<exists>U V. amendment_definition_domains C q H U V"
  by (rule exI[of _ "system_comparison_definitions P Q (native_package_roots E pu pr)"],
      rule exI[of _ "system_comparison_definitions Q P (native_package_roots F qu qr)"])
     (simp add: amendment_definition_domains_with_scopes[OF assms])

theorem amendment_definition_domains_unique:
  assumes first: "amendment_definition_domains C q H U V"
    and second: "amendment_definition_domains C q H X Y"
  shows "U=X \<and> V=Y"
proof -
  obtain A l G p E pu pr P d F qu qr Q where scopes:
    "current_entry_scope_quoted_at C q A l G p E pu pr P d" "generation_program_scope H F qu qr Q"
    using first unfolding amendment_definition_domains_def by blast
  show ?thesis using first second
    by (auto simp: amendment_definition_domains_with_scopes[OF scopes])
qed

theorem amendment_definition_domain_boundaries:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and domains: "amendment_definition_domains C q H U V"
  shows "U\<subseteq>system_definitions P \<and> V\<subseteq>system_definitions Q \<and> finite U \<and> finite V"
    and "native_package_roots E pu pr\<subseteq>U \<and> native_package_roots F qu qr\<subseteq>V"
    and "rel_dom (system_comparison_calls P Q (native_package_roots E pu pr))=U"
    and "rel_dom (system_comparison_calls Q P (native_package_roots F qu qr))=V"
    and "(U={}\<longleftrightarrow>system_definitions P={}) \<and> (V={}\<longleftrightarrow>system_definitions Q={})"
proof -
  have packages: "native_package_at E pu pr P" "native_package_at F qu qr Q"
    using current_entry_scope_closed[OF current] generation_program_scope_closed[OF candidate]
    by (auto simp: closed_native_package_at_def)
  have formed: "schema_system_formed P" "schema_system_formed Q"
    using native_package_system_formed[OF packages(1)] native_package_system_formed[OF packages(2)] by auto
  have roots: "native_package_roots E pu pr\<subseteq>system_definitions P"
    "native_package_roots F qu qr\<subseteq>system_definitions Q"
    using native_package_roots_inside[OF packages(1)] native_package_roots_inside[OF packages(2)] by auto
  have exact: "U=system_comparison_definitions P Q (native_package_roots E pu pr)"
    "V=system_comparison_definitions Q P (native_package_roots F qu qr)"
    using domains by (auto simp: amendment_definition_domains_with_scopes[OF current candidate])
  show boundary: "U\<subseteq>system_definitions P \<and> V\<subseteq>system_definitions Q \<and> finite U \<and> finite V"
    using system_comparison_definitions_boundary[where Q=Q, OF formed(1) roots(1)]
      system_comparison_definitions_boundary[where Q=P, OF formed(2) roots(2)] exact by auto
  show root_boundary: "native_package_roots E pu pr\<subseteq>U \<and> native_package_roots F qu qr\<subseteq>V"
    using exact by (auto simp: system_comparison_definitions_def)
  show "rel_dom (system_comparison_calls P Q (native_package_roots E pu pr))=U"
    using system_comparison_calls_projection[OF formed(1) roots(1)] exact(1) by simp
  show "rel_dom (system_comparison_calls Q P (native_package_roots F qu qr))=V"
    using system_comparison_calls_projection[OF formed(2) roots(2)] exact(2) by simp
  show "(U={}\<longleftrightarrow>system_definitions P={}) \<and> (V={}\<longleftrightarrow>system_definitions Q={})"
    using boundary root_boundary native_package_roots_empty[OF packages(1)]
      native_package_roots_empty[OF packages(2)] by blast
qed

theorem amendment_outside_domain_preserved:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and domains: "amendment_definition_domains C q H U V"
    and member: "e\<in>system_definitions P" and outside: "e\<notin>U"
  shows "schema_call_formed P e t\<longleftrightarrow>schema_call_formed Q e t"
    and "(e,t)\<in>positive_meaning P\<longleftrightarrow>(e,t)\<in>positive_meaning Q"
proof -
  have packages: "native_package_at E pu pr P" "native_package_at F qu qr Q"
    using current_entry_scope_closed[OF current] generation_program_scope_closed[OF candidate]
    by (auto simp: closed_native_package_at_def)
  have formed: "schema_system_formed P" "schema_system_formed Q"
    using native_package_system_formed[OF packages(1)] native_package_system_formed[OF packages(2)] by auto
  have unaffected: "e\<notin>system_affected_definitions P (system_changed_definitions P Q)"
    using domains outside by (auto simp: amendment_definition_domains_with_scopes[OF current candidate]
      system_comparison_definitions_def)
  show "schema_call_formed P e t\<longleftrightarrow>schema_call_formed Q e t"
    "(e,t)\<in>positive_meaning P\<longleftrightarrow>(e,t)\<in>positive_meaning Q"
    by (rule system_unaffected_meaning[OF formed member unaffected])+
qed

text \<open>
  The exact current frame and the candidate's complete program payload fix both
  programs, both native root families, and both comparison domains. No certificate
  supplies a root list or chooses a smaller domain. The two domains remain
  relative to their respective exact scopes even when coordinates coincide.

  Each finite definition boundary contains every actual public root and every
  caller of a changed definition. Its corresponding call boundary contains all
  arguments admitted by the actual interfaces. It is empty exactly when that
  native program has no definitions. Outside the boundary, complete clause and
  dependency agreement already preserves formation and positive meaning.

  This profile compares complete recovered rows at their given coordinates.
  An explicit relocation may establish semantic preservation while those rows
  change. Structural migration and semantic interpretation still need separate
  relations and certificates; computing these domains neither grants authority
  nor establishes an admissible transition.
\<close>

end
