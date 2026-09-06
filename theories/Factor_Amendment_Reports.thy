theory Factor_Amendment_Reports
  imports Factor_Amendment_Domains Factor_Report_Programs
begin

section \<open>The current frame fixes the domains before reports are supplied\<close>

definition amendment_reports_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    (local_address option definition_site option\<times>local_address option definition_site option) set \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site \<Rightarrow> bool" where
  "amendment_reports_at C q H M F fu fr b \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d N qu qr Q T.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      generation_program_scope H N qu qr Q \<and>
      closed_native_package_at F fu fr T \<and> native_package_environment F fu fr=F \<and>
      b\<in>system_definitions T \<and> program_reports_only T b \<and>
      system_report_coverage P Q
        (system_comparison_definitions P Q (native_package_roots E pu pr))
        (system_comparison_definitions Q P (native_package_roots N qu qr))
        M (program_judgment_reports T b) \<and>
      system_report_sound P Q (program_judgment_reports T b))"

theorem amendment_reports_with_scopes:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H N qu qr Q"
    and reporter: "closed_native_package_at F fu fr T"
    and minimal: "native_package_environment F fu fr=F"
  shows "amendment_reports_at C q H M F fu fr b \<longleftrightarrow>
    b\<in>system_definitions T \<and> program_reports_only T b \<and>
    system_report_coverage P Q
      (system_comparison_definitions P Q (native_package_roots E pu pr))
      (system_comparison_definitions Q P (native_package_roots N qu qr))
      M (program_judgment_reports T b) \<and>
    system_report_sound P Q (program_judgment_reports T b)"
proof
  assume valid: "amendment_reports_at C q H M F fu fr b"
  obtain A' l' G' p' E' pu' pr' P' d' N' qu' qr' Q' T' where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' P' d'"
    "generation_program_scope H N' qu' qr' Q'"
    "closed_native_package_at F fu fr T'"
    "b\<in>system_definitions T'" "program_reports_only T' b"
    "system_report_coverage P' Q'
      (system_comparison_definitions P' Q' (native_package_roots E' pu' pr'))
      (system_comparison_definitions Q' P' (native_package_roots N' qu' qr'))
      M (program_judgment_reports T' b)"
    "system_report_sound P' Q' (program_judgment_reports T' b)"
    using valid unfolding amendment_reports_at_def by blast
  have before: "E=E' \<and> pu=pu' \<and> pr=pr' \<and> P=P'"
    using current_entry_scope_unique[OF current other(1)] by blast
  have after: "N=N' \<and> qu=qu' \<and> qr=qr' \<and> Q=Q'"
    by (rule generation_program_scope_unique[OF candidate other(2) refl])
  have left: "native_package_at F fu fr T" and right: "native_package_at F fu fr T'"
    using reporter other(3) by (auto simp: closed_native_package_at_def)
  have same: "T=T'" by (rule native_package_unique[OF left right])
  show "b\<in>system_definitions T \<and> program_reports_only T b \<and>
    system_report_coverage P Q
      (system_comparison_definitions P Q (native_package_roots E pu pr))
      (system_comparison_definitions Q P (native_package_roots N qu qr))
      M (program_judgment_reports T b) \<and>
    system_report_sound P Q (program_judgment_reports T b)"
    using other(4-7) before after same by simp
next
  assume "b\<in>system_definitions T \<and> program_reports_only T b \<and>
    system_report_coverage P Q
      (system_comparison_definitions P Q (native_package_roots E pu pr))
      (system_comparison_definitions Q P (native_package_roots N qu qr))
      M (program_judgment_reports T b) \<and>
    system_report_sound P Q (program_judgment_reports T b)"
  then show "amendment_reports_at C q H M F fu fr b"
    using current candidate reporter minimal unfolding amendment_reports_at_def by blast
qed

theorem amendment_reports_complete_calls:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H N qu qr Q"
    and reporter: "closed_native_package_at F fu fr T" "native_package_environment F fu fr=F"
    and accepted: "amendment_reports_at C q H M F fu fr b"
  shows "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    and "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls Q P (native_package_roots N qu qr)"
proof -
  have coverage: "system_report_coverage P Q
      (system_comparison_definitions P Q (native_package_roots E pu pr))
      (system_comparison_definitions Q P (native_package_roots N qu qr))
      M (program_judgment_reports T b)"
    using accepted by (simp add: amendment_reports_with_scopes[OF current candidate reporter])
  show "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls Q P (native_package_roots N qu qr)"
    using system_report_every_call[OF coverage] by (simp_all add: system_comparison_calls_boundary)
qed

theorem amendment_reports_nonempty:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H N qu qr Q"
    and reporter: "closed_native_package_at F fu fr T" "native_package_environment F fu fr=F"
    and accepted: "amendment_reports_at C q H M F fu fr b"
  shows "finite M \<and> M\<noteq>{} \<and> program_judgment_reports T b\<noteq>{}"
proof -
  let ?U="system_comparison_definitions P Q (native_package_roots E pu pr)"
  let ?V="system_comparison_definitions Q P (native_package_roots N qu qr)"
  have coverage: "system_report_coverage P Q ?U ?V M (program_judgment_reports T b)"
    using accepted by (simp add: amendment_reports_with_scopes[OF current candidate reporter])
  have domains: "amendment_definition_domains C q H ?U ?V"
    by (simp add: amendment_definition_domains_with_scopes[OF current candidate])
  have old: "?U={} \<longleftrightarrow> system_definitions P={}"
    using amendment_definition_domain_boundaries(5)[OF current candidate domains] by blast
  have entry: "d\<in>system_definitions P" using current_entry_scope_closed[OF current] by blast
  have nonempty: "?U\<noteq>{}" using old entry by blast
  show ?thesis using system_report_migration_finite[OF coverage] system_report_empty[OF coverage] nonempty by blast
qed

text \<open>
  The exact current frame and candidate generation determine both programs and
  both required domains. The reporter supplies neither a root list nor a domain.
  Its finite native scope and selected entry determine all judgment reports;
  the structural migration relation is finite as a consequence of coverage.

  Every required call has both declaration fields. No current frame can pass
  this profile with empty structural or judgment reports. Report syntax,
  complete coverage, preservation soundness, and current amendment acceptance
  remain different relations. In particular, this theory does not insert the
  reporter's clauses into the predecessor's active rule package.

  This is a checked mathematical profile for comparison material. Native
  admission of the complete submitted certificate, migration evidence, the
  exact cross-version bridge, continuation, and successor adoption remain
  separate obligations. Future amendment policies may change this profile
  through the predecessor-authorized mechanism.
\<close>

end
