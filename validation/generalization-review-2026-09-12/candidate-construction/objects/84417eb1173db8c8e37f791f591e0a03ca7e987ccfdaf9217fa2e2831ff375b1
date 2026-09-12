theory Factor_Copy_Reports
  imports Factor_Report_Families Factor_Program_Scopes
begin

section \<open>Actual native interfaces determine a finite complete reporter\<close>

theorem copied_judgment_reports_native:
  fixes E F :: "local_address option artifact_environment"
  assumes old: "native_package_at E pu pr P" and candidate: "native_package_at F qu qr Q"
    and inside: "U\<subseteq>system_definitions P" "V\<subseteq>system_definitions Q"
    and mapped: "f ` U\<subseteq>V"
    and calls: "\<And>d t. d\<in>U \<Longrightarrow> schema_call_formed Q (f d) t \<longleftrightarrow> schema_call_formed P d t"
    and truth: "\<And>d t. d\<in>U \<Longrightarrow> (f d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  shows "\<exists>N :: local_address option artifact_environment. \<exists>nu R c.
    closed_native_package_at N nu [] R \<and> native_package_environment N nu []=N \<and>
    c\<in>system_definitions R \<and> program_reports_only R c \<and>
    program_judgment_reports R c=copied_judgment_reports P Q U V f \<and>
    system_report_coverage P Q U V (correspondence_completion U V ((\<lambda>d. (d,f d)) ` U))
      (program_judgment_reports R c) \<and>
    system_report_sound P Q (program_judgment_reports R c)"
proof -
  have formed: "schema_system_formed P" "schema_system_formed Q"
    using native_package_system_formed[OF old] native_package_system_formed[OF candidate] by auto
  have environments: "environment_formed E" "environment_formed F"
    using native_package_projection(1)[OF old] native_package_projection(1)[OF candidate]
    by (auto simp: native_package_formed_def)
  have finite: "finite U" "finite V"
    using finite_subset[OF inside(1) system_definitions_finite[OF formed(1)]]
      finite_subset[OF inside(2) system_definitions_finite[OF formed(2)]] by blast+
  have old_address: "octets_formed (snd d)" if "d\<in>U" for d
    by (rule environment_position_address[OF environments(1)], rule native_package_entry_position[OF old])
      (use inside(1) that in blast)
  have new_address: "octets_formed (snd e)" if "e\<in>V" for e
    by (rule environment_position_address[OF environments(2)], rule native_package_entry_position[OF candidate])
      (use inside(2) that in blast)
  have old_pattern: "pattern_formed (system_interface P d)" if "d\<in>U" for d
    by (rule system_interface_formed[OF formed(1)]) (use inside(1) that in blast)
  have new_pattern: "pattern_formed (system_interface Q e)" if "e\<in>V" for e
    by (rule system_interface_formed[OF formed(2)]) (use inside(2) that in blast)
  have old_accepts: "pattern_accepts (system_interface P d) t \<longleftrightarrow> schema_call_formed P d t"
    if "d\<in>U" for d t
    using inside(1) that by (auto simp: schema_call_at_interface[OF formed(1)])
  have new_accepts: "pattern_accepts (system_interface Q e) t \<longleftrightarrow> schema_call_formed Q e t"
    if "e\<in>V" for e t
    using inside(2) that by (auto simp: schema_call_at_interface[OF formed(2)])
  let ?D="Inl ` U \<union> Inr ` (V-f ` U)"
  let ?l="case_sum Some (\<lambda>_. None)"
  let ?r="case_sum (\<lambda>d. Some (f d)) Some"
  let ?b="case_sum (\<lambda>_. (True,False)) (\<lambda>_. (False,True))"
  let ?p="case_sum (system_interface P) (system_interface Q)"
  have df: "finite ?D" using finite by simp
  have mapped_address: "octets_formed (snd (f d))" if "d\<in>U" for d
    by (rule new_address) (use mapped that in auto)
  have sites: "\<forall>k\<in>?D. report_definition_formed (?l k)" "\<forall>k\<in>?D. report_definition_formed (?r k)"
    using old_address new_address mapped_address by auto
  have nonempty: "\<forall>k\<in>?D. ?l k\<noteq>None \<or> ?r k\<noteq>None" by auto
  have patterns: "\<forall>k\<in>?D. pattern_formed (?p k)" using old_pattern new_pattern by auto
  obtain N :: "local_address option artifact_environment" and nu R c where reporter:
    "closed_native_package_at N nu [] R" "native_package_environment N nu []=N"
    "c\<in>system_definitions R" "program_reports_only R c"
    "program_judgment_reports R c=
      (\<Union>k\<in>?D. (\<lambda>t. (report_endpoints (?l k) (?r k) t,?b k)) ` {t. pattern_accepts (?p k) t})"
    "\<forall>t. term_formed t \<longrightarrow> (\<exists>L au I K.
      environment_formed L \<and> environment_included N L \<and> native_package_at L nu [] R \<and>
      native_package_environment L nu []=N \<and> native_application_at L au [] c t I K \<and>
      native_application_formed L nu [] au [] \<and>
      (native_positive_holds L nu [] au [] \<longleftrightarrow>
        (\<exists>k\<in>?D. \<exists>x. pattern_accepts (?p k) x \<and>
          t=judgment_report_term (report_endpoints (?l k) (?r k) x) (?b k))))"
    using report_family_native[OF df sites nonempty patterns, where b="?b"] by (atomize_elim) assumption
  have exact: "program_judgment_reports R c=copied_judgment_reports P Q U V f"
    by (auto simp: reporter(5) copied_judgment_reports_def report_endpoints_def old_accepts new_accepts image_iff)
  have coverage: "system_report_coverage P Q U V (correspondence_completion U V ((\<lambda>d. (d,f d)) ` U))
      (program_judgment_reports R c)"
    using copied_judgment_reports_complete[OF formed inside mapped calls] exact by simp
  have sound: "system_report_sound P Q (program_judgment_reports R c)"
    using copied_judgment_reports_sound[OF truth, where V=V] exact by simp
  show ?thesis by (rule exI[of _ N], rule exI[of _ nu], rule exI[of _ R], rule exI[of _ c])
    (use reporter(1-4) exact coverage sound in blast)
qed

text \<open>
  Each required old definition contributes its actual interface pattern and
  reports preservation at the supplied corresponding definition. Every other
  required candidate definition contributes its own actual interface pattern
  and an explicit missing-old-counterpart row with intentional incompatibility.
  Both declaration fields occur at every admitted argument.

  Complete interface agreement makes every required call occur in these rows.
  Independent equality of positive truth establishes the preservation claims.
  The map need not be injective for reporting; the historical compilation
  supplies injective copies as a sufficient case. Missing counterparts refer
  to this declared correspondence and do not rule out a different one.

  Only the finite interface family is compiled. The complete report relation
  and the absence of extra output shapes follow from ordinary clauses for all
  arguments, including nested patterns and exact literal targets. The native
  reporter is supplied comparison material; it does not become a rule of the
  predecessor's acceptance program.
\<close>

end
