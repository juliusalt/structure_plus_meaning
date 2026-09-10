theory Factor_Specialization_Report_Total
  imports Factor_Specialization_Reports
begin

section \<open>Every actually admitted specialization has a complete report\<close>

theorem specialization_report_total:
  assumes admitted: "(294,t)\<in>positive_meaning clause_specialization_reading_system"
  shows "\<exists>v. (342,Pair_Term t v)\<in>positive_meaning specialization_report_system"
proof -
  obtain z where presented: "clause_specialization_context_presents z t"
    using admitted by (simp only: clause_specialization_context_admission; blast)
  obtain E pu pr d c F bu br G qu qr where
    shape: "z=(((E,pu,pr),(d,c)),((F,bu,br),(G,qu,qr)))" by (metis surjective_pairing)
  obtain a b q where actual: "schema_clause_specialization_at E pu pr d c F bu br G qu qr"
    and site: "site_value_presents G qu qr q"
    and body: "t=Pair_Term (Pair_Term a (Pair_Term (definition_site_value d) (Payload_Term c))) (Pair_Term b q)"
    using presented by (simp only: shape clause_specialization_context_fields; blast)
  obtain T where native: "native_schema_at G qu qr T"
    using actual by (simp only: schema_clause_specialization_at_def; blast)
  obtain v where reference: "schema_reference_presents T v"
    using native_schema_reference_total[OF native] by blast
  have read: "(126,Pair_Term q v)\<in>positive_meaning schema_reading_system"
    using native by (simp only: schema_reading_at_reference[OF site reference])
  have report: "(126,Pair_Term q v)\<in>positive_meaning clause_specialization_reading_system"
    using read by (simp only: specialization_report_reference_meaning)
  show ?thesis by (rule exI[of _ v])
    (use admitted report in \<open>simp only: body specialization_report_at_arguments\<close>)
qed

corollary specialization_report_inhabited:
  "\<exists>z. (342,z)\<in>positive_meaning specialization_report_system"
  using clause_specialization_reading_inhabited specialization_report_total by blast

text \<open>
  This uses the actual native target recovered from an admitted specialization.
  Its complete schema presentation supplies the second premise of the report
  rule. The construction is therefore available on every admitted source,
  including its private variables and pending material operands. It does not
  infer admission from a merely formed frontier term or establish material truth.

  The universal result and its inhabited instance are semantic proofs. They
  are distinct from executing the earlier structural frontier controls.
\<close>

end
