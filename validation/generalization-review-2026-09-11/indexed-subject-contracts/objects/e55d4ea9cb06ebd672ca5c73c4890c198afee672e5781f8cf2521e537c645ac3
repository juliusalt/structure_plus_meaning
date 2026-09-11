theory Factor_Assembly_Contracts
  imports Factor_Assembly_Admission
begin

section \<open>The native report owns the complete output function contract\<close>

lemma assembly_output_presented:
  "(230,Pair_Term p q)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    presented_relation (assembly_value_presents payload_value_presents) artifact_value_presents
      (\<lambda>W R. R=assembly_output W) p q"
  by (auto simp: assembly_report_exact assembly_report_presents_def factor_pair_presents_def presented_relation_def)

interpretation assembly_output_reading: presented_function_contract
  "assembly_value_presents payload_value_presents" "assembly_domain octets_formed"
  "\<lambda>p. (231,p)\<in>positive_meaning assembly_checking_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  assembly_output "\<lambda>p q. (230,Pair_Term p q)\<in>positive_meaning assembly_checking_system"
  using assembly_source_native_class artifact_presentations.presentation_class_axioms
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def assembly_output_presented)
    (auto simp: K2_def)

theorem assembly_source_at_tables:
  assumes pieces: "piece_family_presents payload_value_presents P p"
    and origins: "origin_table_presents payload_value_presents q t"
  shows "(231,Pair_Term p t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    K2 \<lparr>assembly_pieces=P,assembly_origin=q\<rparr>"
proof
  assume accepted: "(231,Pair_Term p t)\<in>positive_meaning assembly_checking_system"
  obtain W where witness: "K2 W"
    "piece_family_presents payload_value_presents (assembly_pieces W) p"
    "origin_table_presents payload_value_presents (assembly_origin W) t"
    using accepted by (auto simp: assembly_source_exact assembly_value_fields)
  have same: "assembly_pieces W=P" "assembly_origin W=q"
    using native_piece_families.recovery[OF witness(2) pieces]
      native_origin_tables.recovery[OF witness(3) origins] by auto
  have witness_record: "W=\<lparr>assembly_pieces=P,assembly_origin=q\<rparr>" using same by (cases W) auto
  show "K2 \<lparr>assembly_pieces=P,assembly_origin=q\<rparr>" using witness(1) by (simp only: witness_record)
next
  assume formed: "K2 \<lparr>assembly_pieces=P,assembly_origin=q\<rparr>"
  have source: "assembly_value_presents payload_value_presents
      \<lparr>assembly_pieces=P,assembly_origin=q\<rparr> (Pair_Term p t)"
    using formed pieces origins by (simp only: assembly_value_fields) simp
  show "(231,Pair_Term p t)\<in>positive_meaning assembly_checking_system"
    using source by (simp only: assembly_source_exact; blast)
qed

corollary assembly_incomplete_origins_rejected:
  assumes pieces: "piece_family_presents payload_value_presents P p"
    and origins: "origin_table_presents payload_value_presents q t"
    and incomplete: "rel_dom q\<noteq>copied_carrier P"
  shows "(231,Pair_Term p t)\<notin>positive_meaning assembly_checking_system"
  using incomplete by (auto simp: assembly_source_at_tables[OF pieces origins]
    K2_iff_complete_compatible_origins exact_map_def)

corollary assembly_functional_conflict_rejected:
  assumes pieces: "piece_family_presents payload_value_presents P p"
    and origins: "origin_table_presents payload_value_presents q t"
    and conflict: "\<not>basis_compatible (rel_value q) (copied_basis P)"
  shows "(231,Pair_Term p t)\<notin>positive_meaning assembly_checking_system"
  using conflict by (simp only: assembly_source_at_tables[OF pieces origins]
    K2_iff_complete_compatible_origins; simp)

corollary assembly_wrong_output_rejected:
  assumes source: "assembly_value_presents payload_value_presents W p"
    and result: "artifact_value_presents R q" and different: "R\<noteq>assembly_output W"
  shows "(230,Pair_Term p q)\<notin>positive_meaning assembly_checking_system"
  using assembly_output_reading.at[OF source result] different by blast

section \<open>Every complete source and output presentation remains available\<close>

theorem assembly_native_total:
  assumes domain: "assembly_domain octets_formed W"
  shows "\<exists>p. assembly_value_presents payload_value_presents W p \<and>
    (231,p)\<in>positive_meaning assembly_checking_system \<and>
    complete_data_quoted_at (term_syntax p) [] p \<and>
    (\<forall>q. artifact_value_presents (assembly_output W) q \<longrightarrow>
      (230,Pair_Term p q)\<in>positive_meaning assembly_checking_system \<and>
      assembly_report_presents payload_value_presents W (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q))"
proof -
  obtain p where source: "assembly_value_presents payload_value_presents W p"
    using presentation_class.total[OF assembly_source_native_class domain] by blast
  have admitted: "(231,p)\<in>positive_meaning assembly_checking_system"
    using source by (simp only: assembly_source_exact; blast)
  have data: "term_formed p" "self_contained_term p"
    using assembly_value_formed[OF source] by auto
  have quotation: "complete_data_quoted_at (term_syntax p) [] p"
    by (rule complete_data_quotation_total[OF data])
  have reports: "(230,Pair_Term p q)\<in>positive_meaning assembly_checking_system \<and>
      assembly_report_presents payload_value_presents W (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    if result: "artifact_value_presents (assembly_output W) q" for q
  proof -
    have accepted: "(230,Pair_Term p q)\<in>positive_meaning assembly_checking_system"
      by (simp only: assembly_output_reading.output[OF source]) (rule result)
    have report: "assembly_report_presents payload_value_presents W (Pair_Term p q)"
      using source result by (simp only: assembly_report_presents_def factor_pair_presents_at)
    have data: "term_formed (Pair_Term p q)" "self_contained_term (Pair_Term p q)"
      using assembly_report_formed[OF report] by auto
    show ?thesis using accepted report complete_data_quotation_total[OF data] by blast
  qed
  show ?thesis using source admitted quotation reports by blast
qed

theorem assembly_report_native_quotation_class:
  "presentation_class
    (composed_presentation (assembly_report_presents payload_value_presents)
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (assembly_domain octets_formed)
    (\<lambda>p. \<exists>t. (230,t)\<in>positive_meaning assembly_checking_system \<and>
      complete_data_quoted_at (fst p) (snd p) t)"
  by (simp only: assembly_report_exact)
    (rule assembly_report_quotation_class[OF payload_value_presentation_class]; auto)

section \<open>One fixed native program checks every future source and report\<close>

abbreviation assembly_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "assembly_operation_result d t \<equiv> if d=230 then (\<exists>W. assembly_report_presents payload_value_presents W t)
    else (\<exists>W. assembly_value_presents payload_value_presents W t)"

lemma assembly_operations_exact:
  assumes "d\<in>{230,231}"
  shows "(d,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow> assembly_operation_result d t"
  using assms by (auto simp: assembly_report_exact assembly_source_exact)

theorem native_assembly_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {230::nat,231} \<and>
    (\<forall>d\<in>{230,231}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> assembly_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{230,231}\<subseteq>system_definitions assembly_checking_system" by auto
  have calls: "schema_call_formed assembly_checking_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{230,231}" for d t using assembly_checking_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF assembly_checking_system_formed selected calls assembly_operations_exact])
qed

text \<open>
  Clients use the exported function contract for totality, every compatible
  output form, presentation invariance, adaptation, and composition. The
  source and report classes retain their original semantic subjects and
  complete boundaries. Quotations retain the actual complete report body.

  Missing and extra origin keys fail full coverage, including keys for unused
  atoms. Functional conflicts fail even when both component tables are
  admitted. The output relation sums counted occurrences and takes set images
  for incidence and functional bindings, as specified by the original K2
  assembly. It imposes no injectivity on destinations.

  Both public entries belong to a program fixed before every future operand.
  Its native realization retains exact package scope, artifacts, and bindings.
  Assembly admission establishes structural reuse. Construction permission and
  its global invariance remain separate judgments and obligations.
\<close>

end
