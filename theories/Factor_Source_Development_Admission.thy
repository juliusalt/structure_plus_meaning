theory Factor_Source_Development_Admission
  imports Factor_Source_Development_Cycle Factor_Workflow_Evidence_Meaning
begin

lemma source_development_admission_fields:
  assumes "source_development_admission R report=Some (proposal,installed,query)"
  obtains Q native accepted S where
    "source_development_question R=Some Q"
    "native_development_admission Q native=Some accepted"
    "source_development_selection R accepted=Some proposal"
    "source_development_install R proposal=Some installed"
    "S=source_development_query_stage R installed"
    "workflow_stage_evidence S (source_development_input R) query"
    "source_report_proposals report=source_development_proposals R"
    "source_report_observations report=source_development_observations R"
    "source_report_stage report=Some S" "source_report_query report=Some query"
  using assms by (auto simp: source_development_admission_def
    split: option.splits prod.splits if_splits)

theorem source_development_committed_target:
  assumes result: "source_development_admission R report=Some ((Q,e),(d,F,u),query)"
  shows "(Q,e)\<in>set (source_development_targets R)"
    "source_development_compatible R Q"
    "e |\<in>| finite_system_definitions Q"
    "finite_development_scope_complete (source_development_values R)"
    "finite_install_source_entry (source_development_environment R) (source_development_use R)
      (source_development_root R) Q e=Some (d,F,u)"
proof -
  obtain question native accepted where q: "source_development_question R=Some question"
    and admission: "native_development_admission question native=Some accepted"
    and selected: "source_development_selection R accepted=Some (Q,e)"
    and installed: "source_development_install R (Q,e)=Some (d,F,u)"
    by (rule source_development_admission_fields[OF result]) blast
  show "(Q,e)\<in>set (source_development_targets R)"
    "source_development_compatible R Q" "e |\<in>| finite_system_definitions Q"
    "finite_development_scope_complete (source_development_values R)"
    using source_development_selected_original_target[OF q admission selected] by blast+
  show "finite_install_source_entry (source_development_environment R) (source_development_use R)
      (source_development_root R) Q e=Some (d,F,u)"
    using installed by (simp only: source_development_install_def case_prod_conv)
qed

theorem source_development_committed_meaning:
  assumes result: "source_development_admission R report=Some ((Q,e),(d,F,u),query)"
  obtains P T where
    "native_package_at (decode_finite_environment (source_development_environment R))
      (source_development_use R) (source_development_root R) (decode_finite_system P)"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment (source_development_environment R)) (decode_finite_environment F)"
    "native_package_at (decode_finite_environment F) (source_development_use R)
      (source_development_root R) (decode_finite_system P)"
    "native_package_at (decode_finite_environment F) u [] T"
    "d\<in>system_definitions T"
    "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> (e,t)\<in>positive_meaning (decode_finite_system Q)"
    "\<forall>w\<in>fset (finite_environment_uses (source_development_environment R)). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow>
        artifact_at (decode_finite_environment (source_development_environment R)) w A"
    "\<forall>w\<in>fset (finite_environment_uses (source_development_environment R)). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow>
        binds_slot (decode_finite_environment (source_development_environment R)) w k v"
proof -
  have installed: "finite_install_source_entry (source_development_environment R) (source_development_use R)
      (source_development_root R) Q e=Some (d,F,u)"
    by (rule source_development_committed_target(5)[OF result])
  obtain P where ready: "finite_source_extension_context (source_development_environment R)
      (source_development_use R) (source_development_root R) Q=Some P"
    using installed finite_install_source_entry_total by blast
  show thesis using finite_install_source_entry_correct[OF installed ready] that by blast
qed

theorem source_development_query_uses_installed_source:
  assumes result: "source_development_admission R report=Some (proposal,(d,F,u),query)"
  shows "source_report_stage report=Some
    \<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
      workflow_outputs=Workflow_Values (source_development_outputs R)\<rparr>"
    "workflow_stage_evidence
      \<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
        workflow_outputs=Workflow_Values (source_development_outputs R)\<rparr>
      (source_development_input R) query"
  using source_development_admission_fields[OF result]
  by (auto simp: source_development_query_stage_def)

theorem source_development_query_original_exact:
  assumes result: "source_development_admission R report=Some ((Q,e),(d,F,u),(P,D,A,T,ys))"
  shows "ys=filter (\<lambda>y. (e,Pair_Term (decode_finite_term (source_development_input R))
    (decode_finite_term y))\<in>positive_meaning (decode_finite_system Q)) (source_development_outputs R)"
proof -
  let ?S="\<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
      workflow_outputs=Workflow_Values (source_development_outputs R)\<rparr>"
  let ?x="source_development_input R"
  have evidence: "workflow_stage_evidence ?S ?x (P,D,A,T,ys)"
    by (rule source_development_query_uses_installed_source(2)[OF result])
  have source: "finite_native_source (workflow_source ?S) (workflow_source_use ?S) (workflow_source_root ?S)=Some P"
    and entry: "workflow_entry ?S |\<in>| finite_system_definitions P"
    using evidence by (auto simp: workflow_stage_evidence_def)
  have actual: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    using source by (simp add: finite_native_source_correct)
  obtain N where native: "native_package_at (decode_finite_environment F) u [] N"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning N \<longleftrightarrow>
      (e,t)\<in>positive_meaning (decode_finite_system Q)"
    by (rule source_development_committed_meaning[OF result]) blast
  have same: "decode_finite_system P=N" by (rule native_package_unique[OF actual native])
  have scope: "workflow_scope_values ?S ?x=source_development_outputs R"
    by (simp add: workflow_scope_values_def workflow_scope_result_def)
  have relation: "workflow_stage_relation ?S ?x y \<longleftrightarrow> y\<in>set (source_development_outputs R) \<and>
    (e,Pair_Term (decode_finite_term ?x) (decode_finite_term y))\<in>positive_meaning (decode_finite_system Q)" for y
    using meaning by (simp add: workflow_stage_relation_at_source[OF source entry] scope same)
  show ?thesis
    unfolding workflow_stage_evidence_exact[OF evidence] scope
    by (rule filter_cong[OF refl]) (use relation in auto)
qed

theorem source_development_query_original_meaning:
  assumes result: "source_development_admission R report=Some ((Q,e),(d,F,u),(P,D,A,T,ys))"
    and answer: "y\<in>set ys"
  shows "(e,Pair_Term (decode_finite_term (source_development_input R)) (decode_finite_term y))
    \<in>positive_meaning (decode_finite_system Q)"
  using answer by (simp only: source_development_query_original_exact[OF result] set_filter; blast)

corollary source_development_missing_query_refuses:
  "source_report_query report=None \<Longrightarrow> source_development_admission R report=None"
  by (auto simp: source_development_admission_def split: option.splits prod.splits)

corollary source_development_missing_installation_refuses:
  "source_report_installed report=None \<Longrightarrow> source_development_admission R report=None"
  by (auto simp: source_development_admission_def split: option.splits prod.splits)

text \<open>
  A completed change belongs to the original requested target family. Its entire
  program meaning is preserved at the installed entry for every term, not only
  the subsequent query scope. Every old artifact, binding and native package
  reading remains intact. The later query consumes the actual installed source;
  its admitted answers belong to that original target program.
  These are source-extension and query contracts, not historical continuation
  permission or a self-authorized genesis handoff.
\<close>

end
