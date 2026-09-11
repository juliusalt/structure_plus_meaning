theory Factor_Fragment_Contracts
  imports Factor_Fragment_Projections
begin

section \<open>Each derived projection owns a complete function contract\<close>

lemma fragment_material_presented:
  "(206,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    presented_relation fragment_value_presents artifact_value_presents (\<lambda>G z. z=fragment_material G) p q"
  by (auto simp: fragment_material_exact presented_relation_def)

interpretation fragment_material_reading: presented_function_contract
  fragment_value_presents fragment_formed "\<lambda>p. (205,p)\<in>positive_meaning fragment_system"
  artifact_value_presents "exact_formed" "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  fragment_material "\<lambda>p q. (206,Pair_Term p q)\<in>positive_meaning fragment_system"
  using fragment_value_native_class artifact_presentations.presentation_class_axioms fragment_material_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def fragment_material_presented; blast)

lemma fragment_remainder_presented:
  "(207,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    presented_relation fragment_value_presents artifact_value_presents (\<lambda>G z. z=fragment_remainder G) p q"
  by (auto simp: fragment_remainder_exact presented_relation_def)

interpretation fragment_remainder_reading: presented_function_contract
  fragment_value_presents fragment_formed "\<lambda>p. (205,p)\<in>positive_meaning fragment_system"
  artifact_value_presents "exact_formed" "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  fragment_remainder "\<lambda>p q. (207,Pair_Term p q)\<in>positive_meaning fragment_system"
  using fragment_value_native_class artifact_presentations.presentation_class_axioms fragment_remainder_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def fragment_remainder_presented; blast)

lemma fragment_omission_presented:
  "(208,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    presented_relation fragment_value_presents payload_set_presents (\<lambda>G z. z=fragment_omission G) p q"
  by (auto simp: fragment_omission_exact presented_relation_def)

interpretation fragment_omission_reading: presented_function_contract
  fragment_value_presents fragment_formed "\<lambda>p. (205,p)\<in>positive_meaning fragment_system"
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)" "\<lambda>q. (1,q)\<in>positive_meaning distinct_payloads_system"
  fragment_omission "\<lambda>p q. (208,Pair_Term p q)\<in>positive_meaning fragment_system"
  using fragment_value_native_class payload_set_presentation_class fragment_omission_coordinates
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def fragment_omission_presented; blast)

lemma fragment_boundary_presented:
  "(209,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    presented_relation fragment_value_presents incidence_set_presents (\<lambda>G z. z=fragment_boundary G) p q"
  by (auto simp: fragment_boundary_exact presented_relation_def)

interpretation fragment_boundary_reading: presented_function_contract
  fragment_value_presents fragment_formed "\<lambda>p. (205,p)\<in>positive_meaning fragment_system"
  incidence_set_presents "\<lambda>A. finite A \<and> (\<forall>z\<in>A. incidence_coordinates_formed z)" "presented_predicate (data_sequence_presents incidence_value_presents) distinct"
  fragment_boundary "\<lambda>p q. (209,Pair_Term p q)\<in>positive_meaning fragment_system"
  using fragment_value_native_class incidence_set_presentation_class fragment_boundary_coordinates
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def fragment_boundary_presented; blast)

section \<open>The joint report composes those contracts at the same source\<close>

lemma fragment_report_at_source:
  assumes source: "fragment_value_presents G p"
  shows "(210,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    fragment_views_presents (fragment_views G) q"
  by (auto simp: fragment_report_calls fragment_material_reading.output[OF source]
    fragment_remainder_reading.output[OF source] fragment_boundary_reading.output[OF source]
    factor_pair_presents_def)

theorem fragment_report_exact:
  "(210,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>G. fragment_report_presents G t)"
proof
  assume holds: "(210,t)\<in>positive_meaning fragment_system"
  obtain p m b r where shape: "t=Pair_Term p (Pair_Term m (Pair_Term b r))"
    and material: "(206,Pair_Term p m)\<in>positive_meaning fragment_system"
    using holds by (simp only: fragment_report_calls; blast)
  obtain G where source: "fragment_value_presents G p"
    using fragment_projection_source[of 206 "Pair_Term p m"] material by auto
  have views: "fragment_views_presents (fragment_views G) (Pair_Term m (Pair_Term b r))"
    using holds by (simp only: shape fragment_report_at_source[OF source])
  show "\<exists>G. fragment_report_presents G t" by (rule exI[of _ G])
    (use source views shape in \<open>auto simp: fragment_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>G. fragment_report_presents G t"
  then obtain G p q where source: "fragment_value_presents G p"
    and views: "fragment_views_presents (fragment_views G) q" and shape: "t=Pair_Term p q"
    by (auto simp: fragment_report_presents_def factor_pair_presents_def)
  show "(210,t)\<in>positive_meaning fragment_system"
    by (simp only: shape fragment_report_at_source[OF source]) (rule views)
qed

theorem fragment_report_native_class:
  "presentation_class fragment_report_presents fragment_formed
    (\<lambda>p. (210,p)\<in>positive_meaning fragment_system)"
  using fragment_report_presentation_class by (simp only: fragment_report_exact)

lemma fragment_views_presented:
  "(210,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    presented_relation fragment_value_presents fragment_views_presents (\<lambda>G z. z=fragment_views G) p q"
  by (auto simp: fragment_report_exact fragment_report_presents_def factor_pair_presents_def presented_relation_def)

interpretation fragment_views_reading: presented_function_contract
  fragment_value_presents fragment_formed "\<lambda>p. (205,p)\<in>positive_meaning fragment_system"
  fragment_views_presents fragment_views_formed "\<lambda>q. \<exists>z. fragment_views_presents z q"
  fragment_views "\<lambda>p q. (210,Pair_Term p q)\<in>positive_meaning fragment_system"
  using fragment_value_native_class fragment_views_presentation_class fragment_views_boundary
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def fragment_views_presented; blast)

section \<open>The report recovers the complete original artifact\<close>

theorem fragment_native_source_reconstructed:
  assumes source: "fragment_value_presents G p"
    and views: "fragment_views_presents (M,(C,N)) q"
    and accepted: "(210,Pair_Term p q)\<in>positive_meaning fragment_system"
  shows "fragment_selection G=rra_carrier (object_structure M)"
    and "fragment_source G=
      \<lparr>object_structure=\<lparr>rra_carrier=rra_carrier (object_structure M)\<union>rra_carrier (object_structure N),
        rra_incidence=rra_incidence (object_structure M)\<union>rra_incidence (object_structure N)\<union>C\<rparr>,
       object_data=\<lparr>bag_count=(\<lambda>(a,v). bag_count (object_data M) (a,v)+bag_count (object_data N) (a,v)),
         functional_bindings=functional_bindings (object_data M)\<union>functional_bindings (object_data N)\<rparr>\<rparr>"
proof -
  have equality: "(M,(C,N))=fragment_views G"
    using fragment_views_reading.at[OF source views] accepted by blast
  have same: "M=fragment_material G" "C=fragment_boundary G" "N=fragment_remainder G"
    using equality by auto
  have formed: "fragment_formed G" by (rule fragments.subject_boundary[OF source])
  show "fragment_selection G=rra_carrier (object_structure M)"
    using formed by (auto simp: same fragment_formed_def fragment_material_def restrict_object_def restrict_structure_def)
  show "fragment_source G=
      \<lparr>object_structure=\<lparr>rra_carrier=rra_carrier (object_structure M)\<union>rra_carrier (object_structure N),
        rra_incidence=rra_incidence (object_structure M)\<union>rra_incidence (object_structure N)\<union>C\<rparr>,
       object_data=\<lparr>bag_count=(\<lambda>(a,v). bag_count (object_data M) (a,v)+bag_count (object_data N) (a,v)),
         functional_bindings=functional_bindings (object_data M)\<union>functional_bindings (object_data N)\<rparr>\<rparr>"
    using fragment_source_reconstructed[OF formed] by (simp only: same)
qed

corollary fragment_wrong_report_rejected:
  assumes source: "fragment_value_presents G p" and views: "fragment_views_presents z q"
    and different: "z\<noteq>fragment_views G"
  shows "(210,Pair_Term p q)\<notin>positive_meaning fragment_system"
  using different fragment_views_reading.at[OF source views] by blast

lemma fragment_operations_require_admission:
  assumes "d\<in>{206,207,208,209,210}" "(d,Pair_Term p q)\<in>positive_meaning fragment_system"
  shows "(205,p)\<in>positive_meaning fragment_system"
  using assms by (auto simp: fragment_material_calls fragment_remainder_calls fragment_omission_calls
    fragment_boundary_calls fragment_report_calls; blast)

corollary fragment_invalid_selection_no_outputs:
  assumes source: "artifact_value_presents R p" and selection: "payload_set_presents X c"
    and invalid: "\<not>X\<subseteq>rra_carrier (object_structure R)" and entry: "d\<in>{206,207,208,209,210}"
  shows "(d,Pair_Term (Pair_Term p c) q)\<notin>positive_meaning fragment_system"
  using fragment_operations_require_admission[OF entry] fragment_invalid_selection_rejected[OF source selection invalid] by blast

section \<open>Every formed fragment has complete native source and report material\<close>

theorem fragment_native_total:
  assumes formed: "fragment_formed G"
  shows "\<exists>p. fragment_value_presents G p \<and> (205,p)\<in>positive_meaning fragment_system \<and>
    complete_data_quoted_at (term_syntax p) [] p \<and>
    (\<forall>q. fragment_views_presents (fragment_views G) q \<longrightarrow>
      (210,Pair_Term p q)\<in>positive_meaning fragment_system \<and>
      fragment_report_presents G (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q))"
proof -
  obtain p where source: "fragment_value_presents G p" using fragments.total[OF formed] by blast
  have admitted: "(205,p)\<in>positive_meaning fragment_system"
    using source by (simp only: fragment_admission_exact; blast)
  have data: "term_formed p" "self_contained_term p" using fragment_value_formed[OF source] by blast+
  have quotation: "complete_data_quoted_at (term_syntax p) [] p" by (rule complete_data_quotation_total[OF data])
  have reports: "(210,Pair_Term p q)\<in>positive_meaning fragment_system \<and>
      fragment_report_presents G (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    if views: "fragment_views_presents (fragment_views G) q" for q
  proof -
    have accepted: "(210,Pair_Term p q)\<in>positive_meaning fragment_system"
      by (simp only: fragment_views_reading.output[OF source]) (rule views)
    have presented: "fragment_report_presents G (Pair_Term p q)"
      using source views by (simp add: fragment_report_presents_def)
    have data: "term_formed (Pair_Term p q)" "self_contained_term (Pair_Term p q)"
      using fragment_report_formed[OF presented] by blast+
    have quoted: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
      by (rule complete_data_quotation_total[OF data])
    show ?thesis using accepted presented quoted by blast
  qed
  show ?thesis using source admitted quotation reports by blast
qed

section \<open>One fixed native program precedes every future operand\<close>

abbreviation fragment_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "fragment_operation_result d t \<equiv>
    if d=205 then (\<exists>G. fragment_value_presents G t)
    else if d=206 then (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> artifact_value_presents (fragment_material G) q)
    else if d=207 then (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> artifact_value_presents (fragment_remainder G) q)
    else if d=208 then (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> payload_set_presents (fragment_omission G) q)
    else if d=209 then (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> incidence_set_presents (fragment_boundary G) q)
    else (\<exists>G. fragment_report_presents G t)"

theorem fragment_operations_exact:
  assumes "d\<in>{205,206,207,208,209,210}"
  shows "(d,t)\<in>positive_meaning fragment_system \<longleftrightarrow> fragment_operation_result d t"
proof -
  consider (source) "d=205" | (material) "d=206" | (remainder) "d=207"
    | (omission) "d=208" | (boundary) "d=209" | (report) "d=210" using assms by auto
  then show ?thesis
  proof cases
    case source show ?thesis by (simp only: source fragment_admission_exact; simp)
  next
    case material show ?thesis by (simp only: material fragment_material_exact; simp)
  next
    case remainder show ?thesis by (simp only: remainder fragment_remainder_exact; simp)
  next
    case omission show ?thesis by (simp only: omission fragment_omission_exact; simp)
  next
    case boundary show ?thesis by (simp only: boundary fragment_boundary_exact; simp)
  next
    case report show ?thesis by (simp only: report fragment_report_exact; simp)
  qed
qed

theorem native_fragment_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {205::nat,206,207,208,209,210} \<and>
    (\<forall>d\<in>{205,206,207,208,209,210}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> fragment_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{205,206,207,208,209,210}\<subseteq>system_definitions fragment_system" by auto
  have calls: "schema_call_formed fragment_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{205,206,207,208,209,210}" for d t using fragment_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF fragment_system_formed selected calls fragment_operations_exact])
qed

text \<open>
  The four projection contracts and their combined report accept exactly the
  complete presentations of the independent fragment notions. Every report
  recovers the selected carrier and the full original artifact, including all
  incidence and every counted or functional attachment. Invalid selections
  and altered views fail the native entries.

  A single closed program provides all six public operations before future
  operands are supplied. Its native applications preserve the complete program
  scope, artifacts, and bindings. These results supply fragment operations to
  later assembly work. The separate structural assembly and universally
  invariant construction-permission judgments are not discharged here.
\<close>

end
