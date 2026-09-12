theory Factor_Fragment_Admission
  imports Factor_Fragment_Filters
begin

section \<open>Admission compares the complete selection with its source intersection\<close>

theorem fragment_admission_at_enumeration:
  assumes source: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c"
  shows "(205,Pair_Term (artifact_data_term A E B F) c)\<in>positive_meaning fragment_system
    \<longleftrightarrow> fragment_formed G"
proof -
  let ?p="Pair_Term (artifact_data_term A E B F) c"
  let ?a="data_list_term (map Payload_Term A)"
  have raw: "(205,?p)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (11,artifact_data_term A E B F)\<in>positive_meaning fragment_system \<and>
      (\<exists>q. (197,Pair_Term c (Pair_Term ?a q))\<in>positive_meaning fragment_system \<and>
        (6,Pair_Term q c)\<in>positive_meaning fragment_system)"
    by (auto simp: fragment_admission_calls artifact_data_term_def)
  have admitted: "(11,artifact_data_term A E B F)\<in>positive_meaning fragment_system"
    by (simp only: fragment_components(5) artifact_value_presents_def; use source in blast)
  have filtered: "(197,Pair_Term c (Pair_Term ?a q))\<in>positive_meaning fragment_system \<longleftrightarrow>
      q=data_list_term (map Payload_Term (filter (\<lambda>a. a\<in>fragment_selection G) A))" for q
    by (rule fragment_selected_payloads_at_selection[OF selection artifact_enumeration_coordinates(1)[OF source]])
  show ?thesis using fragment_selection_compared[OF source selection]
    by (simp only: raw admitted simp_thms filtered fragment_components(3); auto)
qed

theorem fragment_admission_exact:
  "(205,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>G. fragment_value_presents G t)"
proof
  assume holds: "(205,t)\<in>positive_meaning fragment_system"
  obtain a e b f c q where shape: "t=Pair_Term (artifact_fields_term a e b f) c"
    and source_call: "(11,artifact_fields_term a e b f)\<in>positive_meaning fragment_system"
    and filtered: "(197,Pair_Term c (Pair_Term a q))\<in>positive_meaning fragment_system"
    using holds by (simp only: fragment_admission_calls; blast)
  obtain R A E B F where source: "artifact_enumeration R A E B F"
    and encoded: "artifact_fields_term a e b f=artifact_data_term A E B F"
    using source_call by (simp only: fragment_components(5) artifact_value_presents_def; blast)
  have admitted: "(1,c)\<in>positive_meaning distinct_payloads_system"
    using fragment_selected_payloads.sound[OF filtered] by auto
  obtain X where selection: "payload_set_presents X c" using admitted by (simp only: payload_set_admission; blast)
  let ?G="\<lparr>fragment_source=R,fragment_selection=X\<rparr>"
  have enumeration: "artifact_enumeration (fragment_source ?G) A E B F"
    and selected: "payload_set_presents (fragment_selection ?G) c" using source selection by simp_all
  have formed: "fragment_formed ?G"
    using holds by (simp only: shape encoded fragment_admission_at_enumeration[OF enumeration selected])
  show "\<exists>G. fragment_value_presents G t" by (rule exI[of _ ?G])
    (use formed source selection shape encoded in \<open>auto simp: fragment_value_enumerations\<close>)
next
  assume "\<exists>G. fragment_value_presents G t"
  then obtain G A E B F c where formed: "fragment_formed G"
    and source: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c"
    and shape: "t=Pair_Term (artifact_data_term A E B F) c"
    by (simp only: fragment_value_enumerations; blast)
  show "(205,t)\<in>positive_meaning fragment_system"
    by (simp only: shape fragment_admission_at_enumeration[OF source selection]) (rule formed)
qed

theorem fragment_value_native_class:
  "presentation_class fragment_value_presents fragment_formed
    (\<lambda>p. (205,p)\<in>positive_meaning fragment_system)"
  using fragment_value_presentation_class by (simp only: fragment_admission_exact)

lemma fragment_admission_at_components:
  assumes source: "artifact_value_presents R p" and selection: "payload_set_presents X c"
  shows "(205,Pair_Term p c)\<in>positive_meaning fragment_system \<longleftrightarrow>
    X\<subseteq>rra_carrier (object_structure R)"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F" and shape: "p=artifact_data_term A E B F"
    using source by (simp only: artifact_value_presents_def; blast)
  let ?G="\<lparr>fragment_source=R,fragment_selection=X\<rparr>"
  have listed: "artifact_enumeration (fragment_source ?G) A E B F"
    and chosen: "payload_set_presents (fragment_selection ?G) c" using enumeration selection by simp_all
  show ?thesis using payload_set_formed[OF selection] artifact_value_presents_formed[OF source]
    by (simp only: shape fragment_admission_at_enumeration[OF listed chosen] fragment_formed_def; simp)
qed

corollary fragment_invalid_selection_rejected:
  assumes "artifact_value_presents R p" "payload_set_presents X c"
    "\<not>X\<subseteq>rra_carrier (object_structure R)"
  shows "(205,Pair_Term p c)\<notin>positive_meaning fragment_system"
  using assms(3) fragment_admission_at_components[OF assms(1,2)] by blast

text \<open>
  Fragment admission recovers one complete source artifact and one complete
  selection, then verifies that every selected address occurs in that source.
  The empty selection and the whole carrier are covered by the same clauses.
  No derived view is accepted as a substitute for the source or selection.
\<close>

end
