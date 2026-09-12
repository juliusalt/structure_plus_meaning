theory Factor_Collection_Selection
  imports Factor_Presentation_Transport
begin

section \<open>Literal selection is complete when each value has one presentation\<close>

theorem data_collection_selection_unique:
  assumes source: "data_collection_presents R X p"
    and data: "\<And>x t. x\<in>X \<Longrightarrow> R x t \<Longrightarrow>
      term_formed t \<and> self_contained_term t"
    and unique: "\<And>x t u. x\<in>X \<Longrightarrow> R x t \<Longrightarrow> R x u \<Longrightarrow> t=u"
  shows "selected_data_member q p \<longleftrightarrow> (\<exists>x\<in>X. R x q)"
proof -
  have selection: "(\<forall>x\<in>X. \<exists>u. selected_data_member u p \<and> R x u) \<and>
      (\<forall>u. selected_data_member u p \<longrightarrow> (\<exists>x\<in>X. R x u))"
    by (rule data_collection_selection[where R=R and A=X and a=p, OF source]) (use data in blast)
  show ?thesis
  proof
    assume selected: "selected_data_member q p"
    show "\<exists>x\<in>X. R x q" using selection selected by blast
  next
    assume "\<exists>x\<in>X. R x q"
    then obtain x where member: "x\<in>X" and reading: "R x q" by blast
    obtain u where selected: "selected_data_member u p" and stored: "R x u"
      using selection member by blast
    have same: "u=q" by (rule unique[OF member stored reading])
    show "selected_data_member q p" using selected same by simp
  qed
qed

section \<open>Comparison transports an actual selected form to every compatible form\<close>

theorem data_collection_selection_transport:
  assumes elements: "presentation_class R D A"
    and source: "data_collection_presents R X p"
    and data: "\<And>x t. x\<in>X \<Longrightarrow> R x t \<Longrightarrow>
      term_formed t \<and> self_contained_term t"
  shows "(\<exists>u. selected_data_member u p \<and> presentation_transport R S u q)
    \<longleftrightarrow> (\<exists>x\<in>X. S x q)"
proof -
  have selected: "(\<forall>x\<in>X. \<exists>u. selected_data_member u p \<and> R x u) \<and>
      (\<forall>u. selected_data_member u p \<longrightarrow> (\<exists>x\<in>X. R x u))"
    by (rule data_collection_selection[where R=R and A=X and a=p, OF source]) (use data in blast)
  show ?thesis using selected presentation_class.recovery[OF elements]
    by (auto simp: presentation_transport_def; blast)
qed

theorem data_collection_membership_contract:
  assumes elements: "presentation_class R D A"
    and data: "\<And>x t. R x t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  shows "presented_relation_contract
    (data_collection_presents R) (\<lambda>X. finite X \<and> (\<forall>x\<in>X. D x))
    (presented_predicate (data_sequence_presents R) distinct) R D A (\<lambda>X x. x\<in>X)
    (\<lambda>p q. (\<exists>X. data_collection_presents R X p) \<and>
      (\<exists>u. selected_data_member u p \<and> presentation_transport R R u q))"
proof -
  have collections: "presentation_class (data_collection_presents R)
      (\<lambda>X. finite X \<and> (\<forall>x\<in>X. D x))
      (presented_predicate (data_sequence_presents R) distinct)"
    by (rule data_collection_presentation_class[OF elements])
  have exact: "((\<exists>X. data_collection_presents R X p) \<and>
      (\<exists>u. selected_data_member u p \<and> presentation_transport R R u q)) \<longleftrightarrow>
      presented_relation (data_collection_presents R) R (\<lambda>X x. x\<in>X) p q" for p q
    using data_collection_selection_transport[OF elements, where S=R] data
    by (auto simp: presented_relation_def; blast)
  show ?thesis using collections elements exact
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem different_value_form_is_not_literal_selection:
  assumes first: "R x p" and other: "R x q" "p\<noteq>q"
    and data: "term_formed p" "self_contained_term p"
  shows "data_collection_presents R {x} (data_list_term [p]) \<and>
    selected_data_member p (data_list_term [p]) \<and>
    presentation_transport R R p q \<and>
    \<not>selected_data_member q (data_list_term [p])"
proof -
  have source: "data_collection_presents R {x} (data_list_term [p])"
    unfolding data_collection_presents_def
    by (intro exI[of _ "[x]"] exI[of _ "[p]"]) (use first in simp)
  have actual: "selected_data_member z (data_list_term [p]) \<longleftrightarrow> z=p" for z
    by (simp only: selected_data_member_exact data_list_term_injective) (use data in auto)
  show ?thesis using source first other
    by (simp only: actual) (auto simp: presentation_transport_def)
qed

text \<open>
  Selection returns a form present in the supplied complete collection. A
  value with one presentation therefore supports literal membership lookup.
  Multiple value forms require comparison with the selected form. Recovery
  of the element's subject makes that composition exact for every compatible
  output form; the target relation may even use another presentation type.

  The complete membership contract also requires admission of the whole
  source collection. Selection alone cannot establish that source boundary.
  These are consequences of the existing selection rule and presentation
  contracts, not additional native truth rules or implicit table readers.
\<close>

end
