theory Factor_Publication_Scopes
  imports Factor_Site_Values RRA_Publication_Dependencies
begin

section \<open>Publication views recovered from their complete recorded scope\<close>

definition publication_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> publication_view \<Rightarrow> bool" where
  "publication_scope_quoted_at C q E u root P \<longleftrightarrow>
    site_value_quoted_at C q E u root \<and> publication_environment_closed E u root P"

theorem publication_scope_quoted_unique:
  assumes first: "publication_scope_quoted_at C q E u root P"
    and second: "publication_scope_quoted_at C q F v other Q"
  shows "E=F \<and> u=v \<and> root=other \<and> P=Q"
proof -
  have left: "site_value_quoted_at C q E u root" "publication_at E u root P"
    using first by (auto simp: publication_scope_quoted_at_def publication_environment_closed_def)
  have right: "site_value_quoted_at C q F v other" "publication_at F v other Q"
    using second by (auto simp: publication_scope_quoted_at_def publication_environment_closed_def)
  have same: "E=F \<and> u=v \<and> root=other" by (rule site_value_quoted_unique[OF left(1) right(1)])
  have other: "publication_at E u root Q" using right(2) same by simp
  have view: "P=Q" by (rule publication_at_unique[OF left(2) other])
  show ?thesis using same view by blast
qed

lemma publication_scope_is_minimal:
  assumes "publication_scope_quoted_at C q E u root P"
  shows "publication_environment E u root=E"
  using assms unfolding publication_scope_quoted_at_def
  by (meson publication_closed_environment_fixed)

lemma publication_scope_quoted_formed:
  assumes quote: "publication_scope_quoted_at C q E u root P"
  shows "exact_formed C \<and> environment_formed E \<and> publication_formed P \<and>
    (u,root)\<in>environment_positions E"
proof -
  have site: "site_value_quoted_at C q E u root" and pub: "publication_at E u root P"
    using quote by (auto simp: publication_scope_quoted_at_def publication_environment_closed_def)
  show ?thesis using site_value_quoted_formed[OF site] publication_at_formed[OF pub] by blast
qed

theorem publication_scope_quoted_total:
  assumes pub: "publication_at E u root P"
  shows "\<exists>C. exact_formed C \<and> publication_scope_quoted_at C [] (publication_environment E u root) u root P"
proof -
  let ?F="publication_environment E u root"
  have closed: "publication_environment_closed ?F u root P" by (rule publication_closed_restriction[OF pub])
  have retained: "publication_at ?F u root P" using closed by (simp add: publication_environment_closed_def)
  have formed: "environment_formed ?F" by (rule publication_environment_formed[OF pub])
  obtain R where source: "artifact_at ?F u R" "anchor_formed (R,root)"
    using publication_at_has_anchor[OF retained] by blast
  have site: "(u,root)\<in>environment_positions ?F" using source by (auto simp: anchor_formed_def)
  obtain C where cf: "exact_formed C" and quote: "site_value_quoted_at C [] ?F u root"
    using site_value_quoted_total[OF formed site] by blast
  show ?thesis by (rule exI[of _ C])
    (use cf quote closed in \<open>simp add: publication_scope_quoted_at_def\<close>)
qed

theorem publication_scope_quoted_in_environment:
  assumes quote: "publication_scope_quoted_at C q E u root P"
    and formed: "environment_formed F" and source: "artifact_at F v C"
  shows "\<exists>t. site_value_presents E u root t \<and>
    term_quoted_at F v q t (rra_carrier (object_structure C)) {}"
  using quote unfolding publication_scope_quoted_at_def
  by (meson site_value_quoted_in_environment[OF _ formed source])

text \<open>
  The stored data contains the exact retained environment and publication site.
  The publication view is recovered from that scope; it is not a second stored
  field. Both the scope and its recovered view are determined by the exact
  quotation artifact and root, independently of an enclosing environment.

  This records the publication's reading boundary. It supplies no adoption,
  authority, evidence validation, or currentness judgment.
\<close>

end
