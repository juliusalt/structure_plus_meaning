theory Factor_Admitted_Pair
  imports Factor_Data_Term_Presentations Factor_Admission_Pair_Schemas
begin

section \<open>Each field retains its own native admission\<close>

locale admitted_pair_profile =
  fixes P :: "(nat,nat,'d,nat) schema_system" and entry first second :: 'd
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow> c=0 \<and> S=admitted_pair_schema first second"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (first,h 0)\<in>positive_meaning P \<and> (second,h 1)\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family admitted_pair_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P)"
  by (rule admitted_pair_rule_family[OF call]) (auto simp: system_clause_member family)

corollary at_pair:
  "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P"
  by (auto simp only: exact factor_term.inject)

theorem presentation_class:
  assumes left: "presentation_class R D (\<lambda>p. (first,p)\<in>positive_meaning P)"
    and right: "presentation_class S E (\<lambda>q. (second,q)\<in>positive_meaning P)"
  shows "presentation_class (factor_pair_presents R S) (\<lambda>z. D (fst z) \<and> E (snd z))
    (\<lambda>t. (entry,t)\<in>positive_meaning P)"
proof -
  have source: "presentation_class (factor_pair_presents R S) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>t. \<exists>p q. (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF left right])
  have admission: "(\<lambda>t. \<exists>p q. (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P \<and> t=Pair_Term p q)=
      (\<lambda>t. (entry,t)\<in>positive_meaning P)"
    by (rule ext) (simp only: exact; blast)
  show ?thesis using source by (simp only: admission)
qed

end

text \<open>
  The two actual callees admit separate fields at distinct premise sockets.
  Their locally owned classes give the complete pair class without adding
  a relation between its subjects. The existing data-pair clause is the case
  in which both fields call data admission. The same construction applies
  when the two fields have different complete domains.
\<close>

end
