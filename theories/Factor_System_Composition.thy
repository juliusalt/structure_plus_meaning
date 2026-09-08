theory Factor_System_Composition
  imports Factor_System_Unions Factor_View_Definitions
begin

lemma systems_agree_on_reflexive [simp]: "systems_agree_on P P U"
  by (simp add: systems_agree_on_def)

lemma systems_agree_on_subdomain:
  assumes "systems_agree_on P Q U" "V\<subseteq>U"
  shows "systems_agree_on P Q V"
  using assms by (auto simp: systems_agree_on_def)

lemma systems_agree_on_transitive:
  assumes "systems_agree_on P Q U" "systems_agree_on Q T U"
  shows "systems_agree_on P T U"
  using assms by (auto simp: systems_agree_on_def; blast)

lemma systems_agree_on_added:
  assumes "d\<notin>U"
  shows "systems_agree_on P (add_view_definition Q d p C) U \<longleftrightarrow> systems_agree_on P Q U"
  using assms by (auto simp: systems_agree_on_def)

section \<open>Complete shared definitions support local program composition\<close>

theorem system_union_agree_formed:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
  shows "schema_system_formed (system_union P Q)"
proof -
  have left_interfaces: "single_valued (system_interfaces P)"
    and right_interfaces: "single_valued (system_interfaces Q)"
    and left_clauses: "single_valued (system_clauses P)"
    and right_clauses: "single_valued (system_clauses Q)"
    using left right unfolding schema_system_formed_def by blast+
  have interfaces: "\<And>d p q. (d,p)\<in>system_interfaces P \<Longrightarrow>
      (d,q)\<in>system_interfaces Q \<Longrightarrow> p=q"
  proof -
    fix d p q assume first: "(d,p)\<in>system_interfaces P" and second: "(d,q)\<in>system_interfaces Q"
    have inside: "d\<in>system_definitions P" "d\<in>system_definitions Q"
      using first second by (auto simp: system_definitions_def rel_dom_def)
    have other: "(d,q)\<in>system_interfaces P"
      using agree inside second unfolding systems_agree_on_def by blast
    show "p=q" using left_interfaces first other unfolding single_valued_def by blast
  qed
  have clauses: "\<And>d c S T. ((d,c),S)\<in>system_clauses P \<Longrightarrow>
      ((d,c),T)\<in>system_clauses Q \<Longrightarrow> S=T"
  proof -
    fix d c S T assume first: "((d,c),S)\<in>system_clauses P" and second: "((d,c),T)\<in>system_clauses Q"
    have inside: "d\<in>system_definitions P" "d\<in>system_definitions Q"
      using left right first second unfolding schema_system_formed_def by blast+
    have other: "((d,c),T)\<in>system_clauses P"
      using agree inside second unfolding systems_agree_on_def by blast
    show "S=T" using left_clauses first other unfolding single_valued_def by blast
  qed
  have finite: "finite (system_interfaces (system_union P Q))"
    "finite (system_clauses (system_union P Q))"
    using left right by (auto simp: system_union_def schema_system_formed_def)
  have functional_interfaces: "single_valued (system_interfaces (system_union P Q))"
    using left_interfaces right_interfaces interfaces
    by (auto simp: single_valued_def; blast)
  have functional_clauses: "single_valued (system_clauses (system_union P Q))"
    using left_clauses right_clauses clauses
    by (auto simp: single_valued_def; blast)
  have patterns: "\<forall>d p. (d,p)\<in>system_interfaces (system_union P Q) \<longrightarrow> pattern_formed p"
    using left right by (auto simp: schema_system_formed_def)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses (system_union P Q) \<longrightarrow>
    d\<in>system_definitions (system_union P Q) \<and> schema_formed S \<and>
    schema_dependencies S \<subseteq> system_definitions (system_union P Q)"
    using left right by (auto simp: schema_system_formed_def; blast)
  show ?thesis using finite functional_interfaces functional_clauses patterns schemas
    by (simp only: schema_system_formed_def)
qed

lemma system_union_agree_left:
  assumes right: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
  shows "systems_agree_on P (system_union P Q) (system_definitions P)"
proof -
  have interfaces: "(d,p)\<in>system_interfaces P"
    if inside: "d\<in>system_definitions P" and row: "(d,p)\<in>system_interfaces Q" for d p
  proof -
    have other: "d\<in>system_definitions Q"
      using row by (auto simp: system_definitions_def rel_dom_def)
    show ?thesis using agree inside other row unfolding systems_agree_on_def by blast
  qed
  have clauses: "((d,c),S)\<in>system_clauses P"
    if inside: "d\<in>system_definitions P" and row: "((d,c),S)\<in>system_clauses Q" for d c S
  proof -
    have other: "d\<in>system_definitions Q"
      using right row unfolding schema_system_formed_def by blast
    show ?thesis using agree inside other row unfolding systems_agree_on_def by blast
  qed
  show ?thesis using interfaces clauses by (auto simp: systems_agree_on_def)
qed

theorem system_union_agree_left_locality:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
    and member: "d\<in>system_definitions P"
  shows "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed P d t"
    and "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have formed: "schema_system_formed (system_union P Q)"
    by (rule system_union_agree_formed[OF left right agree])
  have same: "systems_agree_on P (system_union P Q) (system_definitions P)"
    by (rule system_union_agree_left[OF right agree])
  have closed: "system_dependency_closed P (system_definitions P)"
    using system_dependency_boundary(1)[OF left] by (auto simp: system_dependency_closed_def)
  show "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed P d t"
    using schema_call_agreement[OF left formed same member] by blast
  show "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    using positive_meaning_dependency_locality[OF left formed same closed member] by blast
qed

theorem system_union_agree_right_locality:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
    and member: "d\<in>system_definitions Q"
  shows "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed Q d t"
    and "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
proof -
  have reverse: "systems_agree_on Q P (system_definitions Q \<inter> system_definitions P)"
    using systems_agree_on_sym[OF agree] by (simp only: Int_commute)
  show "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed Q d t"
    using system_union_agree_left_locality(1)[OF right left reverse member]
    by (simp only: system_union_commute)
  show "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
    using system_union_agree_left_locality(2)[OF right left reverse member]
    by (simp only: system_union_commute)
qed

theorem system_union_agree_call:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
  shows "schema_call_formed (system_union P Q) d t \<longleftrightarrow>
    schema_call_formed P d t \<or> schema_call_formed Q d t"
  using left right system_union_agree_formed[OF left right agree]
  by (auto simp: schema_call_formed_def)

text \<open>
  A locally defined program retains its complete interface and clauses when
  composed with another formed program. Shared definition coordinates must
  denote the same actual definitions, including the whole clause families.
  The existing dependency-locality theorem then preserves both programs'
  complete meanings and call boundaries. The shared boundary is closed by
  the existing intersection theorem.

  This is physical sharing of definitions, whose actual material is part of
  the program subject. It does not replace the semantic correspondences
  between different implementations of one notion. Those implementations
  retain their own scopes and exported contracts. The fresh-definition rule
  and transitivity allow each local module to export a structural agreement
  once, so a later program join need not reprove the meanings of its readers.
\<close>

end
