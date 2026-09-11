theory Factor_System_Unions
  imports Factor_System_Relocation Factor_Positive_Locality
begin

section \<open>Complete union of systems with disjoint definition boundaries\<close>

definition system_union ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow>
    ('a,'s,'d,'c) schema_system" where
  "system_union P Q =
    \<lparr>system_interfaces=system_interfaces P \<union> system_interfaces Q,
      system_clauses=system_clauses P \<union> system_clauses Q\<rparr>"

lemma system_union_interfaces [simp]:
  "(d,p)\<in>system_interfaces (system_union P Q) \<longleftrightarrow>
    (d,p)\<in>system_interfaces P \<or> (d,p)\<in>system_interfaces Q"
  by (simp add: system_union_def)

lemma system_union_clauses [simp]:
  "((d,c),S)\<in>system_clauses (system_union P Q) \<longleftrightarrow>
    ((d,c),S)\<in>system_clauses P \<or> ((d,c),S)\<in>system_clauses Q"
  by (simp add: system_union_def)

lemma system_union_definitions [simp]:
  "system_definitions (system_union P Q)=system_definitions P \<union> system_definitions Q"
  by (auto simp: system_definitions_def rel_dom_def)

lemma system_union_commute: "system_union P Q=system_union Q P"
  by (simp add: system_union_def Un_commute)

theorem system_union_formed:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and separate: "system_definitions P \<inter> system_definitions Q={}"
  shows "schema_system_formed (system_union P Q)"
proof -
  have no_interfaces: "\<And>d p q. (d,p)\<in>system_interfaces P \<Longrightarrow>
    (d,q)\<in>system_interfaces Q \<Longrightarrow> False"
    using separate by (auto simp: system_definitions_def rel_dom_def)
  have no_clauses: "\<And>d c S T. ((d,c),S)\<in>system_clauses P \<Longrightarrow>
    ((d,c),T)\<in>system_clauses Q \<Longrightarrow> False"
  proof -
    fix d c S T assume lp: "((d,c),S)\<in>system_clauses P" and rq: "((d,c),T)\<in>system_clauses Q"
    have ld: "d\<in>system_definitions P" using left lp unfolding schema_system_formed_def by blast
    have rd: "d\<in>system_definitions Q" using right rq unfolding schema_system_formed_def by blast
    show False using separate ld rd by blast
  qed
  have finite: "finite (system_interfaces (system_union P Q))"
    "finite (system_clauses (system_union P Q))"
    using left right by (auto simp: system_union_def schema_system_formed_def)
  have interfaces: "single_valued (system_interfaces (system_union P Q))"
    using left right no_interfaces
    by (auto simp: single_valued_def schema_system_formed_def; blast)
  have clauses: "single_valued (system_clauses (system_union P Q))"
    using left right no_clauses
    by (auto simp: single_valued_def schema_system_formed_def; blast)
  have patterns: "\<forall>d p. (d,p)\<in>system_interfaces (system_union P Q) \<longrightarrow> pattern_formed p"
    using left right by (auto simp: schema_system_formed_def)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses (system_union P Q) \<longrightarrow>
    d\<in>system_definitions (system_union P Q) \<and> schema_formed S \<and>
    schema_dependencies S \<subseteq> system_definitions (system_union P Q)"
    using left right by (auto simp: schema_system_formed_def; blast)
  show ?thesis using finite interfaces clauses patterns schemas
    by (simp only: schema_system_formed_def)
qed

lemma system_union_left_agreement:
  assumes right: "schema_system_formed Q"
    and separate: "system_definitions P \<inter> system_definitions Q={}"
  shows "systems_agree_on P (system_union P Q) (system_definitions P)"
proof -
  have no_interfaces: "\<And>d p. d\<in>system_definitions P \<Longrightarrow>
    (d,p)\<notin>system_interfaces Q"
    using separate by (auto simp: system_definitions_def rel_dom_def)
  have no_clauses: "\<And>d c S. d\<in>system_definitions P \<Longrightarrow>
    ((d,c),S)\<notin>system_clauses Q"
    using right separate by (auto simp: schema_system_formed_def)
  show ?thesis using no_interfaces no_clauses by (auto simp: systems_agree_on_def)
qed

theorem system_union_left_locality:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and separate: "system_definitions P \<inter> system_definitions Q={}"
    and member: "d\<in>system_definitions P"
  shows "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed P d t"
    and "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have formed: "schema_system_formed (system_union P Q)"
    by (rule system_union_formed[OF left right separate])
  have agree: "systems_agree_on P (system_union P Q) (system_definitions P)"
    by (rule system_union_left_agreement[OF right separate])
  have closed: "system_dependency_closed P (system_definitions P)"
    using system_dependency_boundary(1)[OF left] by (auto simp: system_dependency_closed_def)
  show "schema_call_formed (system_union P Q) d t \<longleftrightarrow> schema_call_formed P d t"
    using schema_call_agreement[OF left formed agree member] by blast
  show "(d,t)\<in>positive_meaning (system_union P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    using positive_meaning_dependency_locality[OF left formed agree closed member] by blast
qed

section \<open>Every pair of systems has separated definition coordinates\<close>

definition separated_systems ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'e,'c) schema_system \<Rightarrow>
    ('a,'s,'d+'e,'c) schema_system" where
  "separated_systems P Q=system_union (rename_system Inl P) (rename_system Inr Q)"

lemma separated_systems_definitions [simp]:
  "system_definitions (separated_systems P Q)=
    Inl ` system_definitions P \<union> Inr ` system_definitions Q"
  by (simp add: separated_systems_def renamed_system_definitions)

theorem separated_systems_formed:
  assumes "schema_system_formed P" "schema_system_formed Q"
  shows "schema_system_formed (separated_systems P Q)"
  unfolding separated_systems_def
  by (rule system_union_formed;
      use renamed_system_formed[OF assms(1), of Inl]
        renamed_system_formed[OF assms(2), of Inr] in
        \<open>auto simp: inj_on_def renamed_system_definitions\<close>)

theorem separated_systems_left:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and member: "d\<in>system_definitions P"
  shows "schema_call_formed (separated_systems P Q) (Inl d) t \<longleftrightarrow> schema_call_formed P d t"
    and "(Inl d,t)\<in>positive_meaning (separated_systems P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have li: "inj_on Inl (system_definitions P)" and ri: "inj_on Inr (system_definitions Q)"
    by (auto simp: inj_on_def)
  have lf: "schema_system_formed (rename_system Inl P)" by (rule renamed_system_formed[OF left li])
  have rf: "schema_system_formed (rename_system Inr Q)" by (rule renamed_system_formed[OF right ri])
  have separate: "system_definitions (rename_system Inl P) \<inter>
    system_definitions (rename_system Inr Q)={}"
    by (auto simp: renamed_system_definitions)
  have inside: "Inl d\<in>system_definitions (rename_system Inl P)"
    using member by (simp add: renamed_system_definitions)
  show "schema_call_formed (separated_systems P Q) (Inl d) t \<longleftrightarrow> schema_call_formed P d t"
    using system_union_left_locality(1)[OF lf rf separate inside]
      renamed_system_call[OF left li member, of t] by (simp add: separated_systems_def)
  have meaning: "(Inl d,t)\<in>positive_meaning (rename_system Inl P) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    by (auto simp: renamed_system_positive_meaning[OF left li] map_prod_def)
  show "(Inl d,t)\<in>positive_meaning (separated_systems P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    using system_union_left_locality(2)[OF lf rf separate inside] meaning
    by (simp add: separated_systems_def)
qed

theorem separated_systems_right:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and member: "d\<in>system_definitions Q"
  shows "schema_call_formed (separated_systems P Q) (Inr d) t \<longleftrightarrow> schema_call_formed Q d t"
    and "(Inr d,t)\<in>positive_meaning (separated_systems P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
proof -
  have li: "inj_on Inl (system_definitions P)" and ri: "inj_on Inr (system_definitions Q)"
    by (auto simp: inj_on_def)
  have lf: "schema_system_formed (rename_system Inl P)" by (rule renamed_system_formed[OF left li])
  have rf: "schema_system_formed (rename_system Inr Q)" by (rule renamed_system_formed[OF right ri])
  have separate: "system_definitions (rename_system Inr Q) \<inter>
    system_definitions (rename_system Inl P)={}"
    by (auto simp: renamed_system_definitions)
  have inside: "Inr d\<in>system_definitions (rename_system Inr Q)"
    using member by (simp add: renamed_system_definitions)
  show "schema_call_formed (separated_systems P Q) (Inr d) t \<longleftrightarrow> schema_call_formed Q d t"
    using system_union_left_locality(1)[OF rf lf separate inside]
      renamed_system_call[OF right ri member, of t]
    by (simp add: separated_systems_def system_union_commute)
  have meaning: "(Inr d,t)\<in>positive_meaning (rename_system Inr Q) \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
    by (auto simp: renamed_system_positive_meaning[OF right ri] map_prod_def)
  show "(Inr d,t)\<in>positive_meaning (separated_systems P Q) \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
    using system_union_left_locality(2)[OF rf lf separate inside] meaning
    by (simp add: separated_systems_def system_union_commute)
qed

text \<open>
  Both complete systems retain their interfaces, clause occurrences, recursion,
  and meaning at the corresponding sites. The sum injections only allocate
  disjoint definition coordinates. They do not dispatch truth; every call is
  evaluated by the same positive operator on the combined ordinary clauses.
  Native compilation can subsequently erase these construction coordinates.
  Argument terms and all literal and material operands remain exact.
\<close>

end
