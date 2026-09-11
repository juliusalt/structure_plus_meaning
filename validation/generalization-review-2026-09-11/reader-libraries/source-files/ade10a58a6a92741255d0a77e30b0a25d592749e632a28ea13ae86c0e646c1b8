theory Factor_Interfaces
  imports Factor_Schemas
begin

section \<open>Application boundaries precede meaning\<close>

definition pattern_accepts :: "'a term_pattern \<Rightarrow> factor_term \<Rightarrow> bool" where
  "pattern_accepts p t \<longleftrightarrow> term_formed t \<and>
    (\<exists>V. term_bindings_formed (pattern_variables p) V \<and> pattern_instance V p t)"

lemma variable_accepts [simp]:
  "pattern_accepts (Pattern_Variable a) t \<longleftrightarrow> term_formed t"
proof
  assume "pattern_accepts (Pattern_Variable a) t"
  then show "term_formed t" by (simp add: pattern_accepts_def)
next
  assume formed: "term_formed t"
  have bindings: "term_bindings_formed {a} {(a,t)}"
    using formed by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def)
  show "pattern_accepts (Pattern_Variable a) t"
    using formed bindings by (auto simp: pattern_accepts_def)
qed

lemma pattern_accepts_total:
  assumes formed: "pattern_formed p"
  shows "\<exists>t. pattern_accepts p t"
proof -
  let ?V="image (\<lambda>a. (a,Payload_Term [])) (pattern_variables p)"
  have bindings: "term_bindings_formed (pattern_variables p) ?V"
    by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  have scope: "pattern_variables p\<subseteq>rel_dom ?V" by (auto simp: rel_dom_def)
  obtain t where inst: "pattern_instance ?V p t" using pattern_instance_exists[OF formed scope] by blast
  have tf: "term_formed t" by (rule pattern_instance_formed_term[OF bindings inst])
  show ?thesis using bindings inst tf unfolding pattern_accepts_def by blast
qed

record ('a,'s,'d,'c) schema_system =
  system_interfaces :: "('d \<times> 'a term_pattern) set"
  system_clauses :: "(('d \<times> 'c) \<times> ('a,'s,'d) factor_schema) set"

definition system_definitions :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set" where
  "system_definitions P = rel_dom (system_interfaces P)"

definition schema_system_formed :: "('a,'s,'d,'c) schema_system \<Rightarrow> bool" where
  "schema_system_formed P \<longleftrightarrow>
    finite (system_interfaces P) \<and> single_valued (system_interfaces P) \<and>
    (\<forall>d p. (d,p) \<in> system_interfaces P \<longrightarrow> pattern_formed p) \<and>
    finite (system_clauses P) \<and> single_valued (system_clauses P) \<and>
    (\<forall>d c S. ((d,c),S) \<in> system_clauses P \<longrightarrow>
      d \<in> system_definitions P \<and> schema_formed S \<and>
      schema_dependencies S \<subseteq> system_definitions P)"

definition schema_call_formed :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> factor_term \<Rightarrow> bool" where
  "schema_call_formed P d t \<longleftrightarrow>
    schema_system_formed P \<and> (\<exists>p. (d,p) \<in> system_interfaces P \<and> pattern_accepts p t)"

lemma schema_call_formed_target:
  assumes "schema_call_formed P d t"
  shows "d \<in> system_definitions P \<and> term_formed t"
  using assms by (auto simp: schema_call_formed_def system_definitions_def rel_dom_def pattern_accepts_def)

lemma schema_call_inhabited:
  assumes formed: "schema_system_formed P" and member: "d\<in>system_definitions P"
  shows "\<exists>t. schema_call_formed P d t"
proof -
  obtain p where row: "(d,p)\<in>system_interfaces P"
    using member by (auto simp: system_definitions_def rel_dom_def)
  have pf: "pattern_formed p" using formed row by (auto simp: schema_system_formed_def)
  obtain t where arg: "pattern_accepts p t" using pattern_accepts_total[OF pf] by blast
  show ?thesis using formed row arg unfolding schema_call_formed_def by blast
qed

lemma system_definitions_finite:
  assumes "schema_system_formed P"
  shows "finite (system_definitions P)"
  using assms finite_rel_dom by (auto simp: system_definitions_def schema_system_formed_def)

definition system_dependency_edges :: "('a,'s,'d,'c) schema_system \<Rightarrow> ('d \<times> 'd) set" where
  "system_dependency_edges P =
    {(d,e). \<exists>c S. ((d,c),S) \<in> system_clauses P \<and> e \<in> schema_dependencies S}"

lemma system_dependency_boundary:
  assumes formed: "schema_system_formed P"
  shows "system_dependency_edges P \<subseteq> system_definitions P \<times> system_definitions P"
    and "finite (system_dependency_edges P)"
proof -
  show subset: "system_dependency_edges P \<subseteq> system_definitions P \<times> system_definitions P"
    using formed by (auto simp: system_dependency_edges_def schema_system_formed_def; blast)
  show "finite (system_dependency_edges P)"
    by (rule finite_subset[OF subset]) (simp add: system_definitions_finite[OF formed])
qed

definition admitted_schema_instance ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow>
    factor_term \<Rightarrow> ('s \<times> ('d \<times> factor_term)) set \<Rightarrow> bool" where
  "admitted_schema_instance P d c V t Q \<longleftrightarrow>
    schema_call_formed P d t \<and>
    (\<exists>S. ((d,c),S) \<in> system_clauses P \<and> schema_instance S V t Q \<and> schema_material_satisfied S V) \<and>
    (\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> schema_call_formed P e x)"

definition system_observation_free :: "('a,'s,'d,'c) schema_system \<Rightarrow> bool" where
  "system_observation_free P \<longleftrightarrow>
    (\<forall>d c S. ((d,c),S) \<in> system_clauses P \<longrightarrow> schema_material_premises S = {})"

lemma admitted_instance_formed:
  assumes "admitted_schema_instance P d c V t Q"
  shows "schema_call_formed P d t \<and> finite Q \<and> single_valued Q \<and>
    (\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> schema_call_formed P e x)"
  using assms schema_instance_socket_boundary by (auto simp: admitted_schema_instance_def)

lemma admitted_instance_unique:
  assumes first: "admitted_schema_instance P d c V t Q"
    and second: "admitted_schema_instance P d c V u W"
  shows "t = u \<and> Q = W"
proof -
  obtain S where source: "((d,c),S) \<in> system_clauses P" "schema_instance S V t Q"
    using first unfolding admitted_schema_instance_def by blast
  obtain T where other: "((d,c),T) \<in> system_clauses P" "schema_instance T V u W"
    using second unfolding admitted_schema_instance_def by blast
  have sv: "single_valued (system_clauses P)"
    using first by (simp add: admitted_schema_instance_def schema_call_formed_def schema_system_formed_def)
  have same: "S = T" using sv source(1) other(1) by (auto simp: single_valued_def)
  have inst: "schema_instance S V u W" using other(2) same by simp
  show ?thesis by (rule schema_instance_unique[OF source(2) inst])
qed

lemma admitted_material_premise_holds:
  assumes admitted: "admitted_schema_instance P d c V t Q"
    and clause: "((d,c),S) \<in> system_clauses P"
    and member: "(s,M) \<in> schema_material_premises S"
    and inst: "material_pattern_instance V M x a e b f"
  shows "material_observation x a e b f"
proof -
  obtain T where selected: "((d,c),T) \<in> system_clauses P" "schema_instance T V t Q"
    "schema_material_satisfied T V"
    using admitted by (auto simp: admitted_schema_instance_def)
  have csv: "single_valued (system_clauses P)"
    using admitted by (simp add: admitted_schema_instance_def schema_call_formed_def schema_system_formed_def)
  have same: "T=S" by (rule single_valued_outputs[OF csv selected(1) clause])
  have sv: "single_valued V" using selected(2) by (simp add: schema_instance_def term_bindings_formed_def)
  have checked: "material_pattern_satisfied V M"
    using selected(3) same member by (auto simp: schema_material_satisfied_def)
  show ?thesis using material_pattern_satisfied_at_instance[OF sv inst] checked by blast
qed

end
