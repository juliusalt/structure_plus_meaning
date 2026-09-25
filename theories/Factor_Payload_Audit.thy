theory Factor_Payload_Audit
  imports Factor_Definition_Call_Admission Factor_Finite_Payload_Literals Factor_Use_Renaming
begin

section \<open>The payloads a term carries and an instance adds\<close>

text \<open>
  The payloads a term carries are the payload leaves of its exact pattern. An instance of a pattern
  carries every payload the pattern states, and each other payload it carries comes from a binding.
\<close>

lemma pattern_instance_payloads_included:
  assumes "pattern_instance V p t" "Payload_Term v\<in>pattern_leaves p"
  shows "v\<in>term_payloads t"
  using assms by (induction rule: pattern_instance.induct) auto

lemma pattern_instance_payloads_origin:
  assumes "pattern_instance V p t" "v\<in>term_payloads t"
  shows "Payload_Term v\<in>pattern_leaves p \<or> (\<exists>a x. (a,x)\<in>V \<and> v\<in>term_payloads x)"
  using assms by (induction rule: pattern_instance.induct) auto

definition schema_payloads :: "('a,'s,'d) factor_schema \<Rightarrow> octets set" where
  "schema_payloads S={v. Payload_Term v\<in>schema_leaves S}"

definition definition_payloads :: "'a term_pattern \<Rightarrow> ('c\<times>('a,'s,'d) factor_schema) set \<Rightarrow> octets set" where
  "definition_payloads p C={v. Payload_Term v\<in>pattern_leaves p} \<union> (\<Union>(c,S)\<in>C. schema_payloads S)"

lemma schema_instance_payloads_included:
  assumes inst: "schema_instance S V t Q" and member: "v\<in>schema_payloads S"
  shows "v\<in>term_payloads t \<or> (\<exists>s d x. (s,d,x)\<in>Q \<and> v\<in>term_payloads x) \<or>
    (\<exists>s x. (s,x)\<in>material_instance_relation V (schema_material_premises S) \<and> v\<in>term_payloads x)"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have leaf: "Payload_Term v\<in>schema_leaves S" using member by (simp add: schema_payloads_def)
  then consider (conclusion) "Payload_Term v\<in>pattern_leaves (schema_conclusion S)"
    | (premise) s d p where "(s,d,p)\<in>schema_premises S" "Payload_Term v\<in>pattern_leaves p"
    | (material) s M where "(s,M)\<in>schema_material_premises S" "Payload_Term v\<in>material_leaves M"
    by (auto simp: schema_leaves_def)
  then show ?thesis
  proof cases
    case conclusion
    then show ?thesis using pattern_instance_payloads_included[OF head] by blast
  next
    case premise
    obtain x where "(s,d,x)\<in>Q" "pattern_instance V p x"
      using body premise(1) unfolding schema_premise_instance_def by blast
    then show ?thesis using pattern_instance_payloads_included premise(2) by blast
  next
    case material
    have mf: "material_pattern_formed M" using sf material(1) by (auto simp: schema_formed_def)
    have scope: "material_variables M\<subseteq>rel_dom V"
      using bindings material(1) by (auto simp: term_bindings_formed_def schema_variables_def)
    obtain x a e b f where matched: "material_pattern_instance V M x a e b f"
      using material_pattern_instance_exists[OF mf scope] by blast
    have row: "(s,material_tuple x a e b f)\<in>material_instance_relation V (schema_material_premises S)"
      unfolding material_instance_relation_def using material(1) matched by blast
    have "v\<in>term_payloads (material_tuple x a e b f)"
      using material(2) matched
      by (auto simp: material_leaves_def material_fields_def material_pattern_instance_def material_tuple_def
        dest: pattern_instance_payloads_included)
    then show ?thesis using row by blast
  qed
qed

lemma schema_instance_payloads_blank:
  assumes inst: "schema_instance S V t Q" and blank: "\<forall>a x. (a,x)\<in>V \<longrightarrow> x=Payload_Term []"
  shows "term_payloads t\<subseteq>insert [] (schema_payloads S)"
    and "\<forall>s d x. (s,d,x)\<in>Q \<longrightarrow> term_payloads x\<subseteq>insert [] (schema_payloads S)"
    and "\<forall>s x. (s,x)\<in>material_instance_relation V (schema_material_premises S) \<longrightarrow>
      term_payloads x\<subseteq>insert [] (schema_payloads S)"
proof -
  have head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have leaves: "\<And>p x. pattern_instance V p x \<Longrightarrow> Payload_Term`term_payloads x\<subseteq>pattern_leaves p \<union> {Payload_Term []}"
    using pattern_instance_payloads_origin blank by fastforce
  show "term_payloads t\<subseteq>insert [] (schema_payloads S)"
    using leaves[OF head] by (auto simp: schema_payloads_def schema_leaves_def)
  show "\<forall>s d x. (s,d,x)\<in>Q \<longrightarrow> term_payloads x\<subseteq>insert [] (schema_payloads S)"
  proof (intro allI impI)
    fix s d x assume "(s,d,x)\<in>Q"
    then obtain p where "(s,d,p)\<in>schema_premises S" "pattern_instance V p x"
      using schema_premise_instance_origin[OF body] by blast
    then show "term_payloads x\<subseteq>insert [] (schema_payloads S)"
      using leaves by (fastforce simp: schema_payloads_def schema_leaves_def)
  qed
  show "\<forall>s x. (s,x)\<in>material_instance_relation V (schema_material_premises S) \<longrightarrow>
      term_payloads x\<subseteq>insert [] (schema_payloads S)"
  proof (intro allI impI)
    fix s x assume "(s,x)\<in>material_instance_relation V (schema_material_premises S)"
    then obtain M y a e b f where row: "(s,M)\<in>schema_material_premises S"
      "material_pattern_instance V M y a e b f" "x=material_tuple y a e b f"
      by (auto simp: material_instance_relation_def)
    have "Payload_Term`term_payloads x\<subseteq>material_leaves M \<union> {Payload_Term []}"
      using row(2,3) leaves
      by (auto simp: material_pattern_instance_def material_tuple_def material_leaves_def material_fields_def; blast)
    then show "term_payloads x\<subseteq>insert [] (schema_payloads S)"
      using row(1) by (fastforce simp: schema_payloads_def schema_leaves_def)
  qed
qed

section \<open>Ordinary clauses over their valuations\<close>

lemma audit_layer_clause:
  assumes formed: "schema_system_formed P" and fresh: "d\<notin>system_definitions P"
  shows "((d,c),S)\<in>system_clauses (add_view_definition P d p C) \<longleftrightarrow> (c,S)\<in>C"
proof -
  have "((d,c),S)\<notin>system_clauses P" using formed fresh unfolding schema_system_formed_def by blast
  then show ?thesis by (auto simp: add_view_definition_def)
qed

lemma audit_target_meaning:
  "(45,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (45,t)\<in>positive_meaning target_projection_system"
  using definition_call_admission_instantiation_meaning[of 45 t] schema_instantiation_pattern_meaning[of 45 t]
    pattern_instantiation_quotation_meaning[of 45 t] quotation_admission_components[of t] by simp

section \<open>Every payload a term carries is the empty payload\<close>

text \<open>
  A term passes when it is the empty payload, a target, or a pair of passing terms. A target is
  recognized by the existing target projection, which reads it through its material; no octet of the
  term other than the empty payload is compared.
\<close>


definition empty_payloads_target_schema :: "(nat,nat,nat) factor_schema" where
  "empty_payloads_target_schema=data_rule data_x {(0,45,Pattern_Pair data_x data_y)}"

definition empty_payloads_pair_schema :: "(nat,nat,nat) factor_schema" where
  "empty_payloads_pair_schema=data_rule (Pattern_Pair data_x data_y) {(0,500,data_x),(1,500,data_y)}"

definition empty_payloads_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "empty_payloads_clauses={(0,data_list_nil_schema),(1,empty_payloads_target_schema),(2,empty_payloads_pair_schema)}"

definition empty_payloads_system :: "(nat,nat,nat,nat) schema_system" where
  "empty_payloads_system=add_view_definition definition_call_admission_system 500 data_x empty_payloads_clauses"

lemmas empty_payloads_schema_defs=data_list_nil_schema_def empty_payloads_target_schema_def
  empty_payloads_pair_schema_def

lemma empty_payloads_system_formed [simp]: "schema_system_formed empty_payloads_system"
  unfolding empty_payloads_system_def
  by (rule add_recursive_definition_formed[OF definition_call_admission_system_formed])
    (auto simp: empty_payloads_clauses_def empty_payloads_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma empty_payloads_definitions [simp]:
  "system_definitions empty_payloads_system=insert 500 (system_definitions definition_call_admission_system)"
  by (simp add: empty_payloads_system_def)

lemma empty_payloads_call:
  "schema_call_formed empty_payloads_system d t \<longleftrightarrow> d\<in>system_definitions empty_payloads_system \<and> term_formed t"
  using added_variable_calls[OF definition_call_admission_system_formed
    empty_payloads_system_formed[unfolded empty_payloads_system_def] definition_call_admission_call]
  by (simp only: empty_payloads_system_def[symmetric])

lemma empty_payloads_old_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning empty_payloads_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_call_admission_system"
  using added_definition_preserves_old(2)[OF definition_call_admission_system_formed
    empty_payloads_system_formed[unfolded empty_payloads_system_def] _ assms]
  by (simp add: empty_payloads_system_def)

lemma empty_payloads_clause [simp]:
  "((500,c),S)\<in>system_clauses empty_payloads_system \<longleftrightarrow> (c,S)\<in>empty_payloads_clauses"
  unfolding empty_payloads_system_def by (rule audit_layer_clause) simp_all

lemma empty_payloads_target:
  "(45,t)\<in>positive_meaning empty_payloads_system \<longleftrightarrow> (45,t)\<in>positive_meaning target_projection_system"
  using empty_payloads_old_meaning[of 45 t] audit_target_meaning[of t] by simp

lemma empty_payloads_cases:
  assumes holds: "(500,t)\<in>positive_meaning empty_payloads_system"
  shows "t=Payload_Term [] \<or> (\<exists>x. t=Target_Term x) \<or>
    (\<exists>x y. t=Pair_Term x y \<and> (500,x)\<in>positive_meaning empty_payloads_system \<and>
      (500,y)\<in>positive_meaning empty_payloads_system)"
proof -
  obtain c S h where clause: "((500,c),S)\<in>system_clauses empty_payloads_system"
    and conclusion: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning empty_payloads_system"
    using positive_meaning_valuationE[OF holds] by blast
  have "(c,S)\<in>empty_payloads_clauses" using clause by simp
  then consider "S=data_list_nil_schema" | "S=empty_payloads_target_schema" | "S=empty_payloads_pair_schema"
    by (auto simp: empty_payloads_clauses_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using conclusion by (simp add: data_list_nil_schema_def)
  next
    case 2
    have "(45,Pair_Term (h 0) (h 1))\<in>positive_meaning target_projection_system"
      using support 2 by (auto simp: empty_payloads_target_schema_def empty_payloads_target)
    then show ?thesis using conclusion 2 by (auto simp: target_projection_exact empty_payloads_target_schema_def)
  next
    case 3
    then show ?thesis using conclusion support by (auto simp: empty_payloads_pair_schema_def)
  qed
qed

lemma empty_payloads_sound:
  assumes "(500,t)\<in>positive_meaning empty_payloads_system"
  shows "term_payloads t\<subseteq>{[]}"
  using assms
proof (induction t)
  case (Target_Term x)
  then show ?case by simp
next
  case (Payload_Term v)
  then show ?case using empty_payloads_cases[OF Payload_Term.prems] by auto
next
  case (Pair_Term x y)
  have "(500,x)\<in>positive_meaning empty_payloads_system" "(500,y)\<in>positive_meaning empty_payloads_system"
    using empty_payloads_cases[OF Pair_Term.prems] by auto
  then show ?case using Pair_Term.IH by auto
qed

lemma empty_payloads_complete:
  assumes "term_formed t" "term_payloads t\<subseteq>{[]}"
  shows "(500,t)\<in>positive_meaning empty_payloads_system"
  using assms
proof (induction t)
  case (Target_Term x)
  have tf: "target_formed x" using Target_Term.prems by simp
  obtain a where presented: "target_value_presents x a" using target_value_presents_total[OF tf] by blast
  have af: "term_formed a" using target_value_presents_formed[OF presented] by blast
  have support: "(45,Pair_Term (Target_Term x) a)\<in>positive_meaning empty_payloads_system"
    by (simp only: empty_payloads_target target_projection_exact) (use presented in blast)
  let ?h="\<lambda>n::nat. if n=0 then Target_Term x else a"
  have "(500,evaluate_pattern ?h (schema_conclusion empty_payloads_target_schema))\<in>positive_meaning empty_payloads_system"
    by (rule ordinary_positive_formed_step[where c=1])
      (use Target_Term.prems af support in \<open>auto simp: empty_payloads_clauses_def empty_payloads_schema_defs
        schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payloads_call\<close>)
  then show ?case by (simp add: empty_payloads_target_schema_def)
next
  case (Payload_Term v)
  have empty: "v=[]" using Payload_Term.prems by simp
  have "(500,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion (data_list_nil_schema::(nat,nat,nat) factor_schema)))
      \<in>positive_meaning empty_payloads_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (auto simp: empty_payloads_clauses_def empty_payloads_schema_defs schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def empty_payloads_call)
  then show ?case using empty by (simp add: data_list_nil_schema_def)
next
  case (Pair_Term x y)
  have children: "(500,x)\<in>positive_meaning empty_payloads_system" "(500,y)\<in>positive_meaning empty_payloads_system"
    using Pair_Term.IH Pair_Term.prems by auto
  let ?h="\<lambda>n::nat. if n=0 then x else y"
  have "(500,evaluate_pattern ?h (schema_conclusion empty_payloads_pair_schema))\<in>positive_meaning empty_payloads_system"
    by (rule ordinary_positive_formed_step[where c=2])
      (use Pair_Term.prems children in \<open>auto simp: empty_payloads_clauses_def empty_payloads_schema_defs
        schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payloads_call\<close>)
  then show ?case by (simp add: empty_payloads_pair_schema_def)
qed

theorem empty_payloads_exact:
  "(500,t)\<in>positive_meaning empty_payloads_system \<longleftrightarrow> term_formed t \<and> term_payloads t\<subseteq>{[]}"
proof
  assume holds: "(500,t)\<in>positive_meaning empty_payloads_system"
  have "term_formed t" using positive_meaning_formed[OF holds] by (simp add: empty_payloads_call)
  then show "term_formed t \<and> term_payloads t\<subseteq>{[]}" using empty_payloads_sound[OF holds] by blast
next
  assume "term_formed t \<and> term_payloads t\<subseteq>{[]}"
  then show "(500,t)\<in>positive_meaning empty_payloads_system" using empty_payloads_complete by blast
qed

section \<open>Keyed rows whose values carry only the empty payload\<close>

text \<open>
  A material row keeps its socket beside its operand tuple; a call row keeps its socket and callee
  site beside its argument. The keys and sites are coordinates of the schema, not what it states,
  so only the row's value, or the call's argument, is audited.
\<close>

definition empty_payload_rows_schema :: "(nat,nat,nat) factor_schema" where
  "empty_payload_rows_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,500,data_y),(1,501,data_z)}"

definition empty_payload_rows_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "empty_payload_rows_clauses={(0,data_list_nil_schema),(1,empty_payload_rows_schema)}"

definition empty_payload_rows_system :: "(nat,nat,nat,nat) schema_system" where
  "empty_payload_rows_system=add_view_definition empty_payloads_system 501 data_x empty_payload_rows_clauses"

lemma empty_payload_rows_system_formed [simp]: "schema_system_formed empty_payload_rows_system"
  unfolding empty_payload_rows_system_def
  by (rule add_recursive_definition_formed[OF empty_payloads_system_formed])
    (auto simp: empty_payload_rows_clauses_def data_list_nil_schema_def empty_payload_rows_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma empty_payload_rows_definitions [simp]:
  "system_definitions empty_payload_rows_system=insert 501 (system_definitions empty_payloads_system)"
  by (simp add: empty_payload_rows_system_def)

lemma empty_payload_rows_call:
  "schema_call_formed empty_payload_rows_system d t \<longleftrightarrow> d\<in>system_definitions empty_payload_rows_system \<and> term_formed t"
  using added_variable_calls[OF empty_payloads_system_formed
    empty_payload_rows_system_formed[unfolded empty_payload_rows_system_def] empty_payloads_call]
  by (simp only: empty_payload_rows_system_def[symmetric])

lemma empty_payload_rows_old_meaning:
  assumes "d\<in>system_definitions empty_payloads_system"
  shows "(d,t)\<in>positive_meaning empty_payload_rows_system \<longleftrightarrow> (d,t)\<in>positive_meaning empty_payloads_system"
  using added_definition_preserves_old(2)[OF empty_payloads_system_formed
    empty_payload_rows_system_formed[unfolded empty_payload_rows_system_def] _ assms]
  by (simp add: empty_payload_rows_system_def)

lemma empty_payload_rows_clause [simp]:
  "((501,c),S)\<in>system_clauses empty_payload_rows_system \<longleftrightarrow> (c,S)\<in>empty_payload_rows_clauses"
  unfolding empty_payload_rows_system_def by (rule audit_layer_clause) simp_all

lemma empty_payload_rows_empty:
  "(500,t)\<in>positive_meaning empty_payload_rows_system \<longleftrightarrow> (500,t)\<in>positive_meaning empty_payloads_system"
  by (rule empty_payload_rows_old_meaning) simp

lemma empty_payload_rows_cases:
  assumes holds: "(501,t)\<in>positive_meaning empty_payload_rows_system"
  shows "t=Payload_Term [] \<or> (\<exists>k x r. t=Pair_Term (Pair_Term k x) r \<and>
    (500,x)\<in>positive_meaning empty_payloads_system \<and> (501,r)\<in>positive_meaning empty_payload_rows_system)"
proof -
  obtain c S h where clause: "((501,c),S)\<in>system_clauses empty_payload_rows_system"
    and conclusion: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning empty_payload_rows_system"
    using positive_meaning_valuationE[OF holds] by blast
  have "(c,S)\<in>empty_payload_rows_clauses" using clause by simp
  then consider "S=data_list_nil_schema" | "S=empty_payload_rows_schema"
    by (auto simp: empty_payload_rows_clauses_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using conclusion by (simp add: data_list_nil_schema_def)
  next
    case 2
    then show ?thesis using conclusion support by (auto simp: empty_payload_rows_schema_def empty_payload_rows_empty)
  qed
qed

theorem empty_payload_rows_bindings:
  "(501,binding_rows_term cs)\<in>positive_meaning empty_payload_rows_system \<longleftrightarrow>
    term_formed (binding_rows_term cs) \<and> (\<forall>(a,x)\<in>set cs. term_payloads x\<subseteq>{[]})"
proof (induction cs)
  case Nil
  have "(501,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion (data_list_nil_schema::(nat,nat,nat) factor_schema)))
      \<in>positive_meaning empty_payload_rows_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (auto simp: empty_payload_rows_clauses_def data_list_nil_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def empty_payload_rows_call)
  then show ?case by (simp add: data_list_nil_schema_def octets_formed_def)
next
  case (Cons c cs)
  obtain a x where c: "c=(a,x)" by (cases c)
  show ?case
  proof
    assume holds: "(501,binding_rows_term (c#cs))\<in>positive_meaning empty_payload_rows_system"
    have formed: "term_formed (binding_rows_term (c#cs))"
      using positive_meaning_formed[OF holds] by (simp add: empty_payload_rows_call)
    have "(500,x)\<in>positive_meaning empty_payloads_system" "(501,binding_rows_term cs)\<in>positive_meaning empty_payload_rows_system"
      using empty_payload_rows_cases[OF holds] by (auto simp: c)
    then show "term_formed (binding_rows_term (c#cs)) \<and> (\<forall>(a,x)\<in>set (c#cs). term_payloads x\<subseteq>{[]})"
      using formed Cons.IH empty_payloads_exact by (auto simp: c)
  next
    assume given: "term_formed (binding_rows_term (c#cs)) \<and> (\<forall>(a,x)\<in>set (c#cs). term_payloads x\<subseteq>{[]})"
    then have parts: "octets_formed a" "term_formed x" "term_formed (binding_rows_term cs)" "term_payloads x\<subseteq>{[]}"
      "\<forall>(a,x)\<in>set cs. term_payloads x\<subseteq>{[]}" by (auto simp: c)
    let ?h="\<lambda>n::nat. if n=0 then Payload_Term a else if n=1 then x else binding_rows_term cs"
    have "(501,evaluate_pattern ?h (schema_conclusion empty_payload_rows_schema))\<in>positive_meaning empty_payload_rows_system"
      by (rule ordinary_positive_formed_step[where c=1])
        (use parts Cons.IH in \<open>auto simp: empty_payload_rows_clauses_def empty_payload_rows_schema_def
          schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payload_rows_call
          empty_payload_rows_empty empty_payloads_exact\<close>)
    then show "(501,binding_rows_term (c#cs))\<in>positive_meaning empty_payload_rows_system"
      by (simp add: c empty_payload_rows_schema_def)
  qed
qed

definition empty_payload_calls_schema :: "(nat,nat,nat) factor_schema" where
  "empty_payload_calls_schema=data_rule (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) data_w)
    {(0,500,data_z),(1,502,data_w)}"

definition empty_payload_calls_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "empty_payload_calls_clauses={(0,data_list_nil_schema),(1,empty_payload_calls_schema)}"

definition empty_payload_calls_system :: "(nat,nat,nat,nat) schema_system" where
  "empty_payload_calls_system=add_view_definition empty_payload_rows_system 502 data_x empty_payload_calls_clauses"

lemma empty_payload_calls_system_formed [simp]: "schema_system_formed empty_payload_calls_system"
  unfolding empty_payload_calls_system_def
  by (rule add_recursive_definition_formed[OF empty_payload_rows_system_formed])
    (auto simp: empty_payload_calls_clauses_def data_list_nil_schema_def empty_payload_calls_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma empty_payload_calls_definitions [simp]:
  "system_definitions empty_payload_calls_system=insert 502 (system_definitions empty_payload_rows_system)"
  by (simp add: empty_payload_calls_system_def)

lemma empty_payload_calls_call:
  "schema_call_formed empty_payload_calls_system d t \<longleftrightarrow> d\<in>system_definitions empty_payload_calls_system \<and> term_formed t"
  using added_variable_calls[OF empty_payload_rows_system_formed
    empty_payload_calls_system_formed[unfolded empty_payload_calls_system_def] empty_payload_rows_call]
  by (simp only: empty_payload_calls_system_def[symmetric])

lemma empty_payload_calls_old_meaning:
  assumes "d\<in>system_definitions empty_payload_rows_system"
  shows "(d,t)\<in>positive_meaning empty_payload_calls_system \<longleftrightarrow> (d,t)\<in>positive_meaning empty_payload_rows_system"
  using added_definition_preserves_old(2)[OF empty_payload_rows_system_formed
    empty_payload_calls_system_formed[unfolded empty_payload_calls_system_def] _ assms]
  by (simp add: empty_payload_calls_system_def)

lemma empty_payload_calls_clause [simp]:
  "((502,c),S)\<in>system_clauses empty_payload_calls_system \<longleftrightarrow> (c,S)\<in>empty_payload_calls_clauses"
  unfolding empty_payload_calls_system_def by (rule audit_layer_clause) simp_all

lemma empty_payload_calls_empty:
  "(500,t)\<in>positive_meaning empty_payload_calls_system \<longleftrightarrow> (500,t)\<in>positive_meaning empty_payloads_system"
  using empty_payload_calls_old_meaning[of 500 t] empty_payload_rows_empty[of t] by simp

lemma empty_payload_calls_cases:
  assumes holds: "(502,t)\<in>positive_meaning empty_payload_calls_system"
  shows "t=Payload_Term [] \<or> (\<exists>k d x r. t=Pair_Term (Pair_Term k (Pair_Term d x)) r \<and>
    (500,x)\<in>positive_meaning empty_payloads_system \<and> (502,r)\<in>positive_meaning empty_payload_calls_system)"
proof -
  obtain c S h where clause: "((502,c),S)\<in>system_clauses empty_payload_calls_system"
    and conclusion: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning empty_payload_calls_system"
    using positive_meaning_valuationE[OF holds] by blast
  have "(c,S)\<in>empty_payload_calls_clauses" using clause by simp
  then consider "S=data_list_nil_schema" | "S=empty_payload_calls_schema"
    by (auto simp: empty_payload_calls_clauses_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using conclusion by (simp add: data_list_nil_schema_def)
  next
    case 2
    then show ?thesis using conclusion support by (auto simp: empty_payload_calls_schema_def empty_payload_calls_empty)
  qed
qed

theorem empty_payload_calls_rows:
  "(502,call_instance_rows_term qs)\<in>positive_meaning empty_payload_calls_system \<longleftrightarrow>
    term_formed (call_instance_rows_term qs) \<and> (\<forall>(s,d,x)\<in>set qs. term_payloads x\<subseteq>{[]})"
proof (induction qs)
  case Nil
  have "(502,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion (data_list_nil_schema::(nat,nat,nat) factor_schema)))
      \<in>positive_meaning empty_payload_calls_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (auto simp: empty_payload_calls_clauses_def data_list_nil_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def empty_payload_calls_call)
  then show ?case by (simp add: data_list_nil_schema_def octets_formed_def)
next
  case (Cons q qs)
  obtain s d x where q: "q=(s,d,x)" by (cases q) auto
  show ?case
  proof
    assume holds: "(502,call_instance_rows_term (q#qs))\<in>positive_meaning empty_payload_calls_system"
    have formed: "term_formed (call_instance_rows_term (q#qs))"
      using positive_meaning_formed[OF holds] by (simp add: empty_payload_calls_call)
    have "(500,x)\<in>positive_meaning empty_payloads_system"
      "(502,call_instance_rows_term qs)\<in>positive_meaning empty_payload_calls_system"
      using empty_payload_calls_cases[OF holds] by (auto simp: q call_instance_value_def)
    then show "term_formed (call_instance_rows_term (q#qs)) \<and> (\<forall>(s,d,x)\<in>set (q#qs). term_payloads x\<subseteq>{[]})"
      using formed Cons.IH empty_payloads_exact by (auto simp: q)
  next
    assume given: "term_formed (call_instance_rows_term (q#qs)) \<and> (\<forall>(s,d,x)\<in>set (q#qs). term_payloads x\<subseteq>{[]})"
    then have parts: "octets_formed s" "term_formed (site_data_term (fst d) (snd d))" "term_formed x"
      "term_formed (call_instance_rows_term qs)" "term_payloads x\<subseteq>{[]}"
      "\<forall>(s,d,x)\<in>set qs. term_payloads x\<subseteq>{[]}" by (auto simp: q call_instance_value_def)
    let ?h="\<lambda>n::nat. if n=0 then Payload_Term s else if n=1 then site_data_term (fst d) (snd d)
      else if n=2 then x else call_instance_rows_term qs"
    have "(502,evaluate_pattern ?h (schema_conclusion empty_payload_calls_schema))\<in>positive_meaning empty_payload_calls_system"
      by (rule ordinary_positive_formed_step[where c=1])
        (use parts Cons.IH in \<open>auto simp: empty_payload_calls_clauses_def empty_payload_calls_schema_def
          schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payload_calls_call
          empty_payload_calls_empty empty_payloads_exact\<close>)
    then show "(502,call_instance_rows_term (q#qs))\<in>positive_meaning empty_payload_calls_system"
      by (simp add: q empty_payload_calls_schema_def call_instance_value_def)
  qed
qed

section \<open>One clause states only the empty payload\<close>

text \<open>
  A clause at a schema root is instantiated with a hidden complete binding table. Its conclusion, every
  prospective call's argument and every material operand then carry every payload the schema states,
  and a table binding each variable to the empty payload adds none: a clause passes exactly when the
  schema states no payload but the empty one.
\<close>

definition clause_payloads_schema :: "(nat,nat,nat) factor_schema" where
  "clause_payloads_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,65,schema_instantiation_pattern data_x data_y data_z data_w
      (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)),
     (1,500,Pattern_Variable 4),(2,502,Pattern_Variable 5),(3,501,Pattern_Variable 6)}"

definition clause_payloads_system :: "(nat,nat,nat,nat) schema_system" where
  "clause_payloads_system=add_view_definition empty_payload_calls_system 503 data_x {(0,clause_payloads_schema)}"

lemma clause_payloads_system_formed [simp]: "schema_system_formed clause_payloads_system"
  unfolding clause_payloads_system_def
  by (rule add_recursive_definition_formed[OF empty_payload_calls_system_formed])
    (auto simp: clause_payloads_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma clause_payloads_definitions [simp]:
  "system_definitions clause_payloads_system=insert 503 (system_definitions empty_payload_calls_system)"
  by (simp add: clause_payloads_system_def)

lemma clause_payloads_call:
  "schema_call_formed clause_payloads_system d t \<longleftrightarrow> d\<in>system_definitions clause_payloads_system \<and> term_formed t"
  using added_variable_calls[OF empty_payload_calls_system_formed
    clause_payloads_system_formed[unfolded clause_payloads_system_def] empty_payload_calls_call]
  by (simp only: clause_payloads_system_def[symmetric])

lemma clause_payloads_old_meaning:
  assumes "d\<in>system_definitions empty_payload_calls_system"
  shows "(d,t)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (d,t)\<in>positive_meaning empty_payload_calls_system"
  using added_definition_preserves_old(2)[OF empty_payload_calls_system_formed
    clause_payloads_system_formed[unfolded clause_payloads_system_def] _ assms]
  by (simp add: clause_payloads_system_def)

lemma clause_payloads_clause [simp]:
  "((503,c),S)\<in>system_clauses clause_payloads_system \<longleftrightarrow> c=0 \<and> S=clause_payloads_schema"
  unfolding clause_payloads_system_def by (subst audit_layer_clause) simp_all

lemma clause_payloads_components:
  "(65,t)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (65,t)\<in>positive_meaning schema_instantiation_system"
  "(500,t)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (500,t)\<in>positive_meaning empty_payloads_system"
  "(501,t)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (501,t)\<in>positive_meaning empty_payload_rows_system"
  "(502,t)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (502,t)\<in>positive_meaning empty_payload_calls_system"
  using clause_payloads_old_meaning[of 65 t] empty_payload_calls_old_meaning[of 65 t]
    empty_payload_rows_old_meaning[of 65 t] empty_payloads_old_meaning[of 65 t]
    definition_call_admission_instantiation_meaning[of 65 t]
    clause_payloads_old_meaning[of 500 t] empty_payload_calls_empty[of t]
    clause_payloads_old_meaning[of 501 t] empty_payload_calls_old_meaning[of 501 t]
    clause_payloads_old_meaning[of 502 t] by simp_all

lemma clause_payloads_rule:
  "(503,z)\<in>positive_meaning clause_payloads_system \<longleftrightarrow> (\<exists>h. (\<forall>a\<in>schema_variables clause_payloads_schema. term_formed (h a)) \<and>
    z=evaluate_pattern h (schema_conclusion clause_payloads_schema) \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises clause_payloads_schema \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning clause_payloads_system))"
  by (rule variable_single_clause_valuation[OF clause_payloads_system_formed clause_payloads_clause]) (simp_all add: clause_payloads_schema_def clause_payloads_call)

lemma clause_payloads_sound:
  assumes source: "environment_value_presents E e"
    and holds: "(503,Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a))\<in>positive_meaning clause_payloads_system"
  shows "\<exists>S. native_schema_at E u a S \<and> schema_payloads S\<subseteq>{[]}"
proof -
  define S where "S=clause_payloads_schema"
  have schema: "S=clause_payloads_schema" by (rule S_def)
  obtain h where conclusion: "Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning clause_payloads_system"
    using holds unfolding schema clause_payloads_rule by blast
  have fields: "h 0=e" "h 1=use_data_term u" "h 2=Payload_Term a"
    using conclusion by (simp_all add: schema clause_payloads_schema_def)
  have calls: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a) (h 3) (h 4) (h 5) (h 6))
      \<in>positive_meaning schema_instantiation_system"
    "(500,h 4)\<in>positive_meaning empty_payloads_system"
    "(502,h 5)\<in>positive_meaning empty_payload_calls_system"
    "(501,h 6)\<in>positive_meaning empty_payload_rows_system"
    using support fields by (auto simp: schema clause_payloads_schema_def clause_payloads_components)
  obtain v l xs T qs cs where read: "use_data_term u=use_data_term v" "Payload_Term a=Payload_Term l"
    "h 3=binding_rows_term xs" "h 5=call_instance_rows_term qs" "h 6=binding_rows_term cs"
    "native_schema_at E v l T" "schema_instance T (set xs) (h 4) (set qs)"
    "set cs=material_instance_relation (set xs) (schema_material_premises T)"
    using calls(1) by (simp only: schema_instantiation_at_source[OF source]) blast
  have same: "v=u" "l=a" using read(1,2) injD[OF use_data_term_injective] by auto
  have head: "term_payloads (h 4)\<subseteq>{[]}" using calls(2) empty_payloads_exact by blast
  have arguments_empty: "\<forall>(s,d,x)\<in>set qs. term_payloads x\<subseteq>{[]}"
    using calls(3) empty_payload_calls_rows read(4) by simp
  have materials: "\<forall>(s,x)\<in>set cs. term_payloads x\<subseteq>{[]}"
    using calls(4) empty_payload_rows_bindings read(5) by simp
  have "schema_payloads T\<subseteq>{[]}"
  proof
    fix w assume "w\<in>schema_payloads T"
    from schema_instance_payloads_included[OF read(7) this] show "w\<in>{[]}"
      using head arguments_empty materials read(8) by fastforce
  qed
  then show ?thesis using read(6) same by blast
qed

lemma clause_payloads_complete:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u a S"
    and payloads: "schema_payloads S\<subseteq>{[]}"
  shows "(503,Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a))\<in>positive_meaning clause_payloads_system"
proof -
  have sf: "schema_formed S" by (rule native_schema_formed[OF raw])
  let ?V="(\<lambda>b. (b,Payload_Term [])) ` schema_variables S"
  have vf: "finite ?V" using schema_variables_finite[OF sf] by simp
  obtain xs where xs: "set xs=?V" "distinct xs" using finite_distinct_list[OF vf] by blast
  have bindings: "term_bindings_formed (schema_variables S) (set xs)"
    using schema_variables_finite[OF sf]
    by (auto simp: xs(1) term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  obtain t qs cs where holds: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a)
      (binding_rows_term xs) t (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw bindings xs(2)] by blast
  have inst: "schema_instance S (set xs) t (set qs)"
    and materials: "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using holds schema_instantiation_at_schema[OF source raw] by blast+
  have blank: "\<forall>b x. (b,x)\<in>set xs \<longrightarrow> x=Payload_Term []" using xs(1) by auto
  have formed: "term_formed (schema_instantiation_argument e (use_data_term u) (Payload_Term a)
      (binding_rows_term xs) t (call_instance_rows_term qs) (binding_rows_term cs))"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by blast
  have outs: "term_payloads t\<subseteq>{[]}" "\<forall>(s,d,x)\<in>set qs. term_payloads x\<subseteq>{[]}"
    "\<forall>(s,x)\<in>set cs. term_payloads x\<subseteq>{[]}"
    using schema_instance_payloads_blank[OF inst blank] payloads materials by fastforce+
  have head: "(500,t)\<in>positive_meaning empty_payloads_system"
    using formed outs(1) empty_payloads_exact by simp
  have arguments_empty: "(502,call_instance_rows_term qs)\<in>positive_meaning empty_payload_calls_system"
    using formed outs(2) empty_payload_calls_rows by simp
  have rows: "(501,binding_rows_term cs)\<in>positive_meaning empty_payload_rows_system"
    using formed outs(3) empty_payload_rows_bindings by simp
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then use_data_term u else if n=2 then Payload_Term a
    else if n=3 then binding_rows_term xs else if n=4 then t else if n=5 then call_instance_rows_term qs
    else binding_rows_term cs"
  have "(503,evaluate_pattern ?h (schema_conclusion clause_payloads_schema))\<in>positive_meaning clause_payloads_system"
    unfolding clause_payloads_rule by (rule exI[of _ ?h])
      (use formed holds head arguments_empty rows in \<open>auto simp: clause_payloads_schema_def schema_formed_def
        schema_variables_def single_valued_def rel_dom_def clause_payloads_call clause_payloads_components\<close>)
  then show ?thesis by (simp add: clause_payloads_schema_def)
qed

theorem clause_payloads_on_values:
  assumes source: "environment_value_presents E e"
  shows "(503,Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a))\<in>positive_meaning clause_payloads_system
    \<longleftrightarrow> (\<exists>S. native_schema_at E u a S \<and> schema_payloads S\<subseteq>{[]})"
  using clause_payloads_sound[OF source] clause_payloads_complete[OF source] by blast

section \<open>Every clause of a family\<close>

definition clause_family_payloads_system :: "(nat,nat,nat,nat) schema_system" where
  "clause_family_payloads_system=add_view_definition clause_payloads_system 504 data_x (context_list_clauses 503 504)"

lemma clause_family_payloads_system_formed [simp]: "schema_system_formed clause_family_payloads_system"
  unfolding clause_family_payloads_system_def
  by (rule add_recursive_definition_formed[OF clause_payloads_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma clause_family_payloads_definitions [simp]:
  "system_definitions clause_family_payloads_system=insert 504 (system_definitions clause_payloads_system)"
  by (simp add: clause_family_payloads_system_def)

lemma clause_family_payloads_call:
  "schema_call_formed clause_family_payloads_system d t \<longleftrightarrow>
    d\<in>system_definitions clause_family_payloads_system \<and> term_formed t"
  using added_variable_calls[OF clause_payloads_system_formed
    clause_family_payloads_system_formed[unfolded clause_family_payloads_system_def] clause_payloads_call]
  by (simp only: clause_family_payloads_system_def[symmetric])

lemma clause_family_payloads_old_meaning:
  assumes "d\<in>system_definitions clause_payloads_system"
  shows "(d,t)\<in>positive_meaning clause_family_payloads_system \<longleftrightarrow> (d,t)\<in>positive_meaning clause_payloads_system"
  using added_definition_preserves_old(2)[OF clause_payloads_system_formed
    clause_family_payloads_system_formed[unfolded clause_family_payloads_system_def] _ assms]
  by (simp add: clause_family_payloads_system_def)

lemma clause_family_payloads_clause [simp]:
  "((504,c),S)\<in>system_clauses clause_family_payloads_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 503 504"
  unfolding clause_family_payloads_system_def by (rule audit_layer_clause) simp_all

lemma clause_family_payloads_element:
  "(503,t)\<in>positive_meaning clause_family_payloads_system \<longleftrightarrow> (503,t)\<in>positive_meaning clause_payloads_system"
  by (rule clause_family_payloads_old_meaning) simp

interpretation clause_family_payloads_profile: context_list_profile clause_family_payloads_system 503 504
  by (rule context_list_profile.intro) (auto simp: clause_family_payloads_call)

section \<open>The audit of one definition\<close>

text \<open>
  The entry reads the definition at a site of an environment presented as data. The existing
  definition reader admits it at a hidden operand whose every payload is empty, which the interface
  accepts exactly when it states no other payload. The actual record then gives the clause family's
  root, and the family's complete rows give every clause root, each audited by the clause audit.
\<close>

definition payload_audit_schema :: "(nat,nat,nat) factor_schema" where
  "payload_audit_schema=data_rule (source_root_pattern data_x data_y data_z)
    {(0,72,citation_observation_pattern data_x data_y data_z data_w),
     (1,500,data_w),
     (2,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (3,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6),
         Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)])),
     (4,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8)) (Pattern_Variable 9)),
     (5,59,Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)),
     (6,504,Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 10))}"

definition payload_audit_system :: "(nat,nat,nat,nat) schema_system" where
  "payload_audit_system=add_view_definition clause_family_payloads_system 505 data_x {(0,payload_audit_schema)}"

lemma payload_audit_system_formed [simp]: "schema_system_formed payload_audit_system"
  unfolding payload_audit_system_def
  by (rule add_recursive_definition_formed[OF clause_family_payloads_system_formed])
    (auto simp: payload_audit_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma payload_audit_definitions [simp]:
  "system_definitions payload_audit_system=insert 505 (system_definitions clause_family_payloads_system)"
  by (simp add: payload_audit_system_def)

lemma payload_audit_call:
  "schema_call_formed payload_audit_system d t \<longleftrightarrow> d\<in>system_definitions payload_audit_system \<and> term_formed t"
  using added_variable_calls[OF clause_family_payloads_system_formed
    payload_audit_system_formed[unfolded payload_audit_system_def] clause_family_payloads_call]
  by (simp only: payload_audit_system_def[symmetric])

lemma payload_audit_old_meaning:
  assumes "d\<in>system_definitions clause_family_payloads_system"
  shows "(d,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (d,t)\<in>positive_meaning clause_family_payloads_system"
  using added_definition_preserves_old(2)[OF clause_family_payloads_system_formed
    payload_audit_system_formed[unfolded payload_audit_system_def] _ assms]
  by (simp add: payload_audit_system_def)

lemma payload_audit_clause [simp]:
  "((505,c),S)\<in>system_clauses payload_audit_system \<longleftrightarrow> c=0 \<and> S=payload_audit_schema"
  unfolding payload_audit_system_def by (subst audit_layer_clause) simp_all

lemma payload_audit_admission_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_call_admission_system"
  using assms payload_audit_old_meaning[of d t] clause_family_payloads_old_meaning[of d t]
    clause_payloads_old_meaning[of d t] empty_payload_calls_old_meaning[of d t]
    empty_payload_rows_old_meaning[of d t] empty_payloads_old_meaning[of d t] by simp

lemma payload_audit_components:
  "(72,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (72,t)\<in>positive_meaning definition_call_admission_system"
  "(37,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(59,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(500,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (500,t)\<in>positive_meaning empty_payloads_system"
  "(504,t)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (504,t)\<in>positive_meaning clause_family_payloads_system"
  using payload_audit_admission_meaning[of 72 t] payload_audit_admission_meaning[of 37 t]
    payload_audit_admission_meaning[of 34 t] payload_audit_admission_meaning[of 32 t]
    payload_audit_admission_meaning[of 59 t] definition_call_admission_components(1,2)[of t]
    definition_call_admission_old_meaning[of 32 t] definition_call_admission_old_meaning[of 59 t]
    schema_family_admission_components(2,3)[of t]
    payload_audit_old_meaning[of 500 t] clause_family_payloads_old_meaning[of 500 t] clause_payloads_components(2)[of t]
    payload_audit_old_meaning[of 504 t] by simp_all

abbreviation payload_audit_result :: "factor_term \<Rightarrow> bool" where
  "payload_audit_result z \<equiv> \<exists>E e u r p C. z=source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents E e \<and> native_definition_at E u r p C \<and> definition_payloads p C\<subseteq>{[]}"

lemma payload_audit_rule:
  "(505,z)\<in>positive_meaning payload_audit_system \<longleftrightarrow> (\<exists>h. (\<forall>a\<in>schema_variables payload_audit_schema. term_formed (h a)) \<and>
    z=evaluate_pattern h (schema_conclusion payload_audit_schema) \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises payload_audit_schema \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning payload_audit_system))"
  by (rule variable_single_clause_valuation[OF payload_audit_system_formed payload_audit_clause]) (simp_all add: payload_audit_schema_def payload_audit_call)

theorem payload_audit_sound:
  assumes holds: "(505,z)\<in>positive_meaning payload_audit_system"
  shows "payload_audit_result z"
proof -
  define S where "S=payload_audit_schema"
  have schema: "S=payload_audit_schema" by (rule S_def)
  obtain h where conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning payload_audit_system"
    using holds unfolding schema payload_audit_rule by blast
  have calls: "(72,citation_observation_argument (h 0) (h 1) (h 2) (h 3))\<in>positive_meaning definition_call_admission_system"
    "(500,h 3)\<in>positive_meaning empty_payloads_system"
    "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 4) (h 2) (data_list_term [Pair_Term (h 5) (h 6),Pair_Term (h 7) (h 8)]))
      \<in>positive_meaning record_admission_system"
    "(32,rooted_rows_argument (h 4) (h 8) (h 9))\<in>positive_meaning family_admission_system"
    "(59,Pair_Term (h 9) (h 10))\<in>positive_meaning row_values_system"
    "(504,Pair_Term (Pair_Term (h 0) (h 1)) (h 10))\<in>positive_meaning clause_family_payloads_system"
    using support by (auto simp: schema payload_audit_schema_def payload_audit_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 4)"
    using calls(3) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r a i b m where rec: "h 2=Payload_Term r" "h 5=Payload_Term a" "h 6=Payload_Term i"
    "h 7=Payload_Term b" "h 8=Payload_Term m" "record_at R r [a,b] [i,m]"
    using calls(4) by (simp only: record_admission_pair_fields[OF source(4)]) blast
  obtain xs where fam: "h 9=data_list_term (map address_pair_data xs)" "distinct xs" "family_at R m (set xs)"
    using calls(5) by (simp only: rec(5) family_admission_at_source[OF source(4)] factor_term.inject) blast
  have roots: "h 10=data_list_term (map Payload_Term (map snd xs))"
    using calls(6) by (simp only: fam(1) address_row_values)
  have children: "\<forall>x\<in>set (map Payload_Term (map snd xs)).
      (503,Pair_Term (Pair_Term (h 0) (h 1)) x)\<in>positive_meaning clause_payloads_system"
    using calls(7) by (simp only: roots clause_family_payloads_profile.lists clause_family_payloads_element) blast
  have schemas: "\<And>s a. (s,a)\<in>set xs \<Longrightarrow> \<exists>S. native_schema_at E u a S \<and> schema_payloads S\<subseteq>{[]}"
    using children source(2) clause_payloads_on_values[OF source(1)] by force
  obtain F v l p C where defined: "environment_value_presents F (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
    "native_definition_at F v l p C" "pattern_accepts p (h 3)"
    using calls(1) by (simp only: definition_call_admission_exact factor_term.inject) blast
  have same: "F=E" "v=u" "l=r"
    using environment_value_presents_unique[OF defined(1) source(1)] defined(2,3) source(2) rec(1)
      injD[OF use_data_term_injective] by auto
  have raw: "native_definition_at E u r p C" using defined(4) same by simp
  have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  obtain R' ps i' m' where parts: "artifact_at E u R'" "record_at R' r ps [i',m']"
    "native_schema_family_at E u m' C"
    using raw unfolding native_definition_at_def by blast
  have "R'=R" by (rule environment_artifact_unique[OF ef parts(1) source(3)])
  then have "record_at R r ps [i',m']" using parts(2) by simp
  then have "m'=m" using record_at_unique[OF _ rec(6)] by fastforce
  then obtain R'' M where family: "artifact_at E u R''" "family_at R'' m M" "single_valued C"
    "rel_dom C=rel_dom M" "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using parts(3) by (auto simp: native_schema_family_at_def)
  have "R''=R" by (rule environment_artifact_unique[OF ef family(1) source(3)])
  then have "family_at R m M" using family(2) by simp
  then have rows: "M=set xs" by (rule family_at_unique[OF _ fam(3)])
  have interface: "{w. Payload_Term w\<in>pattern_leaves p}\<subseteq>{[]}"
  proof
    fix w assume leaf: "w\<in>{w. Payload_Term w\<in>pattern_leaves p}"
    obtain V where "pattern_instance V p (h 3)" using defined(5) by (auto simp: pattern_accepts_def)
    then have "w\<in>term_payloads (h 3)" using pattern_instance_payloads_included leaf by blast
    then show "w\<in>{[]}" using calls(2) empty_payloads_exact by blast
  qed
  have clauses: "schema_payloads S\<subseteq>{[]}" if member: "(c,S)\<in>C" for c S
  proof -
    obtain a where edge: "(c,a)\<in>M" using member family(4) by (auto simp: rel_dom_def)
    obtain T where T: "(c,T)\<in>C" "native_schema_at E u a T" using family(5) edge by blast
    have "T=S" using family(3) member T(1) by (auto simp: single_valued_def)
    obtain U where U: "native_schema_at E u a U" "schema_payloads U\<subseteq>{[]}" using schemas edge rows by blast
    have "U=T" by (rule native_schema_unique[OF U(1) T(2)])
    then show ?thesis using U(2) \<open>T=S\<close> by simp
  qed
  have payloads: "definition_payloads p C\<subseteq>{[]}"
    using interface clauses by (auto simp: definition_payloads_def)
  have argument: "z=source_root_argument (h 0) (use_data_term u) (Payload_Term r)"
    using conclusion source(2) rec(1) by (simp add: schema payload_audit_schema_def)
  show ?thesis by (intro exI conjI, rule argument, rule source(1), rule raw, rule payloads)
qed

theorem payload_audit_complete:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
    and payloads: "definition_payloads p C\<subseteq>{[]}"
  shows "(505,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning payload_audit_system"
proof -
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    using raw by (auto simp: native_definition_at_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain material where presented: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  obtain a b where ports: "ps=[a,b]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  have pf: "pattern_formed p" using scoped_pattern_formed[OF parts(3)] by blast
  let ?W="(\<lambda>b. (b,Payload_Term [])) ` pattern_variables p"
  have wb: "term_bindings_formed (pattern_variables p) ?W"
    by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  have scope: "pattern_variables p\<subseteq>rel_dom ?W" by (auto simp: rel_dom_def)
  obtain w where wi: "pattern_instance ?W p w" using pattern_instance_exists[OF pf scope] by blast
  have wp: "term_payloads w\<subseteq>{[]}"
  proof
    fix v assume "v\<in>term_payloads w"
    from pattern_instance_payloads_origin[OF wi this] show "v\<in>{[]}"
      using payloads by (auto simp: definition_payloads_def)
  qed
  have wf: "term_formed w" by (rule pattern_instance_formed_term[OF wb wi])
  have accepts: "pattern_accepts p w" using wb wi wf by (auto simp: pattern_accepts_def)
  have admitted: "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) w)
      \<in>positive_meaning definition_call_admission_system"
    by (rule definition_call_admission_complete[OF source raw accepts])
  have empty: "(500,w)\<in>positive_meaning empty_payloads_system" using wf wp empty_payloads_exact by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term a) (Payload_Term i),Pair_Term (Payload_Term b) (Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF presented]) (use parts(2) in \<open>auto simp: ports\<close>)
  obtain R'' M where family: "artifact_at E u R''" "family_at R'' m M"
    "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using parts(4) by (auto simp: native_schema_family_at_def)
  have "R''=R" by (rule environment_artifact_unique[OF ef family(1) parts(1)])
  then have fr: "family_at R m M" using family(2) by simp
  obtain xs where xs: "set xs=M" "distinct xs" using finite_distinct_list[OF family_socket_graph_finite[OF fr]] by blast
  let ?rows="data_list_term (map address_pair_data xs)"
  let ?roots="data_list_term (map Payload_Term (map snd xs))"
  have rows: "(32,rooted_rows_argument material (Payload_Term m) ?rows)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_rows[OF presented]) (use fr xs in auto)
  have formed: "term_formed ?rows" "term_formed e" "term_formed material"
    using schema_call_formed_target[OF positive_meaning_formed[OF rows]]
      schema_call_formed_target[OF positive_meaning_formed[OF lookup]] by auto
  have projection: "(59,Pair_Term ?rows ?roots)\<in>positive_meaning row_values_system"
    by (simp only: address_row_values) (use formed in blast)
  have clauses: "(503,Pair_Term (Pair_Term e (use_data_term u)) x)\<in>positive_meaning clause_payloads_system"
    if member: "x\<in>set (map Payload_Term (map snd xs))" for x
  proof -
    obtain s a' where edge: "(s,a')\<in>M" "x=Payload_Term a'" using member xs(1) by auto
    obtain S where S: "(s,S)\<in>C" "native_schema_at E u a' S" using family(3) edge(1) by blast
    have "schema_payloads S\<subseteq>{[]}" using payloads S(1) by (auto simp: definition_payloads_def)
    then show ?thesis using clause_payloads_complete[OF source S(2)] edge(2) by simp
  qed
  have children: "(504,Pair_Term (Pair_Term e (use_data_term u)) ?roots)\<in>positive_meaning clause_family_payloads_system"
    by (simp only: clause_family_payloads_profile.lists clause_family_payloads_element)
      (use formed clauses in auto)
  have operands: "term_formed (Payload_Term r)" "term_formed (Payload_Term a)" "term_formed (Payload_Term i)"
    "term_formed (Payload_Term b)" "term_formed (Payload_Term m)" "term_formed ?roots"
    using schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF projection]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then use_data_term u else if n=2 then Payload_Term r
    else if n=3 then w else if n=4 then material else if n=5 then Payload_Term a else if n=6 then Payload_Term i
    else if n=7 then Payload_Term b else if n=8 then Payload_Term m else if n=9 then ?rows else ?roots"
  have "(505,evaluate_pattern ?h (schema_conclusion payload_audit_schema))\<in>positive_meaning payload_audit_system"
    unfolding payload_audit_rule by (rule exI[of _ ?h])
      (use formed operands wf admitted empty lookup rec rows projection children in
        \<open>auto simp: payload_audit_schema_def schema_formed_def schema_variables_def single_valued_def rel_dom_def
          payload_audit_call payload_audit_components octets_formed_def\<close>)
  then show ?thesis by (simp add: payload_audit_schema_def)
qed

theorem payload_audit_exact:
  "(505,z)\<in>positive_meaning payload_audit_system \<longleftrightarrow> payload_audit_result z"
  using payload_audit_sound payload_audit_complete by blast

corollary payload_audit_at_source:
  assumes source: "environment_value_presents E e"
  shows "(505,source_root_argument e u r)\<in>positive_meaning payload_audit_system \<longleftrightarrow>
    (\<exists>v a p C. u=use_data_term v \<and> r=Payload_Term a \<and> native_definition_at E v a p C \<and> definition_payloads p C\<subseteq>{[]})"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: payload_audit_exact factor_term.inject) (use source unique in blast)
qed

corollary payload_audit_on_values:
  assumes source: "environment_value_presents E e"
  shows "(505,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning payload_audit_system
    \<longleftrightarrow> (\<exists>p C. native_definition_at E u r p C \<and> definition_payloads p C\<subseteq>{[]})"
  by (simp only: payload_audit_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary payload_audit_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(505,source_root_argument e u r)\<in>positive_meaning payload_audit_system \<longleftrightarrow>
    (505,source_root_argument f u r)\<in>positive_meaning payload_audit_system"
  using payload_audit_at_source[OF assms(1)] payload_audit_at_source[OF assms(2)] by simp

section \<open>The audit is equivariant under permutations of uses\<close>

text \<open>
  The audit's argument is a site context (@{thm [source] source_root_presentation_class}), on which the
  use instance's site context action acts. Its relation is the definition reading's at the site, as the
  definition readers' copy at a renamed use gives it (@{thm [source] native_definition_use_renaming}, the
  fact the definition reader's clause stands on), conjoined with a condition on the reading: the payloads
  the definition states. A renaming relocates the definition's callees and moves no pattern, so the
  payloads are kept; the audit compares no use itself, and the readers it calls compare the use only for
  equality. The first problem's goal G4 is the callee boundary's instance at this relation.
\<close>

lemma schema_payloads_callee_renaming:
  "schema_payloads (rename_schema id id g S)=schema_payloads S"
proof -
  have "schema_leaves (rename_schema id id g S)=schema_leaves S"
    by (simp add: schema_leaves_def rename_schema_def map_socket_graph_def image_image split_def)
  then show ?thesis by (simp add: schema_payloads_def)
qed

lemma definition_payloads_callee_renaming:
  "definition_payloads p ((\<lambda>(s,A). (s,rename_schema id id g A)) ` C)=definition_payloads p C"
  by (simp add: definition_payloads_def image_image split_def schema_payloads_callee_renaming)

lemma native_definition_site_position:
  assumes "native_definition_at E u r p C"
  shows "(u,r)\<in>environment_positions E"
  using assms by (auto simp: native_definition_at_def dest!: record_interior_in_carrier)

theorem payload_audit_renamed:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "(\<exists>p C. native_definition_at (rename_environment h E) (h u) r p C \<and> definition_payloads p C\<subseteq>{[]}) \<longleftrightarrow>
    (\<exists>p C. native_definition_at E u r p C \<and> definition_payloads p C\<subseteq>{[]})"
proof
  assume "\<exists>p C. native_definition_at (rename_environment h E) (h u) r p C \<and> definition_payloads p C\<subseteq>{[]}"
  then obtain p D where read: "native_definition_at (rename_environment h E) (h u) r p D"
    and blank: "definition_payloads p D\<subseteq>{[]}" by blast
  obtain C where original: "native_definition_at E u r p C"
    and moved: "D=(\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C"
    using read unfolding native_definition_use_renaming[OF formed permutation] by blast
  have "definition_payloads p C\<subseteq>{[]}" using blank by (simp add: moved definition_payloads_callee_renaming)
  then show "\<exists>p C. native_definition_at E u r p C \<and> definition_payloads p C\<subseteq>{[]}" using original by blast
next
  assume "\<exists>p C. native_definition_at E u r p C \<and> definition_payloads p C\<subseteq>{[]}"
  then obtain p C where original: "native_definition_at E u r p C" and blank: "definition_payloads p C\<subseteq>{[]}"
    by blast
  have read: "native_definition_at (rename_environment h E) (h u) r p
      ((\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)"
    by (rule native_definition_renamed_use[OF formed bij_is_inj[OF permutation] original])
  have "definition_payloads p ((\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)\<subseteq>{[]}"
    using blank by (simp add: definition_payloads_callee_renaming)
  then show "\<exists>p C. native_definition_at (rename_environment h E) (h u) r p C \<and> definition_payloads p C\<subseteq>{[]}"
    using read by blast
qed

theorem payload_audit_equivariant:
  "renaming_equivariant bij site_context_renaming site_context_formed
    (\<lambda>z. \<exists>p C. native_definition_at (fst z) (fst (snd z)) (snd (snd z)) p C \<and> definition_payloads p C\<subseteq>{[]})"
  by (auto simp: renaming_equivariant_def product_action_def payload_audit_renamed)

corollary payload_audit_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence source_root_presents site_context_renaming h) (=)
    (\<lambda>z. (505,z)\<in>positive_meaning payload_audit_system) (\<lambda>z. (505,z)\<in>positive_meaning payload_audit_system)"
proof -
  have exact: "\<And>p. (505,p)\<in>positive_meaning payload_audit_system \<longleftrightarrow>
      presented_predicate source_root_presents
        (\<lambda>z. \<exists>p C. native_definition_at (fst z) (fst (snd z)) (snd (snd z)) p C \<and> definition_payloads p C\<subseteq>{[]}) p"
    by (simp add: payload_audit_exact presented_predicate_def source_root_presents_def split_paired_Ex
      del: environment_positions_member; blast dest: native_definition_site_position)
  show ?thesis
    by (rule iffD2[OF presented_predicate_renaming[OF source_root_presentation_class site_context_renaming_action
      exact] payload_audit_equivariant])
qed

section \<open>The HOL counterpart of one definition's payloads\<close>

definition finite_definition_payloads ::
    "'a finite_term_pattern \<Rightarrow> ('c\<times>('a,'s,'d) finite_factor_schema) fset \<Rightarrow> octets fset" where
  "finite_definition_payloads p C=finite_pattern_payloads p |\<union>|
    ffUnion (fimage (\<lambda>(c,S). finite_schema_payloads S) C)"

theorem finite_definition_payloads_exact:
  "fset (finite_definition_payloads p C)=
    definition_payloads (decode_finite_pattern p) ((\<lambda>(c,S). (c,decode_finite_schema S)) ` fset C)"
  by (auto simp: finite_definition_payloads_def definition_payloads_def schema_payloads_def ffUnion.rep_eq
    fimage.rep_eq finite_pattern_payloads_exact finite_schema_payloads_exact split: prod.splits; force)

section \<open>A program is audited definition by definition\<close>

theorem system_payloads_definitions:
  assumes formed: "schema_system_formed P"
  shows "system_payloads P=
    (\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
proof (rule set_eqI)
  fix v
  have owned: "\<And>d c S. ((d,c),S)\<in>system_clauses P \<Longrightarrow> d\<in>system_definitions P"
    using formed unfolding schema_system_formed_def by blast
  show "v\<in>system_payloads P \<longleftrightarrow>
    v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
  proof
    assume "v\<in>system_payloads P"
    then have "Payload_Term v\<in>system_leaves P" by (simp add: system_payloads_def)
    then consider (interface) d p where "(d,p)\<in>system_interfaces P" "Payload_Term v\<in>pattern_leaves p"
      | (clause) d c S where "((d,c),S)\<in>system_clauses P" "Payload_Term v\<in>schema_leaves S"
      by (auto simp: system_leaves_def)
    then show "v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
    proof cases
      case interface
      have "d\<in>system_definitions P" using interface(1) by (auto simp: system_definitions_def rel_dom_def)
      moreover have "system_interface P d=p" by (rule system_interface_unique[OF formed interface(1)])
      ultimately show ?thesis using interface(2) by (auto simp: definition_payloads_def)
    next
      case clause
      then show ?thesis using owned[OF clause(1)] by (fastforce simp: definition_payloads_def schema_payloads_def)
    qed
  next
    assume "v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
    then obtain d where d: "d\<in>system_definitions P"
      and v: "v\<in>definition_payloads (system_interface P d) (system_clause_family P d)" by blast
    have member: "(d,system_interface P d)\<in>system_interfaces P" by (rule system_interface_member[OF formed d])
    show "v\<in>system_payloads P"
      using v member by (fastforce simp: definition_payloads_def schema_payloads_def system_payloads_def system_leaves_def)
  qed
qed

corollary system_payloads_audited:
  assumes "schema_system_formed P"
  shows "system_payloads P\<subseteq>{[]} \<longleftrightarrow>
    (\<forall>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d)\<subseteq>{[]})"
  using system_payloads_definitions[OF assms] by auto

corollary finite_system_payloads_audited:
  assumes "schema_system_formed (decode_finite_system P)"
  shows "fset (finite_system_payloads P)\<subseteq>{[]} \<longleftrightarrow>
    (\<forall>d\<in>system_definitions (decode_finite_system P).
      definition_payloads (system_interface (decode_finite_system P) d) (system_clause_family (decode_finite_system P) d)\<subseteq>{[]})"
  using system_payloads_audited[OF assms] finite_system_payloads_exact[of P] by simp

theorem payload_audit_package:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(\<forall>d\<in>system_definitions P.
      (505,source_root_argument e (use_data_term (fst d)) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system)
    \<longleftrightarrow> system_payloads P\<subseteq>{[]}"
proof -
  obtain Q where pk: "native_package_formed E (rel_ran Q)" "P=native_program E (rel_ran Q)"
    and roots: "native_root_family_at E pu pr Q"
    using package unfolding native_package_at_def by blast
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have each: "(505,source_root_argument e (use_data_term (fst d)) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system
      \<longleftrightarrow> definition_payloads (system_interface P d) (system_clause_family P d)\<subseteq>{[]}"
    if d: "d\<in>system_definitions P" for d
  proof -
    have site: "d\<in>native_definition_sites E (rel_ran Q)" using d native_program_definitions[OF pk(1)] pk(2) by simp
    have "d\<in>rel_dom (native_definition_graph E (rel_ran Q))"
      using native_definition_graph_domain[OF pk(1)] site by simp
    then obtain y where graph: "(d,y)\<in>native_definition_graph E (rel_ran Q)" by (auto simp: rel_dom_def)
    obtain p C where "y=(p,C)" by (cases y)
    then have "(d,p,C)\<in>native_definition_graph E (rel_ran Q)" using graph by simp
    then have read: "native_definition_at E (fst d) (snd d) p C" by (simp add: native_definition_graph_def)
    have interface: "system_interface P d=p"
      using system_interface_unique[OF pf] native_program_complete_at(1)[OF site read] pk(2) by blast
    have family: "system_clause_family P d=C"
    proof (rule set_eqI)
      fix x show "x\<in>system_clause_family P d \<longleftrightarrow> x\<in>C"
        using native_program_complete_at(2)[OF site read] pk(2) by (cases x) simp
    qed
    show ?thesis
      using payload_audit_on_values[OF source, of "fst d" "snd d"] read native_definition_unique[OF read]
        interface family by blast
  qed
  show ?thesis using each system_payloads_audited[OF pf] by blast
qed

section \<open>The audit's own payload literals\<close>

text \<open>
  By the same criterion the audit's own clauses state the empty payload alone: as the empty payload
  it accepts and as the terminator of the data lists it matches. Every other octet it meets is compared
  only by the readers it calls, which it does not restate.
\<close>

lemma payload_audit_own_payloads:
  assumes "(c,S)\<in>empty_payloads_clauses \<union> empty_payload_rows_clauses \<union> empty_payload_calls_clauses \<union>
    {(0,clause_payloads_schema)} \<union> context_list_clauses 503 504 \<union> {(0,payload_audit_schema)}"
  shows "schema_payloads S\<subseteq>{[]}"
  using assms
  by (auto simp: empty_payloads_clauses_def empty_payload_rows_clauses_def empty_payload_calls_clauses_def
    empty_payloads_schema_defs empty_payload_rows_schema_def empty_payload_calls_schema_def clause_payloads_schema_def
    payload_audit_schema_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
    schema_payloads_def schema_leaves_def)

end
