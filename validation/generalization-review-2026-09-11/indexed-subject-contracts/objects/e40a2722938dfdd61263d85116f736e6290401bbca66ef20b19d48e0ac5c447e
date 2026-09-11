theory Factor_Tagged_Views
  imports Factor_View_Definitions Factor_Pattern_Families
begin

section \<open>Exact data in a view's argument pattern\<close>

lemma tagged_pattern_accepts:
  assumes label: "term_formed z"
  shows "pattern_accepts (Pattern_Pair (exact_term_pattern z) p) x \<longleftrightarrow>
    (\<exists>t. x=Pair_Term z t \<and> pattern_accepts p t)"
  using label by (auto simp: pattern_accepts_def)

definition tagged_call_schema ::
  "'a \<Rightarrow> 's \<Rightarrow> factor_term \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) factor_schema" where
  "tagged_call_schema a s z d =
    \<lparr>schema_conclusion=Pattern_Pair (exact_term_pattern z) (Pattern_Variable a),
      schema_premises={(s,d,Pattern_Variable a)}, schema_material_premises={}\<rparr>"

lemma tagged_call_schema_formed [simp]:
  "schema_formed (tagged_call_schema a s z d) \<longleftrightarrow> term_formed z"
  by (simp add: tagged_call_schema_def schema_formed_def single_valued_def)

lemma tagged_call_schema_variables [simp]:
  "schema_variables (tagged_call_schema a s z d)={a}"
  by (simp add: tagged_call_schema_def schema_variables_def)

lemma tagged_call_schema_dependencies [simp]:
  "schema_dependencies (tagged_call_schema a s z d)={d}"
  by (auto simp: tagged_call_schema_def schema_dependencies_def rel_ran_def)

theorem tagged_call_schema_rule:
  "schema_rule_instance (tagged_call_schema a s z d) X x \<longleftrightarrow>
    term_formed z \<and> (\<exists>t. term_formed t \<and> x=Pair_Term z t \<and> (d,t)\<in>X)"
proof
  assume rule: "schema_rule_instance (tagged_call_schema a s z d) X x"
  obtain V Q where inst: "schema_instance (tagged_call_schema a s z d) V x Q"
    and support: "\<forall>r e t. (r,e,t)\<in>Q \<longrightarrow> (e,t)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  have zf: "term_formed z"
    and terms: "\<And>b t. (b,t)\<in>V \<Longrightarrow> term_formed t"
    using inst by (auto simp: schema_instance_def term_bindings_formed_def)
  obtain t where shape: "x=Pair_Term z t" and bound: "(a,t)\<in>V"
    using inst by (auto simp: schema_instance_def tagged_call_schema_def)
  have premise: "(s,d,t)\<in>Q"
    using schema_instance_premise_iff[OF inst, of s d t] bound
    by (simp add: tagged_call_schema_def)
  show "term_formed z \<and> (\<exists>t. term_formed t \<and> x=Pair_Term z t \<and> (d,t)\<in>X)"
    using zf terms[OF bound] shape support premise by blast
next
  assume "term_formed z \<and> (\<exists>t. term_formed t \<and> x=Pair_Term z t \<and> (d,t)\<in>X)"
  then obtain t where parts: "term_formed z" "term_formed t" "x=Pair_Term z t" "(d,t)\<in>X"
    by blast
  have inst: "schema_instance (tagged_call_schema a s z d) {(a,t)} x {(s,d,t)}"
    using parts(1-3)
    by (auto simp: schema_instance_def tagged_call_schema_def schema_variables_def
      schema_formed_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)
  have material: "schema_material_satisfied (tagged_call_schema a s z d) {(a,t)}"
    by (simp add: schema_material_satisfied_def tagged_call_schema_def)
  show "schema_rule_instance (tagged_call_schema a s z d) X x"
    using inst material parts(4) unfolding schema_rule_instance_def by blast
qed

text \<open>
  The supplied label is exact ordinary term data in the conclusion pattern.
  One identified premise invokes a fixed callee on the same entire argument.
  The rule reads no semantic target from an unbounded external table. Finite
  families of these clauses can expose many fixed callees through one entry.
  A separate premise-free pattern can expose each original interface.
\<close>

end
