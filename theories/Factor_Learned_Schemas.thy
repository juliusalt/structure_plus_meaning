theory Factor_Learned_Schemas
  imports Factor_Proof_Schemes Factor_Inference_Development
begin

section \<open>A proved argument exports its actual conditional boundary\<close>

definition schema_scheme_rule ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    'b term_pattern \<Rightarrow> ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow>
    ('b,'n+('n\<times>'s),'d) factor_schema" where
  "schema_scheme_rule P G p J =
    \<lparr>schema_conclusion=p,
     schema_premises=(\<lambda>(n,q). (Inl n,q)) ` schema_graph_assumptions G J,
     schema_material_premises=(\<lambda>(k,M). (Inr k,M)) ` schema_scheme_materials P G J\<rparr>"

lemma schema_scheme_rule_head [simp]:
  "schema_conclusion (schema_scheme_rule P G p J)=p"
  by (simp add: schema_scheme_rule_def)

lemma schema_scheme_rule_assertion [simp]:
  "(s,e,q)\<in>schema_premises (schema_scheme_rule P G p J) \<longleftrightarrow>
    (\<exists>n. s=Inl n \<and> (n,e,q)\<in>schema_graph_assumptions G J)"
  by (auto simp: schema_scheme_rule_def)

lemma schema_scheme_rule_material [simp]:
  "(s,M)\<in>schema_material_premises (schema_scheme_rule P G p J) \<longleftrightarrow>
    (\<exists>n k. s=Inr (n,k) \<and> ((n,k),M)\<in>schema_scheme_materials P G J)"
  by (auto simp: schema_scheme_rule_def)

lemma schema_scheme_material_formed:
  assumes read: "schema_scheme_reading P G root d p J"
    and member: "(k,M)\<in>schema_scheme_materials P G J"
  shows "material_pattern_formed M"
proof -
  obtain n A where node: "(n,A)\<in>fset (graph_inferences G)"
    and local: "(k,M)\<in>scheme_node_materials P J n A"
    using member by (auto simp: schema_scheme_materials_def)
  obtain c V where kind: "A=Schema_Inference c V" using local by (cases A) auto
  have check: "checks_schema_scheme_node P G J n (Schema_Inference c V)"
    using read node kind by (simp only: schema_scheme_reading_def; blast)
  obtain S where source: "((fst (rel_value J n),c),S)\<in>system_clauses P"
    and bindings: "pattern_bindings_formed (schema_variables S) (fset V)"
    using check by auto
  have sf: "schema_formed S" and sv: "single_valued (system_clauses P)"
    using read source by (auto simp: schema_scheme_reading_def schema_system_formed_def)
  have lookup: "rel_value (system_clauses P) (fst (rel_value J n),c)=S"
    by (rule rel_value_eq[OF sv source])
  obtain s N where original: "(s,N)\<in>schema_material_premises S"
    and target: "M=material_pattern_substitute (rel_value (fset V)) N"
    using local by (auto simp: kind lookup)
  have nf: "material_pattern_formed N" and scope: "material_variables N\<subseteq>schema_variables S"
    using sf original by (auto simp: schema_formed_def schema_variables_def)
  show ?thesis unfolding target
    by (rule material_substitute_formed[OF nf])
      (use pattern_binding_at(2)[OF bindings] scope in blast)
qed

theorem schema_scheme_rule_formed:
  assumes read: "schema_scheme_reading P G root d p J"
  shows "schema_formed (schema_scheme_rule P G p J)"
proof -
  have claims: "single_valued J" and root: "(root,d,p)\<in>J"
    using read by (auto simp: schema_scheme_reading_def)
  have pf: "pattern_formed q" if "(n,e,q)\<in>J" for n e q
    by (rule schema_pattern_call_formed(1))
      (use read that in \<open>simp only: schema_scheme_reading_def; blast\<close>)
  have sub: "schema_graph_assumptions G J\<subseteq>J"
    by (auto simp: schema_graph_assumptions_def)
  have finite: "finite (schema_graph_assumptions G J)"
    by (rule finite_subset[OF sub schema_scheme_reading_finite[OF read]])
  have functional: "single_valued (schema_graph_assumptions G J)"
    using claims sub by (auto simp: single_valued_def; blast)
  have ordinary: "single_valued ((\<lambda>(n,q). (Inl n,q)) ` schema_graph_assumptions G J)"
    using single_valued_pair_image[OF functional, where f=Inl and g=id]
    by (simp add: inj_on_def)
  have material: "single_valued ((\<lambda>(k,M). (Inr k,M)) ` schema_scheme_materials P G J)"
    using single_valued_pair_image[OF schema_scheme_materials_functional[OF read], where f=Inr and g=id]
    by (simp add: inj_on_def)
  have children: "pattern_formed q" if "(n,e,q)\<in>schema_graph_assumptions G J" for n e q
    by (rule pf) (use sub that in blast)
  show ?thesis using pf[OF root] finite ordinary material children
      schema_scheme_materials_finite[OF read] schema_scheme_material_formed[OF read]
    by (auto simp: schema_formed_def schema_scheme_rule_def rel_dom_def)
qed

lemma schema_scheme_rule_pattern_scope:
  "pattern_variables p\<subseteq>schema_variables (schema_scheme_rule P G p J)"
  "(n,e,q)\<in>schema_graph_assumptions G J \<Longrightarrow>
    pattern_variables q\<subseteq>schema_variables (schema_scheme_rule P G p J)"
  "(k,M)\<in>schema_scheme_materials P G J \<Longrightarrow>
    material_variables M\<subseteq>schema_variables (schema_scheme_rule P G p J)"
  by (auto simp: schema_variables_def schema_scheme_rule_def)

theorem schema_scheme_rule_sound:
  assumes read: "schema_scheme_reading P G root d p J"
    and rule: "schema_rule_instance (schema_scheme_rule P G p J) (positive_meaning P) t"
  shows "(d,t)\<in>positive_meaning P"
proof -
  let ?S="schema_scheme_rule P G p J"
  obtain h where assignment: "\<forall>a\<in>schema_variables ?S. term_formed (h a)"
    and head: "t=evaluate_pattern h p"
    and materials: "\<forall>s M. (s,M)\<in>schema_material_premises ?S \<longrightarrow> evaluate_material_satisfaction h M"
    and assertions: "\<forall>s e q. (s,e,q)\<in>schema_premises ?S \<longrightarrow>
      (e,evaluate_pattern h q)\<in>positive_meaning P"
    using rule by (simp only: schema_rule_instance_valuation schema_scheme_rule_head) blast
  let ?g="\<lambda>a. if a\<in>schema_variables ?S then h a else Payload_Term []"
  have formed: "\<forall>a\<in>schema_scheme_variables G J. term_formed (?g a)"
    using assignment by (auto simp: octets_formed_def)
  have patterns: "evaluate_pattern ?g q=evaluate_pattern h q"
    if "pattern_variables q\<subseteq>schema_variables ?S" for q
    by (rule evaluate_pattern_cong) (use that in auto)
  have tests: "evaluate_material_satisfaction ?g M"
    if member: "(k,M)\<in>schema_scheme_materials P G J" for k M
  proof -
    have same: "evaluate_material_satisfaction ?g M=evaluate_material_satisfaction h M"
      by (rule material_valuation_cong)
        (use schema_scheme_rule_pattern_scope(3)[OF member] in auto)
    have retained: "(Inr k,M)\<in>schema_material_premises ?S"
      using member by (auto simp: schema_scheme_rule_def)
    show ?thesis using materials retained same by blast
  qed
  have support: "(e,evaluate_pattern ?g q)\<in>positive_meaning P"
    if member: "(n,e,q)\<in>schema_graph_assumptions G J" for n e q
  proof -
    have retained: "(Inl n,e,q)\<in>schema_premises ?S"
      using member by (auto simp: schema_scheme_rule_def)
    have holds: "(e,evaluate_pattern h q)\<in>positive_meaning P"
      using assertions retained by blast
    show ?thesis using holds
      by (simp only: patterns[OF schema_scheme_rule_pattern_scope(2)[OF member]])
  qed
  have result: "(d,evaluate_pattern ?g p)\<in>positive_meaning P"
    by (rule schema_scheme_conditional_sound[OF read formed]) (use tests support in blast)+
  show ?thesis using result by (simp only: patterns[OF schema_scheme_rule_pattern_scope(1)] head)
qed

section \<open>Learned conditional rules enter the existing inference closure\<close>

definition learned_schema_inferences ::
  "('d\<times>('b,'k,'d) factor_schema) set \<Rightarrow> ('d\<times>factor_term) \<Rightarrow>
    ('k\<times>('d\<times>factor_term)) set \<Rightarrow> bool" where
  "learned_schema_inferences L q H \<longleftrightarrow>
    (\<exists>S V. (fst q,S)\<in>L \<and> schema_instance S V (snd q) H \<and> schema_material_satisfied S V)"

theorem learned_schema_inferences_sound:
  assumes library: "\<And>d S t. (d,S)\<in>L \<Longrightarrow>
    schema_rule_instance S (positive_meaning P) t \<Longrightarrow> (d,t)\<in>positive_meaning P"
  shows "inference_sound (\<lambda>q. q\<in>positive_meaning P) (learned_schema_inferences L)"
  unfolding inference_sound_def
proof (intro allI impI)
  fix q H
  assume "finite H" "single_valued H" and step: "learned_schema_inferences L q H"
    and support: "rel_ran H\<subseteq>{q. q\<in>positive_meaning P}"
  obtain S V where member: "(fst q,S)\<in>L" and inst: "schema_instance S V (snd q) H"
    and tests: "schema_material_satisfied S V"
    using step by (auto simp: learned_schema_inferences_def)
  have rule: "schema_rule_instance S (positive_meaning P) (snd q)"
    unfolding schema_rule_instance_def
    by (rule exI[of _ V], rule exI[of _ H])
      (use inst tests support in \<open>auto simp: rel_ran_def\<close>)
  show "q\<in>positive_meaning P" using library[OF member rule] by simp
qed

corollary proved_scheme_library_sound:
  assumes library: "\<And>d S. (d,S)\<in>L \<Longrightarrow>
    \<exists>G root p J. schema_scheme_reading P G root d p J \<and> S=schema_scheme_rule P G p J"
  shows "inference_sound (\<lambda>q. q\<in>positive_meaning P) (learned_schema_inferences L)"
proof (rule learned_schema_inferences_sound)
  fix d S t
  assume member: "(d,S)\<in>L" and step: "schema_rule_instance S (positive_meaning P) t"
  obtain G root p J where read: "schema_scheme_reading P G root d p J"
    and schema: "S=schema_scheme_rule P G p J"
    using library[OF member] by blast
  show "(d,t)\<in>positive_meaning P"
    by (rule schema_scheme_rule_sound[OF read]) (use step in \<open>simp only: schema\<close>)
qed

theorem learned_schema_library_growth:
  assumes "L\<subseteq>M"
  shows "inference_closure (learned_schema_inferences L) K\<subseteq>
    inference_closure (learned_schema_inferences M) K"
proof (rule inference_closure_least[OF inference_closure_seed])
  have included: "inference_consequences (learned_schema_inferences L) X\<subseteq>
      inference_consequences (learned_schema_inferences M) X" for X
    using assms by (auto simp: inference_consequences_def learned_schema_inferences_def)
  show "inference_consequences (learned_schema_inferences L)
      (inference_closure (learned_schema_inferences M) K)\<subseteq>
      inference_closure (learned_schema_inferences M) K"
    by (rule subset_trans[OF included inference_closure_closed])
qed

text \<open>
  The extracted rule has the original root pattern. Its ordinary sockets are
  precisely the separate assertion nodes. Its material sockets are precisely
  the original inference-node and material-socket pairs. All five material
  operands remain in the rule. Equal assertions at different nodes therefore
  remain different obligations.

  A variable disappears from the exported binder only when it occurs in none
  of the exported head, assertions, or material operands. The soundness proof
  extends such a valuation to the internal proof; it never drops a condition
  on a private variable. Extraction constructs a new schema that can be
  specialized on future terms. Adding sound extracted rules increases the
  available inference consequences without declaring their premises true.

  These theorems establish the mathematical extraction and inference link.
  They do not themselves implement native admission of submitted symbolic
  proof schemes or discover the construction arguments of a larger contract.
\<close>

end
