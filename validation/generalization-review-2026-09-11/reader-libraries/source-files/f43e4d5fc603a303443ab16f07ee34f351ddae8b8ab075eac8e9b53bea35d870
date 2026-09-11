theory Factor_Substitution
  imports Factor_Rule_Instances Factor_Alpha_Semantics Factor_Pattern_Programs
begin

section \<open>Substitution commutes with every later valuation\<close>

lemma evaluate_pattern_substitute [simp]:
  "evaluate_pattern h (pattern_substitute s p) = evaluate_pattern (\<lambda>a. evaluate_pattern h (s a)) p"
  by (induction p) auto

definition material_pattern_substitute ::
  "('a \<Rightarrow> 'b term_pattern) \<Rightarrow> 'a material_pattern \<Rightarrow> 'b material_pattern" where
  "material_pattern_substitute s M =
    \<lparr>material_source=pattern_substitute s (material_source M),
     material_atoms=pattern_substitute s (material_atoms M),
     material_edges=pattern_substitute s (material_edges M),
     material_counts=pattern_substitute s (material_counts M),
     material_functions=pattern_substitute s (material_functions M)\<rparr>"

lemma material_substitute_fields:
  "material_fields (material_pattern_substitute s M) = map (pattern_substitute s) (material_fields M)"
  by (simp add: material_pattern_substitute_def material_fields_def)

lemma material_substitute_variables:
  "material_variables (material_pattern_substitute s M) =
    (\<Union>a\<in>material_variables M. pattern_variables (s a))"
  by (auto simp: material_variables_def material_substitute_fields pattern_substitute_variables)

lemma material_substitute_formed:
  assumes "material_pattern_formed M" "\<forall>a\<in>material_variables M. pattern_formed (s a)"
  shows "material_pattern_formed (material_pattern_substitute s M)"
  using assms by (auto simp: material_pattern_formed_def material_substitute_fields material_variables_def
    intro: pattern_substitute_formed)

lemma material_substitute_identity [simp]:
  "material_pattern_substitute Pattern_Variable M=M"
  by (cases M) (simp add: material_pattern_substitute_def)

lemma material_substitute_composes:
  "material_pattern_substitute t (material_pattern_substitute s M) =
    material_pattern_substitute (\<lambda>a. pattern_substitute t (s a)) M"
  by (simp add: material_pattern_substitute_def pattern_substitute_composes)

lemma material_substitute_renaming:
  "material_pattern_substitute (Pattern_Variable \<circ> f) M=rename_material_pattern f M"
  by (simp add: material_pattern_substitute_def rename_material_pattern_def rename_pattern_def)

lemma material_substitute_satisfaction [simp]:
  "evaluate_material_satisfaction h (material_pattern_substitute s M) =
    evaluate_material_satisfaction (\<lambda>a. evaluate_pattern h (s a)) M"
  by (simp add: material_pattern_substitute_def)

section \<open>Every identified premise retains its socket and callee\<close>

definition schema_substitute ::
  "('a \<Rightarrow> 'b term_pattern) \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow> ('b,'s,'d) factor_schema" where
  "schema_substitute s S =
    \<lparr>schema_conclusion=pattern_substitute s (schema_conclusion S),
     schema_premises=map_socket_graph id id (pattern_substitute s) (schema_premises S),
     schema_material_premises=(\<lambda>(q,M). (q,material_pattern_substitute s M)) ` schema_material_premises S\<rparr>"

lemma schema_substitute_conclusion [simp]:
  "schema_conclusion (schema_substitute s S)=pattern_substitute s (schema_conclusion S)"
  by (simp add: schema_substitute_def)

lemma schema_substitute_premise [simp]:
  "(q,d,p)\<in>schema_premises (schema_substitute s S) \<longleftrightarrow>
    (\<exists>a. (q,d,a)\<in>schema_premises S \<and> p=pattern_substitute s a)"
  by (auto simp: schema_substitute_def map_socket_graph_member)

lemma schema_substitute_material [simp]:
  "(q,M)\<in>schema_material_premises (schema_substitute s S) \<longleftrightarrow>
    (\<exists>N. (q,N)\<in>schema_material_premises S \<and> M=material_pattern_substitute s N)"
  by (auto simp: schema_substitute_def)

lemma schema_substitute_variables:
  "schema_variables (schema_substitute s S) = (\<Union>a\<in>schema_variables S. pattern_variables (s a))"
  by (auto simp: schema_variables_def schema_substitute_def map_socket_graph_def
    map_prod_def split_def material_substitute_variables pattern_substitute_variables
    intro: rev_image_eqI; blast)

lemma schema_substitute_sockets [simp]:
  "schema_sockets (schema_substitute s S)=schema_sockets S"
  by (simp add: schema_sockets_def schema_substitute_def map_socket_graph_domain pair_image_domain)

lemma schema_substitute_dependencies [simp]:
  "schema_dependencies (schema_substitute s S)=schema_dependencies S"
  by (simp add: schema_dependencies_def schema_substitute_def map_socket_graph_def
    pair_image_range image_image)

lemma schema_substitute_formed:
  assumes formed: "schema_formed S" and replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
  shows "schema_formed (schema_substitute s S)"
proof -
  have calls: "single_valued (map_socket_graph id id (pattern_substitute s) (schema_premises S))"
    by (rule map_socket_graph_functional) (use formed in \<open>auto simp: schema_formed_def\<close>)
  have materials: "single_valued ((\<lambda>(q,M). (q,material_pattern_substitute s M)) ` schema_material_premises S)"
    by (rule single_valued_pair_image[where f=id, simplified])
      (use formed in \<open>auto simp: schema_formed_def\<close>)
  have premise_formed: "pattern_formed (pattern_substitute s p)"
    if member: "(q,d,p)\<in>schema_premises S" for q d p
    by (rule pattern_substitute_formed)
      (use formed replacements member in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have material_formed: "material_pattern_formed (material_pattern_substitute s M)"
    if member: "(q,M)\<in>schema_material_premises S" for q M
    by (rule material_substitute_formed)
      (use formed replacements member in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  show ?thesis using formed replacements calls materials premise_formed material_formed
    by (auto simp: schema_formed_def schema_substitute_def map_socket_graph_def
      map_socket_graph_domain pair_image_domain schema_variables_def
      intro: pattern_substitute_formed material_substitute_formed)
qed

lemma schema_substitute_identity [simp]:
  "schema_substitute Pattern_Variable S=S"
  by (cases S) (simp add: schema_substitute_def map_socket_graph_def map_prod_def split_def)

lemma schema_substitute_composes:
  "schema_substitute t (schema_substitute s S)=schema_substitute (\<lambda>a. pattern_substitute t (s a)) S"
  by (simp add: schema_substitute_def map_socket_graph_def map_prod_def image_image split_def
    comp_def pattern_substitute_composes material_substitute_composes)

lemma schema_substitute_renaming:
  "schema_substitute (Pattern_Variable \<circ> f) S=rename_schema f id id S"
proof -
  have patterns: "pattern_substitute (Pattern_Variable \<circ> f)=rename_pattern f"
    by (rule ext) (simp add: rename_pattern_def)
  show ?thesis by (simp add: schema_substitute_def rename_schema_def patterns material_substitute_renaming)
qed

lemma evaluate_schema_premises_substitute [simp]:
  "evaluate_schema_premises h (schema_substitute s S)=
    evaluate_schema_premises (\<lambda>a. evaluate_pattern h (s a)) S"
  by (simp add: evaluate_schema_premises_def schema_substitute_def map_socket_graph_def
    map_prod_def image_image split_def)

lemma substituted_valuation_formed:
  assumes replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
    and valuation: "\<forall>b\<in>schema_variables (schema_substitute s S). term_formed (h b)"
  shows "\<forall>a\<in>schema_variables S. term_formed (evaluate_pattern h (s a))"
  using assms by (auto simp: schema_substitute_variables intro: evaluate_pattern_formed)

section \<open>Complete rule instances have an exact valuation account\<close>

lemma schema_graph_instance_iff:
  "schema_instance S ((\<lambda>a. (a,h a)) ` schema_variables S) t Q \<longleftrightarrow>
    schema_formed S \<and> (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> Q=evaluate_schema_premises h S"
proof
  assume inst: "schema_instance S ((\<lambda>a. (a,h a)) ` schema_variables S) t Q"
  have formed: "schema_formed S" and assignment_values: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    using inst by (auto simp: schema_instance_def term_bindings_formed_def)
  have outputs: "t=evaluate_pattern h (schema_conclusion S) \<and> Q=evaluate_schema_premises h S"
    by (rule schema_instance_unique[OF inst schema_evaluation_instance[OF formed assignment_values]])
  show "schema_formed S \<and> (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> Q=evaluate_schema_premises h S"
    using formed assignment_values outputs by blast
next
  assume "schema_formed S \<and> (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> Q=evaluate_schema_premises h S"
  then show "schema_instance S ((\<lambda>a. (a,h a)) ` schema_variables S) t Q"
    using schema_evaluation_instance[of S h] by blast
qed

theorem schema_rule_instance_valuation:
  "schema_rule_instance S X t \<longleftrightarrow> schema_formed S \<and>
    (\<exists>h. (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      t=evaluate_pattern h (schema_conclusion S) \<and>
      (\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M) \<and>
      (\<forall>q d p. (q,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>X))"
proof
  assume rule: "schema_rule_instance S X t"
  obtain V Q where inst: "schema_instance S V t Q" and material: "schema_material_satisfied S V"
    and support: "\<forall>q d x. (q,d,x)\<in>Q \<longrightarrow> (d,x)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  obtain h where assignment: "\<forall>a\<in>schema_variables S. (a,h a)\<in>V \<and> term_formed (h a)"
    and head: "t=evaluate_pattern h (schema_conclusion S)" and calls: "Q=evaluate_schema_premises h S"
    using schema_instance_evaluation[OF inst] by blast
  have materials: "\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M"
    using schema_material_evaluation[OF inst, of h] assignment material by blast
  show "schema_formed S \<and> (\<exists>h. (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      t=evaluate_pattern h (schema_conclusion S) \<and>
      (\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M) \<and>
      (\<forall>q d p. (q,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>X))"
    using inst assignment head calls materials support by (auto simp: schema_instance_def; blast)
next
  assume "schema_formed S \<and> (\<exists>h. (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      t=evaluate_pattern h (schema_conclusion S) \<and>
      (\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M) \<and>
      (\<forall>q d p. (q,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>X))"
  then obtain h where formed: "schema_formed S" and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and head: "t=evaluate_pattern h (schema_conclusion S)"
    and material: "\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M"
    and support: "\<forall>q d p. (q,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>X" by blast
  let ?V="(\<lambda>a. (a,h a)) ` schema_variables S"
  have inst: "schema_instance S ?V t (evaluate_schema_premises h S)"
    using schema_evaluation_instance[OF formed assignment] head by simp
  have materials: "schema_material_satisfied S ?V"
    using schema_material_evaluation[OF inst, of h] material by simp
  show "schema_rule_instance S X t" unfolding schema_rule_instance_def
    by (rule exI[of _ ?V], rule exI[of _ "evaluate_schema_premises h S"])
      (use inst materials support in auto)
qed

theorem schema_substitute_specializes:
  assumes formed: "schema_formed S" and replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
    and rule: "schema_rule_instance (schema_substitute s S) X t"
  shows "schema_rule_instance S X t"
proof -
  obtain h where assignment: "\<forall>b\<in>schema_variables (schema_substitute s S). term_formed (h b)"
    and head: "t=evaluate_pattern h (schema_conclusion (schema_substitute s S))"
    and material: "\<forall>q M. (q,M)\<in>schema_material_premises (schema_substitute s S) \<longrightarrow>
      evaluate_material_satisfaction h M"
    and support: "\<forall>q d p. (q,d,p)\<in>schema_premises (schema_substitute s S) \<longrightarrow>
      (d,evaluate_pattern h p)\<in>X"
    using rule by (simp only: schema_rule_instance_valuation) blast
  have lifted: "\<forall>a\<in>schema_variables S. term_formed (evaluate_pattern h (s a))"
    by (rule substituted_valuation_formed[OF replacements assignment])
  have lifted_material: "evaluate_material_satisfaction (\<lambda>a. evaluate_pattern h (s a)) M"
    if member: "(q,M)\<in>schema_material_premises S" for q M
    using material[rule_format, of q "material_pattern_substitute s M"] member by auto
  have lifted_support: "(d,evaluate_pattern (\<lambda>a. evaluate_pattern h (s a)) p)\<in>X"
    if member: "(q,d,p)\<in>schema_premises S" for q d p
    using support[rule_format, of q d "pattern_substitute s p"] member by auto
  show ?thesis unfolding schema_rule_instance_valuation
    by (intro conjI[OF formed], rule exI[of _ "\<lambda>a. evaluate_pattern h (s a)"])
      (use lifted head lifted_material lifted_support in auto)
qed

section \<open>The reverse direction has a separate valuation coverage obligation\<close>

definition substitution_covers :: "('a \<Rightarrow> 'b term_pattern) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "substitution_covers s B \<longleftrightarrow> (\<forall>h. (\<forall>a\<in>B. term_formed (h a)) \<longrightarrow>
    (\<exists>g. (\<forall>b\<in>(\<Union>a\<in>B. pattern_variables (s a)). term_formed (g b)) \<and>
      (\<forall>a\<in>B. h a=evaluate_pattern g (s a))))"

lemma variable_substitution_covers:
  assumes "inj_on f B"
  shows "substitution_covers (Pattern_Variable \<circ> f) B"
proof (unfold substitution_covers_def, intro allI impI)
  fix h assume formed: "\<forall>a\<in>B. term_formed (h a)"
  show "\<exists>g. (\<forall>b\<in>(\<Union>a\<in>B. pattern_variables ((Pattern_Variable \<circ> f) a)). term_formed (g b)) \<and>
    (\<forall>a\<in>B. h a=evaluate_pattern g ((Pattern_Variable \<circ> f) a))"
    by (rule exI[of _ "h \<circ> inv_into B f"])
      (use formed assms in \<open>auto simp: inv_into_f_f\<close>)
qed

lemma material_valuation_cong:
  assumes "\<And>a. a\<in>material_variables M \<Longrightarrow> h a=g a"
  shows "evaluate_material_satisfaction h M=evaluate_material_satisfaction g M"
proof -
  have same: "evaluate_pattern h p=evaluate_pattern g p" if "p\<in>set (material_fields M)" for p
    by (rule evaluate_pattern_cong) (use assms that in \<open>auto simp: material_variables_def\<close>)
  show ?thesis using same by (simp add: material_fields_def)
qed

theorem schema_substitute_equivalent:
  assumes formed: "schema_formed S" and replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
    and coverage: "substitution_covers s (schema_variables S)"
  shows "schema_rule_instance (schema_substitute s S) X t \<longleftrightarrow> schema_rule_instance S X t"
proof
  assume "schema_rule_instance (schema_substitute s S) X t"
  then show "schema_rule_instance S X t" by (rule schema_substitute_specializes[OF formed replacements])
next
  assume rule: "schema_rule_instance S X t"
  obtain h where assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and head: "t=evaluate_pattern h (schema_conclusion S)"
    and material: "\<forall>q M. (q,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h M"
    and support: "\<forall>q d p. (q,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>X"
    using rule by (simp only: schema_rule_instance_valuation) blast
  obtain g where target: "\<forall>b\<in>schema_variables (schema_substitute s S). term_formed (g b)"
    and agreement: "\<forall>a\<in>schema_variables S. h a=evaluate_pattern g (s a)"
    using coverage assignment by (auto simp: substitution_covers_def schema_substitute_variables)
  have same: "evaluate_pattern h p=evaluate_pattern (\<lambda>a. evaluate_pattern g (s a)) p"
    if "pattern_variables p\<subseteq>schema_variables S" for p
    by (rule evaluate_pattern_cong) (use agreement that in auto)
  have same_material: "evaluate_material_satisfaction h M=
      evaluate_material_satisfaction (\<lambda>a. evaluate_pattern g (s a)) M"
    if "(q,M)\<in>schema_material_premises S" for q M
    by (rule material_valuation_cong) (use agreement that in \<open>auto simp: schema_variables_def\<close>)
  have target_formed: "schema_formed (schema_substitute s S)"
    by (rule schema_substitute_formed[OF formed replacements])
  have head_same: "evaluate_pattern h (schema_conclusion S)=
      evaluate_pattern (\<lambda>a. evaluate_pattern g (s a)) (schema_conclusion S)"
    by (rule same) (auto simp: schema_variables_def)
  have lifted_support: "(d,evaluate_pattern (\<lambda>a. evaluate_pattern g (s a)) p)\<in>X"
    if member: "(q,d,p)\<in>schema_premises S" for q d p
  proof -
    have equal: "evaluate_pattern h p=evaluate_pattern (\<lambda>a. evaluate_pattern g (s a)) p"
      by (rule same) (use member in \<open>auto simp: schema_variables_def\<close>)
    have supported: "(d,evaluate_pattern h p)\<in>X" using support member by blast
    show ?thesis using supported by (simp only: equal)
  qed
  show "schema_rule_instance (schema_substitute s S) X t" unfolding schema_rule_instance_valuation
    by (intro conjI[OF target_formed], rule exI[of _ g])
      (use target head head_same material lifted_support same_material in auto)
qed

theorem schema_substitution_can_be_strict:
  "schema_rule_instance (recognizer_schema (Pattern_Variable ()) :: (unit,unit,unit) factor_schema) {}
      (Pair_Term (Payload_Term []) (Payload_Term [])) \<and>
    \<not>schema_rule_instance
      (schema_substitute (\<lambda>_. Pattern_Payload [] :: unit term_pattern) (recognizer_schema (Pattern_Variable ()))) {}
      (Pair_Term (Payload_Term []) (Payload_Term []))"
proof -
  have original: "schema_rule_instance (recognizer_schema (Pattern_Variable ()) :: (unit,unit,unit) factor_schema) {}
      (Pair_Term (Payload_Term []) (Payload_Term []))"
    unfolding schema_rule_instance_valuation
    apply (rule conjI)
     apply simp
    apply (rule exI[of _ "\<lambda>_::unit. Pair_Term (Payload_Term []) (Payload_Term [])"])
    apply (simp add: recognizer_schema_def schema_variables_def octets_formed_def)
    done
  show ?thesis using original
    by (simp add: schema_rule_instance_valuation schema_substitute_def recognizer_schema_def)
qed

text \<open>
  Substitution acts only on variable occurrences. It retains every prospective
  socket, callee, and material socket, including repeated arguments at different
  sockets. All five material operands undergo the same substitution. Identity,
  composition, scope, formation, and valuation laws use that one operation;
  the existing coordinate renamings are its variable-only specializations.

  A substituted rule specializes the original rule for every later valuation
  and support set. Equality requires a further argument. Complete valuation
  coverage is sufficient, and injective variable renaming supplies it. Replacing
  a variable by one literal can lose instances. These rule-level conclusions
  keep material satisfaction; admission into a program also retains its head
  and every prospective-call interface.
\<close>

end
