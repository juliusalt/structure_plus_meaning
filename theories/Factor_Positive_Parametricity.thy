theory Factor_Positive_Parametricity
  imports Factor_Pattern_Programs
begin

section \<open>Literal leaves in a finite positive program\<close>

text \<open>
  The leaves of a term are its targets and its payloads. A pattern meets a leaf in two ways: a
  variable accepts every formed term, and a literal accepts exactly the leaf it states. The leaves a
  program states literally are therefore the only leaves it can tell apart from others, and targets
  and payloads are the two kinds of leaf, so one argument serves both: the targets a program states
  are the exact values it reads, and the payloads it states are exactly the octets it reads as
  structure. An octet the program does not state is only ever compared for equality, through a
  variable that occurs twice.
\<close>

fun pattern_leaves :: "'a term_pattern \<Rightarrow> factor_term set" where
  "pattern_leaves (Pattern_Variable a) = {}"
| "pattern_leaves (Pattern_Target t) = {Target_Term t}"
| "pattern_leaves (Pattern_Payload v) = {Payload_Term v}"
| "pattern_leaves (Pattern_Pair p q) = pattern_leaves p \<union> pattern_leaves q"

lemma pattern_leaves_finite [simp]: "finite (pattern_leaves p)"
  by (induction p) auto

definition material_leaves :: "'a material_pattern \<Rightarrow> factor_term set" where
  "material_leaves M = (\<Union>p\<in>set (material_fields M). pattern_leaves p)"

lemma material_leaves_finite [simp]: "finite (material_leaves M)"
  by (simp add: material_leaves_def)

definition schema_leaves :: "('a,'s,'d) factor_schema \<Rightarrow> factor_term set" where
  "schema_leaves S = pattern_leaves (schema_conclusion S) \<union>
    (\<Union>(s,d,p)\<in>schema_premises S. pattern_leaves p) \<union>
    (\<Union>(s,M)\<in>schema_material_premises S. material_leaves M)"

definition system_leaves :: "('a,'s,'d,'c) schema_system \<Rightarrow> factor_term set" where
  "system_leaves P = (\<Union>(d,p)\<in>system_interfaces P. pattern_leaves p) \<union>
    (\<Union>(dc,S)\<in>system_clauses P. schema_leaves S)"

lemma schema_leaves_finite:
  assumes "schema_formed S"
  shows "finite (schema_leaves S)"
proof -
  have fin: "finite (schema_premises S)" using assms by (simp add: schema_formed_def)
  have calls: "finite (\<Union>(s,d,p)\<in>schema_premises S. pattern_leaves p)"
    by (rule finite_UN_I[OF fin]) (auto split: prod.splits)
  have finM: "finite (schema_material_premises S)" using assms by (simp add: schema_formed_def)
  have mats: "finite (\<Union>(s,M)\<in>schema_material_premises S. material_leaves M)"
    by (rule finite_UN_I[OF finM]) (auto split: prod.splits)
  show ?thesis using calls mats by (simp add: schema_leaves_def)
qed

lemma system_leaves_finite:
  assumes "schema_system_formed P"
  shows "finite (system_leaves P)"
proof -
  have interfaces: "finite (system_interfaces P)" and clauses: "finite (system_clauses P)"
    and each: "\<And>d c S. ((d,c),S) \<in> system_clauses P \<Longrightarrow> schema_formed S"
    using assms by (auto simp: schema_system_formed_def)
  have first: "finite (\<Union>(d,p)\<in>system_interfaces P. pattern_leaves p)"
    by (rule finite_UN_I[OF interfaces]) (auto split: prod.splits)
  have second: "finite (\<Union>(dc,S)\<in>system_clauses P. schema_leaves S)"
    by (rule finite_UN_I[OF clauses]) (auto split: prod.splits intro: schema_leaves_finite each)
  show ?thesis using first second by (simp add: system_leaves_def)
qed

text \<open>
  The two kinds of leaf are read from the one set of literal leaves: the targets a program states
  and the payloads it states.
\<close>

definition system_targets :: "('a,'s,'d,'c) schema_system \<Rightarrow> exact_target set" where
  "system_targets P = {t. Target_Term t \<in> system_leaves P}"

definition system_payloads :: "('a,'s,'d,'c) schema_system \<Rightarrow> octets set" where
  "system_payloads P = {v. Payload_Term v \<in> system_leaves P}"

lemma system_targets_finite:
  assumes "schema_system_formed P"
  shows "finite (system_targets P)"
proof -
  have inj: "inj Target_Term" by (simp add: inj_def)
  have "system_targets P = Target_Term -` system_leaves P" by (auto simp: system_targets_def)
  then show ?thesis using finite_vimageI[OF system_leaves_finite[OF assms] inj] by simp
qed

lemma system_payloads_finite:
  assumes "schema_system_formed P"
  shows "finite (system_payloads P)"
proof -
  have inj: "inj Payload_Term" by (simp add: inj_def)
  have "system_payloads P = Payload_Term -` system_leaves P" by (auto simp: system_payloads_def)
  then show ?thesis using finite_vimageI[OF system_leaves_finite[OF assms] inj] by simp
qed

section \<open>Changing the leaves a program does not state\<close>

fun term_leaf :: "factor_term \<Rightarrow> bool" where
  "term_leaf (Target_Term t) = True"
| "term_leaf (Payload_Term v) = True"
| "term_leaf (Pair_Term x y) = False"

fun map_term_leaves :: "(factor_term \<Rightarrow> factor_term) \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "map_term_leaves h (Target_Term t) = h (Target_Term t)"
| "map_term_leaves h (Payload_Term v) = h (Payload_Term v)"
| "map_term_leaves h (Pair_Term x y) = Pair_Term (map_term_leaves h x) (map_term_leaves h y)"

lemma map_term_leaves_leaf:
  assumes "term_leaf x"
  shows "map_term_leaves h x = h x"
  using assms by (cases x) auto

definition leaf_map_formed :: "(factor_term \<Rightarrow> factor_term) \<Rightarrow> bool" where
  "leaf_map_formed h \<longleftrightarrow> (\<forall>t. target_formed t \<longrightarrow> term_formed (h (Target_Term t))) \<and>
    (\<forall>v. octets_formed v \<longrightarrow> term_formed (h (Payload_Term v)))"

definition map_binding_leaves ::
  "(factor_term \<Rightarrow> factor_term) \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow> ('a \<times> factor_term) set" where
  "map_binding_leaves h V = (\<lambda>(a,t). (a,map_term_leaves h t)) ` V"

definition map_premise_leaves ::
  "(factor_term \<Rightarrow> factor_term) \<Rightarrow> ('s \<times> ('d \<times> factor_term)) set \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set" where
  "map_premise_leaves h Q = (\<lambda>(s,d,t). (s,d,map_term_leaves h t)) ` Q"

lemma map_term_leaves_formed:
  assumes preserve: "leaf_map_formed h" and formed: "term_formed t"
  shows "term_formed (map_term_leaves h t)"
  using formed preserve by (induction t) (auto simp: leaf_map_formed_def)

lemma map_binding_leaves_domain [simp]:
  "rel_dom (map_binding_leaves h V) = rel_dom V"
  using pair_image_domain[of id "map_term_leaves h" V]
  by (simp add: map_binding_leaves_def)

lemma map_binding_leaves_formed:
  assumes bindings: "term_bindings_formed B V" and preserve: "leaf_map_formed h"
  shows "term_bindings_formed B (map_binding_leaves h V)"
proof -
  have sv: "single_valued V" using bindings by (simp add: term_bindings_formed_def)
  have mapped: "single_valued (map_binding_leaves h V)"
    using single_valued_pair_image[OF sv, of id "map_term_leaves h"]
    by (simp add: map_binding_leaves_def)
  show ?thesis using bindings mapped map_term_leaves_formed[OF preserve]
    by (auto simp: term_bindings_formed_def map_binding_leaves_def rel_dom_def)
qed

section \<open>The leaf map of a program\<close>

text \<open>
  A leaf map acts on a program as it acts on the program's arguments: each literal leaf of a pattern becomes the
  exact pattern of the leaf's image (@{const exact_term_pattern}), and every variable, socket, callee, clause key
  and definition is kept. A positive consequence of an observation-free program then carries to the mapped program
  at the mapped argument, whatever the map does to the program's own leaves. A map fixing those leaves leaves the
  program as it is: the fixed-program facts are that case, each proved from the one argument below.
\<close>

fun map_pattern_leaves :: "(factor_term \<Rightarrow> factor_term) \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "map_pattern_leaves h (Pattern_Variable a)=Pattern_Variable a"
| "map_pattern_leaves h (Pattern_Target t)=exact_term_pattern (h (Target_Term t))"
| "map_pattern_leaves h (Pattern_Payload v)=exact_term_pattern (h (Payload_Term v))"
| "map_pattern_leaves h (Pattern_Pair p q)=Pattern_Pair (map_pattern_leaves h p) (map_pattern_leaves h q)"

definition map_material_leaves ::
  "(factor_term \<Rightarrow> factor_term) \<Rightarrow> 'a material_pattern \<Rightarrow> 'a material_pattern" where
  "map_material_leaves h M=\<lparr>material_source=map_pattern_leaves h (material_source M),
    material_atoms=map_pattern_leaves h (material_atoms M), material_edges=map_pattern_leaves h (material_edges M),
    material_counts=map_pattern_leaves h (material_counts M),
    material_functions=map_pattern_leaves h (material_functions M)\<rparr>"

definition map_schema_leaves ::
  "(factor_term \<Rightarrow> factor_term) \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow> ('a,'s,'d) factor_schema" where
  "map_schema_leaves h S=\<lparr>schema_conclusion=map_pattern_leaves h (schema_conclusion S),
    schema_premises=map_relation_values (map_prod id (map_pattern_leaves h)) (schema_premises S),
    schema_material_premises=map_relation_values (map_material_leaves h) (schema_material_premises S)\<rparr>"

definition map_system_leaves ::
  "(factor_term \<Rightarrow> factor_term) \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system" where
  "map_system_leaves h P=\<lparr>system_interfaces=map_relation_values (map_pattern_leaves h) (system_interfaces P),
    system_clauses=map_relation_values (map_schema_leaves h) (system_clauses P)\<rparr>"

text \<open>
  The leaf maps of material patterns and schemas are the maps of their patterns (@{const map_material_patterns},
  @{const map_schema_patterns}) at the leaf map of patterns; their laws are those maps' laws at it.
\<close>

lemma map_material_leaves_patterns: "map_material_leaves h=map_material_patterns (map_pattern_leaves h)"
  by (rule ext) (simp add: map_material_leaves_def map_material_patterns_def)

lemma map_schema_leaves_patterns: "map_schema_leaves h=map_schema_patterns (map_pattern_leaves h)"
  by (rule ext) (simp add: map_schema_leaves_def map_schema_patterns_def map_material_leaves_patterns)

text \<open>The map of patterns and the map of terms agree on the exact pattern of a term.\<close>

lemma map_pattern_leaves_exact:
  "map_pattern_leaves h (exact_term_pattern t)=exact_term_pattern (map_term_leaves h t)"
  by (induction t) simp_all

lemma map_material_leaves_fields [simp]:
  "material_fields (map_material_leaves h M)=map (map_pattern_leaves h) (material_fields M)"
  by (simp only: map_material_leaves_patterns map_material_patterns_fields)

lemma map_schema_leaves_fields [simp]:
  "schema_conclusion (map_schema_leaves h S)=map_pattern_leaves h (schema_conclusion S)"
  "schema_premises (map_schema_leaves h S)=map_relation_values (map_prod id (map_pattern_leaves h)) (schema_premises S)"
  "schema_material_premises (map_schema_leaves h S)=map_relation_values (map_material_leaves h) (schema_material_premises S)"
  by (simp_all add: map_schema_leaves_patterns map_material_leaves_patterns)

lemma map_system_leaves_fields [simp]:
  "system_interfaces (map_system_leaves h P)=map_relation_values (map_pattern_leaves h) (system_interfaces P)"
  "system_clauses (map_system_leaves h P)=map_relation_values (map_schema_leaves h) (system_clauses P)"
  by (simp_all add: map_system_leaves_def)

lemma map_schema_premises_member:
  "(s,d,q)\<in>schema_premises (map_schema_leaves h S) \<longleftrightarrow>
    (\<exists>p. (s,d,p)\<in>schema_premises S \<and> q=map_pattern_leaves h p)"
  by (auto simp: split_paired_Ex)

subsection \<open>What the map keeps\<close>

lemma map_pattern_leaves_variables [simp]: "pattern_variables (map_pattern_leaves h p)=pattern_variables p"
  by (induction p) simp_all

lemma map_material_leaves_variables [simp]: "material_variables (map_material_leaves h M)=material_variables M"
  by (simp add: material_variables_def)

lemma map_schema_leaves_variables [simp]: "schema_variables (map_schema_leaves h S)=schema_variables S"
proof -
  have "schema_variables (map_schema_patterns (map_pattern_leaves h) S)=(\<Union>a\<in>schema_variables S. {a})"
    by (rule map_schema_patterns_variables) simp
  then show ?thesis by (simp add: map_schema_leaves_patterns)
qed

lemma map_schema_leaves_sockets:
  "rel_dom (schema_premises (map_schema_leaves h S))=rel_dom (schema_premises S)"
  "rel_dom (schema_material_premises (map_schema_leaves h S))=rel_dom (schema_material_premises S)"
  by simp_all

lemma map_schema_leaves_dependencies [simp]: "schema_dependencies (map_schema_leaves h S)=schema_dependencies S"
  by (simp add: map_schema_leaves_patterns)

lemma map_system_leaves_definitions [simp]: "system_definitions (map_system_leaves h P)=system_definitions P"
  by (simp add: system_definitions_def)

lemma map_system_clauses_member:
  "((d,c),T)\<in>system_clauses (map_system_leaves h P) \<longleftrightarrow>
    (\<exists>S. ((d,c),S)\<in>system_clauses P \<and> T=map_schema_leaves h S)"
  by simp

lemma map_system_leaves_dependency_edges [simp]:
  "system_dependency_edges (map_system_leaves h P)=system_dependency_edges P"
proof -
  have "(d,e)\<in>system_dependency_edges (map_system_leaves h P) \<longleftrightarrow> (d,e)\<in>system_dependency_edges P" for d e
  proof
    assume "(d,e)\<in>system_dependency_edges (map_system_leaves h P)"
    then have "\<exists>c T. ((d,c),T)\<in>system_clauses (map_system_leaves h P) \<and> e\<in>schema_dependencies T"
      by (simp only: system_dependency_edges_def mem_Collect_eq case_prod_conv)
    then obtain c T where clause: "((d,c),T)\<in>system_clauses (map_system_leaves h P)"
      and dep: "e\<in>schema_dependencies T" by blast
    obtain S where source: "((d,c),S)\<in>system_clauses P" and T: "T=map_schema_leaves h S"
      using clause unfolding map_system_clauses_member by blast
    have "e\<in>schema_dependencies S" using dep T by simp
    then show "(d,e)\<in>system_dependency_edges P"
      unfolding system_dependency_edges_def using source by blast
  next
    assume "(d,e)\<in>system_dependency_edges P"
    then have "\<exists>c S. ((d,c),S)\<in>system_clauses P \<and> e\<in>schema_dependencies S"
      by (simp only: system_dependency_edges_def mem_Collect_eq case_prod_conv)
    then obtain c S where source: "((d,c),S)\<in>system_clauses P"
      and dep: "e\<in>schema_dependencies S" by blast
    have clause: "((d,c),map_schema_leaves h S)\<in>system_clauses (map_system_leaves h P)"
      unfolding map_system_clauses_member using source by blast
    have "e\<in>schema_dependencies (map_schema_leaves h S)" using dep by simp
    then show "(d,e)\<in>system_dependency_edges (map_system_leaves h P)"
      unfolding system_dependency_edges_def using clause by blast
  qed
  then show ?thesis by auto
qed


lemma map_pattern_leaves_fixed:
  assumes "\<forall>x\<in>pattern_leaves p. h x=x"
  shows "map_pattern_leaves h p=p"
  using assms by (induction p) simp_all

lemma map_material_leaves_fixed:
  assumes fixed: "\<forall>x\<in>material_leaves M. h x=x"
  shows "map_material_leaves h M=M"
  unfolding map_material_leaves_patterns
  by (rule map_material_patterns_ident) (use fixed in \<open>auto simp: material_leaves_def intro: map_pattern_leaves_fixed\<close>)

lemma map_schema_leaves_fixed:
  assumes fixed: "\<forall>x\<in>schema_leaves S. h x=x"
  shows "map_schema_leaves h S=S"
  unfolding map_schema_leaves_patterns
proof (rule map_schema_patterns_ident)
  show "map_pattern_leaves h (schema_conclusion S)=schema_conclusion S"
    using fixed by (simp add: schema_leaves_def map_pattern_leaves_fixed)
  show "map_pattern_leaves h p=p" if member: "(s,d,p)\<in>schema_premises S" for s d p
    by (rule map_pattern_leaves_fixed) (use fixed member in \<open>auto simp: schema_leaves_def\<close>)
  show "map_pattern_leaves h p=p"
    if member: "(s,M)\<in>schema_material_premises S" and field: "p\<in>set (material_fields M)" for s M p
    by (rule map_pattern_leaves_fixed)
      (use fixed member field in \<open>auto simp: schema_leaves_def material_leaves_def\<close>)
qed

lemma map_system_leaves_fixed:
  assumes fixed: "\<forall>x\<in>system_leaves P. h x=x"
  shows "map_system_leaves h P=P"
proof (rule schema_system.equality)
  have interface: "map_pattern_leaves h p=p" if member: "(d,p)\<in>system_interfaces P" for d p
  proof (rule map_pattern_leaves_fixed)
    show "\<forall>x\<in>pattern_leaves p. h x=x" using fixed member by (auto simp: system_leaves_def)
  qed
  show "system_interfaces (map_system_leaves h P)=system_interfaces P"
    by (simp add: map_relation_values_fixed interface)
  have clause: "map_schema_leaves h S=S" if member: "(k,S)\<in>system_clauses P" for k S
  proof (rule map_schema_leaves_fixed)
    show "\<forall>x\<in>schema_leaves S. h x=x" using fixed member by (auto simp: system_leaves_def)
  qed
  show "system_clauses (map_system_leaves h P)=system_clauses P"
    by (simp add: map_relation_values_fixed clause)
qed simp

subsection \<open>Formation under a formation-preserving map\<close>

lemma pattern_leaves_leaf: "x\<in>pattern_leaves p \<Longrightarrow> term_leaf x"
  by (induction p) auto

lemma material_leaves_leaf: "x\<in>material_leaves M \<Longrightarrow> term_leaf x"
  by (auto simp: material_leaves_def intro: pattern_leaves_leaf)

lemma schema_leaves_leaf: "x\<in>schema_leaves S \<Longrightarrow> term_leaf x"
  by (auto simp: schema_leaves_def split: prod.splits intro: pattern_leaves_leaf material_leaves_leaf)

lemma leaf_map_formed_leaf:
  assumes "leaf_map_formed h" "term_leaf x" "term_formed x"
  shows "term_formed (h x)"
  using assms by (cases x) (auto simp: leaf_map_formed_def)

lemma map_pattern_leaves_formed:
  assumes "pattern_formed p" "leaf_map_formed h"
  shows "pattern_formed (map_pattern_leaves h p)"
  using assms by (induction p) (auto simp: leaf_map_formed_def)

lemma map_material_leaves_formed:
  assumes "material_pattern_formed M" "leaf_map_formed h"
  shows "material_pattern_formed (map_material_leaves h M)"
  using assms by (auto simp: material_pattern_formed_def intro: map_pattern_leaves_formed)

lemma map_schema_leaves_formed:
  assumes formed: "schema_formed S" and preserve: "leaf_map_formed h"
  shows "schema_formed (map_schema_leaves h S)"
  unfolding map_schema_leaves_patterns
  by (rule map_schema_patterns_formed[OF formed]) (rule map_pattern_leaves_formed[OF _ preserve])

lemma map_system_leaves_formed:
  assumes formed: "schema_system_formed P" and preserve: "leaf_map_formed h"
  shows "schema_system_formed (map_system_leaves h P)"
proof -
  have sv: "single_valued (system_interfaces P)" "single_valued (system_clauses P)"
    using formed by (simp_all add: schema_system_formed_def)
  have fin: "finite (system_interfaces (map_system_leaves h P))" "finite (system_clauses (map_system_leaves h P))"
    using formed by (simp_all add: schema_system_formed_def)
  have sv': "single_valued (system_interfaces (map_system_leaves h P))"
    "single_valued (system_clauses (map_system_leaves h P))"
    using map_relation_values_single_valued[OF sv(1)] map_relation_values_single_valued[OF sv(2)] by simp_all
  have interfaces: "\<forall>d p. (d,p)\<in>system_interfaces (map_system_leaves h P) \<longrightarrow> pattern_formed p"
    using formed by (auto simp: schema_system_formed_def intro: map_pattern_leaves_formed[OF _ preserve])
  have clauses: "\<forall>d c S. ((d,c),S)\<in>system_clauses (map_system_leaves h P) \<longrightarrow>
      d\<in>system_definitions P \<and> schema_formed S \<and> schema_dependencies S\<subseteq>system_definitions P"
  proof (intro allI impI)
    fix d c S assume "((d,c),S)\<in>system_clauses (map_system_leaves h P)"
    then obtain S0 where clause: "((d,c),S0)\<in>system_clauses P" and S: "S=map_schema_leaves h S0"
      unfolding map_system_clauses_member by blast
    have "d\<in>system_definitions P \<and> schema_formed S0 \<and> schema_dependencies S0\<subseteq>system_definitions P"
      using formed clause unfolding schema_system_formed_def by blast
    then show "d\<in>system_definitions P \<and> schema_formed S \<and> schema_dependencies S\<subseteq>system_definitions P"
      using S map_schema_leaves_formed[OF _ preserve] by auto
  qed
  show ?thesis unfolding schema_system_formed_def map_system_leaves_definitions
    using fin sv' interfaces clauses by blast
qed

subsection \<open>Pattern instances and acceptance carried forward\<close>

text \<open>
  A pattern instance carries forward wherever the map keeps the program's leaves formed: a formation-preserving
  map does, and so does a map fixing them.
\<close>

lemma pattern_instance_mapped:
  assumes inst: "pattern_instance V p t"
    and leaves: "\<And>x. x\<in>pattern_leaves p \<Longrightarrow> term_formed x \<Longrightarrow> term_formed (h x)"
  shows "pattern_instance (map_binding_leaves h V) (map_pattern_leaves h p) (map_term_leaves h t)"
  using inst leaves
proof (induction rule: pattern_instance.induct)
  case (variable a t)
  then show ?case by (auto simp: map_binding_leaves_def intro: rev_image_eqI pattern_instance.variable)
next
  case (target t)
  then show ?case by simp
next
  case (payload v)
  then show ?case by simp
next
  case (pair p x q y)
  then show ?case by auto
qed

lemma pattern_instance_leaf_map:
  assumes inst: "pattern_instance V p t" and fixed: "\<forall>x\<in>pattern_leaves p. h x = x"
  shows "pattern_instance (map_binding_leaves h V) p (map_term_leaves h t)"
proof -
  have "pattern_instance (map_binding_leaves h V) (map_pattern_leaves h p) (map_term_leaves h t)"
    by (rule pattern_instance_mapped[OF inst]) (use fixed in auto)
  then show ?thesis by (simp only: map_pattern_leaves_fixed[OF fixed])
qed

lemma pattern_accepts_mapped:
  assumes accepts: "pattern_accepts p t" and preserve: "leaf_map_formed h"
  shows "pattern_accepts (map_pattern_leaves h p) (map_term_leaves h t)"
proof -
  obtain V where bindings: "term_bindings_formed (pattern_variables p) V"
    and inst: "pattern_instance V p t" and formed: "term_formed t"
    using accepts by (auto simp: pattern_accepts_def)
  have mapped: "pattern_instance (map_binding_leaves h V) (map_pattern_leaves h p) (map_term_leaves h t)"
    by (rule pattern_instance_mapped[OF inst]) (auto intro: leaf_map_formed_leaf[OF preserve] pattern_leaves_leaf)
  show ?thesis using map_binding_leaves_formed[OF bindings preserve] mapped map_term_leaves_formed[OF preserve formed]
    unfolding pattern_accepts_def by auto
qed

lemma pattern_accepts_leaf_map:
  assumes accepts: "pattern_accepts p t" and fixed: "\<forall>x\<in>pattern_leaves p. h x = x"
    and preserve: "leaf_map_formed h"
  shows "pattern_accepts p (map_term_leaves h t)"
  using pattern_accepts_mapped[OF accepts preserve] by (simp only: map_pattern_leaves_fixed[OF fixed])

lemma map_premise_leaves_domain [simp]:
  "rel_dom (map_premise_leaves h Q) = rel_dom Q"
  using pair_image_domain[of id "\<lambda>(d,t). (d,map_term_leaves h t)" Q]
  by (simp add: map_premise_leaves_def case_prod_unfold)

lemma map_premise_leaves_single_valued:
  assumes "single_valued Q"
  shows "single_valued (map_premise_leaves h Q)"
  using single_valued_pair_image[OF assms, of id "\<lambda>(d,t). (d,map_term_leaves h t)"]
  by (simp add: map_premise_leaves_def case_prod_unfold)

subsection \<open>Schema instances, calls and admitted instances carried forward\<close>

lemma schema_premise_instance_mapped:
  assumes inst: "schema_premise_instance S V Q"
    and leaves: "\<And>x. x\<in>schema_leaves S \<Longrightarrow> term_formed x \<Longrightarrow> term_formed (h x)"
  shows "schema_premise_instance (map_schema_leaves h S) (map_binding_leaves h V) (map_premise_leaves h Q)"
proof -
  have finite: "finite Q" and sv: "single_valued Q"
    and domain: "rel_dom Q = rel_dom (schema_premises S)"
    using inst by (auto simp: schema_premise_instance_def)
  have each: "\<exists>t. (s,d,t) \<in> map_premise_leaves h Q \<and> pattern_instance (map_binding_leaves h V) q t"
    if member: "(s,d,q) \<in> schema_premises (map_schema_leaves h S)" for s d q
  proof -
    obtain p where source: "(s,d,p)\<in>schema_premises S" and mapped_pattern: "q=map_pattern_leaves h p"
      using member by (auto simp: map_schema_premises_member)
    obtain t where premise: "(s,d,t) \<in> Q" and match: "pattern_instance V p t"
      using inst source unfolding schema_premise_instance_def by blast
    have mapped: "pattern_instance (map_binding_leaves h V) q (map_term_leaves h t)"
      unfolding mapped_pattern
      by (rule pattern_instance_mapped[OF match], rule leaves)
         (use source in \<open>auto simp: schema_leaves_def\<close>)
    have present: "(s,d,map_term_leaves h t) \<in> map_premise_leaves h Q"
      using premise by (auto simp: map_premise_leaves_def intro: rev_image_eqI)
    show ?thesis using mapped present by blast
  qed
  have mapped_finite: "finite (map_premise_leaves h Q)"
    using finite by (simp add: map_premise_leaves_def)
  have mapped_sv: "single_valued (map_premise_leaves h Q)"
    by (rule map_premise_leaves_single_valued[OF sv])
  have mapped_domain: "rel_dom (map_premise_leaves h Q) = rel_dom (schema_premises (map_schema_leaves h S))"
    using domain by simp
  show ?thesis using mapped_finite mapped_sv mapped_domain each
    unfolding schema_premise_instance_def by blast
qed

lemma schema_premise_instance_leaf_map:
  assumes inst: "schema_premise_instance S V Q"
    and fixed: "\<forall>x\<in>schema_leaves S. h x = x"
  shows "schema_premise_instance S (map_binding_leaves h V) (map_premise_leaves h Q)"
proof -
  have "schema_premise_instance (map_schema_leaves h S) (map_binding_leaves h V) (map_premise_leaves h Q)"
    by (rule schema_premise_instance_mapped[OF inst]) (use fixed in auto)
  then show ?thesis by (simp only: map_schema_leaves_fixed[OF fixed])
qed

lemma schema_instance_mapped:
  assumes inst: "schema_instance S V t Q" and preserve: "leaf_map_formed h"
  shows "schema_instance (map_schema_leaves h S) (map_binding_leaves h V) (map_term_leaves h t)
    (map_premise_leaves h Q)"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have mapped_head: "pattern_instance (map_binding_leaves h V) (map_pattern_leaves h (schema_conclusion S))
    (map_term_leaves h t)"
    by (rule pattern_instance_mapped[OF head]) (auto intro: leaf_map_formed_leaf[OF preserve] pattern_leaves_leaf)
  have mapped_body: "schema_premise_instance (map_schema_leaves h S) (map_binding_leaves h V) (map_premise_leaves h Q)"
    by (rule schema_premise_instance_mapped[OF body]) (auto intro: leaf_map_formed_leaf[OF preserve] schema_leaves_leaf)
  show ?thesis using map_schema_leaves_formed[OF sf preserve] map_binding_leaves_formed[OF bindings preserve]
    mapped_head mapped_body
    by (simp add: schema_instance_def)
qed

lemma schema_instance_leaf_map:
  assumes inst: "schema_instance S V t Q" and fixed: "\<forall>x\<in>schema_leaves S. h x = x"
    and preserve: "leaf_map_formed h"
  shows "schema_instance S (map_binding_leaves h V) (map_term_leaves h t) (map_premise_leaves h Q)"
  using schema_instance_mapped[OF inst preserve] by (simp only: map_schema_leaves_fixed[OF fixed])

lemma schema_call_mapped:
  assumes call: "schema_call_formed P d t" and preserve: "leaf_map_formed h"
  shows "schema_call_formed (map_system_leaves h P) d (map_term_leaves h t)"
proof -
  obtain p where pf: "schema_system_formed P" and interface: "(d,p) \<in> system_interfaces P"
    and accepts: "pattern_accepts p t"
    using call by (auto simp: schema_call_formed_def)
  have mapped: "(d,map_pattern_leaves h p)\<in>system_interfaces (map_system_leaves h P)"
    using interface by auto
  show ?thesis using map_system_leaves_formed[OF pf preserve] mapped pattern_accepts_mapped[OF accepts preserve]
    unfolding schema_call_formed_def by blast
qed

lemma schema_call_leaf_map:
  assumes call: "schema_call_formed P d t" and fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
  shows "schema_call_formed P d (map_term_leaves h t)"
  using schema_call_mapped[OF call preserve] by (simp only: map_system_leaves_fixed[OF fixed])

lemma admitted_instance_mapped:
  assumes inst: "admitted_schema_instance P d c V t Q"
    and preserve: "leaf_map_formed h"
    and free: "system_observation_free P"
  shows "admitted_schema_instance (map_system_leaves h P) d c (map_binding_leaves h V)
    (map_term_leaves h t) (map_premise_leaves h Q)"
proof -
  obtain S where head: "schema_call_formed P d t" and clause: "((d,c),S) \<in> system_clauses P"
    and schema: "schema_instance S V t Q"
    and calls: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> schema_call_formed P e x"
    using inst by (auto simp: admitted_schema_instance_def)
  have mapped_clause: "((d,c),map_schema_leaves h S)\<in>system_clauses (map_system_leaves h P)"
    using clause by auto
  have mapped_calls: "\<forall>s e x. (s,e,x) \<in> map_premise_leaves h Q \<longrightarrow>
    schema_call_formed (map_system_leaves h P) e x"
  proof (intro allI impI)
    fix s e x assume "(s,e,x) \<in> map_premise_leaves h Q"
    then obtain y where premise: "(s,e,y)\<in>Q" and x: "x=map_term_leaves h y"
      by (auto simp: map_premise_leaves_def)
    show "schema_call_formed (map_system_leaves h P) e x"
      unfolding x by (rule schema_call_mapped[OF _ preserve]) (use calls premise in blast)
  qed
  have empty: "schema_material_premises (map_schema_leaves h S) = {}"
    using free clause by (auto simp: system_observation_free_def)
  show ?thesis using schema_call_mapped[OF head preserve] mapped_clause schema_instance_mapped[OF schema preserve]
    mapped_calls empty_schema_material_satisfied[OF empty]
    unfolding admitted_schema_instance_def by blast
qed

lemma admitted_instance_leaf_map:
  assumes inst: "admitted_schema_instance P d c V t Q"
    and fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
    and free: "system_observation_free P"
  shows "admitted_schema_instance P d c (map_binding_leaves h V)
    (map_term_leaves h t) (map_premise_leaves h Q)"
  using admitted_instance_mapped[OF inst preserve free] by (simp only: map_system_leaves_fixed[OF fixed])

subsection \<open>Positive meaning carried forward\<close>

text \<open>
  One consequence step carries forward over any support relation: the support is mapped with the argument. The
  least fixed point of the source program then lies inside the mapped program's, read through the map.
\<close>

lemma schema_consequences_mapped:
  assumes step: "(d,t)\<in>schema_consequences P X"
    and preserve: "leaf_map_formed h" and free: "system_observation_free P"
  shows "(d,map_term_leaves h t)\<in>schema_consequences (map_system_leaves h P)
    (map_relation_values (map_term_leaves h) X)"
proof -
  obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
    and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> X"
    using step by (auto simp: schema_consequences_def)
  have children: "\<forall>s e x. (s,e,x) \<in> map_premise_leaves h Q \<longrightarrow> (e,x) \<in> map_relation_values (map_term_leaves h) X"
    using support by (auto simp: map_premise_leaves_def)
  show ?thesis unfolding schema_consequences_def
    using admitted_instance_mapped[OF inst preserve free] children by auto
qed

theorem positive_meaning_mapped:
  assumes holds: "(d,t)\<in>positive_meaning P"
    and preserve: "leaf_map_formed h" and free: "system_observation_free P"
  shows "(d,map_term_leaves h t)\<in>positive_meaning (map_system_leaves h P)"
proof -
  let ?Q = "map_system_leaves h P"
  let ?X = "{(d,t). (d,map_term_leaves h t) \<in> positive_meaning ?Q}"
  have closed: "schema_consequences ?Q (positive_meaning ?Q) \<subseteq> positive_meaning ?Q"
    by (rule equalityD1[OF positive_meaning_unfold[symmetric]])
  have support: "map_relation_values (map_term_leaves h) ?X \<subseteq> positive_meaning ?Q"
    by auto
  have stable: "schema_consequences P ?X \<subseteq> ?X"
  proof
    fix call assume step: "call \<in> schema_consequences P ?X"
    obtain e u where shape: "call = (e,u)" by (cases call)
    have mapped: "(e,map_term_leaves h u)\<in>schema_consequences ?Q (map_relation_values (map_term_leaves h) ?X)"
      by (rule schema_consequences_mapped[OF step[unfolded shape] preserve free])
    have "(e,map_term_leaves h u)\<in>positive_meaning ?Q"
      using monoD[OF schema_consequences_mono support] mapped closed by blast
    then show "call \<in> ?X" by (simp add: shape)
  qed
  show ?thesis using positive_meaning_least[OF stable] holds by blast
qed

theorem positive_meaning_leaf_map:
  assumes fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
    and free: "system_observation_free P"
    and holds: "(d,t) \<in> positive_meaning P"
  shows "(d,map_term_leaves h t) \<in> positive_meaning P"
  using positive_meaning_mapped[OF holds preserve free] by (simp only: map_system_leaves_fixed[OF fixed])

theorem positive_meaning_leaf_involution:
  assumes fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
    and inverse: "\<And>u. map_term_leaves h (map_term_leaves h u) = u"
    and free: "system_observation_free P"
  shows "(d,map_term_leaves h t) \<in> positive_meaning P \<longleftrightarrow> (d,t) \<in> positive_meaning P"
proof
  assume source: "(d,map_term_leaves h t) \<in> positive_meaning P"
  have "(d,map_term_leaves h (map_term_leaves h t)) \<in> positive_meaning P"
    by (rule positive_meaning_leaf_map[OF fixed preserve free source])
  then show "(d,t) \<in> positive_meaning P" by (simp only: inverse)
next
  assume source: "(d,t) \<in> positive_meaning P"
  show "(d,map_term_leaves h t) \<in> positive_meaning P"
    by (rule positive_meaning_leaf_map[OF fixed preserve free source])
qed

section \<open>Two leaves a program does not state cannot be told apart\<close>

definition swap_leaves :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "swap_leaves x y z = (if z=x then y else if z=y then x else z)"

lemma swap_leaves_involution:
  assumes "term_leaf x" "term_leaf y"
  shows "map_term_leaves (swap_leaves x y) (map_term_leaves (swap_leaves x y) t) = t"
proof (induction t)
  case (Target_Term s)
  have leaf: "term_leaf (swap_leaves x y (Target_Term s))"
    using assms by (auto simp: swap_leaves_def)
  show ?case using map_term_leaves_leaf[OF leaf] by (auto simp: swap_leaves_def)
next
  case (Payload_Term v)
  have leaf: "term_leaf (swap_leaves x y (Payload_Term v))"
    using assms by (auto simp: swap_leaves_def)
  show ?case using map_term_leaves_leaf[OF leaf] by (auto simp: swap_leaves_def)
next
  case (Pair_Term u w)
  then show ?case by simp
qed

lemma swap_leaves_formed:
  assumes "term_formed x" "term_formed y"
  shows "leaf_map_formed (swap_leaves x y)"
  using assms by (auto simp: leaf_map_formed_def swap_leaves_def)

theorem positive_meaning_unlisted_leaves:
  assumes leaves: "term_leaf x" "term_leaf y" and formed: "term_formed x" "term_formed y"
    and absent: "x \<notin> system_leaves P" "y \<notin> system_leaves P"
    and free: "system_observation_free P"
  shows "(d,x) \<in> positive_meaning P \<longleftrightarrow> (d,y) \<in> positive_meaning P"
proof -
  have fixed: "\<forall>z\<in>system_leaves P. swap_leaves x y z = z"
    using absent by (auto simp: swap_leaves_def)
  have invariant: "(d,map_term_leaves (swap_leaves x y) x) \<in> positive_meaning P \<longleftrightarrow>
    (d,x) \<in> positive_meaning P"
    by (rule positive_meaning_leaf_involution[OF fixed swap_leaves_formed[OF formed]
      swap_leaves_involution[OF leaves] free])
  have swapped: "map_term_leaves (swap_leaves x y) x = y"
    using map_term_leaves_leaf[OF leaves(1)] by (simp add: swap_leaves_def)
  show ?thesis using invariant by (simp add: swapped)
qed

text \<open>
  The two kinds of leaf are instances. Two targets a program does not state are indistinguishable
  to it, and so are two payloads it does not state: the payloads a program states literally are
  exactly the octets it reads as structure, and every other octet is inert to it.
\<close>

corollary positive_meaning_unlisted_targets:
  assumes af: "target_formed a" and bf: "target_formed b"
    and absent: "a \<notin> system_targets P" "b \<notin> system_targets P"
    and free: "system_observation_free P"
  shows "(d,Target_Term a) \<in> positive_meaning P \<longleftrightarrow>
    (d,Target_Term b) \<in> positive_meaning P"
  using absent by (intro positive_meaning_unlisted_leaves[OF _ _ _ _ _ _ free])
    (simp_all add: af bf system_targets_def)

corollary positive_meaning_unlisted_payloads:
  assumes af: "octets_formed a" and bf: "octets_formed b"
    and absent: "a \<notin> system_payloads P" "b \<notin> system_payloads P"
    and free: "system_observation_free P"
  shows "(d,Payload_Term a) \<in> positive_meaning P \<longleftrightarrow>
    (d,Payload_Term b) \<in> positive_meaning P"
  using absent by (intro positive_meaning_unlisted_leaves[OF _ _ _ _ _ _ free])
    (simp_all add: af bf system_payloads_def)

section \<open>A concrete structural observation is not definable in this class\<close>

lemma pattern_leaves_formed:
  assumes "pattern_formed p" "x \<in> pattern_leaves p"
  shows "term_formed x"
  using assms by (induction p) auto

lemma material_leaves_formed:
  assumes "material_pattern_formed M" "x \<in> material_leaves M"
  shows "term_formed x"
  using assms unfolding material_pattern_formed_def material_leaves_def
  by (blast intro: pattern_leaves_formed)

lemma schema_leaves_formed:
  assumes "schema_formed S" "x \<in> schema_leaves S"
  shows "term_formed x"
  using assms by (auto simp: schema_leaves_def schema_formed_def;
      blast intro: pattern_leaves_formed material_leaves_formed)

lemma system_leaves_formed:
  assumes "schema_system_formed P" "x \<in> system_leaves P"
  shows "term_formed x"
  using assms
  by (auto simp: system_leaves_def schema_system_formed_def;
      blast intro: pattern_leaves_formed schema_leaves_formed)

lemma system_targets_formed:
  assumes "schema_system_formed P" "a \<in> system_targets P"
  shows "target_formed a"
  using system_leaves_formed[OF assms(1), of "Target_Term a"] assms(2)
  by (simp add: system_targets_def)

lemma system_payloads_formed:
  assumes "schema_system_formed P" "v \<in> system_payloads P"
  shows "octets_formed v"
  using system_leaves_formed[OF assms(1), of "Payload_Term v"] assms(2)
  by (simp add: system_payloads_def)

definition isolated_artifact :: "local_address \<Rightarrow> exact_artifact" where
  "isolated_artifact a = \<lparr>object_structure = \<lparr>rra_carrier={a}, rra_incidence={}\<rparr>,
    object_data=empty_basis\<rparr>"

definition loop_artifact :: "local_address \<Rightarrow> exact_artifact" where
  "loop_artifact a = \<lparr>object_structure = \<lparr>rra_carrier={a}, rra_incidence={(a,a,a)}\<rparr>,
    object_data=empty_basis\<rparr>"

lemma isolated_artifact_formed:
  assumes "octets_formed a"
  shows "exact_formed (isolated_artifact a)"
  using assms by (simp add: isolated_artifact_def exact_formed_def object_formed_def rra_formed_def)

lemma loop_artifact_formed:
  assumes "octets_formed a"
  shows "exact_formed (loop_artifact a)"
  using assms by (simp add: loop_artifact_def exact_formed_def object_formed_def rra_formed_def)

theorem positive_program_cannot_distinguish_all_incidence:
  assumes pf: "schema_system_formed P"
    and free: "system_observation_free P"
  shows "\<exists>R S. exact_formed R \<and> exact_formed S \<and>
    rra_carrier (object_structure R) = rra_carrier (object_structure S) \<and> object_data R = object_data S \<and>
    rra_incidence (object_structure R) = {} \<and> rra_incidence (object_structure S) \<noteq> {} \<and>
    ((d,Target_Term (Whole_Artifact R)) \<in> positive_meaning P \<longleftrightarrow>
     (d,Target_Term (Whole_Artifact S)) \<in> positive_meaning P)"
proof -
  let ?U = "\<Union>t\<in>system_targets P. rra_carrier (object_structure (target_artifact t))"
  have each: "\<And>t. t \<in> system_targets P \<Longrightarrow>
    finite (rra_carrier (object_structure (target_artifact t)))"
    using system_targets_formed[OF pf] target_formed_artifact
    by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have finite: "finite ?U" by (rule finite_UN_I[OF system_targets_finite[OF pf]]) (rule each)
  let ?a = "fresh_address ?U"
  have fresh: "?a \<notin> ?U" by (rule fresh_address_not_in[OF finite])
  have absent_R: "Whole_Artifact (isolated_artifact ?a) \<notin> system_targets P"
  proof
    assume member: "Whole_Artifact (isolated_artifact ?a) \<in> system_targets P"
    have "?a \<in> rra_carrier (object_structure (target_artifact (Whole_Artifact (isolated_artifact ?a))))"
      by (simp add: isolated_artifact_def)
    then have "?a \<in> ?U" using member by blast
    then show False using fresh by blast
  qed
  have absent_S: "Whole_Artifact (loop_artifact ?a) \<notin> system_targets P"
  proof
    assume member: "Whole_Artifact (loop_artifact ?a) \<in> system_targets P"
    have "?a \<in> rra_carrier (object_structure (target_artifact (Whole_Artifact (loop_artifact ?a))))"
      by (simp add: loop_artifact_def)
    then have "?a \<in> ?U" using member by blast
    then show False using fresh by blast
  qed
  have rf: "exact_formed (isolated_artifact ?a)" by (rule isolated_artifact_formed) simp
  have sf: "exact_formed (loop_artifact ?a)" by (rule loop_artifact_formed) simp
  have rtf: "target_formed (Whole_Artifact (isolated_artifact ?a))" using rf by simp
  have stf: "target_formed (Whole_Artifact (loop_artifact ?a))" using sf by simp
  have same: "(d,Target_Term (Whole_Artifact (isolated_artifact ?a))) \<in> positive_meaning P \<longleftrightarrow>
    (d,Target_Term (Whole_Artifact (loop_artifact ?a))) \<in> positive_meaning P"
    by (rule positive_meaning_unlisted_targets[OF rtf stf absent_R absent_S free])
  show ?thesis
    by (rule exI[of _ "isolated_artifact ?a"], rule exI[of _ "loop_artifact ?a"])
       (use rf sf same in \<open>simp add: isolated_artifact_def loop_artifact_def\<close>)
qed

corollary positive_incidence_test_not_definable:
  assumes "schema_system_formed P" "system_observation_free P"
  shows "\<not> (\<forall>R. exact_formed R \<longrightarrow>
    ((d,Target_Term (Whole_Artifact R)) \<in> positive_meaning P \<longleftrightarrow>
      rra_incidence (object_structure R) \<noteq> {}))"
  using positive_program_cannot_distinguish_all_incidence[OF assms, of d] by blast

text \<open>
  These transformations are proof devices. They change ordinary argument
  values, leave definition and socket occurrences fixed, and are not an
  equality of exact artifacts or a permitted readdressing of an exact anchor.
  The result identifies an expressive limit of the subclass without material
  observations: the only leaf observations available in its patterns are
  formation and comparison with its finitely many literal leaves. For payloads
  this is the criterion by which a program's use of octets is audited: the
  payloads it states literally are the octets it reads as structure, and a
  payload it does not state is inert to it, compared at most for equality with
  another occurrence of the same variable.
\<close>

end
