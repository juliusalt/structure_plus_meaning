theory Factor_Positive_Parametricity
  imports Factor_Positive_Meaning
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

lemma pattern_instance_leaf_map:
  assumes inst: "pattern_instance V p t" and fixed: "\<forall>x\<in>pattern_leaves p. h x = x"
  shows "pattern_instance (map_binding_leaves h V) p (map_term_leaves h t)"
  using inst fixed
  by (induction rule: pattern_instance.induct)
     (auto simp: map_binding_leaves_def intro: rev_image_eqI pattern_instance.intros)

lemma pattern_accepts_leaf_map:
  assumes accepts: "pattern_accepts p t" and fixed: "\<forall>x\<in>pattern_leaves p. h x = x"
    and preserve: "leaf_map_formed h"
  shows "pattern_accepts p (map_term_leaves h t)"
proof -
  obtain V where bindings: "term_bindings_formed (pattern_variables p) V"
    and inst: "pattern_instance V p t" and formed: "term_formed t"
    using accepts by (auto simp: pattern_accepts_def)
  have mapped_bindings: "term_bindings_formed (pattern_variables p) (map_binding_leaves h V)"
    by (rule map_binding_leaves_formed[OF bindings preserve])
  have mapped_inst: "pattern_instance (map_binding_leaves h V) p (map_term_leaves h t)"
    by (rule pattern_instance_leaf_map[OF inst fixed])
  show ?thesis using mapped_bindings mapped_inst map_term_leaves_formed[OF preserve formed]
    unfolding pattern_accepts_def by blast
qed

lemma map_premise_leaves_domain [simp]:
  "rel_dom (map_premise_leaves h Q) = rel_dom Q"
  using pair_image_domain[of id "\<lambda>(d,t). (d,map_term_leaves h t)" Q]
  by (simp add: map_premise_leaves_def case_prod_unfold)

lemma map_premise_leaves_single_valued:
  assumes "single_valued Q"
  shows "single_valued (map_premise_leaves h Q)"
  using single_valued_pair_image[OF assms, of id "\<lambda>(d,t). (d,map_term_leaves h t)"]
  by (simp add: map_premise_leaves_def case_prod_unfold)

lemma schema_premise_instance_leaf_map:
  assumes inst: "schema_premise_instance S V Q"
    and fixed: "\<forall>x\<in>schema_leaves S. h x = x"
  shows "schema_premise_instance S (map_binding_leaves h V) (map_premise_leaves h Q)"
proof -
  have finite: "finite Q" and sv: "single_valued Q"
    and domain: "rel_dom Q = rel_dom (schema_premises S)"
    using inst by (auto simp: schema_premise_instance_def)
  have each: "\<And>s d p. (s,d,p) \<in> schema_premises S \<Longrightarrow>
    \<exists>t. (s,d,t) \<in> map_premise_leaves h Q \<and> pattern_instance (map_binding_leaves h V) p t"
  proof -
    fix s d p assume member: "(s,d,p) \<in> schema_premises S"
    obtain t where premise: "(s,d,t) \<in> Q" and match: "pattern_instance V p t"
      using inst member unfolding schema_premise_instance_def by blast
    have literals: "\<forall>x\<in>pattern_leaves p. h x = x"
      using fixed member by (auto simp: schema_leaves_def)
    have mapped: "pattern_instance (map_binding_leaves h V) p (map_term_leaves h t)"
      by (rule pattern_instance_leaf_map[OF match literals])
    have present: "(s,d,map_term_leaves h t) \<in> map_premise_leaves h Q"
      using premise by (auto simp: map_premise_leaves_def intro: rev_image_eqI)
    show "\<exists>t. (s,d,t) \<in> map_premise_leaves h Q \<and>
      pattern_instance (map_binding_leaves h V) p t"
      using mapped present by blast
  qed
  have mapped_finite: "finite (map_premise_leaves h Q)"
    using finite by (simp add: map_premise_leaves_def)
  have mapped_sv: "single_valued (map_premise_leaves h Q)"
    by (rule map_premise_leaves_single_valued[OF sv])
  have mapped_domain: "rel_dom (map_premise_leaves h Q) = rel_dom (schema_premises S)"
    using domain by simp
  show ?thesis using mapped_finite mapped_sv mapped_domain each
    unfolding schema_premise_instance_def by blast
qed

lemma schema_instance_leaf_map:
  assumes inst: "schema_instance S V t Q" and fixed: "\<forall>x\<in>schema_leaves S. h x = x"
    and preserve: "leaf_map_formed h"
  shows "schema_instance S (map_binding_leaves h V) (map_term_leaves h t) (map_premise_leaves h Q)"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have literals: "\<forall>x\<in>pattern_leaves (schema_conclusion S). h x = x"
    using fixed by (auto simp: schema_leaves_def)
  show ?thesis using sf map_binding_leaves_formed[OF bindings preserve]
    pattern_instance_leaf_map[OF head literals] schema_premise_instance_leaf_map[OF body fixed]
    by (simp add: schema_instance_def)
qed

lemma schema_call_leaf_map:
  assumes call: "schema_call_formed P d t" and fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
  shows "schema_call_formed P d (map_term_leaves h t)"
proof -
  obtain p where pf: "schema_system_formed P" and interface: "(d,p) \<in> system_interfaces P"
    and accepts: "pattern_accepts p t"
    using call by (auto simp: schema_call_formed_def)
  have literals: "\<forall>x\<in>pattern_leaves p. h x = x"
    using fixed interface by (auto simp: system_leaves_def)
  show ?thesis using pf interface pattern_accepts_leaf_map[OF accepts literals preserve]
    unfolding schema_call_formed_def by blast
qed

lemma admitted_instance_leaf_map:
  assumes inst: "admitted_schema_instance P d c V t Q"
    and fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
    and free: "system_observation_free P"
  shows "admitted_schema_instance P d c (map_binding_leaves h V)
    (map_term_leaves h t) (map_premise_leaves h Q)"
proof -
  obtain S where head: "schema_call_formed P d t" and clause: "((d,c),S) \<in> system_clauses P"
    and schema: "schema_instance S V t Q"
    and calls: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> schema_call_formed P e x"
    using inst by (auto simp: admitted_schema_instance_def)
  have literals: "\<forall>x\<in>schema_leaves S. h x = x"
    using fixed clause by (auto simp: system_leaves_def)
  have mapped_head: "schema_call_formed P d (map_term_leaves h t)"
    by (rule schema_call_leaf_map[OF head fixed preserve])
  have mapped_schema: "schema_instance S (map_binding_leaves h V)
    (map_term_leaves h t) (map_premise_leaves h Q)"
    by (rule schema_instance_leaf_map[OF schema literals preserve])
  have mapped_calls: "\<forall>s e x. (s,e,x) \<in> map_premise_leaves h Q \<longrightarrow> schema_call_formed P e x"
    using calls schema_call_leaf_map[OF _ fixed preserve]
    by (auto simp: map_premise_leaves_def)
  have empty: "schema_material_premises S = {}" using free clause by (auto simp: system_observation_free_def)
  have material: "schema_material_satisfied S (map_binding_leaves h V)"
    by (rule empty_schema_material_satisfied[OF empty])
  show ?thesis using mapped_head clause mapped_schema mapped_calls material
    unfolding admitted_schema_instance_def by blast
qed

theorem positive_meaning_leaf_map:
  assumes fixed: "\<forall>x\<in>system_leaves P. h x = x"
    and preserve: "leaf_map_formed h"
    and free: "system_observation_free P"
    and holds: "(d,t) \<in> positive_meaning P"
  shows "(d,map_term_leaves h t) \<in> positive_meaning P"
proof -
  let ?X = "{(d,t). (d,map_term_leaves h t) \<in> positive_meaning P}"
  have stable: "schema_consequences P ?X \<subseteq> ?X"
  proof
    fix call assume step: "call \<in> schema_consequences P ?X"
    obtain d t where shape: "call = (d,t)" by (cases call)
    obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
      and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> ?X"
      using step by (auto simp: shape schema_consequences_def)
    have mapped: "admitted_schema_instance P d c (map_binding_leaves h V)
      (map_term_leaves h t) (map_premise_leaves h Q)"
      by (rule admitted_instance_leaf_map[OF inst fixed preserve free])
    have children: "\<forall>s e x. (s,e,x) \<in> map_premise_leaves h Q \<longrightarrow> (e,x) \<in> positive_meaning P"
      using support by (auto simp: map_premise_leaves_def)
    have result: "(d,map_term_leaves h t) \<in> positive_meaning P"
      by (rule positive_meaning_step[OF mapped children])
    show "call \<in> ?X" using result by (simp add: shape)
  qed
  show ?thesis using positive_meaning_least[OF stable] holds by blast
qed

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
