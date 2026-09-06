theory Factor_Positive_Parametricity
  imports Factor_Positive_Meaning
begin

section \<open>Literal targets in a finite positive program\<close>

fun pattern_targets :: "'a term_pattern \<Rightarrow> exact_target set" where
  "pattern_targets (Pattern_Variable a) = {}"
| "pattern_targets (Pattern_Target t) = {t}"
| "pattern_targets (Pattern_Payload v) = {}"
| "pattern_targets (Pattern_Pair p q) = pattern_targets p \<union> pattern_targets q"

lemma pattern_targets_finite [simp]: "finite (pattern_targets p)"
  by (induction p) auto

definition material_targets :: "'a material_pattern \<Rightarrow> exact_target set" where
  "material_targets M = (\<Union>p\<in>set (material_fields M). pattern_targets p)"

lemma material_targets_finite [simp]: "finite (material_targets M)"
  by (simp add: material_targets_def)

definition schema_targets :: "('a,'s,'d) factor_schema \<Rightarrow> exact_target set" where
  "schema_targets S = pattern_targets (schema_conclusion S) \<union>
    (\<Union>(s,d,p)\<in>schema_premises S. pattern_targets p) \<union>
    (\<Union>(s,M)\<in>schema_material_premises S. material_targets M)"

definition system_targets :: "('a,'s,'d,'c) schema_system \<Rightarrow> exact_target set" where
  "system_targets P = (\<Union>(d,p)\<in>system_interfaces P. pattern_targets p) \<union>
    (\<Union>(dc,S)\<in>system_clauses P. schema_targets S)"

lemma schema_targets_finite:
  assumes "schema_formed S"
  shows "finite (schema_targets S)"
proof -
  have fin: "finite (schema_premises S)" using assms by (simp add: schema_formed_def)
  have calls: "finite (\<Union>(s,d,p)\<in>schema_premises S. pattern_targets p)"
    by (rule finite_UN_I[OF fin]) (auto split: prod.splits)
  have finM: "finite (schema_material_premises S)" using assms by (simp add: schema_formed_def)
  have mats: "finite (\<Union>(s,M)\<in>schema_material_premises S. material_targets M)"
    by (rule finite_UN_I[OF finM]) (auto split: prod.splits)
  show ?thesis using calls mats by (simp add: schema_targets_def)
qed

lemma system_targets_finite:
  assumes "schema_system_formed P"
  shows "finite (system_targets P)"
proof -
  have interfaces: "finite (system_interfaces P)" and clauses: "finite (system_clauses P)"
    and each: "\<And>d c S. ((d,c),S) \<in> system_clauses P \<Longrightarrow> schema_formed S"
    using assms by (auto simp: schema_system_formed_def)
  have first: "finite (\<Union>(d,p)\<in>system_interfaces P. pattern_targets p)"
    by (rule finite_UN_I[OF interfaces]) (auto split: prod.splits)
  have second: "finite (\<Union>(dc,S)\<in>system_clauses P. schema_targets S)"
    by (rule finite_UN_I[OF clauses]) (auto split: prod.splits intro: schema_targets_finite each)
  show ?thesis using first second by (simp add: system_targets_def)
qed

section \<open>Changing opaque operands while fixing all program literals\<close>

fun map_term_targets :: "(exact_target \<Rightarrow> exact_target) \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "map_term_targets f (Target_Term t) = Target_Term (f t)"
| "map_term_targets f (Payload_Term v) = Payload_Term v"
| "map_term_targets f (Pair_Term x y) = Pair_Term (map_term_targets f x) (map_term_targets f y)"

definition map_binding_targets ::
  "(exact_target \<Rightarrow> exact_target) \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow> ('a \<times> factor_term) set" where
  "map_binding_targets f V = (\<lambda>(a,t). (a,map_term_targets f t)) ` V"

definition map_premise_targets ::
  "(exact_target \<Rightarrow> exact_target) \<Rightarrow> ('s \<times> ('d \<times> factor_term)) set \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set" where
  "map_premise_targets f Q = (\<lambda>(s,d,t). (s,d,map_term_targets f t)) ` Q"

lemma map_term_targets_formed:
  assumes preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)" and formed: "term_formed t"
  shows "term_formed (map_term_targets f t)"
  using formed by (induction t) (auto intro: preserve)

lemma map_term_targets_involution:
  assumes "\<And>a. f (f a) = a"
  shows "map_term_targets f (map_term_targets f t) = t"
  using assms by (induction t) auto

lemma map_binding_targets_domain [simp]:
  "rel_dom (map_binding_targets f V) = rel_dom V"
  using pair_image_domain[of id "map_term_targets f" V]
  by (simp add: map_binding_targets_def)

lemma map_binding_targets_formed:
  assumes bindings: "term_bindings_formed B V"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
  shows "term_bindings_formed B (map_binding_targets f V)"
proof -
  have sv: "single_valued V" using bindings by (simp add: term_bindings_formed_def)
  have mapped: "single_valued (map_binding_targets f V)"
    using single_valued_pair_image[OF sv, of id "map_term_targets f"]
    by (simp add: map_binding_targets_def)
  show ?thesis using bindings mapped map_term_targets_formed[where f=f, OF preserve]
    by (auto simp: term_bindings_formed_def map_binding_targets_def rel_dom_def)
qed

lemma pattern_instance_target_map:
  assumes inst: "pattern_instance V p t" and fixed: "\<forall>a\<in>pattern_targets p. f a = a"
  shows "pattern_instance (map_binding_targets f V) p (map_term_targets f t)"
  using inst fixed
  by (induction rule: pattern_instance.induct)
     (auto simp: map_binding_targets_def intro: rev_image_eqI pattern_instance.intros)

lemma pattern_accepts_target_map:
  assumes accepts: "pattern_accepts p t" and fixed: "\<forall>a\<in>pattern_targets p. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
  shows "pattern_accepts p (map_term_targets f t)"
proof -
  obtain V where bindings: "term_bindings_formed (pattern_variables p) V"
    and inst: "pattern_instance V p t" and formed: "term_formed t"
    using accepts by (auto simp: pattern_accepts_def)
  have target_bindings: "term_bindings_formed (pattern_variables p) (map_binding_targets f V)"
    by (rule map_binding_targets_formed[OF bindings preserve])
  have target_inst: "pattern_instance (map_binding_targets f V) p (map_term_targets f t)"
    by (rule pattern_instance_target_map[OF inst fixed])
  show ?thesis using target_bindings target_inst map_term_targets_formed[where f=f, OF preserve formed]
    unfolding pattern_accepts_def by blast
qed

lemma map_premise_targets_domain [simp]:
  "rel_dom (map_premise_targets f Q) = rel_dom Q"
  using pair_image_domain[of id "\<lambda>(d,t). (d,map_term_targets f t)" Q]
  by (simp add: map_premise_targets_def case_prod_unfold)

lemma map_premise_targets_single_valued:
  assumes "single_valued Q"
  shows "single_valued (map_premise_targets f Q)"
  using single_valued_pair_image[OF assms, of id "\<lambda>(d,t). (d,map_term_targets f t)"]
  by (simp add: map_premise_targets_def case_prod_unfold)

lemma schema_premise_instance_target_map:
  assumes inst: "schema_premise_instance S V Q"
    and fixed: "\<forall>a\<in>schema_targets S. f a = a"
  shows "schema_premise_instance S (map_binding_targets f V) (map_premise_targets f Q)"
proof -
  have finite: "finite Q" and sv: "single_valued Q"
    and domain: "rel_dom Q = rel_dom (schema_premises S)"
    using inst by (auto simp: schema_premise_instance_def)
  have each: "\<And>s d p. (s,d,p) \<in> schema_premises S \<Longrightarrow>
    \<exists>t. (s,d,t) \<in> map_premise_targets f Q \<and> pattern_instance (map_binding_targets f V) p t"
  proof -
    fix s d p assume member: "(s,d,p) \<in> schema_premises S"
    obtain t where premise: "(s,d,t) \<in> Q" and match: "pattern_instance V p t"
      using inst member unfolding schema_premise_instance_def by blast
    have literals: "\<forall>a\<in>pattern_targets p. f a = a"
      using fixed member by (auto simp: schema_targets_def)
    have mapped: "pattern_instance (map_binding_targets f V) p (map_term_targets f t)"
      by (rule pattern_instance_target_map[OF match literals])
    have present: "(s,d,map_term_targets f t) \<in> map_premise_targets f Q"
      using premise by (auto simp: map_premise_targets_def intro: rev_image_eqI)
    show "\<exists>t. (s,d,t) \<in> map_premise_targets f Q \<and>
      pattern_instance (map_binding_targets f V) p t"
      using mapped present by blast
  qed
  have mapped_finite: "finite (map_premise_targets f Q)"
    using finite by (simp add: map_premise_targets_def)
  have mapped_sv: "single_valued (map_premise_targets f Q)"
    by (rule map_premise_targets_single_valued[OF sv])
  have mapped_domain: "rel_dom (map_premise_targets f Q) = rel_dom (schema_premises S)"
    using domain by simp
  show ?thesis using mapped_finite mapped_sv mapped_domain each
    unfolding schema_premise_instance_def by blast
qed

lemma schema_instance_target_map:
  assumes inst: "schema_instance S V t Q" and fixed: "\<forall>a\<in>schema_targets S. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
  shows "schema_instance S (map_binding_targets f V) (map_term_targets f t) (map_premise_targets f Q)"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have literals: "\<forall>a\<in>pattern_targets (schema_conclusion S). f a = a"
    using fixed by (auto simp: schema_targets_def)
  show ?thesis using sf map_binding_targets_formed[OF bindings preserve]
    pattern_instance_target_map[OF head literals] schema_premise_instance_target_map[OF body fixed]
    by (simp add: schema_instance_def)
qed

lemma schema_call_target_map:
  assumes call: "schema_call_formed P d t" and fixed: "\<forall>a\<in>system_targets P. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
  shows "schema_call_formed P d (map_term_targets f t)"
proof -
  obtain p where pf: "schema_system_formed P" and interface: "(d,p) \<in> system_interfaces P"
    and accepts: "pattern_accepts p t"
    using call by (auto simp: schema_call_formed_def)
  have literals: "\<forall>a\<in>pattern_targets p. f a = a"
    using fixed interface by (auto simp: system_targets_def)
  show ?thesis using pf interface pattern_accepts_target_map[OF accepts literals preserve]
    unfolding schema_call_formed_def by blast
qed

lemma admitted_instance_target_map:
  assumes inst: "admitted_schema_instance P d c V t Q"
    and fixed: "\<forall>a\<in>system_targets P. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
    and free: "system_observation_free P"
  shows "admitted_schema_instance P d c (map_binding_targets f V)
    (map_term_targets f t) (map_premise_targets f Q)"
proof -
  obtain S where head: "schema_call_formed P d t" and clause: "((d,c),S) \<in> system_clauses P"
    and schema: "schema_instance S V t Q"
    and calls: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> schema_call_formed P e x"
    using inst by (auto simp: admitted_schema_instance_def)
  have literals: "\<forall>a\<in>schema_targets S. f a = a"
    using fixed clause by (auto simp: system_targets_def)
  have target_head: "schema_call_formed P d (map_term_targets f t)"
    by (rule schema_call_target_map[OF head fixed preserve])
  have target_schema: "schema_instance S (map_binding_targets f V)
    (map_term_targets f t) (map_premise_targets f Q)"
    by (rule schema_instance_target_map[OF schema literals preserve])
  have target_calls: "\<forall>s e x. (s,e,x) \<in> map_premise_targets f Q \<longrightarrow> schema_call_formed P e x"
    using calls schema_call_target_map[OF _ fixed preserve]
    by (auto simp: map_premise_targets_def)
  have empty: "schema_material_premises S = {}" using free clause by (auto simp: system_observation_free_def)
  have material: "schema_material_satisfied S (map_binding_targets f V)"
    by (rule empty_schema_material_satisfied[OF empty])
  show ?thesis using target_head clause target_schema target_calls material
    unfolding admitted_schema_instance_def by blast
qed

theorem positive_meaning_target_map:
  assumes fixed: "\<forall>a\<in>system_targets P. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
    and free: "system_observation_free P"
    and holds: "(d,t) \<in> positive_meaning P"
  shows "(d,map_term_targets f t) \<in> positive_meaning P"
proof -
  let ?X = "{(d,t). (d,map_term_targets f t) \<in> positive_meaning P}"
  have stable: "schema_consequences P ?X \<subseteq> ?X"
  proof
    fix call assume step: "call \<in> schema_consequences P ?X"
    obtain d t where shape: "call = (d,t)" by (cases call)
    obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
      and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> ?X"
      using step by (auto simp: shape schema_consequences_def)
    have mapped: "admitted_schema_instance P d c (map_binding_targets f V)
      (map_term_targets f t) (map_premise_targets f Q)"
      by (rule admitted_instance_target_map[OF inst fixed preserve free])
    have children: "\<forall>s e x. (s,e,x) \<in> map_premise_targets f Q \<longrightarrow> (e,x) \<in> positive_meaning P"
      using support by (auto simp: map_premise_targets_def)
    have result: "(d,map_term_targets f t) \<in> positive_meaning P"
      by (rule positive_meaning_step[OF mapped children])
    show "call \<in> ?X" using result by (simp add: shape)
  qed
  show ?thesis using positive_meaning_least[OF stable] holds by blast
qed

theorem positive_meaning_target_involution:
  assumes fixed: "\<forall>a\<in>system_targets P. f a = a"
    and preserve: "\<And>a. target_formed a \<Longrightarrow> target_formed (f a)"
    and inverse: "\<And>a. f (f a) = a"
    and free: "system_observation_free P"
  shows "(d,map_term_targets f t) \<in> positive_meaning P \<longleftrightarrow> (d,t) \<in> positive_meaning P"
proof
  assume source: "(d,map_term_targets f t) \<in> positive_meaning P"
  have "(d,map_term_targets f (map_term_targets f t)) \<in> positive_meaning P"
    by (rule positive_meaning_target_map[where f=f and P=P and d=d and t="map_term_targets f t"])
       (fact fixed preserve free source)+
  then show "(d,t) \<in> positive_meaning P" by (simp add: map_term_targets_involution[where f=f, OF inverse])
next
  assume source: "(d,t) \<in> positive_meaning P"
  show "(d,map_term_targets f t) \<in> positive_meaning P"
    by (rule positive_meaning_target_map[where f=f and P=P and d=d and t=t])
       (fact fixed preserve free source)+
qed

section \<open>A concrete structural observation is not definable in this class\<close>

lemma pattern_targets_formed:
  assumes "pattern_formed p" "a \<in> pattern_targets p"
  shows "target_formed a"
  using assms by (induction p) auto

lemma material_targets_formed:
  assumes "material_pattern_formed M" "a \<in> material_targets M"
  shows "target_formed a"
  using assms unfolding material_pattern_formed_def material_targets_def
  by (blast intro: pattern_targets_formed)

lemma schema_targets_formed:
  assumes "schema_formed S" "a \<in> schema_targets S"
  shows "target_formed a"
  using assms by (auto simp: schema_targets_def schema_formed_def;
      blast intro: pattern_targets_formed material_targets_formed)

lemma system_targets_formed:
  assumes "schema_system_formed P" "a \<in> system_targets P"
  shows "target_formed a"
  using assms
  by (auto simp: system_targets_def schema_system_formed_def;
      blast intro: pattern_targets_formed schema_targets_formed)

definition swap_exact_targets :: "exact_target \<Rightarrow> exact_target \<Rightarrow> exact_target \<Rightarrow> exact_target" where
  "swap_exact_targets a b t = (if t=a then b else if t=b then a else t)"

lemma swap_exact_targets_involution [simp]:
  "swap_exact_targets a b (swap_exact_targets a b t) = t"
  by (auto simp: swap_exact_targets_def)

lemma swap_exact_targets_formed:
  assumes "target_formed a" "target_formed b" "target_formed t"
  shows "target_formed (swap_exact_targets a b t)"
  using assms by (auto simp: swap_exact_targets_def)

theorem positive_meaning_unlisted_targets:
  assumes af: "target_formed a" and bf: "target_formed b"
    and absent: "a \<notin> system_targets P" "b \<notin> system_targets P"
    and free: "system_observation_free P"
  shows "(d,Target_Term a) \<in> positive_meaning P \<longleftrightarrow>
    (d,Target_Term b) \<in> positive_meaning P"
proof -
  have fixed: "\<forall>x\<in>system_targets P. swap_exact_targets a b x = x"
    using absent by (auto simp: swap_exact_targets_def)
  have preserve: "\<And>x. target_formed x \<Longrightarrow> target_formed (swap_exact_targets a b x)"
    by (rule swap_exact_targets_formed[OF af bf])
  have invariant: "(d,map_term_targets (swap_exact_targets a b) (Target_Term a)) \<in> positive_meaning P
    \<longleftrightarrow> (d,Target_Term a) \<in> positive_meaning P"
  proof (rule positive_meaning_target_involution[where f="swap_exact_targets a b" and P=P])
    show "\<forall>x\<in>system_targets P. swap_exact_targets a b x = x" by (rule fixed)
    show "system_observation_free P" by (rule free)
    fix x
    show "target_formed x \<Longrightarrow> target_formed (swap_exact_targets a b x)" by (rule preserve)
    show "swap_exact_targets a b (swap_exact_targets a b x) = x" by simp
  qed
  show ?thesis using invariant by (simp add: swap_exact_targets_def eq_commute)
qed

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
  observations: the only
  target observations available in its patterns are formation and comparison
  with its finitely many literal targets.
\<close>

end
