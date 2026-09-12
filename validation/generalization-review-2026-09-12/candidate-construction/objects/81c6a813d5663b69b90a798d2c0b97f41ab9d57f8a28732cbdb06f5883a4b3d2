theory Factor_Prescribed_Schemas
  imports Factor_Syntax_Copy RRA_Prescribed_Addresses
begin

section \<open>Binder coordinates can avoid an existing finite socket boundary\<close>

lemma binder_addressing_avoiding:
  assumes variables: "finite B" and forbidden: "finite W"
  shows "\<exists>f. binder_addressing B f \<and> f ` B \<inter> W={}"
proof -
  have tails: "finite (tl ` W)" using forbidden by simp
  obtain g where chosen: "finite_addressing B g" "g ` B \<inter> tl ` W={}"
    using finite_addressing_avoiding[OF variables tails] by blast
  let ?f="Cons 6 \<circ> g"
  have addressing: "binder_addressing B ?f"
    using chosen(1) by (auto simp: binder_addressing_def finite_addressing_def inj_on_def octets_formed_def)
  have outside: "?f ` B \<inter> W={}"
  proof (rule equals0I)
    fix z assume member: "z\<in>?f ` B \<inter> W"
    obtain a where source: "a\<in>B" "z=6#g a" "z\<in>W" using member by auto
    have tail: "g a\<in>tl ` W" using imageI[OF source(3), of tl] source(2) by simp
    show False using chosen(2) source(1) tail by blast
  qed
  show ?thesis by (rule exI[of _ ?f]) (use addressing outside in blast)
qed

lemma prescribed_binder_socket_map:
  assumes finite: "finite U" and inside: "B \<union> set ss\<subseteq>U"
    and separate: "B \<inter> set ss={}" and old_formed: "\<forall>a\<in>B. octets_formed a"
    and lengths: "length ss=length os" and orders: "distinct ss" "distinct os"
    and sockets: "finite_addressing (set os) h" and destination: "B \<inter> h ` set os={}"
  shows "\<exists>g. inj g \<and> finite_addressing U g \<and>
    (\<forall>a\<in>B. g a=a) \<and> map g ss=map h os"
proof -
  have hinj: "inj_on h (set os)" using sockets by (simp add: finite_addressing_def)
  have hdistinct: "distinct (map h os)" using orders(2) hinj by (simp add: distinct_map)
  have hlength: "length ss=length (map h os)" using lengths by simp
  obtain k where correspondence: "inj_on k (set ss)" "map k ss=map h os"
    using distinct_list_rekey[OF hlength orders(1) hdistinct] by blast
  have image: "k ` set ss=h ` set os"
    using arg_cong[OF correspondence(2), of set] by simp
  let ?p="\<lambda>a. if a\<in>B then a else k a"
  have disjoint: "B \<inter> k ` set ss={}" using destination by (simp only: image)
  have outside: "k a\<notin>B" if "a\<in>set ss" for a using disjoint that by blast
  have pinj: "inj_on ?p (B \<union> set ss)"
    using correspondence(1) outside by (auto simp: inj_on_def split: if_splits)
  have new_formed: "\<forall>a\<in>k ` set ss. octets_formed a"
    using sockets by (simp only: image finite_addressing_def; blast)
  have pformed: "\<forall>a\<in>B \<union> set ss. octets_formed (?p a)"
    using old_formed new_formed by auto
  have prescribed: "finite_addressing (B \<union> set ss) ?p"
    using pinj pformed by (simp add: finite_addressing_def)
  obtain g where extension: "inj g" "finite_addressing U g"
    "\<forall>a\<in>B \<union> set ss. g a=?p a"
    using prescribed_addressing_extension[OF finite inside prescribed, where W="{}"] by blast
  have fixed: "\<forall>a\<in>B. g a=a" using extension(3) by simp
  have moved: "map g ss=map k ss"
    by (rule map_cong[OF refl]) (use extension(3) separate in auto)
  have target: "map g ss=map h os" by (rule trans[OF moved correspondence(2)])
  show ?thesis by (rule exI[of _ g]) (use extension(1,2) fixed target in blast)
qed

section \<open>Complete schema syntax at prescribed binder and socket coordinates\<close>

theorem schema_compilation_at_coordinates:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes formed: "schema_formed S"
    and addresses: "\<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
    and binders: "binder_addressing (schema_variables S) f"
    and sockets: "finite_addressing (schema_sockets S) h"
    and separate: "f ` schema_variables S \<inter> h ` schema_sockets S={}"
  shows "\<exists>R r L C. exact_formed R \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u L C \<longrightarrow> native_schema_at E u r (rename_schema f h id S)) \<and>
    (\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    reference_table_formed L C \<and> rel_dom L \<union> rel_dom C\<subseteq>rra_carrier (object_structure R) \<and>
    rel_ran C=schema_dependencies S \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
    r\<in>rra_carrier (object_structure R)"
proof -
  obtain os :: "'s list" and ts :: "('a,local_address option) premise_template list" where enumeration:
    "length os=length ts" "distinct os"
    "set (zip os ts)=socket_sum (schema_premises S) (schema_material_premises S)"
    using schema_template_enumeration[OF formed] by metis
  have variables: "schema_body_variables (schema_conclusion S) ts=schema_variables S"
    by (rule schema_enumerated_variables[OF enumeration(1,3)])
  have socket_set: "schema_sockets S=set os" by (rule schema_enumerated_sockets[OF enumeration(1,3)])
  have pf: "pattern_formed (schema_conclusion S)" using formed by (simp add: schema_formed_def)
  have tf: "\<forall>t\<in>set ts. template_formed t"
    by (rule schema_enumerated_templates_formed[OF formed addresses enumeration(1,3)])
  have faddr: "binder_addressing (schema_body_variables (schema_conclusion S) ts) f"
    using binders by (simp only: variables)
  have bodies: "schema_bodies f (schema_conclusion S) ts" by (rule schema_bodies.intro[OF pf tf faddr])
  let ?L="schema_body_literals (schema_conclusion S) ts"
  let ?C="schema_body_callees ts"
  let ?B="f ` schema_variables S"
  obtain R r ss where built:
    "exact_formed R" "length ss=length ts" "distinct ss"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u ?L ?C \<longrightarrow> native_schema_at E u r (schema_list_projection f (schema_conclusion S) ss ts)"
    "reference_table_formed ?L ?C" "rel_dom ?L \<union> rel_dom ?C\<subseteq>rra_carrier (object_structure R)"
    "bag_count (object_data R)=(\<lambda>_. 0)" "r\<in>rra_carrier (object_structure R)"
    "set ss \<inter> ?B={}" "set ss \<union> ?B\<subseteq>rra_carrier (object_structure R)"
    using schema_syntax_total[OF bodies] by (simp only: variables; metis)
  have same_length: "length os=length ss" using enumeration(1) built(2) by simp
  obtain k where rekey: "inj_on k (set os)" "map k os=ss"
    using distinct_list_rekey[OF same_length enumeration(2) built(3)] by metis
  have projection: "schema_list_projection f (schema_conclusion S) ss ts=rename_schema f k id S"
    using schema_list_recovers_source[OF enumeration(3), of f k] rekey(2) by simp
  have recover: "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u ?L ?C \<longrightarrow> native_schema_at E u r (rename_schema f k id S)"
    using built(4) by (simp only: projection)
  have finite: "finite (rra_carrier (object_structure R))"
    using built(1) by (simp add: exact_formed_def object_formed_def rra_formed_def)
  have inside: "?B \<union> set ss\<subseteq>rra_carrier (object_structure R)" using built(10) by blast
  have source_separate: "?B \<inter> set ss={}" using built(9) by blast
  have bformed: "\<forall>a\<in>?B. octets_formed a"
    using binders by (auto simp: binder_addressing_def finite_addressing_def)
  have slength: "length ss=length os" using same_length by simp
  have haddr: "finite_addressing (set os) h" using sockets by (simp only: socket_set)
  have target_separate: "?B \<inter> h ` set os={}" using separate by (simp only: socket_set)
  obtain g where placement: "inj g" "finite_addressing (rra_carrier (object_structure R)) g"
    "\<forall>a\<in>?B. g a=a" "map g ss=map h os"
    using prescribed_binder_socket_map[OF finite inside source_separate bformed slength built(3)
      enumeration(2) haddr target_separate] by blast
  have mapped: "map (g \<circ> k) os=map h os"
  proof -
    have "map (g \<circ> k) os=map g (map k os)" by simp
    also have "\<dots>=map g ss" by (simp only: rekey(2))
    also have "\<dots>=map h os" by (rule placement(4))
    finally show ?thesis .
  qed
  have socket_agreement: "\<forall>a\<in>schema_sockets S. (g \<circ> k) a=h a"
    using mapped by (simp add: map_eq_conv socket_set)
  have binder_agreement: "\<forall>a\<in>schema_variables S. (g \<circ> f) a=f a"
    using placement(3) by auto
  have schema_agreement: "rename_schema g g id (rename_schema f k id S)=rename_schema f h id S"
    unfolding rename_schema_composition
    by (rule rename_schema_agreement[OF binder_agreement socket_agreement]) simp
  let ?R="push_object g R"
  let ?A="map_slot_keys g ?L"
  let ?D="map_slot_keys g ?C"
  have rf: "exact_formed ?R" by (rule exact_push_formed[OF built(1) placement(2)])
  have reads: "object_reads_agree ?R ?R (g ` rra_carrier (object_structure R))"
    by (simp add: object_reads_agree_def push_object_def)
  have dependencies: "rel_ran ?C=schema_dependencies S"
    by (rule schema_enumerated_callees[OF enumeration(1,3)])
  have dependency_bound: "schema_dependencies (rename_schema f k id S)\<subseteq>rel_ran ?C"
    by (simp add: renamed_schema_dependencies dependencies)
  have native: "native_schema_at E u (g r) (rename_schema f h id S)"
    if ef: "environment_formed E" and source: "artifact_at E u ?R" and refs: "syntax_references E u ?A ?D"
    for E u
    using compiled_schema_copy[OF built(1,6) recover dependency_bound ef source placement(1,2) reads refs]
    by (simp only: schema_agreement)
  have table: "reference_table_formed ?A ?D" by (rule reference_table_map[OF built(5) placement(1)])
  have bounds: "rel_dom ?A \<union> rel_dom ?D\<subseteq>rra_carrier (object_structure ?R)"
    using built(6) by (auto simp: map_slot_keys_domain push_object_def)
  have range: "rel_ran ?D=schema_dependencies S" by (simp add: map_slot_keys_range dependencies)
  have counts: "bag_count (object_data ?R)=(\<lambda>_. 0)"
    by (simp add: push_object_def push_basis_def pushed_count_def built(7) fun_eq_iff)
  have root: "g r\<in>rra_carrier (object_structure ?R)" using built(8) by (auto simp: push_object_def)
  have finj: "inj_on f (schema_variables S)" using binders by (simp add: binder_addressing_def finite_addressing_def)
  have hinj: "inj_on h (schema_sockets S)" using sockets by (simp add: finite_addressing_def)
  have semantics: "\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t"
    by (intro allI; rule schema_rule_instance_alpha[OF finj hinj])
  show ?thesis by (rule exI[of _ ?R], rule exI[of _ "g r"], rule exI[of _ ?A], rule exI[of _ ?D])
    (use rf native semantics table bounds range counts root in blast)
qed

text \<open>
  Binder and socket coordinates are inputs to this constructor. The finite
  boundary must be formed and injective, and the two coordinate images must
  be disjoint. These conditions are established before placing private code.
  The existing complete schema compiler and native copy theorem then retain
  every specified coordinate, literal value, and external callee target.

  A later collection of schemas can use one binder map chosen on its complete
  variable scope. Restricting that map to each schema discharges the local
  addressing condition. This theorem does not itself put separate artifacts
  under one physical binder.
\<close>

end
