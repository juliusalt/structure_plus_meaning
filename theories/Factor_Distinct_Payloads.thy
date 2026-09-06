theory Factor_Distinct_Payloads
  imports Factor_Compiled_Applications Factor_Self_Contained_Terms
begin

section \<open>Projecting complete carrier rows to their payload fields\<close>

inductive carrier_payload_projection :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  empty: "carrier_payload_projection (enumeration_term []) (data_list_term [])"
| cons: "term_formed x \<Longrightarrow> term_formed a \<Longrightarrow> carrier_payload_projection r t \<Longrightarrow>
    carrier_payload_projection (Pair_Term (Pair_Term x a) r) (Pair_Term x t)"

lemma carrier_payload_projection_formed:
  assumes "carrier_payload_projection a t"
  shows "term_formed a \<and> term_formed t"
  using assms by (induction rule: carrier_payload_projection.induct)
    (auto simp: octets_formed_def)

lemma carrier_payload_projection_nil:
  "carrier_payload_projection (enumeration_term []) t \<longleftrightarrow> t=data_list_term []"
proof
  assume "carrier_payload_projection (enumeration_term []) t"
  then show "t=data_list_term []" by (cases rule: carrier_payload_projection.cases) auto
next
  assume "t=data_list_term []"
  then show "carrier_payload_projection (enumeration_term []) t"
    using carrier_payload_projection.empty by simp
qed

lemma carrier_payload_projection_cons:
  "carrier_payload_projection (Pair_Term (Pair_Term x a) r) t \<longleftrightarrow>
    term_formed x \<and> term_formed a \<and>
    (\<exists>u. t=Pair_Term x u \<and> carrier_payload_projection r u)"
  by (auto elim: carrier_payload_projection.cases intro: carrier_payload_projection.cons)

lemma carrier_payload_projection_material:
  assumes formed: "exact_formed R" and inside: "set A \<subseteq> rra_carrier (object_structure R)"
  shows "carrier_payload_projection (enumeration_term (map (atom_term R) A)) t \<longleftrightarrow>
    t=data_list_term (map Payload_Term A)"
  using inside
proof (induction A arbitrary: t)
  case Nil
  then show ?case using carrier_payload_projection_nil by simp
next
  case (Cons a A)
  have address: "octets_formed a" and member: "a\<in>rra_carrier (object_structure R)"
    using formed Cons.prems by (auto simp: exact_formed_def)
  have tail: "set A\<subseteq>rra_carrier (object_structure R)" using Cons.prems by auto
  have head: "atom_term R a=Pair_Term (Payload_Term a) (occurrence_term R a)"
    by (simp add: atom_term_def)
  show ?case by (simp add: head carrier_payload_projection_cons
    address occurrence_term_formed formed member Cons.IH[OF tail])
qed

section \<open>Three ordinary schemas and their exact meaning\<close>

definition carrier_projection_empty_schema :: "(nat,nat,nat) factor_schema" where
  "carrier_projection_empty_schema =
    \<lparr>schema_conclusion=Pattern_Pair (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Payload []),
      schema_premises={}, schema_material_premises={}\<rparr>"

definition carrier_projection_cons_schema :: "(nat,nat,nat) factor_schema" where
  "carrier_projection_cons_schema =
    \<lparr>schema_conclusion=Pattern_Pair
      (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 3)),
      schema_premises={(0,0,Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))},
      schema_material_premises={}\<rparr>"

definition distinct_payloads_material :: "nat material_pattern" where
  "distinct_payloads_material =
    \<lparr>material_source=Pattern_Variable 2, material_atoms=Pattern_Variable 1,
      material_edges=Pattern_Target (Whole_Artifact empty_artifact),
      material_counts=Pattern_Target (Whole_Artifact empty_artifact),
      material_functions=Pattern_Target (Whole_Artifact empty_artifact)\<rparr>"

definition distinct_payloads_schema :: "(nat,nat,nat) factor_schema" where
  "distinct_payloads_schema =
    \<lparr>schema_conclusion=Pattern_Variable 0,
      schema_premises={(0,0,Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 0))},
      schema_material_premises={(1,distinct_payloads_material)}\<rparr>"

definition distinct_payloads_system :: "(nat,nat,nat,nat) schema_system" where
  "distinct_payloads_system =
    \<lparr>system_interfaces={(0,Pattern_Variable 0),(1,Pattern_Variable 0)},
      system_clauses={((0,0),carrier_projection_empty_schema),
        ((0,1),carrier_projection_cons_schema),((1,0),distinct_payloads_schema)}\<rparr>"

lemma distinct_payloads_system_formed [simp]: "schema_system_formed distinct_payloads_system"
  by (auto simp: schema_system_formed_def distinct_payloads_system_def
    carrier_projection_empty_schema_def carrier_projection_cons_schema_def distinct_payloads_schema_def
    distinct_payloads_material_def schema_formed_def material_pattern_formed_def material_fields_def
    system_definitions_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma distinct_payloads_definitions [simp]: "system_definitions distinct_payloads_system={0,1}"
  by (auto simp: system_definitions_def distinct_payloads_system_def rel_dom_def)

lemma distinct_payloads_call:
  "schema_call_formed distinct_payloads_system d t \<longleftrightarrow> d\<in>{0,1} \<and> term_formed t"
  by (simp only: schema_call_formed_def distinct_payloads_system_formed)
    (auto simp: distinct_payloads_system_def)

lemma carrier_projection_variables:
  "schema_variables carrier_projection_cons_schema={0,1,2,3}"
  "schema_variables distinct_payloads_schema={0,1,2}"
  by (auto simp: schema_variables_def carrier_projection_cons_schema_def distinct_payloads_schema_def
    distinct_payloads_material_def material_variables_def material_fields_def)

lemma carrier_projection_cons_instance:
  assumes inst: "schema_instance carrier_projection_cons_schema V t Q"
  shows "\<exists>x a r u. term_formed x \<and> term_formed a \<and> term_formed r \<and> term_formed u \<and>
    t=Pair_Term (Pair_Term (Pair_Term x a) r) (Pair_Term x u) \<and> Q={(0,0,Pair_Term r u)}"
proof -
  have sv: "single_valued V" and formed: "\<And>a x. (a,x)\<in>V \<Longrightarrow> term_formed x"
    using inst by (auto simp: schema_instance_def term_bindings_formed_def)
  obtain x a r y u where head: "t=Pair_Term (Pair_Term (Pair_Term x a) r) (Pair_Term y u)"
    and entries: "(0,x)\<in>V" "(1,a)\<in>V" "(2,r)\<in>V" "(0,y)\<in>V" "(3,u)\<in>V"
    using inst by (auto simp: schema_instance_def carrier_projection_cons_schema_def)
  have same: "x=y" by (rule single_valued_outputs[OF sv entries(1,4)])
  have premise: "pattern_instance V (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)) (Pair_Term r u)"
    using entries by simp
  have body: "Q={(0,0,Pair_Term r u)}"
    using schema_instance_premise_iff[OF inst] pattern_instance_unique[OF sv premise] premise
    by (auto simp: carrier_projection_cons_schema_def; blast)
  show ?thesis using head same body formed[OF entries(1)] formed[OF entries(2)]
    formed[OF entries(3)] formed[OF entries(5)] by blast
qed

lemma carrier_projection_step_sound:
  assumes inst: "admitted_schema_instance distinct_payloads_system 0 c V t Q"
    and children: "\<And>s d u. (s,d,u)\<in>Q \<Longrightarrow> d=0 \<Longrightarrow>
      \<exists>a b. u=Pair_Term a b \<and> carrier_payload_projection a b"
  shows "\<exists>a b. t=Pair_Term a b \<and> carrier_payload_projection a b"
proof -
  have alternatives: "schema_instance carrier_projection_empty_schema V t Q \<or>
    schema_instance carrier_projection_cons_schema V t Q"
    using inst by (auto simp: admitted_schema_instance_def distinct_payloads_system_def)
  then show ?thesis
  proof
    assume "schema_instance carrier_projection_empty_schema V t Q"
    then have "t=Pair_Term (enumeration_term []) (data_list_term [])"
      by (simp add: schema_instance_def carrier_projection_empty_schema_def)
    then show ?thesis using carrier_payload_projection.empty by blast
  next
    assume clause: "schema_instance carrier_projection_cons_schema V t Q"
    obtain x a r u where parts: "term_formed x" "term_formed a"
      "t=Pair_Term (Pair_Term (Pair_Term x a) r) (Pair_Term x u)" "Q={(0,0,Pair_Term r u)}"
      using carrier_projection_cons_instance[OF clause] by blast
    have tail: "carrier_payload_projection r u" using children parts(4) by auto
    have result: "carrier_payload_projection (Pair_Term (Pair_Term x a) r) (Pair_Term x u)"
      by (rule carrier_payload_projection.cons[OF parts(1,2) tail])
    show ?thesis using parts(3) result by blast
  qed
qed

theorem carrier_projection_positive_sound:
  assumes holds: "(0,t)\<in>positive_meaning distinct_payloads_system"
  shows "\<exists>a b. t=Pair_Term a b \<and> carrier_payload_projection a b"
proof -
  let ?X="{(d,t). d=0 \<longrightarrow> (\<exists>a b. t=Pair_Term a b \<and> carrier_payload_projection a b)}"
  have stable: "schema_consequences distinct_payloads_system ?X \<subseteq> ?X"
  proof
    fix z assume step: "z\<in>schema_consequences distinct_payloads_system ?X"
    obtain d t c V Q where parts: "z=(d,t)" "admitted_schema_instance distinct_payloads_system d c V t Q"
      "\<forall>s e x. (s,e,x)\<in>Q \<longrightarrow> (e,x)\<in>?X"
      using step unfolding schema_consequences_def by blast
    show "z\<in>?X"
    proof (cases "d=0")
      case True
      have inst: "admitted_schema_instance distinct_payloads_system 0 c V t Q" using parts(2) True by simp
      have result: "\<exists>a b. t=Pair_Term a b \<and> carrier_payload_projection a b"
        by (rule carrier_projection_step_sound[OF inst]) (use parts(3) in auto)
      show ?thesis using result parts(1) by simp
    next
      case False
      then show ?thesis using parts(1) by simp
    qed
  qed
  show ?thesis using positive_meaning_least[OF stable] holds by blast
qed

theorem carrier_projection_positive_complete:
  assumes "carrier_payload_projection a t"
  shows "(0,Pair_Term a t)\<in>positive_meaning distinct_payloads_system"
  using assms
proof (induction rule: carrier_payload_projection.induct)
  case empty
  have inst: "admitted_schema_instance distinct_payloads_system 0 0 {}
    (Pair_Term (enumeration_term []) (data_list_term [])) {}"
    by (simp only: admitted_schema_instance_def distinct_payloads_call)
      (auto simp: distinct_payloads_system_def
      schema_instance_def carrier_projection_empty_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def schema_material_satisfied_def term_bindings_formed_def
      single_valued_def rel_dom_def octets_formed_def)
  show ?case by (rule positive_meaning_step[OF inst]) simp
next
  case (cons x a r t)
  let ?V="{(0,x),(1,a),(2,r),(3,t)}"
  have formed: "term_formed x" "term_formed a" "term_formed r" "term_formed t"
    using cons.hyps carrier_payload_projection_formed by auto
  have bindings: "term_bindings_formed (schema_variables carrier_projection_cons_schema) ?V"
    using formed by (auto simp: carrier_projection_variables term_bindings_formed_def single_valued_def rel_dom_def)
  have schema: "schema_instance carrier_projection_cons_schema ?V
    (Pair_Term (Pair_Term (Pair_Term x a) r) (Pair_Term x t)) {(0,0,Pair_Term r t)}"
    using bindings by (auto simp: schema_instance_def carrier_projection_cons_schema_def
      schema_formed_def schema_premise_instance_def single_valued_def rel_dom_def)
  have inst: "admitted_schema_instance distinct_payloads_system 0 1 ?V
    (Pair_Term (Pair_Term (Pair_Term x a) r) (Pair_Term x t)) {(0,0,Pair_Term r t)}"
    using schema formed
    by (simp only: admitted_schema_instance_def distinct_payloads_call)
      (auto simp: distinct_payloads_system_def schema_material_satisfied_def carrier_projection_cons_schema_def)
  show ?case by (rule positive_meaning_step[OF inst]) (use cons.IH in auto)
qed

theorem carrier_projection_positive_exact:
  "(0,Pair_Term a t)\<in>positive_meaning distinct_payloads_system \<longleftrightarrow> carrier_payload_projection a t"
  using carrier_projection_positive_sound carrier_projection_positive_complete by auto

lemma distinct_payloads_instance_material:
  assumes inst: "schema_instance distinct_payloads_schema V t Q"
    and material: "schema_material_satisfied distinct_payloads_schema V"
  shows "\<exists>s a. material_observation s a (enumeration_term []) (enumeration_term []) (enumeration_term []) \<and>
    (0,0,Pair_Term a t)\<in>Q"
proof -
  have head: "(0,t)\<in>V" using inst by (simp add: schema_instance_def distinct_payloads_schema_def)
  obtain s a e b f where fields: "material_pattern_instance V distinct_payloads_material s a e b f"
    and observation: "material_observation s a e b f"
    using material by (auto simp: schema_material_satisfied_def distinct_payloads_schema_def
      material_pattern_satisfied_def)
  have atoms: "(1,a)\<in>V" and shape: "e=enumeration_term []" "b=enumeration_term []" "f=enumeration_term []"
    using fields by (auto simp: material_pattern_instance_def distinct_payloads_material_def)
  have premise: "pattern_instance V (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 0)) (Pair_Term a t)"
    using head atoms by simp
  have member: "(0,0,Pair_Term a t)\<in>Q"
    using schema_instance_premise_iff[OF inst] premise by (simp add: distinct_payloads_schema_def)
  show ?thesis using observation shape member by blast
qed

theorem distinct_payloads_positive_sound:
  assumes holds: "(1,t)\<in>positive_meaning distinct_payloads_system"
  shows "\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A)"
proof -
  obtain c V Q where admitted: "admitted_schema_instance distinct_payloads_system 1 c V t Q"
    and children: "\<forall>s e x. (s,e,x)\<in>Q \<longrightarrow> (e,x)\<in>positive_meaning distinct_payloads_system"
    using holds by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have inst: "schema_instance distinct_payloads_schema V t Q"
    and material: "schema_material_satisfied distinct_payloads_schema V"
    using admitted by (auto simp: admitted_schema_instance_def distinct_payloads_system_def)
  obtain s a where observation:
    "material_observation s a (enumeration_term []) (enumeration_term []) (enumeration_term [])"
    and member: "(0,0,Pair_Term a t)\<in>Q"
    using distinct_payloads_instance_material[OF inst material] by blast
  have project: "carrier_payload_projection a t"
    using children member carrier_projection_positive_exact by blast
  obtain R A E B F where enumeration: "artifact_enumeration R A E B F"
    and atoms: "a=enumeration_term (map (atom_term R) A)"
    using observation by (auto simp: material_observation_def)
  have rf: "exact_formed R" and carrier: "set A=rra_carrier (object_structure R)"
    using artifact_enumeration_material[OF enumeration] by auto
  have address: "\<forall>a\<in>set A. octets_formed a" using rf carrier by (simp add: exact_formed_def)
  have different: "distinct A" using enumeration by (simp add: artifact_enumeration_def)
  have data: "t=data_list_term (map Payload_Term A)"
    using carrier_payload_projection_material[OF rf, of A t] carrier project atoms by simp
  show ?thesis using different address data by blast
qed

theorem distinct_payloads_positive_complete:
  assumes different: "distinct A" and formed: "\<forall>a\<in>set A. octets_formed a"
  shows "(1,data_list_term (map Payload_Term A))\<in>positive_meaning distinct_payloads_system"
proof -
  let ?R="enumerated_artifact A [] [] []"
  let ?a="enumeration_term (map (atom_term ?R) A)"
  let ?s="Target_Term (Whole_Artifact ?R)"
  let ?t="data_list_term (map Payload_Term A)"
  let ?V="{(0,?t),(1,?a),(2,?s)}"
  have rf: "exact_formed ?R"
    using formed by (auto simp: enumerated_artifact_def exact_formed_def object_formed_def
      rra_formed_def basis_formed_def basis_values_def bag_support_def single_valued_def)
  have enumeration: "artifact_enumeration ?R A [] [] []"
    using rf different by (simp add: artifact_enumeration_def)
  have observed: "material_observation ?s ?a (enumeration_term []) (enumeration_term []) (enumeration_term [])"
    using material_observation_exact[of ?R A "[]" "[]" "[]"] enumeration by simp
  have project: "carrier_payload_projection ?a ?t"
    by (rule carrier_payload_projection_material[OF rf, THEN iffD2]) (simp_all add: enumerated_artifact_def)
  have premise: "(0,Pair_Term ?a ?t)\<in>positive_meaning distinct_payloads_system"
    by (rule carrier_projection_positive_complete[OF project])
  have terms: "term_formed ?s" "term_formed ?a" "term_formed ?t"
    using material_observation_formed[OF observed] carrier_payload_projection_formed[OF project] by auto
  have bindings: "term_bindings_formed (schema_variables distinct_payloads_schema) ?V"
    using terms by (auto simp: carrier_projection_variables term_bindings_formed_def single_valued_def rel_dom_def)
  have schema: "schema_instance distinct_payloads_schema ?V ?t {(0,0,Pair_Term ?a ?t)}"
    using bindings by (auto simp: schema_instance_def distinct_payloads_schema_def schema_formed_def
      distinct_payloads_material_def material_pattern_formed_def material_fields_def
      schema_premise_instance_def single_valued_def rel_dom_def)
  have fields: "material_pattern_instance ?V distinct_payloads_material ?s ?a
    (enumeration_term []) (enumeration_term []) (enumeration_term [])"
    by (simp add: material_pattern_instance_def distinct_payloads_material_def)
  have material: "schema_material_satisfied distinct_payloads_schema ?V"
    using fields observed by (auto simp: schema_material_satisfied_def distinct_payloads_schema_def
      material_pattern_satisfied_def; blast)
  have admitted: "admitted_schema_instance distinct_payloads_system 1 0 ?V ?t {(0,0,Pair_Term ?a ?t)}"
    using schema material terms
    by (simp only: admitted_schema_instance_def distinct_payloads_call)
      (auto simp: distinct_payloads_system_def)
  show ?thesis by (rule positive_meaning_step[OF admitted]) (use premise in auto)
qed

theorem distinct_payloads_positive_exact:
  "(1,t)\<in>positive_meaning distinct_payloads_system \<longleftrightarrow>
    (\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A))"
  using distinct_payloads_positive_sound distinct_payloads_positive_complete by blast

corollary distinct_payload_list_exact:
  "(1,data_list_term (map Payload_Term A))\<in>positive_meaning distinct_payloads_system \<longleftrightarrow>
    distinct A \<and> (\<forall>a\<in>set A. octets_formed a)"
proof -
  have injective: "inj Payload_Term" by (rule injI) simp
  show ?thesis by (simp only: distinct_payloads_positive_exact data_list_term_injective
    injective_mapped_lists[OF injective]) auto
qed

corollary payload_recognition_exact:
  "(1,data_list_term [t])\<in>positive_meaning distinct_payloads_system \<longleftrightarrow>
    (\<exists>v. octets_formed v \<and> t=Payload_Term v)"
proof
  assume holds: "(1,data_list_term [t])\<in>positive_meaning distinct_payloads_system"
  obtain A where formed: "\<forall>a\<in>set A. octets_formed a"
    and data: "data_list_term [t]=data_list_term (map Payload_Term A)"
    using distinct_payloads_positive_sound[OF holds] by blast
  have shape: "map Payload_Term A=[t]" using data by (simp only: data_list_term_injective)
  show "\<exists>v. octets_formed v \<and> t=Payload_Term v" using formed shape by (cases A) auto
next
  assume "\<exists>v. octets_formed v \<and> t=Payload_Term v"
  then obtain v where formed: "octets_formed v" and shape: "t=Payload_Term v" by blast
  show "(1,data_list_term [t])\<in>positive_meaning distinct_payloads_system"
    using distinct_payloads_positive_complete[of "[v]"] formed shape by auto
qed

corollary unequal_payloads_exact:
  "(1,data_list_term [Payload_Term a,Payload_Term b])\<in>positive_meaning distinct_payloads_system \<longleftrightarrow>
    octets_formed a \<and> octets_formed b \<and> a\<noteq>b"
  using distinct_payload_list_exact[of "[a,b]"] by auto

lemma distinct_payload_term_list_sound:
  assumes holds: "(1,data_list_term ts)\<in>positive_meaning distinct_payloads_system"
  shows "distinct ts \<and> (\<forall>t\<in>set ts. \<exists>v. octets_formed v \<and> t=Payload_Term v)"
proof -
  obtain A where parts: "distinct A" "\<forall>a\<in>set A. octets_formed a"
    "data_list_term ts=data_list_term (map Payload_Term A)"
    using distinct_payloads_positive_sound[OF holds] by blast
  have same: "ts=map Payload_Term A" using parts(3) by (simp only: data_list_term_injective)
  show ?thesis using parts(1,2) same by (auto simp: distinct_map inj_on_def)
qed

theorem native_distinct_payload_lists:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d. closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A)))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions distinct_payloads_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed distinct_payloads_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning distinct_payloads_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF distinct_payloads_system_formed] by blast
  have member: "1\<in>system_definitions distinct_payloads_system" by simp
  have every: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 1) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A))))"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g 1) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed distinct_payloads_system 1 t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
      using future[rule_format, OF member tf] by blast
    have call: "native_application_formed F pu [] au []"
      using parts(7) tf distinct_payloads_call[of 1 t] by simp
    have truth: "native_positive_holds F pu [] au [] \<longleftrightarrow>
      (\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A))"
      using parts(8) distinct_payloads_positive_exact[of t] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 1) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>A. distinct A \<and> (\<forall>a\<in>set A. octets_formed a) \<and> t=data_list_term (map Payload_Term A)))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts(1-6) call truth in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 1"])
    (use closed every in blast)
qed

text \<open>
  A complete carrier enumeration lists each address once. Every formed opaque
  payload is also a possible local address, so an artifact with that finite
  carrier and no other material exists exactly when the requested address list
  is formed and has no repetition. The ordinary recursive projection removes
  the accompanying occurrence anchors. Its graph is compared with the first
  definition's independently fixed positive meaning above.

  The second definition has one complete material premise and one ordinary
  call. These three schemas recognize arbitrary future finite lists of distinct
  payloads. Singleton recognition and two-payload inequality are derived cases.
  No byte is interpreted, no inequality primitive is added, and no witness
  artifact supplies a semantic rule. One closed native compilation serves every
  formed future argument with unchanged canonical program environment.

  This exact comparison is a component for finite native checking. It does not
  by itself implement grammar admission, reflection, or amendment acceptance.
\<close>

end
