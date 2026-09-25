theory Development_Given_Declarations
  imports Factor_Resolution_Commitments Development_Given_Program Factor_Bag_Presentations Factor_Binder_Admission
begin

text \<open>
  The given's declarations (R6 of DECISIONS.md "The native evaluator constructs the missing witnesses by
  resolution", its section "Committed choice, for refusals"): the presentation-free producers of the given's
  readers that the form of @{text Factor_Resolution_Commitments} fits, with the sockets inside them and the
  consumers a contract states invariant, each discharged at its notion's own system from the notion's exact
  contract. The sites are the given's readers' own numbers, so the declarations are read over the given's rooted
  readers (@{const finite_rooted_given_readers}) unchanged; carrying their discharge to the given's programs is
  the transfer's. No clause of any program changes: the declarations are read by the committed search alone.
\<close>

section \<open>The classes at the producers' outputs\<close>

text \<open>
  Each producer's output is a presentation of one subject of its notion: 6's (in its output direction) a bag of
  data terms (@{const data_bag_value_presents}), 10's an artifact (@{const artifact_value_presents}), 32's the
  finite set of a family's socket rows (@{const data_collection_presents} of the rows' data), 45's a target
  (@{const target_value_presents}). Two outputs correspond when they present one subject: the class's
  @{const presentation_transport}.
\<close>

abbreviation family_rows_presents :: "(local_address \<times> local_address) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "family_rows_presents \<equiv> data_collection_presents (\<lambda>z t. t = address_pair_data z)"

definition given_correspondence :: "nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "given_correspondence d = (if d = 6 then presentation_transport data_bag_value_presents data_bag_value_presents
    else if d = 10 then presentation_transport artifact_value_presents artifact_value_presents
    else if d = 32 then presentation_transport family_rows_presents family_rows_presents
    else if d = 45 then presentation_transport target_value_presents target_value_presents
    else (=))"

section \<open>Each producer discharged at its notion's system\<close>

theorem bag_producer_discharged:
  "producer_discharged (positive_meaning bag_comparison_system) 6 (given_correspondence 6)"
  unfolding producer_discharged_def
proof (intro allI impI)
  fix x y y'
  assume a: "(6,Pair_Term x y) \<in> positive_meaning bag_comparison_system"
    and b: "(6,Pair_Term x y') \<in> positive_meaning bag_comparison_system"
  from a obtain xs ys where x: "x = data_list_term xs" and y: "y = data_list_term ys"
    and e: "data_elements ys" "mset xs = mset ys" by (auto simp: bag_comparison_exact)
  from b obtain xs' ys' where x': "x = data_list_term xs'" and y': "y' = data_list_term ys'"
    and e': "data_elements ys'" "mset xs' = mset ys'" by (auto simp: bag_comparison_exact)
  have same: "xs' = xs" using x x' by (simp add: data_list_term_injective)
  have "data_bag_value_presents (mset xs) y" "data_bag_value_presents (mset xs) y'"
    using y y' e e' same by (auto simp: data_bag_value_presents_def)
  then show "given_correspondence 6 y y'" by (auto simp: given_correspondence_def presentation_transport_def)
qed

theorem artifact_producer_discharged:
  "producer_discharged (positive_meaning artifact_projection_system) 10 (given_correspondence 10)"
  unfolding producer_discharged_def
proof (intro allI impI)
  fix x y y'
  assume a: "(10,Pair_Term x y) \<in> positive_meaning artifact_projection_system"
    and b: "(10,Pair_Term x y') \<in> positive_meaning artifact_projection_system"
  from a obtain R where x: "x = Target_Term (Whole_Artifact R)" and y: "artifact_value_presents R y"
    by (auto simp: artifact_projection_exact)
  from b obtain R' where x': "x = Target_Term (Whole_Artifact R')" and y': "artifact_value_presents R' y'"
    by (auto simp: artifact_projection_exact)
  have "R' = R" using x x' by simp
  then show "given_correspondence 10 y y'"
    using y y' by (auto simp: given_correspondence_def presentation_transport_def)
qed

theorem target_producer_discharged:
  "producer_discharged (positive_meaning target_projection_system) 45 (given_correspondence 45)"
  unfolding producer_discharged_def
proof (intro allI impI)
  fix x y y'
  assume a: "(45,Pair_Term x y) \<in> positive_meaning target_projection_system"
    and b: "(45,Pair_Term x y') \<in> positive_meaning target_projection_system"
  from a obtain z where x: "x = Target_Term z" and y: "target_value_presents z y"
    by (auto simp: target_projection_exact)
  from b obtain z' where x': "x = Target_Term z'" and y': "target_value_presents z' y'"
    by (auto simp: target_projection_exact)
  have "z' = z" using x x' by simp
  then show "given_correspondence 45 y y'"
    using y y' by (auto simp: given_correspondence_def presentation_transport_def)
qed

theorem family_producer_discharged:
  "producer_discharged (positive_meaning family_admission_system) 32 (given_correspondence 32)"
  unfolding producer_discharged_def
proof (intro allI impI)
  fix x y y'
  assume a: "(32,Pair_Term x y) \<in> positive_meaning family_admission_system"
    and b: "(32,Pair_Term x y') \<in> positive_meaning family_admission_system"
  from a obtain R c r xs where x: "x = Pair_Term c (Payload_Term r)"
    and y: "y = data_list_term (map address_pair_data xs)"
    and R: "artifact_value_presents R c" and d: "distinct xs" and f: "family_at R r (set xs)"
    by (auto simp: family_admission_exact)
  from b obtain R' c' r' xs' where x': "x = Pair_Term c' (Payload_Term r')"
    and y': "y' = data_list_term (map address_pair_data xs')"
    and R': "artifact_value_presents R' c'" and d': "distinct xs'" and f': "family_at R' r' (set xs')"
    by (auto simp: family_admission_exact)
  have "c' = c" "r' = r" using x x' by simp_all
  then have "R' = R" using R R' artifact_value_presents_unique by metis
  then have same: "set xs' = set xs" using f f' \<open>r' = r\<close> family_at_unique by metis
  have "family_rows_presents (set xs) y" "family_rows_presents (set xs) y'"
    using y y' d d' same by (auto simp: data_collection_presents_def list_all2_function)
  then show "given_correspondence 32 y y'"
    by (auto simp: given_correspondence_def presentation_transport_def)
qed

section \<open>The selection inside 6, committed at its recursion's socket\<close>

text \<open>
  6's second clause concludes the bag of x#xs from the selection 5 of x out of its output and 6 at xs over the
  remainder. At every true instance, every answer of the recursion at the same xs extends to a true instance
  keeping the head's input: select x at the head of the answer. The socket is declared without the kept head.
\<close>

definition given_bag_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "given_bag_socket_schema = \<lparr>finite_schema_conclusion =
      Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,5,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))),
      (1,6,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))|},
    finite_schema_materials = {||}\<rparr>"

lemma given_bag_socket_decoded: "decode_finite_schema given_bag_socket_schema = bag_cons_schema"
  by (simp add: given_bag_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def bag_cons_schema_def bag_step_schema_def)

lemma bag_cons_premises:
  "schema_premises bag_cons_schema = {(0,5,Pattern_Pair (Pattern_Variable 0)
      (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))),(1,6,Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 3))}"
  "schema_material_premises bag_cons_schema = {}"
  "schema_conclusion bag_cons_schema = Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 2)"
  by (simp_all add: bag_cons_schema_def bag_step_schema_def)

theorem bag_socket_discharged:
  "socket_discharged (positive_meaning bag_comparison_system) bag_cons_schema 1 False"
  unfolding socket_discharged_def
proof (rule allI, rule impI, rule conjI)
  let ?M = "positive_meaning bag_comparison_system"
  fix h assume t: "clause_true ?M bag_cons_schema h"
  have select: "(5,Pair_Term (h 0) (Pair_Term (h 2) (h 3))) \<in> ?M"
    using t by (simp add: clause_true_def bag_cons_premises)
  obtain pre post where element: "data_elements (pre@h 0#post)"
    using data_selection_sound[OF select] by auto
  show "\<forall>d xi yo y'. (1,d,Pattern_Pair xi yo) \<in> schema_premises bag_cons_schema \<longrightarrow>
      (d,Pair_Term (evaluate_pattern h xi) y') \<in> ?M \<longrightarrow> (\<exists>h'. clause_true ?M bag_cons_schema h' \<and>
        head_kept False bag_cons_schema h h' \<and> evaluate_pattern h' xi = evaluate_pattern h xi \<and> evaluate_pattern h' yo = y')"
  proof (rule allI, rule allI, rule allI, rule allI, rule impI, rule impI)
    fix d xi yo y' assume p: "(1,d,Pattern_Pair xi yo) \<in> schema_premises bag_cons_schema"
      and answer: "(d,Pair_Term (evaluate_pattern h xi) y') \<in> ?M"
    have fields: "d = 6" "xi = Pattern_Variable 1" "yo = Pattern_Variable 3" using p by (simp_all add: bag_cons_premises)
    have answer': "(6,Pair_Term (h 1) y') \<in> ?M" using answer fields by simp
    then obtain ys where y: "y' = data_list_term ys" and ye: "data_elements ys" by (auto simp: bag_comparison_exact)
    let ?h = "h(2 := data_list_term (h 0#ys), 3 := y')"
    have elements: "data_elements (h 0#ys)" using element ye by auto
    have selected: "(5,Pair_Term (h 0) (Pair_Term (data_list_term (h 0#ys)) (data_list_term ys))) \<in> ?M"
      using elements by (simp only: data_selection_exact) (metis append_Nil)
    have formed: "term_formed (Pair_Term (h 0) (Pair_Term (data_list_term (h 0#ys)) (data_list_term ys)))"
      using positive_meaning_formed[OF selected] by (simp add: bag_comparison_call)
    have vars: "schema_variables bag_cons_schema = {0,1,2,3}"
      by (auto simp: schema_variables_def bag_cons_schema_def bag_step_schema_def)
    have old: "\<forall>a\<in>schema_variables bag_cons_schema. term_formed (h a)" using t by (simp add: clause_true_def)
    have true: "clause_true ?M bag_cons_schema ?h"
      using old formed selected answer' y by (auto simp: clause_true_def bag_cons_premises vars)
    have kept: "head_kept False bag_cons_schema h ?h" by (simp add: head_kept_def bag_cons_premises)
    show "\<exists>h'. clause_true ?M bag_cons_schema h' \<and> head_kept False bag_cons_schema h h' \<and>
        evaluate_pattern h' xi = evaluate_pattern h xi \<and> evaluate_pattern h' yo = y'"
      using true kept fields by (intro exI[of _ ?h]) simp
  qed
  show "\<forall>N g. (1,N) \<in> schema_material_premises bag_cons_schema \<longrightarrow> evaluate_material_satisfaction g N \<longrightarrow>
      evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N) \<longrightarrow>
      (\<exists>h'. clause_true ?M bag_cons_schema h' \<and> head_kept False bag_cons_schema h h' \<and> (\<forall>a\<in>material_variables N. h' a = g a))"
    by (simp add: bag_cons_premises)
qed

section \<open>A consumer of 6's output, discharged at its notion's system\<close>

text \<open>
  Payload disjointness (49) reads its left list as a set of distinct payloads: a bag with the same members is
  distinct exactly when the list is and has the same set, so 49 is invariant under 6's class at its left side.
\<close>

lemma payload_disjoint_bag:
  assumes holds: "(49,Pair_Term (data_list_term ys) x) \<in> positive_meaning payload_disjoint_system"
    and same: "mset ys = mset ys'"
  shows "(49,Pair_Term (data_list_term ys') x) \<in> positive_meaning payload_disjoint_system"
proof -
  from holds obtain A B where ys: "ys = map Payload_Term A" and x: "x = data_list_term (map Payload_Term B)"
    and conditions: "distinct A" "distinct B" "set A \<inter> set B = {}" "\<forall>a\<in>set A \<union> set B. octets_formed a"
    by (auto simp: payload_disjoint_exact data_list_term_injective)
  have "\<forall>y\<in>set ys'. \<exists>a. y = Payload_Term a" using mset_eq_setD[OF same] ys by auto
  then obtain A' where ys': "ys' = map Payload_Term A'" by (auto simp: ex_map_conv[symmetric])
  have "distinct ys" using conditions(1) ys by (simp add: distinct_map inj_on_subset[OF payload_term_inj subset_UNIV])
  then have "distinct ys'" using same by (metis distinct_count_atmost_1 mset_eq_setD)
  then have distinct: "distinct A'" using ys' by (simp add: distinct_map)
  have "Payload_Term ` set A' = Payload_Term ` set A" using mset_eq_setD[OF same] ys ys' by simp
  then have set: "set A' = set A" using inj_image_eq_iff[OF payload_term_inj] by blast
  show ?thesis unfolding ys' x payload_disjoint_lists using conditions distinct set by simp
qed

theorem disjoint_consumer_discharged:
  "consumer_discharged (positive_meaning payload_disjoint_system) 49 False (given_correspondence 6)"
  unfolding consumer_discharged_def consumer_argument_def if_False
proof (intro allI impI)
  fix x y y' assume "given_correspondence 6 y y'"
  then obtain N where y: "data_bag_value_presents N y" and y': "data_bag_value_presents N y'"
    by (auto simp: given_correspondence_def presentation_transport_def)
  from y y' obtain ys ys' where "y = data_list_term ys" "y' = data_list_term ys'" "mset ys = mset ys'"
    by (auto simp: data_bag_value_presents_def)
  then show "(49,Pair_Term y x) \<in> positive_meaning payload_disjoint_system \<longleftrightarrow>
      (49,Pair_Term y' x) \<in> positive_meaning payload_disjoint_system"
    using payload_disjoint_bag by metis
qed

text \<open>
  Binder admission (54) reads its rows as a set of distinct binder payloads, at the right side of its argument: a
  bag with the same members is distinct exactly when the list is and has the same set, so 54 is invariant under
  6's class at its right side.
\<close>

lemma binder_admission_bag:
  assumes holds: "(54,Pair_Term x (data_list_term ys)) \<in> positive_meaning binder_admission_system"
    and same: "mset ys = mset ys'"
  shows "(54,Pair_Term x (data_list_term ys')) \<in> positive_meaning binder_admission_system"
proof -
  from holds obtain R a r Vs where x: "x = Pair_Term a (Payload_Term r)" and ys: "ys = map Payload_Term Vs"
    and R: "artifact_value_presents R a" and conditions: "distinct Vs" "binder_scope_at R r (set Vs)"
    by (auto simp: binder_admission_exact data_list_term_injective)
  have "\<forall>y\<in>set ys'. \<exists>a. y = Payload_Term a" using mset_eq_setD[OF same] ys by auto
  then obtain Vs' where ys': "ys' = map Payload_Term Vs'" by (auto simp: ex_map_conv[symmetric])
  have "distinct ys" using conditions(1) ys by (simp add: distinct_map inj_on_subset[OF payload_term_inj subset_UNIV])
  then have "distinct ys'" using same by (metis distinct_count_atmost_1 mset_eq_setD)
  then have distinct: "distinct Vs'" using ys' by (simp add: distinct_map)
  have "Payload_Term ` set Vs' = Payload_Term ` set Vs" using mset_eq_setD[OF same] ys ys' by simp
  then have set: "set Vs' = set Vs" using inj_image_eq_iff[OF payload_term_inj] by blast
  show ?thesis unfolding x ys' using binder_admission_on_values[OF R] conditions distinct set by simp
qed

theorem binder_consumer_discharged:
  "consumer_discharged (positive_meaning binder_admission_system) 54 True (given_correspondence 6)"
  unfolding consumer_discharged_def consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "given_correspondence 6 y y'"
  then obtain N where y: "data_bag_value_presents N y" and y': "data_bag_value_presents N y'"
    by (auto simp: given_correspondence_def presentation_transport_def)
  from y y' obtain ys ys' where "y = data_list_term ys" "y' = data_list_term ys'" "mset ys = mset ys'"
    by (auto simp: data_bag_value_presents_def)
  then show "(54,Pair_Term x y) \<in> positive_meaning binder_admission_system \<longleftrightarrow>
      (54,Pair_Term x y') \<in> positive_meaning binder_admission_system"
    using binder_admission_bag by metis
qed

section \<open>The artifact's enumeration inside 10, committed at its material socket\<close>

text \<open>
  10's clause observes the artifact at its input through its complete material equation and converts the observed
  fields through 0 and 9. Every enumeration of the artifact is a solution of the material premise, and each one
  extends to a true instance of the clause keeping the head's input: its converted fields are the data of that
  enumeration. The socket is declared without the kept head.
\<close>

definition given_artifact_material :: "nat finite_material_pattern" where
  "given_artifact_material = \<lparr>finite_material_source = Finite_Variable 0, finite_material_atoms = Finite_Variable 1,
    finite_material_edges = Finite_Variable 2, finite_material_counts = Finite_Variable 3,
    finite_material_functions = Finite_Variable 4\<rparr>"

lemma given_artifact_material_decoded: "decode_finite_material given_artifact_material = artifact_projection_material"
  by (simp add: given_artifact_material_def decode_finite_material_def artifact_projection_material_def)

definition given_artifact_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "given_artifact_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6)
        (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 8)))),
    finite_schema_premises = {|(0,0,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 5)),
      (1,9,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 6))),
      (2,9,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 7))),
      (3,9,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 8)))|},
    finite_schema_materials = {|(4,given_artifact_material)|}\<rparr>"

lemma given_artifact_socket_decoded: "decode_finite_schema given_artifact_socket_schema = artifact_projection_schema"
  by (simp add: given_artifact_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def artifact_projection_schema_def given_artifact_material_decoded)

lemma artifact_projection_parts:
  "schema_premises artifact_projection_schema =
    {(0,0,Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 5)),
     (1,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 6))),
     (2,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 7))),
     (3,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8)))}"
  "schema_material_premises artifact_projection_schema = {(4,artifact_projection_material)}"
  "schema_conclusion artifact_projection_schema = Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 5)
    (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8))))"
  "material_variables artifact_projection_material = {0,1,2,3,4}"
  "schema_variables artifact_projection_schema = {0,1,2,3,4,5,6,7,8}"
  by (auto simp: artifact_projection_schema_def artifact_projection_material_def material_variables_def
    material_fields_def schema_variables_def)

lemma artifact_material_solution:
  assumes "evaluate_material_satisfaction g artifact_projection_material"
  obtains R A E B F where "artifact_enumeration R A E B F" "g 0 = Target_Term (Whole_Artifact R)"
    "g 1 = enumeration_term (map (atom_term R) A)" "g 2 = enumeration_term (map (incidence_term R) E)"
    "g 3 = enumeration_term (map (attachment_term R) B)" "g 4 = enumeration_term (map (attachment_term R) F)"
    "term_formed (g 0)" "term_formed (g 1)" "term_formed (g 2)" "term_formed (g 3)" "term_formed (g 4)"
proof -
  have obs: "material_observation (g 0) (g 1) (g 2) (g 3) (g 4)"
    using assms by (simp add: artifact_projection_material_def)
  show ?thesis using that obs material_observation_formed[OF obs] unfolding material_observation_def by blast
qed

theorem artifact_socket_discharged:
  "socket_discharged (positive_meaning artifact_projection_system) artifact_projection_schema 4 False"
  unfolding socket_discharged_def
proof (rule allI, rule impI, rule conjI)
  let ?M = "positive_meaning artifact_projection_system"
  fix h assume t: "clause_true ?M artifact_projection_schema h"
  show "\<forall>d xi yo y'. (4,d,Pattern_Pair xi yo) \<in> schema_premises artifact_projection_schema \<longrightarrow>
      (d,Pair_Term (evaluate_pattern h xi) y') \<in> ?M \<longrightarrow> (\<exists>h'. clause_true ?M artifact_projection_schema h' \<and>
        head_kept False artifact_projection_schema h h' \<and> evaluate_pattern h' xi = evaluate_pattern h xi \<and>
        evaluate_pattern h' yo = y')"
    by (simp add: artifact_projection_parts)
  show "\<forall>N g. (4,N) \<in> schema_material_premises artifact_projection_schema \<longrightarrow> evaluate_material_satisfaction g N \<longrightarrow>
      evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N) \<longrightarrow>
      (\<exists>h'. clause_true ?M artifact_projection_schema h' \<and> head_kept False artifact_projection_schema h h' \<and>
        (\<forall>a\<in>material_variables N. h' a = g a))"
  proof (rule allI, rule allI, rule impI, rule impI, rule impI)
    fix N g assume n: "(4,N) \<in> schema_material_premises artifact_projection_schema"
      and sat: "evaluate_material_satisfaction g N"
      and source: "evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N)"
    have N: "N = artifact_projection_material" using n by (simp add: artifact_projection_parts)
    obtain R A E B F where e: "artifact_enumeration R A E B F" and g0: "g 0 = Target_Term (Whole_Artifact R)"
      and g1: "g 1 = enumeration_term (map (atom_term R) A)" and g2: "g 2 = enumeration_term (map (incidence_term R) E)"
      and g3: "g 3 = enumeration_term (map (attachment_term R) B)"
      and g4: "g 4 = enumeration_term (map (attachment_term R) F)"
      and fg: "term_formed (g 0)" "term_formed (g 1)" "term_formed (g 2)" "term_formed (g 3)" "term_formed (g 4)"
      using sat unfolding N by (rule artifact_material_solution)
    have formed: "exact_formed R" and atoms: "set A = rra_carrier (object_structure R)"
      using artifact_enumeration_material[OF e] by simp_all
    let ?h = "\<lambda>a::nat. if a \<le> 4 then g a else if a = 5 then data_list_term (map Payload_Term A)
      else if a = 6 then data_list_term (map incidence_data E) else if a = 7 then data_list_term (map address_pair_data B)
      else data_list_term (map address_pair_data F)"
    have p0: "(0,Pair_Term (g 1) (data_list_term (map Payload_Term A))) \<in> positive_meaning material_data_system"
      using material_data_carrier[OF formed] atoms g1 by simp
    have p1: "(9,Pair_Term (g 1) (Pair_Term (g 2) (data_list_term (map incidence_data E)))) \<in> positive_meaning material_data_system"
      using material_projection_incidence_list[OF formed atoms] fg(3) g1 g2 by simp
    have p2: "(9,Pair_Term (g 1) (Pair_Term (g 3) (data_list_term (map address_pair_data B)))) \<in> positive_meaning material_data_system"
      using material_projection_attachment_list[OF formed atoms] fg(4) g1 g3 by simp
    have p3: "(9,Pair_Term (g 1) (Pair_Term (g 4) (data_list_term (map address_pair_data F)))) \<in> positive_meaning material_data_system"
      using material_projection_attachment_list[OF formed atoms] fg(5) g1 g4 by simp
    have f: "term_formed (data_list_term (map Payload_Term A))" "term_formed (data_list_term (map incidence_data E))"
      "term_formed (data_list_term (map address_pair_data B))" "term_formed (data_list_term (map address_pair_data F))"
      using positive_meaning_formed[OF p0] positive_meaning_formed[OF p1] positive_meaning_formed[OF p2]
        positive_meaning_formed[OF p3] by (simp_all add: material_data_call)
    have obs: "material_observation (g 0) (g 1) (g 2) (g 3) (g 4)"
      using sat unfolding N by (simp add: artifact_projection_material_def)
    have true: "clause_true ?M artifact_projection_schema ?h"
      using p0 p1 p2 p3 f fg obs
      by (auto simp: clause_true_def artifact_projection_parts artifact_projection_old_meaning artifact_projection_material_def)
    have kept: "head_kept False artifact_projection_schema h ?h"
      using source by (simp add: head_kept_def artifact_projection_parts N artifact_projection_material_def)
    show "\<exists>h'. clause_true ?M artifact_projection_schema h' \<and> head_kept False artifact_projection_schema h h' \<and>
        (\<forall>a\<in>material_variables N. h' a = g a)"
      using true kept by (intro exI[of _ ?h]) (auto simp: N artifact_projection_parts)
  qed
qed

section \<open>The artifact's enumeration inside 45's occurrence clause, committed at its material socket\<close>

text \<open>
  45's occurrence clause reads the artifact of the target's anchor through 10, observes it through the material
  equation and selects the anchor's address through the atom lookup 8. Every enumeration of the observed artifact
  is a solution, and each keeps the anchor and its address among its atoms: the clause stays true with the new
  enumeration, the head's input kept. The socket is declared without the kept head.
\<close>

lemma target_projection_material_meaning:
  assumes "d \<in> {0,1,2,3,4,5,6,7,8,9}"
  shows "(d,t) \<in> positive_meaning target_projection_system \<longleftrightarrow> (d,t) \<in> positive_meaning material_data_system"
proof -
  have located: "d \<in> system_definitions located_admission_system"
    using assms whole_agreement_definitions[OF located_target_agreement] by auto
  have identity: "d \<in> system_definitions artifact_identity_system" using assms by auto
  have "(d,t) \<in> positive_meaning target_projection_system \<longleftrightarrow> (d,t) \<in> positive_meaning located_admission_system"
    by (rule target_projection_old_meaning[OF located])
  also have "\<dots> \<longleftrightarrow> (d,t) \<in> positive_meaning complete_data_admission_system"
    using whole_system_agreement_meaning[OF located_admission_system_formed complete_data_admission_system_formed
      complete_data_located_agreement located] by simp
  also have "\<dots> \<longleftrightarrow> (d,t) \<in> positive_meaning artifact_identity_system"
    by (rule whole_system_agreement_meaning[OF artifact_identity_system_formed complete_data_admission_system_formed
      identity_complete_data_agreement identity])
  also have "\<dots> \<longleftrightarrow> (d,t) \<in> positive_meaning material_data_system"
  proof -
    have d11: "d \<in> {0,1,2,3,4,5,6,7,8,9,10,11}" and d10: "d \<in> {0,1,2,3,4,5,6,7,8,9,10}" using assms by auto
    show ?thesis using artifact_identity_previous_meaning[OF d11] artifact_admission_old_meaning[OF d10]
      artifact_projection_old_meaning[OF assms] by simp
  qed
  finally show ?thesis .
qed

definition given_target_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "given_target_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 5)
      (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Pattern_Payload []))),
    finite_schema_premises = {|(0,10,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 7)),
      (1,8,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))|},
    finite_schema_materials = {|(2,given_artifact_material)|}\<rparr>"

lemma given_target_socket_decoded: "decode_finite_schema given_target_socket_schema = target_projection_occurrence_schema"
  by (simp add: given_target_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def target_projection_occurrence_schema_def given_artifact_material_decoded)

lemma target_projection_occurrence_parts:
  "schema_premises target_projection_occurrence_schema =
    {(0,10,Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 7)),
     (1,8,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)))}"
  "schema_material_premises target_projection_occurrence_schema = {(2,artifact_projection_material)}"
  "schema_conclusion target_projection_occurrence_schema = Pattern_Pair (Pattern_Variable 5)
    (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 6) (Pattern_Payload [])))"
  "schema_variables target_projection_occurrence_schema = {0,1,2,3,4,5,6,7}"
  by (auto simp: target_projection_occurrence_schema_def artifact_projection_material_def material_variables_def
    material_fields_def schema_variables_def)

theorem target_socket_discharged:
  "socket_discharged (positive_meaning target_projection_system) target_projection_occurrence_schema 2 False"
  unfolding socket_discharged_def
proof (rule allI, rule impI, rule conjI)
  let ?M = "positive_meaning target_projection_system"
  fix h assume t: "clause_true ?M target_projection_occurrence_schema h"
  show "\<forall>d xi yo y'. (2,d,Pattern_Pair xi yo) \<in> schema_premises target_projection_occurrence_schema \<longrightarrow>
      (d,Pair_Term (evaluate_pattern h xi) y') \<in> ?M \<longrightarrow> (\<exists>h'. clause_true ?M target_projection_occurrence_schema h' \<and>
        head_kept False target_projection_occurrence_schema h h' \<and> evaluate_pattern h' xi = evaluate_pattern h xi \<and>
        evaluate_pattern h' yo = y')"
    by (simp add: target_projection_occurrence_parts)
  show "\<forall>N g. (2,N) \<in> schema_material_premises target_projection_occurrence_schema \<longrightarrow>
      evaluate_material_satisfaction g N \<longrightarrow>
      evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N) \<longrightarrow>
      (\<exists>h'. clause_true ?M target_projection_occurrence_schema h' \<and>
        head_kept False target_projection_occurrence_schema h h' \<and> (\<forall>a\<in>material_variables N. h' a = g a))"
  proof (rule allI, rule allI, rule impI, rule impI, rule impI)
    fix N g assume n: "(2,N) \<in> schema_material_premises target_projection_occurrence_schema"
      and sat: "evaluate_material_satisfaction g N"
      and source: "evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N)"
    have N: "N = artifact_projection_material" using n by (simp add: target_projection_occurrence_parts)
    have hparts: "evaluate_material_satisfaction h artifact_projection_material"
      "(10,Pair_Term (h 0) (h 7)) \<in> ?M" "(8,Pair_Term (h 1) (Pair_Term (h 5) (h 6))) \<in> ?M"
      "\<forall>a\<in>{0,1,2,3,4,5,6,7::nat}. term_formed (h a)"
      using t by (auto simp: clause_true_def target_projection_occurrence_parts)
    obtain R A E B F where e: "artifact_enumeration R A E B F" and g0: "g 0 = Target_Term (Whole_Artifact R)"
      and g1: "g 1 = enumeration_term (map (atom_term R) A)"
      and fg: "term_formed (g 0)" "term_formed (g 1)" "term_formed (g 2)" "term_formed (g 3)" "term_formed (g 4)"
      using sat unfolding N by (rule artifact_material_solution) blast
    obtain R' A' E' B' F' where e': "artifact_enumeration R' A' E' B' F'" and h0: "h 0 = Target_Term (Whole_Artifact R')"
      and h1: "h 1 = enumeration_term (map (atom_term R') A')"
      using hparts(1) by (rule artifact_material_solution) blast
    have same: "R' = R" using source g0 h0 by (simp add: N artifact_projection_material_def)
    have formed: "exact_formed R" and atoms: "set A = rra_carrier (object_structure R)"
      using artifact_enumeration_material[OF e] by simp_all
    have atoms': "set A' = rra_carrier (object_structure R)"
      using artifact_enumeration_material[OF e'] same by simp
    have "(8,Pair_Term (h 1) (Pair_Term (h 5) (h 6))) \<in> positive_meaning material_data_system"
      using hparts(3) target_projection_material_meaning[of 8] by simp
    then obtain a where a: "a \<in> set A'" "h 5 = occurrence_term R a" "h 6 = Payload_Term a"
      using atom_lookup_exact[of R A' "h 5" "h 6"] formed atoms' h1 same by auto
    have lookup: "(8,Pair_Term (g 1) (Pair_Term (h 5) (h 6))) \<in> ?M"
      using atom_lookup_exact[of R A "h 5" "h 6"] formed atoms a atoms' g1 target_projection_material_meaning[of 8]
      by auto
    let ?h = "\<lambda>a::nat. if a \<le> 4 then g a else h a"
    have obs: "material_observation (g 0) (g 1) (g 2) (g 3) (g 4)"
      using sat unfolding N by (simp add: artifact_projection_material_def)
    have whole: "(10,Pair_Term (g 0) (h 7)) \<in> ?M" using hparts(2) source by (simp add: N artifact_projection_material_def)
    have true: "clause_true ?M target_projection_occurrence_schema ?h"
      using whole lookup hparts(4) fg obs
      by (auto simp: clause_true_def target_projection_occurrence_parts artifact_projection_material_def)
    have kept: "head_kept False target_projection_occurrence_schema h ?h"
      by (simp add: head_kept_def target_projection_occurrence_parts)
    show "\<exists>h'. clause_true ?M target_projection_occurrence_schema h' \<and>
        head_kept False target_projection_occurrence_schema h h' \<and> (\<forall>a\<in>material_variables N. h' a = g a)"
      using true kept by (intro exI[of _ ?h]) (auto simp: N target_projection_occurrence_parts artifact_projection_parts)
  qed
qed

section \<open>The given's declarations\<close>

text \<open>
  Each notion's declarations, discharged at the notion's own system with the one correspondence
  @{const given_correspondence}. Their union, read over the given's rooted readers, is what the committed search
  takes; its discharge at the given's programs is the transfer's, from these.
\<close>

definition given_bag_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_bag_declarations = \<lparr>declared_producers = {|6|}, declared_consumers = {||},
    declared_sockets = {|(6,given_bag_socket_schema,1,False)|}\<rparr>"

definition given_artifact_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_artifact_declarations = \<lparr>declared_producers = {|10|}, declared_consumers = {||},
    declared_sockets = {|(10,given_artifact_socket_schema,4,False)|}\<rparr>"

definition given_family_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_family_declarations = \<lparr>declared_producers = {|32|}, declared_consumers = {||}, declared_sockets = {||}\<rparr>"

definition given_target_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_target_declarations = \<lparr>declared_producers = {|45|}, declared_consumers = {||},
    declared_sockets = {|(45,given_target_socket_schema,2,False)|}\<rparr>"

definition given_disjoint_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_disjoint_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(6,49,False)|},
    declared_sockets = {||}\<rparr>"

definition given_binder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_binder_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(6,54,True)|},
    declared_sockets = {||}\<rparr>"

theorem given_notion_declarations_discharged:
  "declarations_discharged (positive_meaning bag_comparison_system) given_bag_declarations given_correspondence"
  "declarations_discharged (positive_meaning artifact_projection_system) given_artifact_declarations given_correspondence"
  "declarations_discharged (positive_meaning family_admission_system) given_family_declarations given_correspondence"
  "declarations_discharged (positive_meaning target_projection_system) given_target_declarations given_correspondence"
  "declarations_discharged (positive_meaning payload_disjoint_system) given_disjoint_declarations given_correspondence"
  "declarations_discharged (positive_meaning binder_admission_system) given_binder_declarations given_correspondence"
  using bag_producer_discharged bag_socket_discharged artifact_producer_discharged artifact_socket_discharged
    family_producer_discharged target_producer_discharged target_socket_discharged disjoint_consumer_discharged
    binder_consumer_discharged
  by (simp_all add: declarations_discharged_def given_bag_declarations_def given_artifact_declarations_def
    given_family_declarations_def given_target_declarations_def given_disjoint_declarations_def
    given_binder_declarations_def
    given_bag_socket_decoded given_artifact_socket_decoded given_target_socket_decoded)

definition given_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_declarations = \<lparr>declared_producers = {|6,10,32,45|}, declared_consumers = {|(6,49,False),(6,54,True)|},
    declared_sockets = {|(6,given_bag_socket_schema,1,False),(10,given_artifact_socket_schema,4,False),
      (45,given_target_socket_schema,2,False)|}\<rparr>"

end
