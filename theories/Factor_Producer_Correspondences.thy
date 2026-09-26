theory Factor_Producer_Correspondences
  imports Factor_Resolution_Views Factor_Bag_Presentations Factor_Binder_Admission Factor_Target_Projection
begin

text \<open>
  The classes at the outputs of four presentation-free producers, each a notion's reader (bag comparison 6, artifact
  projection 10, family admission 32, target projection 45, at their numbers in the given's readers), the
  correspondence of two outputs presenting one subject (@{text given_correspondence}), and each producer discharged
  at its notion's own system from the notion's exact contract. They are stated below the declaration theories that
  read them, so that no Factor theory reads the given's program (moved from @{text Development_Given_Declarations},
  names kept). Two enumerations of one family's rows are one bag of rows (@{text family_rows_enumerations}): stated
  once here, and read as a bag by every declaration that carries 32's output.
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
  "producer_discharged (positive_meaning bag_comparison_system) 6 view_identity [view_output]
    (\<lambda>i. given_correspondence 6)"
  unfolding producer_discharged_identity
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
  "producer_discharged (positive_meaning artifact_projection_system) 10 view_identity [view_output]
    (\<lambda>i. given_correspondence 10)"
  unfolding producer_discharged_identity
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
  "producer_discharged (positive_meaning target_projection_system) 45 view_identity [view_output]
    (\<lambda>i. given_correspondence 45)"
  unfolding producer_discharged_identity
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
  "producer_discharged (positive_meaning family_admission_system) 32 view_identity [view_output]
    (\<lambda>i. given_correspondence 32)"
  unfolding producer_discharged_identity
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

text \<open>
  Two outputs of 32 in correspondence enumerate one set of rows, each without repetition: as lists they hold the same
  rows with the same multiplicities.
\<close>

lemma family_rows_enumerations:
  assumes "given_correspondence 32 x y"
  obtains xs ys where "distinct xs" "distinct ys" "mset xs = mset ys"
    "x = data_list_term (map address_pair_data xs)" "y = data_list_term (map address_pair_data ys)"
proof -
  obtain A where presents: "family_rows_presents A x" "family_rows_presents A y"
    using assms by (auto simp: given_correspondence_def presentation_transport_def)
  obtain xs where left: "distinct xs" "set xs = A" "x = data_list_term (map address_pair_data xs)"
    using presents(1) by (auto simp: data_collection_presents_def list_all2_function)
  obtain ys where right: "distinct ys" "set ys = A" "y = data_list_term (map address_pair_data ys)"
    using presents(2) by (auto simp: data_collection_presents_def list_all2_function)
  have "mset xs = mset ys" using left right set_eq_iff_mset_eq_distinct by metis
  then show thesis using that left(1,3) right(1,3) by blast
qed

end
