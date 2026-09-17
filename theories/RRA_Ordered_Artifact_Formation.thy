theory RRA_Ordered_Artifact_Formation
  imports Finite_Ordered_Relation_Checks
begin

definition ordered_object_formed ::
  "('a::linorder,'v::linorder) finite_structured_object \<Rightarrow> bool" where
  "ordered_object_formed C=(
    let S=finite_structure C; D=finite_data C;
        incidence=sorted_list_of_fset (finite_incidence S);
        counted=sorted_list_of_multiset (finite_bag D);
        bindings=sorted_list_of_fset (finite_bindings D);
        used=concat (map (\<lambda>(r,p,x). [r,p,x]) incidence) @ map fst counted @ map fst bindings
    in ascending_listing (map fst bindings) \<and>
      ordered_fset_subset (fset_of_list used) (finite_carrier S))"

lemma listed_fields_subset:
  "fset_of_list (concat (map slots_of xs)) |\<subseteq>| U \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<forall>a\<in>set (slots_of x). a |\<in>| U)"
  by (auto simp: fsubset_iff fset_of_list.rep_eq)

theorem ordered_object_formed_exact:
  "ordered_object_formed C=finite_object_formed C"
proof -
  let ?S="finite_structure C" and ?D="finite_data C"
  have incidence:
    "fset_of_list (concat (map (\<lambda>(r,p,x). [r,p,x]) (sorted_list_of_fset (finite_incidence ?S))))
      |\<subseteq>| finite_carrier ?S \<longleftrightarrow> finite_structure_formed ?S"
    by (simp add: listed_fields_subset finite_structure_formed_def split_beta)
  have counted:
    "fset_of_list (map fst (sorted_list_of_multiset (finite_bag ?D))) |\<subseteq>| finite_carrier ?S
      \<longleftrightarrow> (\<forall>x\<in>set_mset (finite_bag ?D). fst x |\<in>| finite_carrier ?S)"
    by (auto simp: fsubset_iff fset_of_list.rep_eq)
  have bindings:
    "fset_of_list (map fst (sorted_list_of_fset (finite_bindings ?D))) |\<subseteq>| finite_carrier ?S
      \<longleftrightarrow> fBall (finite_bindings ?D) (\<lambda>x. fst x |\<in>| finite_carrier ?S)"
    by (auto simp: fsubset_iff fset_of_list.rep_eq)
  show ?thesis
    by (simp only: ordered_object_formed_def Let_def ordered_relation_functional_def[symmetric]
        ordered_relation_functional_exact
        ordered_fset_subset_exact fset_of_list_append funion_fsubset_iff incidence counted bindings
        finite_object_formed_def finite_basis_formed_def conj_assoc conj_left_commute)
qed

declare finite_exact_formed_def[code del]

theorem finite_exact_formed_ordered_code [code]:
  "finite_exact_formed C=(ordered_object_formed C \<and>
    fBall (finite_carrier (finite_structure C)) octets_formed \<and>
    (\<forall>x\<in>set_mset (finite_bag (finite_data C)). octets_formed (snd x)) \<and>
    fBall (finite_bindings (finite_data C)) (\<lambda>x. octets_formed (snd x)))"
  by (simp only: finite_exact_formed_def ordered_object_formed_exact)

text \<open>Every original incidence endpoint and data address must still belong
  to the carrier, and functional bindings must still be functional. All original
  byte conditions remain. The exact Boolean equation applies to arbitrary
  complete artifacts, including malformed objects and repeated counted data;
  the artifact and every count remain unchanged.\<close>

end
