theory RRA_Fragment
  imports RRA_Structural_Syntax
begin

section \<open>Boundary-complete structural selection\<close>

text \<open>
  A fragment is not a copied subobject carrying a second source of truth.  It is
  an exact source artifact together with an exact selected carrier.  Its
  material, crossing boundary, and omitted remainder are derived projections.
\<close>

record exact_fragment =
  fragment_source :: exact_artifact
  fragment_selection :: "local_address set"

definition fragment_formed :: "exact_fragment \<Rightarrow> bool" where
  "fragment_formed F \<longleftrightarrow>
     exact_formed (fragment_source F) \<and>
     finite (fragment_selection F) \<and>
     fragment_selection F \<subseteq>
       rra_carrier (object_structure (fragment_source F))"

definition fragment_material :: "exact_fragment \<Rightarrow> exact_artifact" where
  "fragment_material F =
     restrict_object (fragment_source F) (fragment_selection F)"

definition fragment_boundary ::
  "exact_fragment \<Rightarrow> (local_address \<times> local_address \<times> local_address) set" where
  "fragment_boundary F =
     crossing_incidence (object_structure (fragment_source F))
                        (fragment_selection F)"

definition fragment_omission :: "exact_fragment \<Rightarrow> local_address set" where
  "fragment_omission F =
     rra_carrier (object_structure (fragment_source F)) - fragment_selection F"

definition fragment_remainder :: "exact_fragment \<Rightarrow> exact_artifact" where
  "fragment_remainder F = restrict_object (fragment_source F) (fragment_omission F)"

lemma fragment_material_formed:
  assumes "fragment_formed F"
  shows "exact_formed (fragment_material F)"
  using assms restrict_object_formed basis_values_restrict
  by (auto simp: fragment_formed_def fragment_material_def exact_formed_def
      restrict_object_def restrict_structure_def internal_incidence_def
      dest: basis_values_restrictD)

lemma fragment_incidence_partition:
  assumes "fragment_formed F"
  defines "S \<equiv> object_structure (fragment_source F)"
      and "A \<equiv> fragment_selection F"
  shows "rra_incidence S =
           internal_incidence S A \<union>
           internal_incidence S (rra_carrier S - A) \<union>
           crossing_incidence S A"
proof
  show "rra_incidence S \<subseteq>
        internal_incidence S A \<union>
        internal_incidence S (rra_carrier S - A) \<union>
        crossing_incidence S A"
  proof
    fix t
    assume t: "t \<in> rra_incidence S"
    obtain r p x where teq: "t = (r,p,x)"
      by (cases t) auto
    from assms t teq have members:
      "r \<in> rra_carrier S" "p \<in> rra_carrier S" "x \<in> rra_carrier S"
      by (auto simp: fragment_formed_def exact_formed_def object_formed_def
          rra_formed_def S_def)
    show "t \<in> internal_incidence S A \<union>
              internal_incidence S (rra_carrier S - A) \<union>
              crossing_incidence S A"
      using t teq members
      by (auto simp: internal_incidence_def crossing_incidence_def
          touching_incidence_def)
  qed
  show "internal_incidence S A \<union>
        internal_incidence S (rra_carrier S - A) \<union>
        crossing_incidence S A \<subseteq> rra_incidence S"
    by (auto simp: internal_incidence_def crossing_incidence_def
        touching_incidence_def)
qed

lemma fragment_boundary_complete:
  assumes "fragment_formed F"
  shows "fragment_boundary F =
   touching_incidence (object_structure (fragment_source F))
                      (fragment_selection F) -
   rra_incidence (object_structure (fragment_material F))"
  using assms
  by (auto simp: fragment_formed_def fragment_boundary_def fragment_material_def
      crossing_incidence_def restrict_object_def restrict_structure_def
      internal_incidence_def)

lemma fragment_remainder_formed:
  assumes "fragment_formed F"
  shows "exact_formed (fragment_remainder F)"
  using assms restrict_object_formed basis_values_restrict
  by (auto simp: fragment_formed_def fragment_remainder_def exact_formed_def
      restrict_object_def restrict_structure_def internal_incidence_def
      dest: basis_values_restrictD)

lemma fragment_carrier_partition:
  assumes "fragment_formed F"
  shows "rra_carrier (object_structure (fragment_source F)) =
    rra_carrier (object_structure (fragment_material F)) \<union>
    rra_carrier (object_structure (fragment_remainder F))"
    and "rra_carrier (object_structure (fragment_material F)) \<inter>
      rra_carrier (object_structure (fragment_remainder F)) = {}"
  using assms
  by (auto simp: fragment_formed_def fragment_material_def fragment_remainder_def
    fragment_omission_def restrict_object_def restrict_structure_def)

lemma fragment_data_partition:
  assumes formed: "fragment_formed F"
  shows "bag_count (object_data (fragment_source F)) (a,v) =
    bag_count (object_data (fragment_material F)) (a,v) +
    bag_count (object_data (fragment_remainder F)) (a,v)"
    and "functional_bindings (object_data (fragment_source F)) =
      functional_bindings (object_data (fragment_material F)) \<union>
      functional_bindings (object_data (fragment_remainder F))"
    and "bag_support (object_data (fragment_material F)) \<inter>
      bag_support (object_data (fragment_remainder F)) = {}"
    and "functional_bindings (object_data (fragment_material F)) \<inter>
      functional_bindings (object_data (fragment_remainder F)) = {}"
proof -
  have bf: "basis_formed (rra_carrier (object_structure (fragment_source F)))
    (object_data (fragment_source F))"
    using formed by (simp add: fragment_formed_def exact_formed_def object_formed_def)
  have zero: "a \<notin> rra_carrier (object_structure (fragment_source F)) \<Longrightarrow>
    bag_count (object_data (fragment_source F)) (a,v) = 0"
    by (rule count_outside_carrier[OF bf])
  show "bag_count (object_data (fragment_source F)) (a,v) =
    bag_count (object_data (fragment_material F)) (a,v) +
    bag_count (object_data (fragment_remainder F)) (a,v)"
    using zero
    by (auto simp: fragment_material_def fragment_remainder_def fragment_omission_def
      restrict_object_def restrict_basis_def)
  show "functional_bindings (object_data (fragment_source F)) =
      functional_bindings (object_data (fragment_material F)) \<union>
      functional_bindings (object_data (fragment_remainder F))"
    using bf
    by (auto simp: basis_formed_def fragment_material_def fragment_remainder_def
      fragment_omission_def restrict_object_def restrict_basis_def)
  show "bag_support (object_data (fragment_material F)) \<inter>
      bag_support (object_data (fragment_remainder F)) = {}"
    and "functional_bindings (object_data (fragment_material F)) \<inter>
      functional_bindings (object_data (fragment_remainder F)) = {}"
    by (auto simp: fragment_material_def fragment_remainder_def fragment_omission_def
      restrict_object_def restrict_basis_def bag_support_def split: if_splits)
qed

lemma fragment_source_reconstructed:
  assumes formed: "fragment_formed F"
  shows "fragment_source F =
    \<lparr>object_structure =
      \<lparr>rra_carrier =
        rra_carrier (object_structure (fragment_material F)) \<union>
        rra_carrier (object_structure (fragment_remainder F)),
       rra_incidence =
        rra_incidence (object_structure (fragment_material F)) \<union>
        rra_incidence (object_structure (fragment_remainder F)) \<union>
        fragment_boundary F\<rparr>,
     object_data =
       \<lparr>bag_count = (\<lambda>(a,v).
         bag_count (object_data (fragment_material F)) (a,v) +
         bag_count (object_data (fragment_remainder F)) (a,v)),
        functional_bindings =
          functional_bindings (object_data (fragment_material F)) \<union>
          functional_bindings (object_data (fragment_remainder F))\<rparr>\<rparr>"
proof -
  have sel: "rra_carrier (object_structure (fragment_source F)) \<inter> fragment_selection F =
    fragment_selection F"
    using formed by (auto simp: fragment_formed_def)
  have rem: "rra_carrier (object_structure (fragment_source F)) \<inter>
    (rra_carrier (object_structure (fragment_source F)) - fragment_selection F) =
    rra_carrier (object_structure (fragment_source F)) - fragment_selection F"
    by blast
  have inc: "rra_incidence (object_structure (fragment_source F)) =
    rra_incidence (object_structure (fragment_material F)) \<union>
    rra_incidence (object_structure (fragment_remainder F)) \<union> fragment_boundary F"
    using fragment_incidence_partition[OF formed]
    by (simp add: fragment_material_def fragment_remainder_def fragment_omission_def
      fragment_boundary_def restrict_object_def restrict_structure_def sel rem)
  show ?thesis
    using inc fragment_carrier_partition(1)[OF formed] fragment_data_partition(1,2)[OF formed]
    by (auto simp: exact_identity_iff rra_identity basis_identity fun_eq_iff)
qed

text \<open>
  Nonselection is not destruction.  The source, selected material, exact
  crossing boundary, and omitted object are simultaneously recoverable from
  the one fragment witness. The two data restrictions are disjoint and recover
  all source data. Each attachment has one atom; there is no additional crossing
  data relation.
\<close>

end
