theory RRA_Bound_Forests
  imports RRA_Syntax_Composition
begin

section \<open>Combining child syntax without an intervening constructor\<close>

definition bound_union :: "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact" where
  "bound_union R S =
    \<lparr>object_structure =
      \<lparr>rra_carrier = syntax_prefix 2 ` rra_carrier (object_structure R) \<union>
          syntax_prefix 3 ` rra_carrier (object_structure S),
       rra_incidence = rra_incidence (push_structure (syntax_prefix 2) (object_structure R)) \<union>
          rra_incidence (push_structure (syntax_prefix 3) (object_structure S))\<rparr>,
     object_data = object_data (bound_pair_syntax R S)\<rparr>"

lemma bound_union_no_counts [simp]:
  "bag_count (object_data (bound_union R S)) = (\<lambda>_. 0)"
  by (simp add: bound_union_def)

lemma bound_union_formed:
  assumes rf: "exact_formed R" and sf: "exact_formed S"
    and silent: "binder_silent R" "binder_silent S"
  shows "exact_formed (bound_union R S)"
proof -
  have objects: "object_formed R" "object_formed S" using rf sf by (auto simp: exact_formed_def)
  have functional: "single_valued (functional_bindings (object_data (bound_pair_syntax R S)))"
    by (rule bound_pair_bindings_functional[OF objects silent])
  have formed: "object_formed (bound_union R S)"
    using objects functional
    by (auto simp: object_formed_def rra_formed_def basis_formed_def bound_union_def
        bound_pair_syntax_def push_structure_def bag_support_def)
  have left_addressing: "finite_addressing (rra_carrier (object_structure R)) (syntax_prefix 2)"
    by (rule syntax_prefix_addressing[OF rf]) simp_all
  have right_addressing: "finite_addressing (rra_carrier (object_structure S)) (syntax_prefix 3)"
    by (rule syntax_prefix_addressing[OF sf]) simp_all
  have payloads: "\<And>a v. (a,v) \<in> functional_bindings (object_data R) \<union>
    functional_bindings (object_data S) \<Longrightarrow> octets_formed v"
  proof -
    fix a v assume member: "(a,v) \<in> functional_bindings (object_data R) \<union>
      functional_bindings (object_data S)"
    have "v \<in> basis_values (object_data R) \<union> basis_values (object_data S)"
      using member by (force simp: basis_values_def)
    then show "octets_formed v" using rf sf by (auto simp: exact_formed_def)
  qed
  show ?thesis using formed left_addressing right_addressing payloads
    by (auto simp: exact_formed_def bound_union_def bound_pair_syntax_def basis_values_def
        bag_support_def finite_addressing_def; blast)
qed

lemma bound_union_head:
  "headed_incidence (object_structure (bound_union R S)) a =
    headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) a \<union>
    headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) a"
  by (auto simp: bound_union_def headed_incidence_def)

lemma bound_union_head_left:
  assumes "binder_silent S"
  shows "headed_incidence (object_structure (bound_union R S)) (syntax_prefix 2 a) =
    headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) (syntax_prefix 2 a)"
  using other_prefix_head_empty[OF assms, of 2 3 a]
  by (simp add: bound_union_head)

lemma bound_union_head_right:
  assumes "binder_silent R"
  shows "headed_incidence (object_structure (bound_union R S)) (syntax_prefix 3 a) =
    headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) (syntax_prefix 3 a)"
  using other_prefix_head_empty[OF assms, of 3 2 a]
  by (simp add: bound_union_head)

lemma bound_union_reads_left:
  assumes counts: "bag_count (object_data R) = (\<lambda>_. 0)" and silent: "binder_silent S"
  shows "object_reads_agree (push_object (syntax_prefix 2) R) (bound_union R S)
    (syntax_prefix 2 ` rra_carrier (object_structure R))"
proof -
  have original: "object_reads_agree (push_object (syntax_prefix 2) R) (bound_pair_syntax R S)
    (syntax_prefix 2 ` rra_carrier (object_structure R))"
    by (rule bound_pair_reads_left[OF counts silent])
  have heads: "\<And>a. headed_incidence (object_structure (bound_union R S)) (syntax_prefix 2 a) =
    headed_incidence (object_structure (bound_pair_syntax R S)) (syntax_prefix 2 a)"
    using bound_union_head_left[OF silent] bound_pair_head_left[OF silent] by simp
  show ?thesis using original heads
    by (auto simp: object_reads_agree_def bound_union_def)
qed

lemma bound_union_reads_right:
  assumes counts: "bag_count (object_data S) = (\<lambda>_. 0)" and silent: "binder_silent R"
  shows "object_reads_agree (push_object (syntax_prefix 3) S) (bound_union R S)
    (syntax_prefix 3 ` rra_carrier (object_structure S))"
proof -
  have original: "object_reads_agree (push_object (syntax_prefix 3) S) (bound_pair_syntax R S)
    (syntax_prefix 3 ` rra_carrier (object_structure S))"
    by (rule bound_pair_reads_right[OF counts silent])
  have heads: "\<And>a. headed_incidence (object_structure (bound_union R S)) (syntax_prefix 3 a) =
    headed_incidence (object_structure (bound_pair_syntax R S)) (syntax_prefix 3 a)"
    using bound_union_head_right[OF silent] bound_pair_head_right[OF silent] by simp
  show ?thesis using original heads
    by (auto simp: object_reads_agree_def bound_union_def)
qed

lemma bound_union_silent:
  assumes "binder_silent R" "binder_silent S"
  shows "binder_silent (bound_union R S)"
  using bound_pair_silent[OF assms]
  by (auto simp: binder_silent_def bound_union_def bound_pair_syntax_def headed_incidence_def)

lemma empty_artifact_binder_silent [simp]: "binder_silent empty_artifact"
  by (simp add: binder_silent_def empty_artifact_def headed_incidence_def)

text \<open>
  The two child copies overlap only at silent binder occurrences. The union
  contributes no root, port, tag, or data attachment of its own. Both complete
  child reads survive, including incoming uses of shared binders. Iterating
  this operation therefore supports an arbitrary finite family of bodies
  without leaving unused constructor occurrences in the resulting artifact.
\<close>

end
