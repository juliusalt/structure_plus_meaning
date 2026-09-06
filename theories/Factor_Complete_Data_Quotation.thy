theory Factor_Complete_Data_Quotation
  imports Factor_Self_Contained_Terms
begin

section \<open>Complete copies of self-contained data syntax\<close>

definition complete_data_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "complete_data_quoted_at C r t \<longleftrightarrow>
    term_formed t \<and> self_contained_term t \<and>
    (\<exists>f. finite_addressing (rra_carrier (object_structure (term_syntax t))) f \<and>
      C=push_object f (term_syntax t) \<and> r=f [])"

theorem complete_data_quotation_native:
  assumes quoted: "complete_data_quoted_at C r t"
  shows "self_contained_quoted_at C r t (rra_carrier (object_structure C))"
proof -
  obtain f where tf: "term_formed t" and closed: "self_contained_term t"
    and address: "finite_addressing (rra_carrier (object_structure (term_syntax t))) f"
    and source: "C=push_object f (term_syntax t)" and root: "r=f []"
    using quoted unfolding complete_data_quoted_at_def by blast
  let ?S = "term_syntax t"
  let ?E = "singleton_environment ?S"
  let ?F = "singleton_environment C"
  have base: "self_contained_quoted_at ?S [] t (term_syntax_interior t)"
    and sf: "exact_formed ?S" and carrier: "rra_carrier (object_structure ?S)=term_syntax_interior t"
    using self_contained_quotation_total[OF tf closed] by auto
  have read: "term_quoted_at ?E () [] t (term_syntax_interior t) {}"
    using base by (simp add: self_contained_quoted_at_def)
  have art: "artifact_at ?E () ?S" and destination: "artifact_at ?F () C"
    by (simp_all add: singleton_environment_def artifact_at_def)
  have cf: "exact_formed C" using exact_push_formed[OF sf address] source by simp
  have ff: "environment_formed ?F"
    using singleton_environment_closed[OF cf] by (simp add: environment_closed_def)
  have reads: "object_reads_agree (push_object f ?S) C (f ` term_syntax_interior t)"
    using source carrier by (auto simp: object_reads_agree_def push_object_def push_structure_def)
  have slots: "\<forall>k\<in>{}. external_slot_values ?E () k=external_slot_values ?F () (f k)"
    by simp
  have native: "term_quoted_at ?F () (f []) t (f ` term_syntax_interior t) (f ` {})"
    by (rule term_quotation_transport[OF read art address reads slots ff destination])
  have interior: "f ` term_syntax_interior t=rra_carrier (object_structure C)"
    using source carrier by (simp add: push_object_def push_structure_def)
  show ?thesis using closed native interior root by (simp add: self_contained_quoted_at_def)
qed

lemma complete_data_quotation_formed:
  assumes "complete_data_quoted_at C r t"
  shows "exact_formed C \<and> term_formed t \<and> self_contained_term t"
  using self_contained_quoted_formed[OF complete_data_quotation_native[OF assms]]
    assms by (simp add: complete_data_quoted_at_def)

theorem complete_data_quotation_unique:
  assumes "complete_data_quoted_at C r t" "complete_data_quoted_at C r v"
  shows "t=v"
  using self_contained_quoted_unique[
    OF complete_data_quotation_native[OF assms(1)] complete_data_quotation_native[OF assms(2)]] by blast

lemma complete_data_quotation_anchor:
  assumes quote: "complete_data_quoted_at C r t"
  shows "anchor_formed (C,r)"
proof -
  obtain f where source: "C=push_object f (term_syntax t)" and root: "r=f []"
    using quote unfolding complete_data_quoted_at_def by blast
  have formed: "exact_formed C" using complete_data_quotation_formed[OF quote] by blast
  have inside: "r \<in> rra_carrier (object_structure C)"
    using source root by (auto simp: push_object_def push_structure_def)
  show ?thesis using formed inside by (simp add: anchor_formed_def)
qed

theorem complete_data_quotation_total:
  assumes formed: "term_formed t" and closed: "self_contained_term t"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have rf: "exact_formed (term_syntax t)" by (rule term_syntax_formed[OF formed])
  have address: "finite_addressing (rra_carrier (object_structure (term_syntax t))) id"
    using rf by (auto simp: finite_addressing_def exact_formed_def)
  have oformed: "object_formed (term_syntax t)" using rf by (simp add: exact_formed_def)
  have identical: "push_object id (term_syntax t)=term_syntax t"
    by (rule push_object_identity[OF oformed])
  have copy: "\<exists>f. finite_addressing (rra_carrier (object_structure (term_syntax t))) f \<and>
    term_syntax t=push_object f (term_syntax t) \<and> []=f []"
    by (rule exI[of _ id]) (use address identical in simp)
  show ?thesis using formed closed copy by (simp add: complete_data_quoted_at_def)
qed

lemma complete_data_quotation_every_addressing:
  assumes formed: "term_formed t" and closed: "self_contained_term t"
    and address: "finite_addressing (rra_carrier (object_structure (term_syntax t))) f"
  shows "complete_data_quoted_at (push_object f (term_syntax t)) (f []) t"
  using assms unfolding complete_data_quoted_at_def by blast

section \<open>The complete structure determines its quotation root\<close>

lemma unreferenced_positions_push:
  assumes formed: "rra_formed S" and injective: "inj_on f (rra_carrier S)"
  shows "rra_carrier (push_structure f S) -
      (participation_occurrences (push_structure f S) \<union>
       reached_occurrences (push_structure f S)) =
    f ` (rra_carrier S - (participation_occurrences S \<union> reached_occurrences S))"
proof -
  have inside: "participation_occurrences S \<subseteq> rra_carrier S"
    "reached_occurrences S \<subseteq> rra_carrier S"
    using role_occurrences_in_carrier[OF formed] by blast+
  show ?thesis using inside injective
    by (auto simp: participation_occurrences_push reached_occurrences_push inj_on_def)
qed

theorem complete_data_quotation_root_boundary:
  assumes quoted: "complete_data_quoted_at C r t"
  shows "rra_carrier (object_structure C) -
    (participation_occurrences (object_structure C) \<union>
     reached_occurrences (object_structure C)) = {r}"
proof -
  obtain f where tf: "term_formed t" and closed: "self_contained_term t"
    and address: "finite_addressing (rra_carrier (object_structure (term_syntax t))) f"
    and source: "C=push_object f (term_syntax t)" and root: "r=f []"
    using quoted unfolding complete_data_quoted_at_def by blast
  have formed: "rra_formed (object_structure (term_syntax t))"
    using term_syntax_formed[OF tf] by (simp add: exact_formed_def object_formed_def)
  have injective: "inj_on f (rra_carrier (object_structure (term_syntax t)))"
    using address by (simp add: finite_addressing_def)
  show ?thesis using unreferenced_positions_push[OF formed injective]
    self_contained_syntax_unreferenced[OF closed]
    by (simp add: source root push_object_def)
qed

theorem complete_data_quotation_whole_unique:
  assumes first: "complete_data_quoted_at C r t" and second: "complete_data_quoted_at C s v"
  shows "r=s \<and> t=v"
proof -
  have roots: "r=s"
    using complete_data_quotation_root_boundary[OF first]
      complete_data_quotation_root_boundary[OF second] by simp
  have other: "complete_data_quoted_at C r v" using second roots by simp
  show ?thesis using roots complete_data_quotation_unique[OF first other] by blast
qed

text \<open>
  A standalone data quotation uses the complete payload-and-pair syntax,
  including its entire data basis. Every injective formed readdressing is
  admitted. Its ordinary native reader is derived, with the complete carrier
  as interior and no external slots.

  The whole-copy condition excludes ignored attachments and other material
  that the ordinary subterm reader need not inspect. It describes this
  self-contained data profile. It does not assert that every general native
  quotation is a member of this profile or discharge general quotation
  principality by definition.

  In this complete profile, the root is the only carrier position that occurs
  in neither the second nor the third incidence projection. This statement
  survives every admitted readdressing. The whole artifact therefore
  determines both the quotation root and the data term. No distinguished
  address or stored root marker is required. This is a property of these
  complete data copies, not a global restriction on RRA incidence.
\<close>

end
