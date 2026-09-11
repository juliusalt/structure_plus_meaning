theory Factor_Record_Construction
  imports Factor_Material_Encoding
begin

section \<open>Uniform record coordinates for an arbitrary finite field list\<close>

definition syntax_record_ports :: "nat \<Rightarrow> local_address list" where
  "syntax_record_ports n = map (\<lambda>i. 0#unary_address i) [0..<n]"

lemma syntax_record_ports_length [simp]: "length (syntax_record_ports n) = n"
  by (simp add: syntax_record_ports_def)

lemma syntax_record_ports_distinct [simp]: "distinct (syntax_record_ports n)"
  by (simp add: syntax_record_ports_def distinct_map inj_on_def)

lemma syntax_record_ports_root [simp]: "[] \<notin> set (syntax_record_ports n)"
  by (auto simp: syntax_record_ports_def)

lemma syntax_record_headers_outside:
  "insert [] (set (syntax_record_ports n)) \<inter> binder_addresses = {}"
  by (auto simp: syntax_record_ports_def)

lemma syntax_record_ports_formed:
  "\<forall>a\<in>set (syntax_record_ports n). octets_formed a"
  using unary_address_formed by (auto simp: syntax_record_ports_def octets_formed_def)

lemma pattern_forest_roots_length [simp]: "length (pattern_forest_roots ps) = length ps"
  by (induction ps) simp_all

definition pattern_record_syntax :: "('a \<Rightarrow> local_address) \<Rightarrow> 'a term_pattern list \<Rightarrow> exact_artifact" where
  "pattern_record_syntax f ps = record_wrapper (pattern_forest_syntax f ps) []
    (syntax_record_ports (length ps)) (pattern_forest_roots ps)"

definition pattern_record_interior :: "'a term_pattern list \<Rightarrow> local_address set" where
  "pattern_record_interior ps = insert [] (set (syntax_record_ports (length ps)) \<union> pattern_forest_interior ps)"

lemma pattern_record_header_fresh:
  assumes addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "insert [] (set (syntax_record_ports (length ps))) \<inter>
    rra_carrier (object_structure (pattern_forest_syntax f ps)) = {}"
proof -
  have body: "insert [] (set (syntax_record_ports (length ps))) \<inter>
    (pattern_forest_interior ps \<union> rel_dom (pattern_forest_bindings ps)) = {}"
    by (cases ps; simp only: pattern_forest_interior.simps pattern_forest_slots)
       (auto simp: syntax_record_ports_def)
  have vars: "f ` pattern_forest_variables ps \<subseteq> binder_addresses"
    using addressing by (simp add: binder_addressing_def)
  have bound: "insert [] (set (syntax_record_ports (length ps))) \<inter> f ` pattern_forest_variables ps = {}"
    using vars syntax_record_headers_outside[of "length ps"] by blast
  show ?thesis using body bound by (simp add: pattern_forest_carrier[OF addressing] Int_Un_distrib)
qed

lemma pattern_record_syntax_formed:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "exact_formed (pattern_record_syntax f ps)"
proof -
  have roots: "set (pattern_forest_roots ps) \<subseteq> rra_carrier (object_structure (pattern_forest_syntax f ps))"
    using pattern_forest_roots_inside[of ps] pattern_forest_carrier[OF addressing] by blast
  have addresses: "\<forall>a\<in>insert [] (set (syntax_record_ports (length ps))). octets_formed a"
    using syntax_record_ports_formed by (auto simp: octets_formed_def)
  show ?thesis unfolding pattern_record_syntax_def
    by (rule record_wrapper_formed[OF pattern_forest_formed[OF formed addressing] roots addresses])
qed

lemma pattern_record_syntax_record:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "record_at (pattern_record_syntax f ps) [] (syntax_record_ports (length ps)) (pattern_forest_roots ps)"
proof -
  have sf: "exact_formed (pattern_forest_syntax f ps)" by (rule pattern_forest_formed[OF formed addressing])
  have tf: "exact_formed (record_wrapper (pattern_forest_syntax f ps) []
    (syntax_record_ports (length ps)) (pattern_forest_roots ps))"
    using pattern_record_syntax_formed[OF formed addressing] by (simp add: pattern_record_syntax_def)
  show ?thesis unfolding pattern_record_syntax_def
    by (rule record_wrapper_recovers[OF sf tf _ _ pattern_record_header_fresh[OF addressing]]) simp_all
qed

lemma pattern_record_syntax_reads:
  assumes addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "object_reads_agree (pattern_forest_syntax f ps) (pattern_record_syntax f ps)
    (rra_carrier (object_structure (pattern_forest_syntax f ps)))"
  unfolding pattern_record_syntax_def by (rule record_wrapper_reads[OF pattern_record_header_fresh[OF addressing]])

lemma pattern_record_syntax_carrier:
  assumes addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "rra_carrier (object_structure (pattern_record_syntax f ps)) =
    pattern_record_interior ps \<union> rel_dom (pattern_forest_bindings ps) \<union> f ` pattern_forest_variables ps"
  using pattern_forest_roots_inside[of ps]
  by (auto simp: pattern_record_syntax_def record_wrapper_def attach_structure_def record_structure_def
      pattern_record_interior_def pattern_forest_carrier[OF addressing])

lemma pattern_record_interior_outside:
  "pattern_record_interior ps \<inter> binder_addresses = {}"
  using pattern_forest_interior_outside[of ps]
  by (auto simp: pattern_record_interior_def syntax_record_ports_def)

lemma pattern_record_slot_boundary:
  "pattern_record_interior ps \<inter> rel_dom (pattern_forest_bindings ps) = {}"
proof -
  have fresh: "insert [] (set (syntax_record_ports (length ps))) \<inter> rel_dom (pattern_forest_bindings ps) = {}"
    by (cases ps; simp only: pattern_forest_slots) (auto simp: syntax_record_ports_def)
  show ?thesis using fresh pattern_forest_slot_boundary[of ps] by (auto simp: pattern_record_interior_def)
qed

lemma pattern_record_syntax_root [simp]:
  "[] \<in> rra_carrier (object_structure (pattern_record_syntax f ps))"
  by (simp add: pattern_record_syntax_def record_wrapper_def attach_structure_def record_structure_def)

lemma pattern_record_syntax_no_counts [simp]:
  "bag_count (object_data (pattern_record_syntax f ps)) = (\<lambda>_. 0)"
  by (simp add: pattern_record_syntax_def record_wrapper_def attach_structure_def)

lemma pattern_record_syntax_silent [simp]: "binder_silent (pattern_record_syntax f ps)"
proof -
  have heads: "\<forall>a\<in>binder_addresses.
    headed_incidence (object_structure (pattern_record_syntax f ps)) a = {}"
  proof (intro ballI)
    fix a assume member: "a \<in> binder_addresses"
    have old: "headed_incidence (object_structure (pattern_forest_syntax f ps)) a = {}"
      using pattern_forest_silent[of f ps] member unfolding binder_silent_def by blast
    have outside: "a \<notin> insert [] (set (syntax_record_ports (length ps)))"
      using syntax_record_headers_outside[of "length ps"] member by blast
    have new: "headed_incidence (record_structure [] (syntax_record_ports (length ps)) (pattern_forest_roots ps)) a = {}"
      by (rule record_structure_head_outside[OF outside])
    show "headed_incidence (object_structure (pattern_record_syntax f ps)) a = {}"
      using old new by (simp add: pattern_record_syntax_def record_wrapper_def attach_structure_head)
  qed
  have data: "restrict_basis binder_addresses (object_data (pattern_record_syntax f ps)) = empty_basis"
    using pattern_forest_silent[of f ps]
    by (simp add: binder_silent_def pattern_record_syntax_def record_wrapper_def attach_structure_def)
  show ?thesis using heads data by (simp add: binder_silent_def)
qed

theorem pattern_record_syntax_recovers:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
    and scope: "f ` pattern_forest_variables ps \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
    and ef: "environment_formed E" and art: "artifact_at E u (pattern_record_syntax f ps)"
    and slots: "\<forall>k\<in>rel_dom (pattern_forest_bindings ps).
      external_slot_values E u k = {R. (k,R) \<in> pattern_forest_bindings ps}"
  shows "pattern_record_at E u V [] (map (rename_pattern f) ps)
    (pattern_record_interior ps) (rel_dom (pattern_forest_bindings ps))"
proof -
  let ?S = "pattern_forest_syntax f ps"
  let ?R = "pattern_record_syntax f ps"
  let ?J = "pattern_forest_interior ps"
  let ?K = "rel_dom (pattern_forest_bindings ps)"
  have original: "pattern_vector_at (pattern_forest_environment f ps) None V (pattern_forest_roots ps)
    (map (rename_pattern f) ps) ?J ?K"
    by (rule pattern_forest_recovers[OF formed addressing scope boundary])
  have inside: "?J \<subseteq> rra_carrier (object_structure ?S)"
    by (auto simp: pattern_forest_carrier[OF addressing])
  have reads: "object_reads_agree ?S ?R ?J"
    by (rule object_reads_agree_mono[OF pattern_record_syntax_reads[OF addressing] inside])
  have agreement: "\<forall>k\<in>?K. external_slot_values (pattern_forest_environment f ps) None k = external_slot_values E u k"
    using slots by simp
  have vector: "pattern_vector_at E u V (pattern_forest_roots ps) (map (rename_pattern f) ps) ?J ?K"
    by (rule pattern_vector_embedding[OF original pattern_forest_environment_source reads agreement ef art])
  have rec: "record_at ?R [] (syntax_record_ports (length ps)) (pattern_forest_roots ps)"
    by (rule pattern_record_syntax_record[OF formed addressing])
  have header_separate: "insert [] (set (syntax_record_ports (length ps))) \<inter> ?J = {}"
    using pattern_record_header_fresh[OF addressing] inside by blast
  have key_separate: "pattern_record_interior ps \<inter> (?K \<union> V) = {}"
    using pattern_record_slot_boundary[of ps] pattern_record_interior_outside[of ps] boundary by auto
  show ?thesis unfolding pattern_record_at_def
    apply (rule conjI[OF ef])
    apply (rule exI[of _ ?R], rule exI[of _ "syntax_record_ports (length ps)"],
        rule exI[of _ "pattern_forest_roots ps"], rule exI[of _ ?J])
    using art rec vector header_separate key_separate by (simp add: pattern_record_interior_def)
qed

definition material_syntax :: "('a \<Rightarrow> local_address) \<Rightarrow> 'a material_pattern \<Rightarrow> exact_artifact" where
  "material_syntax f M = pattern_record_syntax f (material_fields M)"

lemma material_syntax_formed:
  assumes "material_pattern_formed M" "binder_addressing (material_variables M) f"
  shows "exact_formed (material_syntax f M)"
  unfolding material_syntax_def
  by (rule pattern_record_syntax_formed)
     (use assms in \<open>simp_all add: material_pattern_formed_def pattern_forest_variables_def material_variables_def\<close>)

lemma material_syntax_root [simp]: "[] \<in> rra_carrier (object_structure (material_syntax f M))"
  by (simp add: material_syntax_def)

lemma material_syntax_no_counts [simp]: "bag_count (object_data (material_syntax f M)) = (\<lambda>_. 0)"
  by (simp add: material_syntax_def)

lemma material_syntax_silent [simp]: "binder_silent (material_syntax f M)"
  by (simp add: material_syntax_def)

theorem material_syntax_recovers:
  assumes formed: "material_pattern_formed M" and addressing: "binder_addressing (material_variables M) f"
    and scope: "f ` material_variables M \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
    and ef: "environment_formed E" and art: "artifact_at E u (material_syntax f M)"
    and slots: "\<forall>k\<in>rel_dom (pattern_forest_bindings (material_fields M)).
      external_slot_values E u k = {R. (k,R) \<in> pattern_forest_bindings (material_fields M)}"
  shows "native_material_at E u V [] (rename_material_pattern f M)
    (pattern_record_interior (material_fields M)) (rel_dom (pattern_forest_bindings (material_fields M)))"
proof -
  have fields: "\<forall>p\<in>set (material_fields M). pattern_formed p"
    using formed by (simp add: material_pattern_formed_def)
  have variables: "pattern_forest_variables (material_fields M) = material_variables M"
    by (simp add: pattern_forest_variables_def material_variables_def)
  have faddr: "binder_addressing (pattern_forest_variables (material_fields M)) f" using addressing variables by simp
  have vscope: "f ` pattern_forest_variables (material_fields M) \<subseteq> V" using scope variables by simp
  have source: "artifact_at E u (pattern_record_syntax f (material_fields M))" using art by (simp add: material_syntax_def)
  have rec: "pattern_record_at E u V [] (map (rename_pattern f) (material_fields M))
    (pattern_record_interior (material_fields M)) (rel_dom (pattern_forest_bindings (material_fields M)))"
    by (rule pattern_record_syntax_recovers[OF fields faddr vscope boundary ef source slots])
  show ?thesis using rec by (simp add: native_material_at_def renamed_material_fields)
qed

text \<open>
  Port coordinates are generated from unbounded unary addresses, so there is no
  maximum record arity. No structural reader inspects those byte choices.
  The resulting material body can use any larger declared binder boundary;
  every syntax position remains disjoint from that boundary. This permits
  several call and material bodies to share one complete schema scope.
\<close>

end
