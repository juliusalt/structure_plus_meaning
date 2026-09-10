theory Factor_Material_Encoding
  imports Factor_Pattern_Forests
begin

section \<open>Complete native records of ordinary patterns\<close>

theorem pattern_record_encoding:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>R r I K.
    artifact_at E None R \<and>
    pattern_record_at E None (f ` pattern_forest_variables ps) r (map (rename_pattern f) ps) I K \<and>
    environment_closed E {None} ((\<lambda>k. (None,k)) ` K) \<and>
    rra_carrier (object_structure R) = I \<union> K \<union> f ` pattern_forest_variables ps"
proof -
  let ?S = "pattern_forest_syntax f ps"
  let ?U = "rra_carrier (object_structure ?S)"
  let ?V = "f ` pattern_forest_variables ps"
  let ?J = "pattern_forest_interior ps"
  let ?K = "rel_dom (pattern_forest_bindings ps)"
  let ?roots = "pattern_forest_roots ps"
  have sf: "exact_formed ?S" by (rule pattern_forest_formed[OF formed addressing])
  have carrier: "?U = ?J \<union> ?K \<union> ?V" by (rule pattern_forest_carrier[OF addressing])
  have ji: "?J \<subseteq> ?U" and ki: "?K \<subseteq> ?U" and vi: "?V \<subseteq> ?U" using carrier by blast+
  have roots: "set ?roots \<subseteq> ?U"
    using pattern_forest_roots_inside[of ps] ji by blast
  obtain r ports where wrapper:
    "exact_formed (record_wrapper ?S r ports ?roots)"
    "record_at (record_wrapper ?S r ports ?roots) r ports ?roots"
    "distinct (r#ports)" "insert r (set ports) \<inter> ?U = {}"
    "object_reads_agree ?S (record_wrapper ?S r ports ?roots) ?U"
    "rra_carrier (object_structure (record_wrapper ?S r ports ?roots)) = ?U \<union> insert r (set ports)"
    using record_wrapper_total[OF sf roots] by blast
  let ?R = "record_wrapper ?S r ports ?roots"
  let ?E = "literal_environment ?R (pattern_forest_bindings ps)"
  let ?I = "insert r (set ports \<union> ?J)"
  have new_slots: "?K \<subseteq> rra_carrier (object_structure ?R)" using ki wrapper(6) by blast
  have ef: "environment_formed ?E"
    by (rule literal_environment_formed[OF wrapper(1) pattern_forest_bindings_finite
          pattern_forest_bindings_functional pattern_forest_bindings_formed[OF formed] new_slots])
  have art: "artifact_at ?E None ?R" by simp
  have vb: "?V \<subseteq> binder_addresses" using addressing by (simp add: binder_addressing_def)
  have original: "pattern_vector_at (pattern_forest_environment f ps) None ?V ?roots
    (map (rename_pattern f) ps) ?J ?K"
    by (rule pattern_forest_recovers[OF formed addressing _ vb]) simp
  have reads: "object_reads_agree ?S ?R ?J"
    by (rule object_reads_agree_mono[OF wrapper(5) ji])
  have slots: "\<forall>k\<in>?K. external_slot_values (pattern_forest_environment f ps) None k =
    external_slot_values ?E None k" by simp
  have vector: "pattern_vector_at ?E None ?V ?roots (map (rename_pattern f) ps) ?J ?K"
    by (rule pattern_vector_embedding[OF original pattern_forest_environment_source reads slots ef art])
  have header_separate: "insert r (set ports) \<inter> ?J = {}" using wrapper(4) ji by blast
  have variable_separate: "?J \<inter> ?V = {}" using pattern_forest_interior_outside[of ps] vb by blast
  have key_separate: "?I \<inter> (?K \<union> ?V) = {}"
    using wrapper(4) ki vi variable_separate pattern_forest_slot_boundary[of ps] by auto
  have rec: "pattern_record_at ?E None ?V r (map (rename_pattern f) ps) ?I ?K"
    unfolding pattern_record_at_def
    apply (rule conjI[OF ef])
    apply (rule exI[of _ ?R], rule exI[of _ ports], rule exI[of _ ?roots], rule exI[of _ ?J])
    using art wrapper(2) vector header_separate key_separate by simp
  have closed: "environment_closed ?E {None} ((\<lambda>k. (None,k)) ` ?K)"
    by (rule literal_environment_closed[OF ef])
  have all_positions: "rra_carrier (object_structure ?R) = ?I \<union> ?K \<union> ?V"
    using wrapper(6) carrier by auto
  show ?thesis
    by (rule exI[of _ ?E], rule exI[of _ ?R], rule exI[of _ r], rule exI[of _ ?I], rule exI[of _ ?K])
       (use art rec closed all_positions in blast)
qed

theorem pattern_record_representation_total:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
  shows "\<exists>f. \<exists>E :: local_address option artifact_environment. \<exists>R r I K.
    binder_addressing (pattern_forest_variables ps) f \<and> artifact_at E None R \<and>
    pattern_record_at E None (f ` pattern_forest_variables ps) r (map (rename_pattern f) ps) I K \<and>
    environment_closed E {None} ((\<lambda>k. (None,k)) ` K) \<and>
    rra_carrier (object_structure R) = I \<union> K \<union> f ` pattern_forest_variables ps"
proof -
  obtain f where addressing: "binder_addressing (pattern_forest_variables ps) f"
    using binder_addressing_exists[OF pattern_forest_variables_finite, of ps] by blast
  obtain E :: "local_address option artifact_environment" and R r I K where encoded:
    "artifact_at E None R"
    "pattern_record_at E None (f ` pattern_forest_variables ps) r (map (rename_pattern f) ps) I K"
    "environment_closed E {None} ((\<lambda>k. (None,k)) ` K)"
    "rra_carrier (object_structure R) = I \<union> K \<union> f ` pattern_forest_variables ps"
    using pattern_record_encoding[OF formed addressing] by blast
  show ?thesis
    by (rule exI[of _ f], rule exI[of _ E], rule exI[of _ R], rule exI[of _ r], rule exI[of _ I], rule exI[of _ K])
       (use addressing encoded in blast)
qed

section \<open>Every complete material pattern has native syntax\<close>

theorem material_pattern_representation_total:
  assumes formed: "material_pattern_formed M"
  shows "\<exists>f. \<exists>E :: local_address option artifact_environment. \<exists>R r I K.
    binder_addressing (material_variables M) f \<and> artifact_at E None R \<and>
    native_material_at E None (f ` material_variables M) r (rename_material_pattern f M) I K \<and>
    environment_closed E {None} ((\<lambda>k. (None,k)) ` K) \<and>
    rra_carrier (object_structure R) = I \<union> K \<union> f ` material_variables M"
proof -
  have fields_formed: "\<forall>p\<in>set (material_fields M). pattern_formed p"
    using formed by (simp add: material_pattern_formed_def)
  have vars: "pattern_forest_variables (material_fields M) = material_variables M"
    by (simp add: pattern_forest_variables_def material_variables_def)
  obtain f and E :: "local_address option artifact_environment" and R r I K where encoded:
    "binder_addressing (material_variables M) f" "artifact_at E None R"
    "pattern_record_at E None (f ` material_variables M) r (map (rename_pattern f) (material_fields M)) I K"
    "environment_closed E {None} ((\<lambda>k. (None,k)) ` K)"
    "rra_carrier (object_structure R) = I \<union> K \<union> f ` material_variables M"
    using pattern_record_representation_total[OF fields_formed] vars by auto
  have native: "native_material_at E None (f ` material_variables M) r (rename_material_pattern f M) I K"
    using encoded(3) by (simp add: native_material_at_def renamed_material_fields)
  show ?thesis
    by (rule exI[of _ f], rule exI[of _ E], rule exI[of _ R], rule exI[of _ r], rule exI[of _ I], rule exI[of _ K])
       (use encoded native in blast)
qed

text \<open>
  Every formed finite list of patterns, and hence every five-operand material
  pattern, has a native record. Literal targets remain exact values. Shared
  variables are assigned injective addresses and are all included in the
  recovered scope boundary. The finite environment is closed over exactly
  the recovered literal slots. The carrier equation excludes unused syntax.
  Material instantiation and satisfaction are preserved by this binder
  renaming, as proved independently in Factor_Material_Patterns.
\<close>

end
