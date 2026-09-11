theory RRA_Collection_References
  imports RRA_Collection_Frames RRA_Binding_Extension RRA_Fresh_Uses
begin

section \<open>Finite artifact placement preserves the existing environment\<close>

lemma unused_source_has_no_binding:
  assumes formed: "environment_formed E" and fresh: "u\<notin>environment_uses E"
  shows "\<not>binds_slot E u k v"
proof
  assume bound: "binds_slot E u k v"
  obtain R where source: "artifact_at E u R" using formed bound unfolding environment_formed_def by blast
  have "u\<in>environment_uses E" using source by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  then show False using fresh by blast
qed

theorem finite_artifact_extension:
  fixes E :: "local_address option artifact_environment"
  assumes finite: "finite T" and formed: "\<forall>R\<in>T. exact_formed R" and ef: "environment_formed E"
  shows "\<exists>F. environment_formed F \<and> environment_included E F \<and>
    (\<forall>R\<in>T. \<exists>u. artifact_at F u R)"
  using finite formed
proof (induction T rule: finite_induct)
  case empty
  show ?case using ef environment_included_refl[of E] by blast
next
  case (insert R T)
  have rf: "exact_formed R" and rest: "\<forall>S\<in>T. exact_formed S" using insert.prems by auto
  obtain F where ff: "environment_formed F" and included: "environment_included E F"
    and old: "\<forall>S\<in>T. \<exists>u. artifact_at F u S"
    using insert.IH[OF rest] by blast
  let ?u="fresh_use_map (environment_uses F) None (Some [])"
  let ?H="add_artifact_use F ?u R"
  have fresh: "?u\<notin>environment_uses F"
    using fresh_use_map_outside[OF environment_uses_finite[OF ff], of None "[]"] by blast
  have hf: "environment_formed ?H" by (rule added_artifact_formed[OF ff rf fresh])
  have retains: "environment_included E ?H"
    by (rule environment_included_trans[OF included added_artifact_included])
  have each: "\<forall>S\<in>insert R T. \<exists>u. artifact_at ?H u S" using old by auto
  show ?case using hf retains each by blast
qed

lemma bound_slot_has_exact_artifact:
  assumes formed: "environment_formed E" and bound: "binds_slot E u k v" and art: "artifact_at E v R"
  shows "external_slot_values E u k={R}"
proof (rule set_eqI)
  fix S
  have unique: "S=R" if member: "S\<in>external_slot_values E u k"
  proof -
    obtain w where other: "binds_slot E u k w" "artifact_at E w S"
      using member by (auto simp: external_slot_values_def)
    have same: "w=v" using environment_binding_unique[OF formed bound other(1)] by simp
    have source: "artifact_at E v S" using other(2) same by simp
    show ?thesis using environment_artifact_unique[OF formed art source] by simp
  qed
  show "S\<in>external_slot_values E u k\<longleftrightarrow>S\<in>{R}"
    using bound art unique by (auto simp: external_slot_values_def)
qed

section \<open>Installing a record whose citation slots refer to supplied uses\<close>

context collection_record_frame
begin

theorem reference_extension:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E"
    and artifacts: "\<And>j i. j<length xss \<Longrightarrow> i<length (xss!j) \<Longrightarrow>
      artifact_at E (v j i) (target_artifact (xss!j!i))"
  shows "\<exists>F u. environment_formed F \<and> environment_included E F \<and>
    artifact_at F u (collection_record_syntax xss) \<and>
    (\<forall>j<length xss. \<forall>i<length (xss!j).
      anchored_at F u (collection_field_node j i) (xss!j!i) \<and>
      (\<forall>R a. xss!j!i=Occurrence_Anchor (R,a) \<longrightarrow>
        located_at F u (collection_field_node j i) (v j i) a))"
proof -
  let ?R="collection_record_syntax xss"
  let ?u="fresh_use_map (environment_uses E) None (Some [])"
  let ?B="add_artifact_use E ?u ?R"
  let ?D="image (\<lambda>(j,i). (collection_field_slot j i,v j i)) (collection_indices xss)"
  let ?F="add_source_bindings ?B ?u ?D"
  have fresh: "?u\<notin>environment_uses E"
    using fresh_use_map_outside[OF environment_uses_finite[OF ef], of None "[]"] by blast
  have unbound: "\<And>k w. \<not>binds_slot E ?u k w"
    by (rule unused_source_has_no_binding[OF ef fresh])
  have bf: "environment_formed ?B" by (rule added_artifact_formed[OF ef formed fresh])
  have source_b: "artifact_at ?B ?u ?R" by simp
  have df: "finite ?D" by simp
  have functional: "single_valued ?D"
    by (auto simp: single_valued_def collection_field_slot_eq)
  have dslots: "rel_dom ?D\<subseteq>rra_carrier (object_structure ?R)"
    using slots_inside by (auto simp: rel_dom_def)
  have targets: "rel_ran ?D\<subseteq>environment_uses ?B"
  proof -
    have old: "rel_ran ?D\<subseteq>environment_uses E"
    proof
      fix z assume member: "z\<in>rel_ran ?D"
      obtain j i where field: "j<length xss" and index: "i<length (xss!j)" and same: "z=v j i"
        using member by (auto simp: rel_ran_def)
      have art: "artifact_at E (v j i) (target_artifact (xss!j!i))"
        by (rule artifacts[OF field index])
      show "z\<in>environment_uses E"
        using art same by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
    qed
    show ?thesis using old by auto
  qed
  have ff: "environment_formed ?F"
    by (rule add_source_bindings_formed[OF bf source_b df functional dslots targets])
       (use unbound in simp)
  have included: "environment_included E ?F"
    by (rule environment_included_trans[OF added_artifact_included add_source_included])
  have source: "artifact_at ?F ?u ?R" by simp
  have every: "\<forall>j<length xss. \<forall>i<length (xss!j).
      anchored_at ?F ?u (collection_field_node j i) (xss!j!i) \<and>
      (\<forall>R a. xss!j!i=Occurrence_Anchor (R,a) \<longrightarrow>
        located_at ?F ?u (collection_field_node j i) (v j i) a)"
  proof (intro allI impI)
    fix j i assume field: "j<length xss" and index: "i<length (xss!j)"
    let ?t="xss!j!i"
    let ?f="syntax_branch j \<circ> syntax_branch i"
    have tf: "target_formed ?t" using fields_formed nth_mem[OF field] nth_mem[OF index] by blast
    have entry: "(collection_field_slot j i,v j i)\<in>?D"
      by (rule image_eqI[where x="(j,i)"]) (use field index in auto)
    have bound: "binds_slot ?F ?u (collection_field_slot j i) (v j i)" using entry by simp
    have art: "artifact_at ?F (v j i) (target_artifact ?t)"
      by (rule included_artifact[OF included artifacts[OF field index]])
    have slot_value: "external_slot_values ?F ?u (?f [4])={target_artifact ?t}"
      using bound_slot_has_exact_artifact[OF ff bound art] by (simp add: collection_field_slot_def)
    have anchored: "anchored_at ?F ?u (collection_field_node j i) ?t"
      by (rule anchored_atI[OF source citation[OF field index]
          literal_citation_mapped_interpretation[where f="?f", OF tf slot_value]])
    have located: "\<forall>R a. ?t=Occurrence_Anchor (R,a) \<longrightarrow>
        located_at ?F ?u (collection_field_node j i) (v j i) a"
    proof (intro allI impI)
      fix R a assume shape: "?t=Occurrence_Anchor (R,a)"
      have anchor: "anchor_formed (R,a)" using tf shape by simp
      have target: "artifact_at ?F (v j i) R" using art shape by simp
      have loc: "citation_location ?F ?u (External (collection_field_slot j i) a) (v j i) a"
        using bound target anchor by auto
      have cite: "citation_at ?R (collection_field_node j i) (External (collection_field_slot j i) a)
          (image ?f (literal_interior ?t))"
        using citation[OF field index] shape by (simp add: collection_field_slot_def)
      show "located_at ?F ?u (collection_field_node j i) (v j i) a"
        using source cite loc unfolding located_at_def by blast
    qed
    show "anchored_at ?F ?u (collection_field_node j i) ?t \<and>
      (\<forall>R a. ?t=Occurrence_Anchor (R,a) \<longrightarrow>
        located_at ?F ?u (collection_field_node j i) (v j i) a)"
      using anchored located by blast
  qed
  show ?thesis using ff included source every by blast
qed

end

text \<open>
  Every entry binds its actual citation slot to the supplied existing use.
  Occurrence citations recover that use and its exact address; whole-artifact
  citations recover the artifact value. Existing environments, including
  their recursive bindings, are retained. The construction creates reference
  geometry only and adds no publication, validity, or authority decision.
\<close>

end
