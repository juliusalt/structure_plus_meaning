theory Ordered_Environment_Artifact_Objects
  imports Ordered_Complete_Artifacts Sorted_Finite_Identity_Images Factor_Executable_Environment_Values_Base
begin

definition ordered_artifact_placement_rows where
  "ordered_artifact_placement_rows row=(fst row,ordered_complete_artifact_rows (snd row))"

lemma ordered_artifact_placement_rows_injective:
  "ordered_artifact_placement_rows x=ordered_artifact_placement_rows y \<longleftrightarrow> x=y"
  by (cases x; cases y)
    (simp add: ordered_artifact_placement_rows_def ordered_complete_artifact_rows_injective)

lemma ordered_artifact_placement_rows_order:
  "ordered_artifact_placement_rows x\<le>ordered_artifact_placement_rows y \<longleftrightarrow> x\<le>y"
  by (cases x; cases y)
    (simp add: ordered_artifact_placement_rows_def less_eq_ordered_complete_artifact_def)

definition complete_environment_artifact_objects ::
  "local_address option finite_artifact_environment \<Rightarrow>
    (local_address option \<times> finite_exact_artifact) list" where
  "complete_environment_artifact_objects E=map (\<lambda>(u,R). (u,unordered_complete_artifact R))
    (sorted_list_of_fset (fimage (\<lambda>(u,R). (u,Ordered_Complete_Artifact R))
      (finite_environment_artifacts E)))"

theorem complete_environment_artifact_objects_rows:
  "map (\<lambda>(u,R). (u,finite_artifact_rows R)) (complete_environment_artifact_objects E)=
    finite_environment_artifact_rows E"
proof -
  have presented: "map (\<lambda>(u,R). (u,finite_artifact_rows R)) (complete_environment_artifact_objects E)=
      map ordered_artifact_placement_rows (sorted_list_of_fset
        (fimage (\<lambda>(u,R). (u,Ordered_Complete_Artifact R)) (finite_environment_artifacts E)))"
    by (simp add: complete_environment_artifact_objects_def ordered_artifact_placement_rows_def
        map_map comp_def case_prod_unfold)
  also have "...=sorted_list_of_fset (fimage ordered_artifact_placement_rows
      (fimage (\<lambda>(u,R). (u,Ordered_Complete_Artifact R)) (finite_environment_artifacts E)))"
    by (rule sorted_finite_identity_image[OF ordered_artifact_placement_rows_injective
        ordered_artifact_placement_rows_order])
  also have "...=finite_environment_artifact_rows E"
    by (simp add: finite_environment_artifact_rows_def ordered_artifact_placement_rows_def
        fimage_fimage comp_def case_prod_unfold)
  finally show ?thesis .
qed

text \<open>The complete original placement order is retained even for
  ambiguous, unformed or differently presented environments. The native
  lexicographic comparison examines uses first; complete artifact-row ordering
  is needed only when those uses tie. No unique-use assumption supplies this
  equation. Rendering its returned artifacts therefore preserves the original
  canonical placement list exactly.\<close>

end
