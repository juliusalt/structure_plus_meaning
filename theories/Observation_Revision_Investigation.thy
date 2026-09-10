theory Observation_Revision_Investigation
  imports Finite_Investigation_Interface
begin

section \<open>Actual revision methods are candidates for the same evaluator\<close>

type_synonym revision_workload =
  "nat list\<times>nat list\<times>nat list\<times>(nat\<times>nat\<times>nat) list\<times>(nat\<times>nat) list"

definition revision_workload :: "nat \<Rightarrow> revision_workload" where
  "revision_workload i=([0,1], if i=2 then [0,2,3] else [0,1,2,3],
    if i=1 then [1,2] else if i=3 then [2] else if i=4 then [] else [0,2],
    [(0,0,0),(0,1,1)] @ (if i=2 then [] else [(1,1,0)]) @
      [(2,0,0),(2,1,0),(3,0,0),(3,1,0)], [(0,0),(0,1),(1,1)])"

definition revision_method_selection :: "nat \<Rightarrow> revision_workload \<Rightarrow> nat list" where
  "revision_method_selection method input=(case input of (C,U,F,T,R) \<Rightarrow>
    (let report=investigation_repairs C U F T R;
         retained=investigation_retain C U F T R;
         old_repairs=fst (snd (snd report))
     in if method=0 then investigation_extend F old_repairs
        else if method=1 then investigation_extend retained old_repairs
        else if method=2 then fst (snd (snd (snd (investigation_revision C U F T R))))
        else if method=3 then fst report
        else if method=4 then retained
        else investigation_extend [] (fst (snd (snd (investigation_repairs C U [] T R))))))"

definition revision_quality_condition where
  "revision_quality_condition C relation U F observe G q \<longleftrightarrow>
    (if q=0 then comparison_observations_sound C relation G observe
     else if q=1 then retained_observation_facets C relation U F observe\<subseteq>G
     else if q=2 then comparison_failures C relation G observe=
       comparison_failures C relation (sound_observation_facets C relation U observe) observe
     else q=3 \<and> (\<forall>f\<in>G-F. \<exists>c d w. (c,d,f,w)\<in>available_observation_repairs
       C relation U (retained_observation_facets C relation U F observe) observe))"

theorem revised_selection_meets_every_quality_condition:
  assumes "q\<in>{0,1,2,3}"
  shows "revision_quality_condition C relation U F observe
    (revised_observation_selection C relation U F observe) q"
  using assms revised_observation_selection_sound[of C relation U F observe]
    revised_observation_selection_bounds(1)[of C relation U F observe]
    revision_has_exactly_the_full_sound_language_failures[of C relation U F observe]
    every_added_facet_has_a_recomputed_repair[of _ C relation U F observe]
  by (auto simp only: revision_quality_condition_def insert_iff singleton_iff split: if_splits; blast)

definition revision_method_quality :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "revision_method_quality method workload q=(case revision_workload workload of (C,U,F,T,R) \<Rightarrow>
    (let G=revision_method_selection method (C,U,F,T,R);
         report=investigation_repairs C U G T R;
         retained=investigation_retain C U F T R;
         repairs=fst (snd (snd (investigation_repairs C U retained T R)))
     in if q=0 then fst (snd report)=[]
        else if q=1 then set retained\<subseteq>set G
        else if q=2 then set (filter (\<lambda>(c,d). (c,d)\<notin>set R)
          (fst (snd (investigation_basis C U G T R))))=set (snd (snd (snd report)))
        else q=3 \<and> set G-set F\<subseteq>set (map (\<lambda>(c,d,f,w). f) repairs)))"

lemma revision_method_quality_exact:
  assumes "revision_workload workload=(C,U,F,T,R)"
  shows "revision_method_quality method workload q \<longleftrightarrow>
    revision_quality_condition (set C) (\<lambda>c d. (c,d)\<in>set R) (set U) (set F)
      (finite_table_observations (fset_of_list T))
      (set (revision_method_selection method (C,U,F,T,R))) q"
proof -
  have missing: "set (filter (\<lambda>(c,d). (c,d)\<notin>set R)
      (fst (snd (investigation_basis C U G T R))))=
      comparison_failures (set C) (\<lambda>c d. (c,d)\<in>set R) (set G)
        (finite_table_observations (fset_of_list T))" for G
    by (auto simp: investigation_basis_residual finite_basis_residual_member
      fset_of_list.rep_eq comparison_failures_def candidate_profile_comparison; blast)
  have conflicts: "fst (snd (investigation_repairs C U G T R))=[] \<longleftrightarrow>
      comparison_observations_sound (set C) (\<lambda>c d. (c,d)\<in>set R) (set G)
        (finite_table_observations (fset_of_list T))" for G
    using investigation_conflicts[of C U G T R]
    by (metis observation_conflicts_empty set_empty)
  show ?thesis
    by (simp only: revision_method_quality_def assms case_prod_conv Let_def
      conflicts missing investigation_retain_exact investigation_unrepairable_comparisons
      revision_quality_condition_def;
      auto simp only: set_map image_iff investigation_available_repairs
        investigation_retain_exact subset_iff case_prod_beta' split: if_splits prod.splits; force)
qed

definition revision_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "revision_investigation_observations=concat (map (\<lambda>q.
    concat (map (\<lambda>method. map (\<lambda>workload. (q,method,workload))
      (filter (\<lambda>workload. revision_method_quality method workload q) [0,1,2,3,4])) [0,1,2,3,4,5])) [0,1,2,3])"

definition revision_investigation_relation :: "(nat\<times>nat) list" where
  "revision_investigation_relation=filter (\<lambda>(method,other).
    \<forall>workload\<in>set [0,1,2,3,4]. \<forall>q\<in>set [0,1,2,3].
      revision_method_quality method workload q \<longrightarrow> revision_method_quality other workload q)
    (investigation_pairs [0,1,2,3,4,5])"

definition revision_investigation where
  "revision_investigation selected=investigation_basis [0,1,2,3,4,5] [0,1,2,3] selected
    revision_investigation_observations revision_investigation_relation"

export_code revision_investigation revision_investigation_observations
  revision_investigation_relation checking SML

text \<open>
  The six supplied methods preserve the original selection, reuse its old
  repairs after withdrawal, recompute revision, select the whole sound
  language, only withdraw, or restart from the empty selection. Every method
  calls the existing executable operations. Their quality conditions ask for
  soundness, conservation of selected sound facets, all available missing-pair
  distinctions, and actual witnesses for additions.

  Five workloads include a conflict masking a missing distinction, an already
  adequate selection, a language with no adequate basis, a sound incomplete
  selection, and an empty selection. Recomputed revision satisfies the four
  conditions universally; the finite experiment compares the other supplied
  methods on precisely these workloads. The intended comparison is inclusion
  of satisfied workload conditions, with no score or ordering of identifiers.
\<close>

end
