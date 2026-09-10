theory Presentation_Completion_Investigation
  imports Finite_Investigation_Interface Presentation_Completion
begin

section \<open>Joint feasibility distinguishes separately completable tests\<close>

definition completion_investigation_test :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "completion_investigation_test c=(if c=0 then id else Not)"

definition completion_investigation_observe :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "completion_investigation_observe f c=
    (if f=0 then saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True) id False
     else if f=1 then saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True)
       (completion_investigation_test c) False
     else saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True)
       (\<lambda>p. p \<and> completion_investigation_test c p) False)"

lemma completion_investigation_observe_exact:
  "completion_investigation_observe f c \<longleftrightarrow> f=0 \<or> f=1 \<or> c=0"
  by (auto simp: completion_investigation_observe_def completion_investigation_test_def
    saturate_observation_def presentation_transport_def)

definition completion_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "completion_investigation_observations=concat (map (\<lambda>f.
    map (\<lambda>c. (f,c,0)) (filter (completion_investigation_observe f) [0,1])) [0,1,2])"

definition completion_investigation_relation :: "(nat\<times>nat) list" where
  "completion_investigation_relation=filter (\<lambda>(c,d).
    completion_investigation_observe 2 c \<longrightarrow> completion_investigation_observe 2 d)
      (investigation_pairs [0,1])"

lemma completion_investigation_observations_exact:
  "finite_table_observations (fset_of_list completion_investigation_observations) f c=
    (if f\<in>{0,1,2} \<and> c\<in>{0,1} \<and> completion_investigation_observe f c then {0} else {})"
  by (auto simp: finite_table_observations_def completion_investigation_observations_def completion_investigation_observe_exact)

lemma completion_investigation_relation_exact:
  "(c,d)\<in>set completion_investigation_relation \<longleftrightarrow>
    c\<in>{0,1} \<and> d\<in>{0,1} \<and>
      (completion_investigation_observe 2 c \<longrightarrow> completion_investigation_observe 2 d)"
  by (auto simp: completion_investigation_relation_def investigation_pairs_exact)

definition completion_investigation where
  "completion_investigation selected=investigation_basis [0,1] [0,1,2] selected
    completion_investigation_observations completion_investigation_relation"

theorem component_observations_miss_joint_failure:
  "set (fst (snd (completion_investigation [0,1])))={(0,1)}"
  by (simp add: completion_investigation_def investigation_basis_def Let_def
    investigation_select_def investigation_pairs_def completion_investigation_observations_def
    completion_investigation_relation_def completion_investigation_observe_exact
    finite_basis_residual_def finite_candidate_profile_def)

theorem the_joint_observation_is_an_adequate_basis:
  "fst (completion_investigation [2]) \<and> fst (snd (completion_investigation [2]))=[]"
  by (simp add: completion_investigation_def investigation_basis_def Let_def
    investigation_select_def investigation_pairs_def completion_investigation_observations_def
    completion_investigation_relation_def completion_investigation_observe_exact
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def
    finite_observation_table_formed_def)

theorem no_selected_observation_misses_joint_failure:
  "set (fst (snd (completion_investigation [])))={(0,1)}"
  by (simp add: completion_investigation_def investigation_basis_def Let_def
    investigation_select_def investigation_pairs_def completion_investigation_observations_def
    completion_investigation_relation_def completion_investigation_observe_exact
    finite_basis_residual_def finite_candidate_profile_def)

export_code investigation_inference investigation_basis investigation_repairs investigation_extend completion_investigation
  completion_investigation_observations completion_investigation_relation
  nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

text \<open>
  The two candidates pair the identity test with identity or negation on the
  complete Boolean presentation fibre of one unit subject. Observations are
  computed by the existing existential completion operation. Both component
  tests can succeed separately. Only the first pair can use a common witness.

  The intended comparison preserves joint feasibility. Component observations
  identify a feasible pair with an infeasible pair, returning the exact failed
  direction. The joint observation suffices by itself; adding the two weaker
  facets supplies no further distinction for this comparison. An empty basis
  fails. The numeric coordinates present this finite case and introduce no
  new semantic kind, global method enumeration, or native permission proof.
\<close>

end
