theory Factor_Substitution_Investigation
  imports Factor_Substitution Factor_Pattern_Determination Finite_Investigation_Interface
begin

section \<open>The finite case evaluates actual repeated substitutions\<close>

definition pattern_investigation_replacement :: "nat \<Rightarrow> nat term_pattern" where
  "pattern_investigation_replacement c=(if c=0 then Pattern_Variable 0
    else if c=1 then Pattern_Variable 1 else if c=2 then Pattern_Payload [0]
    else if c=3 then Pattern_Payload [1] else Pattern_Target (Whole_Artifact empty_artifact))"

definition pattern_investigation_pattern :: "nat \<Rightarrow> nat term_pattern" where
  "pattern_investigation_pattern c=pattern_substitute (\<lambda>_. pattern_investigation_replacement c)
    (Pattern_Pair (Pattern_Variable ()) (Pattern_Variable ()))"

definition pattern_investigation_marker :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> factor_term" where
  "pattern_investigation_marker collapsed f a=(if f=0 then Payload_Term (if collapsed then [0] else [a])
    else Target_Term (Whole_Artifact empty_artifact))"

fun pattern_investigation_value :: "factor_term \<Rightarrow> nat" where
  "pattern_investigation_value (Pair_Term (Payload_Term a) y)=(if a=[0] then 0 else if a=[1] then 1 else 3)"
| "pattern_investigation_value (Pair_Term (Target_Term k) y)=2"
| "pattern_investigation_value x=3"

definition pattern_investigation_observation :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pattern_investigation_observation collapsed f c=pattern_investigation_value
    (evaluate_pattern (pattern_investigation_marker collapsed f) (pattern_investigation_pattern c))"

definition pattern_investigation_compare :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "pattern_investigation_compare c d=(pattern_investigation_pattern c=pattern_investigation_pattern d)"

lemma pattern_investigation_compare_code [code]:
  "pattern_investigation_compare c d=
    ((if c=0 then 0 else if c=1 then 1 else if c=2 then 2 else if c=3 then 3 else 4::nat)=
     (if d=0 then 0 else if d=1 then 1 else if d=2 then 2 else if d=3 then 3 else 4))"
  by (auto simp: pattern_investigation_compare_def pattern_investigation_pattern_def
    pattern_investigation_replacement_def split: if_splits)

lemma pattern_investigation_patterns_formed:
  "pattern_formed (pattern_investigation_pattern c)"
  "pattern_variables (pattern_investigation_pattern c)\<subseteq>{0,1}"
  by (auto simp: pattern_investigation_pattern_def pattern_investigation_replacement_def octets_formed_def)

lemma pattern_investigation_output_range:
  "evaluate_pattern (pattern_investigation_marker collapsed f) (pattern_investigation_pattern c)\<in>
    {Pair_Term (Payload_Term [0]) (Payload_Term [0]),
     Pair_Term (Payload_Term [1]) (Payload_Term [1]),
     Pair_Term (Target_Term (Whole_Artifact empty_artifact)) (Target_Term (Whole_Artifact empty_artifact))}"
  by (auto simp: pattern_investigation_pattern_def pattern_investigation_replacement_def
    pattern_investigation_marker_def)

theorem pattern_investigation_value_exact:
  "pattern_investigation_observation collapsed f c=pattern_investigation_observation collapsed' g d \<longleftrightarrow>
    evaluate_pattern (pattern_investigation_marker collapsed f) (pattern_investigation_pattern c)=
      evaluate_pattern (pattern_investigation_marker collapsed' g) (pattern_investigation_pattern d)"
  using pattern_investigation_output_range[of collapsed f c]
    pattern_investigation_output_range[of collapsed' g d]
  by (auto simp: pattern_investigation_observation_def)

definition pattern_investigation_observations :: "bool \<Rightarrow> (nat\<times>nat\<times>nat) list" where
  "pattern_investigation_observations collapsed=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,pattern_investigation_observation collapsed f c)) [0,1]) [0,1,2,3,4])"

definition pattern_investigation_relation :: "(nat\<times>nat) list" where
  "pattern_investigation_relation=filter (\<lambda>(c,d). pattern_investigation_compare c d)
    (investigation_pairs [0,1,2,3,4])"

lemma pattern_investigation_observations_exact:
  "finite_table_observations (fset_of_list (pattern_investigation_observations collapsed)) f c=
    (if f\<in>{0,1} \<and> c\<in>{0,1,2,3,4} then {pattern_investigation_observation collapsed f c} else {})"
  by (auto simp: finite_table_observations_def pattern_investigation_observations_def)

lemma pattern_investigation_relation_exact:
  "(c,d)\<in>set pattern_investigation_relation \<longleftrightarrow>
    c\<in>{0,1,2,3,4} \<and> d\<in>{0,1,2,3,4} \<and>
      pattern_investigation_pattern c=pattern_investigation_pattern d"
  by (simp only: pattern_investigation_relation_def set_filter mem_Collect_eq split_conv
    investigation_pairs_exact mem_Times_iff pattern_investigation_compare_def set_simps conj_assoc fst_conv snd_conv)

lemma pattern_investigation_observations_literal:
  "pattern_investigation_observations False=
    [(0,0,0),(1,0,2),(0,1,1),(1,1,2),(0,2,0),(1,2,0),(0,3,1),(1,3,1),(0,4,2),(1,4,2)]"
  "pattern_investigation_observations True=
    [(0,0,0),(1,0,2),(0,1,0),(1,1,2),(0,2,0),(1,2,0),(0,3,1),(1,3,1),(0,4,2),(1,4,2)]"
  by (simp_all add: pattern_investigation_observations_def pattern_investigation_observation_def
    pattern_investigation_pattern_def pattern_investigation_replacement_def pattern_investigation_marker_def)

lemma pattern_investigation_relation_literal:
  "pattern_investigation_relation=[(0,0),(1,1),(2,2),(3,3),(4,4)]"
  by (simp add: pattern_investigation_relation_def investigation_pairs_def pattern_investigation_compare_code)

definition pattern_investigation where
  "pattern_investigation collapsed selected=investigation_basis [0,1,2,3,4] [0,1] selected
    (pattern_investigation_observations collapsed) pattern_investigation_relation"

theorem pattern_investigation_payload_only:
  "fst (pattern_investigation False [0]) \<and>
    set (fst (snd (pattern_investigation False [0])))={(0,2),(2,0),(1,3),(3,1)}"
  by (simp add: pattern_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def pattern_investigation_observations_literal pattern_investigation_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def; blast)

theorem pattern_investigation_target_only:
  "fst (pattern_investigation False [1]) \<and>
    set (fst (snd (pattern_investigation False [1])))={(0,1),(1,0),(0,4),(4,0),(1,4),(4,1)}"
  by (simp add: pattern_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def pattern_investigation_observations_literal pattern_investigation_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def; blast)

theorem pattern_investigation_two_probes:
  "fst (pattern_investigation False [0,1]) \<and> fst (snd (pattern_investigation False [0,1]))=[]"
  by (simp add: pattern_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def pattern_investigation_observations_literal pattern_investigation_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def)

theorem pattern_investigation_collapsed_markers:
  "fst (pattern_investigation True [0,1]) \<and>
    set (fst (snd (pattern_investigation True [0,1])))={(0,1),(1,0)}"
  by (simp add: pattern_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def pattern_investigation_observations_literal pattern_investigation_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def)

export_code investigation_inference investigation_basis pattern_investigation
  pattern_investigation_observations pattern_investigation_relation
  nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

text \<open>
  The five replacements are two variables, two distinct payload literals, and
  one target literal. Each replaces both occurrences of the same variable in
  a pair pattern. The exported code performs that substitution and evaluates
  its resulting pattern. The intended comparison is equality of those actual
  patterns. The small numeric output encoding is injective on every output
  reachable in this finite case; its exact scope is proved above.

  Either observation alone misses a distinction. Both distinguish all five
  substituted patterns when the payload markers retain variable identity.
  Collapsing those markers loses the two variable replacements even with both
  observations. The finite input remains formed: the residual diagnoses its
  inadequate observation basis, independently of table formation.

  These executions instantiate the general grammar theorem. They do not run
  an arbitrary native program or infer its universal truth from sample calls.
\<close>

end
