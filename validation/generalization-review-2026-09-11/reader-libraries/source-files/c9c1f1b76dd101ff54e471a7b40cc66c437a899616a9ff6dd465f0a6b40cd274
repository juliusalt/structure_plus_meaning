theory Factor_Permission_Invariance
  imports Factor_Positive_Meaning Presentation_Observation_Contracts Presentation_Generators
begin

section \<open>Formation and positive truth descend together\<close>

definition presented_program_invariant ::
  "('v \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
    ('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "presented_program_invariant R P d \<longleftrightarrow>
    rel_fun (presentation_transport R R) (=)
      (\<lambda>t. (schema_call_formed P d t,(d,t)\<in>positive_meaning P))
      (\<lambda>t. (schema_call_formed P d t,(d,t)\<in>positive_meaning P))"

theorem presented_program_observations:
  "presented_program_invariant R P d \<longleftrightarrow>
    rel_fun (presentation_transport R R) (=) (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun (presentation_transport R R) (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
  by (simp only: presented_program_invariant_def observation_invariance_pair)

lemma presented_program_invariant_iff:
  "presented_program_invariant R P d \<longleftrightarrow>
    (\<forall>a p q. R a p \<longrightarrow> R a q \<longrightarrow>
      (schema_call_formed P d p \<longleftrightarrow> schema_call_formed P d q) \<and>
      ((d,p)\<in>positive_meaning P \<longleftrightarrow> (d,q)\<in>positive_meaning P))"
  by (auto simp: presented_program_invariant_def rel_fun_def presentation_transport_def)

lemma presented_program_invariant_at:
  assumes invariant: "presented_program_invariant R P d" and first: "R a p" and second: "R a q"
  shows "schema_call_formed P d p \<longleftrightarrow> schema_call_formed P d q"
    "(d,p)\<in>positive_meaning P \<longleftrightarrow> (d,q)\<in>positive_meaning P"
  using assms by (auto simp: presented_program_invariant_def rel_fun_def presentation_transport_def)

theorem presented_program_factorization:
  "presented_program_invariant R P d \<longleftrightarrow>
    (\<exists>B M. \<forall>a t. R a t \<longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> B a) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> M a))"
  by (simp only: presented_program_invariant_def paired_observation_factorization)

theorem presented_program_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t \<longleftrightarrow> schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  shows "presented_program_invariant R Q e \<longleftrightarrow> presented_program_invariant R P d"
  by (simp only: presented_program_invariant_def boundary meaning)

theorem presented_program_from_saturation:
  assumes class_contract: "presentation_class R D A"
    and formed_values: "\<And>a t. R a t \<Longrightarrow> term_formed t"
    and boundary: "\<And>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and meaning: "(\<lambda>t. (d,t)\<in>positive_meaning P)=saturate_observation R test"
  shows "presented_program_invariant R P d"
proof -
  have formed: "rel_fun (presentation_transport R R) (=) (schema_call_formed P d) (schema_call_formed P d)"
    using formed_values by (auto simp: boundary rel_fun_def presentation_transport_def)
  have truth: "rel_fun (presentation_transport R R) (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
    by (simp only: meaning; rule presentation_class.saturation_invariant[OF class_contract])
  show ?thesis using formed truth by (simp only: presented_program_observations)
qed

section \<open>The exact condition family retains both roles and every endpoint\<close>

definition program_invariance_obligations where
  "program_invariance_obligations E P d=obligation_substitution
    {(False,schema_call_formed P d),(True,\<lambda>t. (d,t)\<in>positive_meaning P)}
    (observation_obligations E)"

theorem program_invariance_obligations_exact:
  "rel_ran (program_invariance_obligations E P d)\<subseteq>{c. observation_condition c} \<longleftrightarrow>
    rel_fun E (=) (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun E (=) (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
proof -
  have observations: "rel_ran {(False,schema_call_formed P d),(True,\<lambda>t. (d,t)\<in>positive_meaning P)}=
      {schema_call_formed P d,\<lambda>t. (d,t)\<in>positive_meaning P}"
    by (auto simp: rel_ran_def ex_bool_eq)
  show ?thesis by (simp add: program_invariance_obligations_def obligation_substitution_values
    observations observation_obligations_exact)
qed

theorem presented_program_invariance_reduction:
  "exact_obligation_reduction UNIV (\<lambda>z. presented_program_invariant R (fst z) (snd z))
    observation_condition
    (\<lambda>z. program_invariance_obligations (presentation_transport R R) (fst z) (snd z))"
  by (simp only: exact_obligation_reduction_def program_invariance_obligations_exact
    presented_program_observations; simp)

theorem presented_program_invariance_residual:
  assumes known: "K\<subseteq>{c. observation_condition c}"
  shows "presented_program_invariant R P d \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (program_invariance_obligations (presentation_transport R R) P d))
      \<subseteq>{c. observation_condition c}"
  using exact_obligation_reduction_residual[OF presented_program_invariance_reduction known,
    unfolded exact_obligation_reduction_def, rule_format, where a="(P,d)"] by simp

theorem presented_program_invariance_local:
  assumes generators: "presentation_generators R D A step"
  shows "presented_program_invariant R P d \<longleftrightarrow>
    rel_ran (program_invariance_obligations step P d)\<subseteq>{c. observation_condition c}"
  by (simp only: presented_program_observations presentation_generators.generator_observation_iff[OF generators]
    program_invariance_obligations_exact)

text \<open>
  This shared contract is derived from the actual program's interface and
  independently fixed positive meaning. Its argument relation retains the
  complete subject of each use. The pair is an observation of the program;
  it is not an additional stored field or a native decision of nonmembership.

  The existing exact reduction evaluates both roles with their endpoint
  occurrences. A complete generator can replace full correspondence only
  after its preservation and coverage proofs. Saturation supplies a sufficient
  construction with a variable interface. It does not change the original
  program or establish agreement with its original decisions.
\<close>

end
