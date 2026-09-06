theory Factor_Resource_Sensitivity
  imports Factor_Native_Equality
begin

section \<open>Resource edits are ordinary changes to an application\<close>

lemma native_context_equality:
  assumes "term_formed gamma" "term_formed result"
  shows "native_application_formed (equality_query_environment (Pair_Term gamma result))
      None [0] (Some []) []"
    "native_positive_holds (equality_query_environment (Pair_Term gamma result))
      None [0] (Some []) [] \<longleftrightarrow> gamma=result"
  using native_equality_future_application_formed[of "Pair_Term gamma result"]
    native_equality_of_future_terms[OF assms] assms by auto

theorem native_weakening_is_not_implicit:
  assumes "term_formed gamma" "term_formed extra"
  shows "native_positive_holds (equality_query_environment (Pair_Term gamma gamma))
      None [0] (Some []) []"
    "native_application_formed
      (equality_query_environment (Pair_Term (Pair_Term gamma extra) gamma)) None [0] (Some []) []"
    "\<not> native_positive_holds
      (equality_query_environment (Pair_Term (Pair_Term gamma extra) gamma)) None [0] (Some []) []"
  using assms native_context_equality[of gamma gamma]
    native_context_equality[of "Pair_Term gamma extra" gamma] by auto

theorem native_contraction_is_not_implicit:
  assumes "term_formed gamma"
  shows "native_positive_holds
      (equality_query_environment (Pair_Term (Pair_Term gamma gamma) (Pair_Term gamma gamma)))
      None [0] (Some []) []"
    "native_application_formed
      (equality_query_environment (Pair_Term gamma (Pair_Term gamma gamma))) None [0] (Some []) []"
    "\<not> native_positive_holds
      (equality_query_environment (Pair_Term gamma (Pair_Term gamma gamma))) None [0] (Some []) []"
  using assms native_context_equality[of "Pair_Term gamma gamma" "Pair_Term gamma gamma"]
    native_context_equality[of gamma "Pair_Term gamma gamma"]
  by (auto simp: eq_commute)

theorem native_exchange_is_not_implicit:
  assumes "term_formed x" "term_formed y" "x \<noteq> y"
  shows "native_positive_holds
      (equality_query_environment (Pair_Term (Pair_Term x y) (Pair_Term x y))) None [0] (Some []) []"
    "native_application_formed
      (equality_query_environment (Pair_Term (Pair_Term y x) (Pair_Term x y))) None [0] (Some []) []"
    "\<not> native_positive_holds
      (equality_query_environment (Pair_Term (Pair_Term y x) (Pair_Term x y))) None [0] (Some []) []"
  using assms native_context_equality[of "Pair_Term x y" "Pair_Term x y"]
    native_context_equality[of "Pair_Term y x" "Pair_Term x y"] by auto

lemma distinct_formed_resource_values:
  "term_formed (Target_Term (Whole_Artifact empty_artifact))"
  "term_formed (Payload_Term [])"
  "Target_Term (Whole_Artifact empty_artifact) \<noteq> Payload_Term []"
  by (simp_all add: octets_formed_def)

text \<open>
  The first component of each argument is an ordinary finite resource term.
  These counterexamples use one fixed, closed, natively recovered equality
  program. Each edited call remains well formed, but its truth changes.
  Consequently no universal weakening, contraction, or exchange rule follows
  from the generic consequence operator. A particular definition may explicitly
  admit such edits; the counterexamples impose no universal linearity rule.
  All these calls retain exactly the original program environment, by
  equality_future_program_environment_unchanged.
\<close>

end
