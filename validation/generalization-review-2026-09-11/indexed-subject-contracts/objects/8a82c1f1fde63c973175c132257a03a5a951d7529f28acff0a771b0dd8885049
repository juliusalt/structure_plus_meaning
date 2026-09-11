theory Factor_Lambda
  imports Factor_Native_SK SK_Lambda_Reflection SK_Lambda_Termination
begin

section \<open>Native replay for independently evaluated lambda programs\<close>

theorem lambda_evaluation_factor_derivation:
  assumes "lambda_evaluates c v"
  shows "\<exists>tree. checks_schema_proof sk_system tree 2
    (Pair_Term (sk_value (compile_lambda_closure c)) (sk_value (compile_lambda_closure v)))"
  using lambda_evaluation_compiles[OF assms] sk_reduction_certificate_adequate by blast

theorem native_lambda_evaluation_certificates:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>c v. lambda_evaluates c v \<longrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d
          (Pair_Term (sk_value (compile_lambda_closure c)) (sk_value (compile_lambda_closure v))) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E))"
  using sk_native_reductions_realized lambda_evaluation_compiles by blast

theorem native_compiled_numeral_certificates:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>n. \<exists>H au I K root. native_package_at H pu [] Q \<and>
      native_application_at H au [] d
        (Pair_Term (sk_value (SK_App (SK_App (sk_numeral n) SK_K) SK_S))
          (sk_value (sk_natural n))) I K \<and>
      native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
  using sk_native_reductions_realized compiled_numeral_observation by blast

lemma native_numeral_results_are_distinct:
  "sk_value (sk_natural m)=sk_value (sk_natural n) \<longleftrightarrow> m=n"
  by (simp add: sk_natural_injective)

theorem compiled_numeral_factor_result:
  "(2,Pair_Term (sk_value (SK_App (SK_App (sk_numeral n) SK_K) SK_S))
    (sk_value (sk_natural m)))\<in>positive_meaning sk_system \<longleftrightarrow> n=m"
  by (simp only: sk_reduction_adequate compiled_numeral_observation_exact)

theorem compiled_numeral_certificate_exact:
  "(\<exists>tree. checks_schema_proof sk_system tree 2
    (Pair_Term (sk_value (SK_App (SK_App (sk_numeral n) SK_K) SK_S))
      (sk_value (sk_natural m)))) \<longleftrightarrow> n=m"
  using sk_reduction_certificate_adequate[
    of "SK_App (SK_App (sk_numeral n) SK_K) SK_S" "sk_natural m"]
    compiled_numeral_observation_exact[of n m] by blast

theorem lambda_numeric_factor_result:
  assumes "lambda_evaluates (Lambda_Closure p []) (Lambda_Closure (lambda_numeral n) e)"
  shows "(2,Pair_Term (sk_value (sk_observe (compile_lambda_closure (Lambda_Closure p []))))
    (sk_value (sk_natural m)))\<in>positive_meaning sk_system \<longleftrightarrow> n=m"
  using sk_reduction_adequate[
    of "sk_observe (compile_lambda_closure (Lambda_Closure p []))" "sk_natural m"]
    lambda_numeric_observation_exact[OF assms, of m] by blast

theorem native_lambda_numeric_certificates:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>p n e. lambda_evaluates (Lambda_Closure p []) (Lambda_Closure (lambda_numeral n) e) \<longrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d
          (Pair_Term (sk_value (sk_observe (compile_lambda_closure (Lambda_Closure p []))))
            (sk_value (sk_natural n))) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E))"
  using sk_native_reductions_realized lambda_numeric_observation by blast

theorem lambda_numeric_factor_reflection:
  assumes closed: "lambda_scoped 0 p"
    and result: "(2,Pair_Term
      (sk_value (sk_observe (compile_lambda_closure (Lambda_Closure p e))))
      (sk_value (sk_natural n)))\<in>positive_meaning sk_system"
  shows "lambda_reduces (lambda_observe p) (lambda_natural n)"
proof -
  have reduction: "sk_reduces
    (sk_observe (compile_lambda_closure (Lambda_Closure p e))) (sk_natural n)"
    using result sk_reduction_adequate[
      of "sk_observe (compile_lambda_closure (Lambda_Closure p e))" "sk_natural n"] by blast
  show ?thesis by (rule compiled_lambda_numeric_result_reflection[OF closed reduction])
qed

theorem lambda_numeric_certificate_reflection:
  assumes closed: "lambda_scoped 0 p"
    and certificate: "checks_schema_proof sk_system tree 2
      (Pair_Term (sk_value (sk_observe (compile_lambda_closure (Lambda_Closure p e))))
        (sk_value (sk_natural n)))"
  shows "lambda_reduces (lambda_observe p) (lambda_natural n)"
proof -
  have reduction: "sk_reduces
    (sk_observe (compile_lambda_closure (Lambda_Closure p e))) (sk_natural n)"
    using certificate sk_reduction_certificate_adequate[
      of "sk_observe (compile_lambda_closure (Lambda_Closure p e))" "sk_natural n"] by blast
  show ?thesis by (rule compiled_lambda_numeric_result_reflection[OF closed reduction])
qed

theorem lambda_termination_factor_iff:
  assumes "lambda_scoped 0 p"
  shows "(\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
    (\<exists>t. sk_head_normal t \<and>
      (2,Pair_Term (sk_value (compile_lambda_closure (Lambda_Closure p [])))
        (sk_value t))\<in>positive_meaning sk_system)"
  using lambda_sk_termination_iff[OF assms] sk_reduction_adequate by blast

theorem lambda_termination_certificate_iff:
  assumes "lambda_scoped 0 p"
  shows "(\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
    (\<exists>t tree. sk_head_normal t \<and> checks_schema_proof sk_system tree 2
      (Pair_Term (sk_value (compile_lambda_closure (Lambda_Closure p []))) (sk_value t)))"
  using lambda_sk_termination_iff[OF assms] sk_reduction_certificate_adequate by blast

theorem native_lambda_termination_iff:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>p. lambda_scoped 0 p \<longrightarrow>
      ((\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
        (\<exists>t H au I K root. sk_head_normal t \<and> native_package_at H pu [] Q \<and>
          native_application_at H au [] d
            (Pair_Term (sk_value (compile_lambda_closure (Lambda_Closure p []))) (sk_value t)) I K \<and>
          native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)))"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d where
    package: "closed_native_package_at E pu [] Q"
    and exact: "\<forall>t u. sk_reduces t u \<longleftrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
    using sk_native_reduction_replay_iff by blast
  have each: "\<forall>p. lambda_scoped 0 p \<longrightarrow>
    ((\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
      (\<exists>t H au I K root. sk_head_normal t \<and> native_package_at H pu [] Q \<and>
        native_application_at H au [] d
          (Pair_Term (sk_value (compile_lambda_closure (Lambda_Closure p []))) (sk_value t)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E))"
  proof (intro allI impI)
    fix p
    assume closed: "lambda_scoped 0 p"
    show "(\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
      (\<exists>t H au I K root. sk_head_normal t \<and> native_package_at H pu [] Q \<and>
        native_application_at H au [] d
          (Pair_Term (sk_value (compile_lambda_closure (Lambda_Closure p []))) (sk_value t)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
      using lambda_sk_termination_iff[OF closed] exact by blast
  qed
  show ?thesis using package each by blast
qed

text \<open>
  One fixed native SK package certifies every compiled finite lambda evaluation
  and every numeral observation, including numeric results of arbitrary source
  programs with a finite numeric evaluation. Those result queries have exact
  positive meaning. These are consequences of the independent
  compilation and replay theorems. A certified numeric answer also recovers the
  corresponding beta observation of every closed source program, independently
  of a source-evaluation premise. For every closed source term, evaluator
  termination is equivalent to a Factor derivation of reduction to an SK head
  and to closed native replay under one fixed finite compiled package. The
  latter equivalence covers every future source term and every exact replay
  of its reduction call under that package, independently of proof addresses.
  No lambda evaluation rule is added to generic Factor truth, and the result
  of a weak-head evaluation is not identified with literal normal-form syntax.
\<close>

end
