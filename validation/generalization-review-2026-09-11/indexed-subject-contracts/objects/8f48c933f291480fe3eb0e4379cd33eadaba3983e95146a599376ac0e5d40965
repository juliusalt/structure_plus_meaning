theory Factor_Program_Tests
  imports Factor_Argument_Packages Factor_Positive_Admission
begin

section \<open>A complete source scope and entry are fixed before future operands\<close>

theorem native_program_test_total:
  fixes C :: "local_address option artifact_environment"
  assumes reference: "native_package_at C cu cr R" and query_entry: "query\<in>system_definitions R"
    and query: "\<And>z. (query,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
    and package: "native_package_at E pu pr P" and entry: "d\<in>system_definitions P"
    and source: "environment_value_presents E e"
  shows "\<exists>H u v T. environment_formed H \<and> environment_included C H \<and>
    u\<notin>environment_uses C \<and> (u,[])\<notin>system_definitions R \<and>
    native_package_at H cu cr R \<and> native_package_at H v [] T \<and>
    system_definitions T=insert (u,[]) (system_definitions R) \<and>
    (\<forall>z. schema_call_formed T (u,[]) z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. ((u,[]),z)\<in>positive_meaning T \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed T b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning T \<longleftrightarrow> (b,z)\<in>positive_meaning R)) \<and>
    (\<forall>w\<in>environment_uses C. \<forall>A. artifact_at H w A \<longleftrightarrow> artifact_at C w A) \<and>
    (\<forall>w\<in>environment_uses C. \<forall>s a. binds_slot H w s a \<longleftrightarrow> binds_slot C w s a)"
proof -
  have ef: "environment_formed E" and formed_source: "term_formed e"
    using environment_value_presents_formed[OF source] by blast+
  have positions: "(pu,pr)\<in>environment_positions E" "d\<in>environment_positions E"
    by (rule native_package_root_position[OF package], rule native_package_entry_position[OF package entry])
  have addresses: "octets_formed pr" "octets_formed (snd d)"
    using environment_position_address[OF ef positions(1)] environment_position_address[OF ef positions(2)] by simp_all
  let ?p="package_subject_pattern (exact_term_pattern e) (exact_term_pattern (use_data_term pu))
    (exact_term_pattern (Payload_Term pr)) (Pattern_Pair (exact_term_pattern (definition_site_value d)) (Pattern_Variable (0::nat)))"
  have pattern: "pattern_formed ?p" using formed_source addresses by simp
  have variables: "pattern_variables ?p\<subseteq>{0}" by simp
  obtain H u v T where built: "environment_formed H" "environment_included C H"
    "u\<notin>environment_uses C" "(u,[])\<notin>system_definitions R"
    "native_package_at H cu cr R" "native_package_at H v [] T"
    "system_definitions T=insert (u,[]) (system_definitions R)"
    "\<forall>z. schema_call_formed T (u,[]) z \<longleftrightarrow> term_formed z"
    "\<forall>z. ((u,[]),z)\<in>positive_meaning T \<longleftrightarrow>
      term_formed z \<and> (query,evaluate_pattern (\<lambda>_. z) ?p)\<in>positive_meaning R"
    "\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed T b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning T \<longleftrightarrow> (b,z)\<in>positive_meaning R)"
    "\<forall>w\<in>environment_uses C. \<forall>A. artifact_at H w A \<longleftrightarrow> artifact_at C w A"
    "\<forall>w\<in>environment_uses C. \<forall>s a. binds_slot H w s a \<longleftrightarrow> binds_slot C w s a"
    using native_argument_call_package_total[OF reference query_entry pattern variables] by blast
  have exact: "positive_query_result (package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) z)) \<longleftrightarrow> (d,z)\<in>positive_meaning P" for z
    using positive_query_at_package[OF source package, of d z] by (simp only: positive_query_exact)
  have tf: "term_formed z" if "(d,z)\<in>positive_meaning P" for z
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  have meaning: "((u,[]),z)\<in>positive_meaning T \<longleftrightarrow> (d,z)\<in>positive_meaning P" for z
    by (simp only: built(9)[rule_format] evaluate_pattern.simps evaluate_exact_term_pattern query exact)
      (use tf in blast)
  show ?thesis by (rule exI[of _ H], rule exI[of _ u], rule exI[of _ v], rule exI[of _ T])
    (use built(1-8,10-12) meaning in blast)
qed

text \<open>
  The supplied source environment and its actual entry occur literally in
  the new clause's argument pattern. The only native callee is the independently
  proved query entry. Every future operand has exactly the original test's
  positive truth, for arbitrary ordinary or material source clauses.

  The source is data, so no compatibility between its uses and the reference
  uses is required. The reference is retained in full. The new test has a
  variable interface; preservation of positive truth does not identify that
  interface with the original entry's call-formation boundary.
\<close>

end
