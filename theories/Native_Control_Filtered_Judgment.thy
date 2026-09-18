theory Native_Control_Filtered_Judgment
  imports Native_Control_Syntax_Candidate Factor_Inference_Development
begin

section \<open>A computed subject predicate supplies a local native meaning\<close>

definition filtered_judgment_rows where
  "filtered_judgment_rows present subjects condition=map present (filter condition subjects)"

definition filtered_judgment_program where
  "filtered_judgment_program present subjects condition=
    finite_ground_program (filtered_judgment_rows present subjects condition)"

theorem filtered_judgment_meaning:
  assumes injective: "inj present"
    and formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
  shows "((Some [],[]),decode_finite_term (present x))\<in>
      positive_meaning (decode_finite_system (filtered_judgment_program present subjects condition))
    \<longleftrightarrow> x\<in>set subjects \<and> condition x"
proof -
  have rows: "list_all finite_term_formed (filtered_judgment_rows present subjects condition)"
    using formed by (auto simp: filtered_judgment_rows_def list_all_iff)
  show ?thesis
    unfolding filtered_judgment_program_def
    by (simp only: finite_ground_program_meaning[OF rows];
      auto simp: filtered_judgment_rows_def image_iff inj_eq[OF injective])
qed

theorem filtered_judgment_known_calls:
  assumes injective: "inj present"
    and formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and established: "X\<subseteq>{x\<in>set subjects. condition x}"
  shows "(\<lambda>x. ((Some [],[]),decode_finite_term (present x))) ` X\<subseteq>
    positive_meaning (decode_finite_system (filtered_judgment_program present subjects condition))"
  using established filtered_judgment_meaning[OF injective formed] by blast

theorem filtered_judgment_graph_receiver:
  assumes injective: "inj present"
    and formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and established: "X\<subseteq>{x\<in>set subjects. condition x}"
    and program: "P=decode_finite_system (filtered_judgment_program present subjects condition)"
    and known: "K=(\<lambda>x. ((Some [],[]),decode_finite_term (present x))) ` X"
    and graph: "schema_graph_derives P G root d t H"
    and closed: "remaining_obligations (inference_closure (schema_inference_rules P) K) H={}"
  shows "(d,t)\<in>positive_meaning P"
  by (rule schema_graph_development_complete[OF graph _ closed])
    (simp only: program known; rule filtered_judgment_known_calls[OF injective formed established])

theorem filtered_judgment_evaluation:
  assumes injective: "inj present"
    and formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and result: "finite_program_evaluation (filtered_judgment_program present subjects condition) D=Some A"
    and demand: "((Some [],[]),present x) |\<in>| D"
  shows "((Some [],[]),present x) |\<in>| A \<longleftrightarrow> x\<in>set subjects \<and> condition x"
  using finite_program_evaluation_exact(2)[OF result] demand
    filtered_judgment_meaning[OF injective formed, where x=x and condition=condition]
  by auto

text \<open>The program's ground rows are computed by the actual predicate. Its
  interpretation still requires the separately established subject/predicate
  contract; no meaning is inferred from membership in an arbitrary supplied
  table. Known calls belong to this exact program. A different receiving
  program needs its own established transport or certificate premises.\<close>

end
