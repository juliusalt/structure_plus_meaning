theory Factor_Admission_Goal_Sequences
  imports Factor_Admission_Goal_Construction
begin

section \<open>One stateful traversal retains every original occurrence\<close>

definition admission_requirements_hold where
  "admission_requirements_hold M gs t \<longleftrightarrow>
    term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds M g t)"

definition admission_requirements_realized where
  "admission_requirements_realized P gs d Q \<longleftrightarrow> admission_extension P Q \<and>
    d\<in>system_definitions Q \<and> (\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow>
      admission_requirements_hold (positive_meaning P) gs t)"

fun construct_admission_sequence :: "('g\<Rightarrow>'s\<Rightarrow>('d\<times>'s) option)\<Rightarrow>
    'g list\<Rightarrow>'s\<Rightarrow>('d list\<times>'s) option" where
  "construct_admission_sequence C [] s=Some ([],s)"
| "construct_admission_sequence C (g#gs) s=(case C g s of None \<Rightarrow> None
    | Some (d,t) \<Rightarrow> map_option (\<lambda>(ds,u). (d#ds,u)) (construct_admission_sequence C gs t))"

definition admission_goal_results where
  "admission_goal_results P gs ds Q \<longleftrightarrow> list_all2 (\<lambda>g d.
    d\<in>system_definitions Q \<and>
      (\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t)) gs ds"

lemma admission_goal_results_length:
  "admission_goal_results P gs ds Q \<Longrightarrow> length gs=length ds"
  by (simp add: admission_goal_results_def list_all2_conv_all_nth)

lemma admission_goal_results_members:
  "admission_goal_results P gs ds Q \<Longrightarrow> set ds\<subseteq>system_definitions Q"
  unfolding admission_goal_results_def
  by (induction rule: list_all2_induct) auto

lemma admission_goal_results_at:
  assumes "admission_goal_results P gs ds Q" "i<length gs"
  shows "i<length ds \<and> ds!i\<in>system_definitions Q \<and>
    (\<forall>t. (ds!i,t)\<in>positive_meaning Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) (gs!i) t)"
  using assms by (auto simp: admission_goal_results_def list_all2_conv_all_nth)

lemma admission_goal_results_all:
  assumes "admission_goal_results P gs ds Q"
  shows "(\<forall>d\<in>set ds. (d,t)\<in>positive_meaning Q) \<longleftrightarrow>
    (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
  using assms unfolding admission_goal_results_def
  by (induction rule: list_all2_induct) auto

theorem admission_goal_sequence_cons:
  assumes head: "admission_goal_realized P g a Q"
    and tail: "admission_extension Q R"
    and results: "admission_goal_results Q gs ds R"
    and supported: "\<forall>h\<in>set gs. admission_goal_sites h\<subseteq>system_definitions P"
  shows "admission_extension P R \<and> admission_goal_results P (g#gs) (a#ds) R"
proof -
  have first: "admission_extension P Q" and member: "a\<in>system_definitions Q"
    and meaning: "\<And>t. (a,t)\<in>positive_meaning Q \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t"
    using head by (simp only: admission_goal_realized_def; blast)+
  have extension: "admission_extension P R" by (rule admission_extension_trans[OF first tail])
  have kept: "a\<in>system_definitions R \<and>
      (\<forall>t. (a,t)\<in>positive_meaning R \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t)"
    using admission_extension_definitions[OF tail] member
      admission_extension_meaning[OF tail member] meaning by blast
  have remaining: "admission_goal_results P gs ds R"
    using results by (simp only: admission_goal_results_def admission_goal_list_agreement[OF first supported])
  show ?thesis using extension kept remaining by (simp add: admission_goal_results_def)
qed

context admission_goal_constructor
begin

theorem sequence_total:
  assumes source: "schema_system_formed (program s)"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (program s)"
  shows "\<exists>ds t. construct_admission_sequence (construct_admission_goal leaf pair collection) gs s=Some (ds,t) \<and>
    admission_extension (program s) (program t) \<and> admission_goal_results (program s) gs ds (program t)"
  using source supported
proof (induction gs arbitrary: s)
  case Nil
  have extension: "admission_extension (program s) (program s)"
    by (rule admission_extension_refl[OF Nil.prems(1)])
  show ?case using extension by (auto simp: admission_goal_results_def)
next
  case (Cons g gs)
  have head_support: "admission_goal_sites g\<subseteq>system_definitions (program s)"
    and tail_support: "\<forall>h\<in>set gs. admission_goal_sites h\<subseteq>system_definitions (program s)"
    using Cons.prems(2) by auto
  obtain a u where head_result: "construct_admission_goal leaf pair collection g s=Some (a,u)"
    and head: "admission_goal_realized (program s) g a (program u)"
    using total[OF Cons.prems(1) head_support] by blast
  have first_extension: "admission_extension (program s) (program u)"
    using head by (simp only: admission_goal_realized_def; blast)
  have formed: "schema_system_formed (program u)"
    using first_extension by (simp only: admission_extension_def; blast)
  have continued_support: "\<forall>h\<in>set gs. admission_goal_sites h\<subseteq>system_definitions (program u)"
    using tail_support admission_extension_definitions[OF first_extension] by blast
  obtain ds t where tail_result:
      "construct_admission_sequence (construct_admission_goal leaf pair collection) gs u=Some (ds,t)"
    and tail: "admission_extension (program u) (program t)"
    and results: "admission_goal_results (program u) gs ds (program t)"
    using Cons.IH[OF formed continued_support] by blast
  have combined: "admission_extension (program s) (program t) \<and>
      admission_goal_results (program s) (g#gs) (a#ds) (program t)"
    by (rule admission_goal_sequence_cons[OF head tail results tail_support])
  show ?case by (rule exI[of _ "a#ds"], rule exI[of _ t])
    (use combined in \<open>simp add: head_result tail_result\<close>)
qed

theorem sequence_correct:
  assumes source: "schema_system_formed (program s)"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (program s)"
    and result: "construct_admission_sequence (construct_admission_goal leaf pair collection) gs s=Some (ds,t)"
  shows "admission_extension (program s) (program t) \<and> admission_goal_results (program s) gs ds (program t)"
  using sequence_total[OF source supported] result by auto

end

end
