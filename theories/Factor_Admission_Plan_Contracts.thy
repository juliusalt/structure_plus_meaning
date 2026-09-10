theory Factor_Admission_Plan_Contracts
  imports Factor_Admission_Installation
begin

section \<open>The generated program meets the supplied admission goal\<close>

theorem admission_plan_installed:
  assumes source: "admission_source P n"
    and supported: "admission_goal_sites g\<subseteq>system_definitions P"
    and plan: "admission_plan g n=(d,k,cs)"
  shows "admission_source (install_admission_plan P cs) k \<and>
    admission_extension P (install_admission_plan P cs) \<and>
    d\<in>system_definitions (install_admission_plan P cs) \<and>
    (\<forall>t. (d,t)\<in>positive_meaning (install_admission_plan P cs) \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t)"
  using source supported plan
proof (induction g arbitrary: P n d k cs)
  case (Existing_Admission a)
  then show ?case by (auto simp: admission_source_def intro: admission_extension_refl)
next
  case (Paired_Admission g h)
  obtain a m xs where first: "admission_plan g n=(a,m,xs)"
    by (cases "admission_plan g n") auto
  obtain b l ys where second: "admission_plan h m=(b,l,ys)"
    by (cases "admission_plan h m") auto
  have fields: "d=l" "k=Suc l" "cs=xs@ys@[Pair_Admission_Instruction l a b]"
    using Paired_Admission.prems(3) by (auto simp: first second)
  have supported_g: "admission_goal_sites g\<subseteq>system_definitions P"
    and supported_h: "admission_goal_sites h\<subseteq>system_definitions P"
    using Paired_Admission.prems(2) by auto
  let ?Q="install_admission_plan P xs"
  let ?R="install_admission_plan ?Q ys"
  have left: "admission_source ?Q m \<and> admission_extension P ?Q \<and>
      a\<in>system_definitions ?Q \<and>
      (\<forall>t. (a,t)\<in>positive_meaning ?Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t)"
    by (rule Paired_Admission.IH(1)[OF Paired_Admission.prems(1) supported_g first])
  have left_source: "admission_source ?Q m" and left_extension: "admission_extension P ?Q"
    and first_member: "a\<in>system_definitions ?Q" using left by blast+
  have supported_right: "admission_goal_sites h\<subseteq>system_definitions ?Q"
    using supported_h left_extension by (auto simp: admission_extension_def)
  have right: "admission_source ?R l \<and> admission_extension ?Q ?R \<and>
      b\<in>system_definitions ?R \<and>
      (\<forall>t. (b,t)\<in>positive_meaning ?R \<longleftrightarrow> admission_goal_holds (positive_meaning ?Q) h t)"
    by (rule Paired_Admission.IH(2)[OF left_source supported_right second])
  have right_source: "admission_source ?R l" and right_extension: "admission_extension ?Q ?R"
    and second_member: "b\<in>system_definitions ?R" using right by blast+
  have retained_first: "a\<in>system_definitions ?R"
    using first_member right_extension by (auto simp: admission_extension_def)
  interpret assembled: install_admission_pair ?R l a b
    by unfold_locales (rule right_source, rule retained_first, rule second_member)
  have left_meaning: "(a,t)\<in>positive_meaning ?R \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t" for t
    using left admission_extension_meaning[OF right_extension first_member] by blast
  have right_meaning: "(b,t)\<in>positive_meaning ?R \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) h t" for t
    using right admission_extension_goal[OF left_extension supported_h] by blast
  have correct: "(l,t)\<in>positive_meaning assembled.target \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) (Paired_Admission g h) t" for t
    by (simp only: assembled.exact admission_goal_holds.simps left_meaning right_meaning)
  have extension: "admission_extension P assembled.target"
    by (rule admission_extension_trans[OF admission_extension_trans[OF left_extension right_extension]
      assembled.extension])
  show ?case
    using assembled.next_source extension correct
    by (simp add: fields install_admission_plan_append)
next
  case (Collected_Admission g)
  obtain a m xs where first: "admission_plan g n=(a,m,xs)"
    by (cases "admission_plan g n") auto
  have fields: "d=m" "k=Suc m" "cs=xs@[List_Admission_Instruction m a]"
    using Collected_Admission.prems(3) by (auto simp: first)
  have supported_g: "admission_goal_sites g\<subseteq>system_definitions P"
    using Collected_Admission.prems(2) by simp
  let ?Q="install_admission_plan P xs"
  have child: "admission_source ?Q m \<and> admission_extension P ?Q \<and>
      a\<in>system_definitions ?Q \<and>
      (\<forall>t. (a,t)\<in>positive_meaning ?Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t)"
    by (rule Collected_Admission.IH[OF Collected_Admission.prems(1) supported_g first])
  have child_source: "admission_source ?Q m" and child_extension: "admission_extension P ?Q"
    and child_member: "a\<in>system_definitions ?Q" using child by blast+
  interpret assembled: install_admission_list ?Q m a
    by unfold_locales (rule child_source, rule child_member)
  have child_meaning: "(a,t)\<in>positive_meaning ?Q \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t" for t using child by blast
  have correct: "(m,t)\<in>positive_meaning assembled.target \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) (Collected_Admission g) t" for t
    by (simp only: assembled.exact admission_goal_holds.simps child_meaning)
  have extension: "admission_extension P assembled.target"
    by (rule admission_extension_trans[OF child_extension assembled.extension])
  show ?case using assembled.next_source extension correct
    by (simp add: fields install_admission_plan_append)
qed

text \<open>
  The source and component conditions remain explicit obligations of planning.
  For every native plan that meets them, installation is formed, retains all
  original definitions, and admits exactly the required terms. The conclusion
  quantifies over all terms, including the empty collection and terms that fail
  a component predicate. A subject-specific class still needs its independently
  owned equivalence with the supplied admission goal.
\<close>

end
