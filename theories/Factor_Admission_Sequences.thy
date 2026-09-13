theory Factor_Admission_Sequences
  imports Factor_Admission_Plan_Contracts Factor_Admission_Goal_Sequences
begin

section \<open>One construction threads every requirement through the current source\<close>

fun admission_sequence :: "nat admission_goal list \<Rightarrow> nat \<Rightarrow>
    nat list\<times>(nat\<times>admission_instruction list)" where
  "admission_sequence [] n=([],n,[])"
| "admission_sequence (g#gs) n=
    (case admission_plan g n of (d,m,xs) \<Rightarrow>
      case admission_sequence gs m of (ds,k,ys) \<Rightarrow> (d#ds,k,xs@ys))"

definition admission_sequence_step where
  "admission_sequence_step g n=(case admission_plan g n of (d,m,xs) \<Rightarrow> Some ((d,xs),m))"

lemma admission_sequence_shared:
  "\<exists>xs k. construct_admission_sequence admission_sequence_step gs n=Some (xs,k) \<and>
    admission_sequence gs n=(map fst xs,k,concat (map snd xs))"
proof (induction gs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons g gs)
  obtain d m cs where head: "admission_plan g n=(d,m,cs)" by (cases "admission_plan g n") auto
  obtain xs k where tail: "construct_admission_sequence admission_sequence_step gs m=Some (xs,k)"
    and original: "admission_sequence gs m=(map fst xs,k,concat (map snd xs))"
    using Cons.IH by blast
  have step: "admission_sequence_step g n=Some ((d,cs),m)"
    by (simp only: admission_sequence_step_def head prod.case)
  show ?case by (rule exI[of _ "(d,cs)#xs"], rule exI[of _ k])
    (simp add: step head tail original)
qed

declare [[code drop: admission_sequence]]

lemma admission_sequence_code [code]:
  "admission_sequence gs n=(case construct_admission_sequence admission_sequence_step gs n of
    None \<Rightarrow> ([],n,[]) | Some (xs,k) \<Rightarrow> (map fst xs,k,concat (map snd xs)))"
  using admission_sequence_shared[of gs n] by auto

lemma admission_sequence_length:
  "admission_sequence gs n=(ds,k,cs) \<Longrightarrow> length ds=length gs"
  by (induction gs arbitrary: n ds k cs) (auto split: prod.splits)

theorem admission_sequence_installed:
  assumes source: "admission_source P n"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
    and sequence: "admission_sequence gs n=(ds,k,cs)"
  shows "admission_source (install_admission_plan P cs) k \<and>
    admission_extension P (install_admission_plan P cs) \<and>
    list_all2 (\<lambda>g d. d\<in>system_definitions (install_admission_plan P cs) \<and>
      (\<forall>t. (d,t)\<in>positive_meaning (install_admission_plan P cs) \<longleftrightarrow>
        admission_goal_holds (positive_meaning P) g t)) gs ds"
  using source supported sequence
proof (induction gs arbitrary: P n ds k cs)
  case Nil
  then show ?case by (auto simp: admission_source_def intro: admission_extension_refl)
next
  case (Cons g gs)
  obtain a m xs where first: "admission_plan g n=(a,m,xs)"
    by (cases "admission_plan g n") auto
  obtain es l ys where rest: "admission_sequence gs m=(es,l,ys)"
    by (cases "admission_sequence gs m") auto
  have fields: "ds=a#es" "k=l" "cs=xs@ys"
    using Cons.prems(3) by (auto simp: first rest)
  have support_g: "admission_goal_sites g\<subseteq>system_definitions P"
    and support_gs: "\<forall>h\<in>set gs. admission_goal_sites h\<subseteq>system_definitions P"
    using Cons.prems(2) by auto
  let ?Q="install_admission_plan P xs"
  let ?R="install_admission_plan ?Q ys"
  have child: "admission_source ?Q m \<and> admission_extension P ?Q \<and>
    a\<in>system_definitions ?Q \<and>
    (\<forall>t. (a,t)\<in>positive_meaning ?Q \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t)"
    by (rule admission_plan_installed[OF Cons.prems(1) support_g first])
  have child_source: "admission_source ?Q m" and child_extension: "admission_extension P ?Q"
    and child_member: "a\<in>system_definitions ?Q" using child by blast+
  have supported_rest: "\<forall>h\<in>set gs. admission_goal_sites h\<subseteq>system_definitions ?Q"
    using support_gs admission_extension_definitions[OF child_extension] by blast
  have tail: "admission_source ?R l \<and> admission_extension ?Q ?R \<and>
    list_all2 (\<lambda>h d. d\<in>system_definitions ?R \<and>
      (\<forall>t. (d,t)\<in>positive_meaning ?R \<longleftrightarrow>
        admission_goal_holds (positive_meaning ?Q) h t)) gs es"
    by (rule Cons.IH[OF child_source supported_rest rest])
  have tail_source: "admission_source ?R l" and tail_extension: "admission_extension ?Q ?R"
    using tail by blast+
  have realized: "admission_goal_realized P g a ?Q"
    using child by (simp only: admission_goal_realized_def; blast)
  have results: "admission_goal_results ?Q gs es ?R"
    using tail by (simp only: admission_goal_results_def; blast)
  have combined: "admission_extension P ?R \<and> admission_goal_results P (g#gs) (a#es) ?R"
    by (rule admission_goal_sequence_cons[OF realized tail_extension results support_gs])
  show ?case using tail_source combined
    by (simp add: admission_goal_results_def fields install_admission_plan_append)
qed

text \<open>
  Every component plan is the existing admission planner's output. The next
  goal starts at the preceding goal's returned counter. The complete sequence
  retains one result entry for each original requirement occurrence, including
  repetitions, and preserves every component's meaning in the final source.
  Its executable equation uses the same stateful traversal as the native
  constructor and combines the returned instruction chunks in their order.
  This shared construction does not decide which requirements a problem has.
\<close>

end
