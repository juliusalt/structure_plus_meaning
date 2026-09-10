theory Factor_Reasoning_Method_Investigation
  imports Factor_Reasoning_Premise_Admission Finite_Investigation_Interface
begin

definition reasoning_workload_frontier :: "nat \<Rightarrow> (nat\<times>finite_factor_term) list" where
  "reasoning_workload_frontier w=(if w=0 then admission_pair_reasoning_frontier else reasoning_false_frontier)"

definition reasoning_workload_goal :: "nat \<Rightarrow> finite_factor_term" where
  "reasoning_workload_goal w=(if w=0 then admission_pair_reasoning_goal else reasoning_false_goal)"

definition reasoning_method_known where
  "reasoning_method_known (m::nat) C=(if m=0 then admitted_reasoning_frontier C
    else if m=1 then C else [])"

definition reasoning_method_report where
  "reasoning_method_report m w=finite_learned_investigation admission_pair_reasoning_library
    (reasoning_workload_frontier w)
    (fset_of_list (reasoning_method_known m (reasoning_workload_frontier w)))
    {|(0::nat,(341,reasoning_workload_goal w))|}"

definition reasoning_workload_native_goal where
  "reasoning_workload_native_goal w \<longleftrightarrow>
    (341,decode_finite_term (reasoning_workload_goal w))\<in>positive_meaning admission_plan_system"

lemma reasoning_workload_native_goal_code [code]:
  "reasoning_workload_native_goal w \<longleftrightarrow> w=0"
  by (simp add: reasoning_workload_native_goal_def reasoning_workload_goal_def
    reasoning_pair_goal_native reasoning_false_goal_not_native)

definition reasoning_method_quality :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "reasoning_method_quality m w f=
    (let known=reasoning_method_known m (reasoning_workload_frontier w);
         settled=(fst (snd (snd (reasoning_method_report m w)))={||});
         actual=reasoning_workload_native_goal w
     in if f=0 then list_all (\<lambda>(d,t). d=340 \<and> finite_admission_counter_check t) known
        else if f=1 then (settled \<longrightarrow> actual)
        else f=2 \<and> (settled=actual))"

definition reasoning_method_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "reasoning_method_investigation_observations=concat (map (\<lambda>q.
    concat (map (\<lambda>m. map (\<lambda>w. (q,m,w))
      (filter (\<lambda>w. reasoning_method_quality m w q) [0,1])) [0,1,2])) [0,1,2])"

definition reasoning_method_investigation_relation :: "(nat\<times>nat) list" where
  "reasoning_method_investigation_relation=filter (\<lambda>(m,k).
    \<forall>w\<in>set [0,1]. \<forall>q\<in>set [0,1,2].
      reasoning_method_quality m w q \<longrightarrow> reasoning_method_quality k w q)
    (investigation_pairs [0,1,2])"

definition reasoning_method_investigation where
  "reasoning_method_investigation selected=investigation_basis [0,1,2] [0,1,2] selected
    reasoning_method_investigation_observations reasoning_method_investigation_relation"

export_code reasoning_method_investigation reasoning_method_investigation_observations
  reasoning_method_investigation_relation checking SML

text \<open>
  The methods admit possible premises through their actual native predicate,
  trust every possible premise, or establish none. Each uses the same generated
  conditional rule family. The two workloads provide all valid counter facts
  or one formed false candidate premise. The conditions ask whether every
  known fact is admitted, whether settlement is sound, and whether the returned
  decision agrees with the independently established native goal outcome.
  The last condition distinguishes useful progress from never settling a goal.

  Observations and comparison are computed from the actual method reports and
  native tests. This is a development question about how to use information,
  evaluated by the same machinery. It covers these three methods and these two
  workloads; it does not decide every question about usefulness or reliability.
\<close>

end
