theory Factor_Reasoning_Premise_Admission
  imports Factor_Admission_Pair_Reasoning
begin

section \<open>Possible premise values have an actual native admission test\<close>

fun finite_admission_counter_number :: "finite_factor_term \<Rightarrow> nat option" where
  "finite_admission_counter_number (Finite_Target t)=None"
| "finite_admission_counter_number (Finite_Payload b)=(if b=[] then Some 0 else None)"
| "finite_admission_counter_number (Finite_Pair a b)=
    (if a=Finite_Payload [] then map_option Suc (finite_admission_counter_number b) else None)"

lemma finite_admission_counter_number_exact:
  "finite_admission_counter_number t=Some n \<longleftrightarrow> t=finite_admission_counter n"
  by (induction t arbitrary: n) (case_tac n; auto split: option.splits if_splits)+

lemma finite_admission_counter_number_correct:
  "finite_admission_counter_number t=Some n \<longleftrightarrow> decode_finite_term t=admission_counter n"
  by (simp only: finite_admission_counter_number_exact finite_admission_counter_exact[symmetric]
    decode_finite_term_injective)

definition finite_admission_counter_check where
  "finite_admission_counter_check t \<longleftrightarrow> (340,decode_finite_term t)\<in>positive_meaning admission_plan_system"

lemma finite_admission_counter_check_code [code]:
  "finite_admission_counter_check t \<longleftrightarrow> finite_admission_counter_number t\<noteq>None"
  by (simp only: finite_admission_counter_check_def admission_plan_counter_exact
    finite_admission_counter_number_correct[symmetric]; cases "finite_admission_counter_number t"; auto)

definition admitted_reasoning_frontier :: "(nat\<times>finite_factor_term) list \<Rightarrow> (nat\<times>finite_factor_term) list" where
  "admitted_reasoning_frontier C=filter (\<lambda>(d,t). d=340 \<and> finite_admission_counter_check t) C"

theorem admitted_reasoning_frontier_sound:
  "q\<in>set (admitted_reasoning_frontier C) \<Longrightarrow>
    decode_finite_call_term q\<in>positive_meaning admission_plan_system"
  by (auto simp: admitted_reasoning_frontier_def finite_admission_counter_check_def
    decode_finite_call_term_def map_prod_def)

section \<open>Formation alone cannot establish a possible premise\<close>

lemma noncounter_payload [simp]:
  "admission_counter n\<noteq>Payload_Term [0]" "Payload_Term [0]\<noteq>admission_counter n"
  by (cases n; auto)+

lemma formed_false_counter:
  "term_formed (Payload_Term [0]) \<and> (340,Payload_Term [0])\<notin>positive_meaning admission_plan_system"
  by (simp add: admission_plan_counter_exact octets_formed_def)

definition reasoning_false_frontier :: "(nat\<times>finite_factor_term) list" where
  "reasoning_false_frontier=[(340,finite_admission_counter 0),(340,finite_admission_counter 1),
    (340,Finite_Payload [0])]"

definition reasoning_false_goal where
  "reasoning_false_goal=admission_direct_pair_head Finite_Pair Finite_Payload
    (finite_admission_counter 0) (finite_admission_counter 1) (Finite_Payload [0])"

lemma reasoning_false_goal_not_native:
  "(341,decode_finite_term reasoning_false_goal)\<notin>positive_meaning admission_plan_system"
proof
  assume holds: "(341,decode_finite_term reasoning_false_goal)\<in>positive_meaning admission_plan_system"
  obtain g n d k cs where frame: "decode_finite_term reasoning_false_goal=
      admission_plan_argument (admission_goal_value g) (admission_counter n)
        (admission_counter d) (admission_counter k) (data_list_term (map admission_instruction_value cs))"
    using admission_plan_sound[OF holds] by (auto simp: admission_plan_result_def)
  show False using frame by (auto simp: reasoning_false_goal_def admission_direct_pair_head_def Let_def)
qed

lemma reasoning_pair_goal_native:
  "(341,decode_finite_term admission_pair_reasoning_goal)\<in>positive_meaning admission_plan_system"
  by (simp only: admission_pair_reasoning_goal_def decode_admission_direct_pair_head
    finite_admission_counter_exact; rule admission_direct_pair_counters_native)

definition reasoning_counterexample_experiment where
  "reasoning_counterexample_experiment trust_frontier=finite_learned_investigation
    admission_pair_reasoning_library reasoning_false_frontier
    (fset_of_list (if trust_frontier then reasoning_false_frontier
      else admitted_reasoning_frontier reasoning_false_frontier)) {|(0::nat,(341,reasoning_false_goal))|}"

text \<open>
  The counter test is the actual native counter call, with a proved executable
  equation on every finite term. The possible frontier contains a formed
  payload that the predicate refuses. Treating that frontier as established
  therefore violates the known-premise condition. The rejected premise is
  retained in the conditional rule, and its proposed result is independently
  proved false in the original native planner. The same admission operation
  can establish all valid counter premises without an external truth label.
\<close>

end
