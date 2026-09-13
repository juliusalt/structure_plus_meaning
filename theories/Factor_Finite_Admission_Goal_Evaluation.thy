theory Factor_Finite_Admission_Goal_Evaluation
  imports Factor_Finite_Checked_Requirements Factor_Finite_Sequence_Reading Factor_Finite_Native_Evaluation
begin

section \<open>The goal determines every leaf call that its observation needs\<close>

fun finite_admission_goal_test :: "('d\<times>finite_factor_term) fset\<Rightarrow>'d admission_goal\<Rightarrow>
    finite_factor_term\<Rightarrow>bool" where
  "finite_admission_goal_test A (Existing_Admission d) t=((d,t) |\<in>| A)"
| "finite_admission_goal_test A (Paired_Admission g h) t=(case t of Finite_Pair x y \<Rightarrow>
    finite_admission_goal_test A g x \<and> finite_admission_goal_test A h y | _ \<Rightarrow> False)"
| "finite_admission_goal_test A (Collected_Admission g) t=(case finite_data_sequence_elements t of None \<Rightarrow> False
    | Some xs \<Rightarrow> list_all (finite_admission_goal_test A g) xs)"

fun finite_admission_goal_demand :: "'d admission_goal\<Rightarrow>finite_factor_term\<Rightarrow>('d\<times>finite_factor_term) fset" where
  "finite_admission_goal_demand (Existing_Admission d) t={|(d,t)|}"
| "finite_admission_goal_demand (Paired_Admission g h) t=(case t of Finite_Pair x y \<Rightarrow>
    finite_admission_goal_demand g x |\<union>| finite_admission_goal_demand h y | _ \<Rightarrow> {||})"
| "finite_admission_goal_demand (Collected_Admission g) t=(case finite_data_sequence_elements t of None \<Rightarrow> {||}
    | Some xs \<Rightarrow> ffUnion (fimage (finite_admission_goal_demand g) (fset_of_list xs)))"

theorem finite_admission_goal_observation_exact:
  assumes agreement: "\<And>d x. (d,x) |\<in>| finite_admission_goal_demand g t \<Longrightarrow>
    ((d,x) |\<in>| A \<longleftrightarrow> (d,decode_finite_term x)\<in>M)"
  shows "finite_admission_goal_test A g t \<longleftrightarrow> admission_goal_holds M g (decode_finite_term t)"
  using agreement
proof (induction g arbitrary: t)
  case (Existing_Admission d)
  then show ?case by simp
next
  case (Paired_Admission g h)
  show ?case
  proof (cases t)
    case (Finite_Target a)
    then show ?thesis by simp
  next
    case (Finite_Payload b)
    then show ?thesis by simp
  next
    case (Finite_Pair x y)
    have first: "finite_admission_goal_test A g x \<longleftrightarrow> admission_goal_holds M g (decode_finite_term x)"
      by (rule Paired_Admission.IH(1)) (use Paired_Admission.prems in \<open>simp add: Finite_Pair\<close>)
    have second: "finite_admission_goal_test A h y \<longleftrightarrow> admission_goal_holds M h (decode_finite_term y)"
      by (rule Paired_Admission.IH(2)) (use Paired_Admission.prems in \<open>simp add: Finite_Pair\<close>)
    show ?thesis by (simp add: Finite_Pair first second)
  qed
next
  case (Collected_Admission g)
  show ?case
  proof (cases "finite_data_sequence_elements t")
    case None
    have absent: "\<not>(\<exists>xs. decode_finite_term t=data_list_term xs)"
      using None by (simp add: finite_data_sequence_elements_absent)
    show ?thesis using absent by (simp add: None)
  next
    case (Some xs)
    have shape: "decode_finite_term t=data_list_term (map decode_finite_term xs)"
      using Some by (simp only: finite_data_sequence_elements_decode)
    have each: "finite_admission_goal_test A g x \<longleftrightarrow> admission_goal_holds M g (decode_finite_term x)"
      if member: "x\<in>set xs" for x
    proof (rule Collected_Admission.IH)
      fix d y assume demand: "(d,y) |\<in>| finite_admission_goal_demand g x"
      show "(d,y) |\<in>| A \<longleftrightarrow> (d,decode_finite_term y)\<in>M"
        by (rule Collected_Admission.prems)
          (use member demand in \<open>auto simp: Some fset_of_list.rep_eq\<close>)
    qed
    show ?thesis by (simp add: Some shape data_list_term_injective list_all_iff each)
  qed
qed

section \<open>The actual source evaluator supplies those leaf observations\<close>

definition finite_native_goal_observation where
  "finite_native_goal_observation E u r D g t=(if finite_admission_goal_demand g t |\<subseteq>| D then
    map_option (\<lambda>(P,A). (P,A,finite_admission_goal_test A g t)) (finite_native_program_evaluation E u r D)
    else None)"

theorem finite_native_goal_observation_conditions:
  "finite_native_goal_observation E u r D g t=Some (P,A,b) \<longleftrightarrow>
    finite_admission_goal_demand g t |\<subseteq>| D \<and>
    finite_native_program_evaluation E u r D=Some (P,A) \<and> b=finite_admission_goal_test A g t"
  by (auto simp: finite_native_goal_observation_def split: option.splits prod.splits if_splits)

theorem finite_native_goal_observation_exact:
  assumes result: "finite_native_goal_observation E u r D g t=Some (P,A,b)"
  shows "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "b \<longleftrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
proof -
  have demands: "finite_admission_goal_demand g t |\<subseteq>| D"
    and evaluated: "finite_native_program_evaluation E u r D=Some (P,A)"
    and answer: "b=finite_admission_goal_test A g t"
    using result by (simp only: finite_native_goal_observation_conditions; blast)+
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    by (rule finite_native_program_evaluation_exact(1)[OF evaluated])
  show "b \<longleftrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
    unfolding answer
    by (rule finite_admission_goal_observation_exact; rule finite_native_program_evaluation_call[OF evaluated])
      (use demands in auto)
qed

export_code finite_native_goal_observation checking SML

text \<open>
  The original goal determines which actual leaf calls matter for this term.
  The native package evaluator computes their truth from the recovered program
  and checks its complete finite decision prerequisites. A missing required
  demand or failed evaluation returns no observation. No satisfaction table is
  supplied to the native observation operation.
\<close>

end
