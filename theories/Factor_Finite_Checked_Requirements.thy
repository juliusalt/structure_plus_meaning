theory Factor_Finite_Checked_Requirements
  imports Factor_Checked_Requirement_Plans "HOL-Library.FSet"
begin

section \<open>The complete finite source boundary executes the original checked planner\<close>

fun finite_admission_goal_sites :: "admission_goal\<Rightarrow>nat fset" where
  "finite_admission_goal_sites (Existing_Admission d)={|d|}"
| "finite_admission_goal_sites (Paired_Admission g h)=finite_admission_goal_sites g |\<union>| finite_admission_goal_sites h"
| "finite_admission_goal_sites (Collected_Admission g)=finite_admission_goal_sites g"

lemma finite_admission_goal_sites_correct [simp]:
  "fset (finite_admission_goal_sites g)=admission_goal_sites g"
  by (induction g) simp_all

definition finite_checked_admission_sequence where
  "finite_checked_admission_sequence D gs n=(if fBall D (\<lambda>d. d<n) \<and>
    list_all (\<lambda>g. finite_admission_goal_sites g |\<subseteq>| D) gs then Some (admission_sequence gs n) else None)"

theorem finite_checked_admission_sequence_correct:
  "finite_checked_admission_sequence D gs n=checked_admission_sequence (fset D) gs n"
  by (simp add: finite_checked_admission_sequence_def checked_admission_sequence_def admission_request_supported_def
    admission_source_floor_exact less_eq_fset.rep_eq list_all_iff)

theorem finite_checked_admission_sequence_native:
  "finite_checked_admission_sequence D gs n=Some (ds,k,cs) \<longleftrightarrow>
    (367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning (admission_request_system (fset D))"
  by (simp only: finite_checked_admission_sequence_correct checked_admission_sequence_at_values[OF finite_fset])

export_code finite_checked_admission_sequence checking SML

end
