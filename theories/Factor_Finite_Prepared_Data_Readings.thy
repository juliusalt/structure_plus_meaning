theory Factor_Finite_Prepared_Data_Readings
  imports RRA_Finite_Syntax_Bodies Factor_Finite_Singleton_Quotation Factor_Finite_Complete_Data_Readings
begin

definition finite_payload_body_readings where
  "finite_payload_body_readings C r=fimage (\<lambda>v. (Finite_Payload v,{|r|},{||}))
    (ffilter (finite_payload_leaf_body C r) (finite_payload_values C r))"

lemma finite_payload_body_readings_exact:
  assumes "finite_object_formed C"
  shows "finite_payload_body_readings C r=finite_payload_readings C r"
proof -
  have same: "finite_payload_leaf_body C r=finite_payload_leaf_at C r"
    by (rule ext) (simp only: finite_payload_leaf_guard assms simp_thms)
  show ?thesis by (simp only: finite_payload_body_readings_def finite_payload_readings_def same)
qed

definition finite_record_body_readings where
  "finite_record_body_readings C r f V reads=ffUnion (fimage (\<lambda>(ps,xs).
    case xs of [l,q] \<Rightarrow> finite_join_readings f V r ps (reads l) (reads q) | _ \<Rightarrow> {||})
      (finite_record_body_candidates C r 2))"

lemma finite_record_body_readings_exact:
  assumes "finite_object_formed C"
  shows "finite_record_body_readings C r f V reads=finite_record_readings C r f V reads"
  by (simp only: finite_record_body_readings_def finite_record_readings_def finite_two_field_record_def
    finite_record_body_candidates_exact[OF assms])

fun finite_data_body_readings where
  "finite_data_body_readings 0 C r={||}"
| "finite_data_body_readings (Suc n) C r=finite_payload_body_readings C r |\<union>|
    finite_record_body_readings C r Finite_Pair {||} (finite_data_body_readings n C)"

lemma finite_data_body_readings_exact:
  assumes formed: "finite_exact_formed C"
  shows "finite_data_body_readings n C r=finite_term_readings_bounded n (finite_singleton_environment C) () r"
proof (induction n arbitrary: r)
  case 0
  show ?case by simp
next
  case (Suc n)
  have object: "finite_object_formed C" using formed by (simp add: finite_exact_formed_def)
  have previous: "finite_data_body_readings n C=finite_term_readings_bounded n (finite_singleton_environment C) ()"
    by (rule ext) (rule Suc.IH)
  show ?case
    by (simp only: finite_data_body_readings.simps finite_singleton_bound_readings_step formed if_True
      finite_payload_body_readings_exact[OF object] finite_record_body_readings_exact[OF object] previous)
qed

definition finite_complete_data_body_values where
  "finite_complete_data_body_values C r=fimage fst
    (ffilter (\<lambda>(t,I,K). I=finite_carrier (finite_structure C) \<and> K={||})
      (finite_data_body_readings (fcard (finite_carrier (finite_structure C))) C r))"

definition finite_complete_data_readings_prepared where
  "finite_complete_data_readings_prepared C r=(if finite_exact_formed C \<and>
    r |\<in>| finite_carrier (finite_structure C) then finite_complete_data_body_values C r else {||})"

theorem finite_complete_data_readings_prepared_exact:
  "finite_complete_data_readings_prepared C r=finite_complete_data_readings C r"
  by (cases "finite_exact_formed C")
    (simp only: finite_complete_data_readings_prepared_def finite_complete_data_body_values_def finite_complete_data_readings_def
      finite_singleton_bound_readings finite_data_body_readings_exact; simp)+

text \<open>
  The complete original source is checked before recursion. Each recursive
  step consumes the local leaf and record bodies under that same proved
  formation premise. A singleton environment has no external bindings, so no
  target reading can contribute. The all-input equality preserves every
  original term, interior, slot boundary, layout and malformed-input refusal.
\<close>

end
