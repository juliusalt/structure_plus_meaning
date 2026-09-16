theory Factor_Steered_Development
  imports Factor_Development_Steering Finite_Singleton_Selection "HOL-Library.Parallel"
begin

type_synonym native_steering_execution = "native_development_question\<times>native_development_report\<times>
  finite_factor_term list option\<times>nat list option"

definition development_steering_choice :: "native_steering_execution option \<Rightarrow> nat option" where
  "development_steering_choice execution=(case execution of None \<Rightarrow> None
    | Some (Q,report,accepted,methods) \<Rightarrow> (case methods of None \<Rightarrow> None
      | Some ms \<Rightarrow> list_singleton_option ms))"

lemma development_steering_choice_fields:
  assumes chosen: "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
  obtains Q report accepted where "development_steering_question qs=Some Q"
    "native_development_admission Q report=Some accepted"
    "m\<in>set (development_selected_methods accepted)"
  using chosen
  by (auto simp: development_steering_packet_question development_steering_choice_def Let_def
    list_singleton_option_some split: option.splits prod.splits)

theorem development_chosen_producer_conditions:
  assumes "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
    "f\<in>set development_facets" "q\<in>set qs"
  shows "development_producer_condition f (development_producer m) q"
proof -
  obtain Q report accepted where "development_steering_question qs=Some Q"
    "native_development_admission Q report=Some accepted"
    "m\<in>set (development_selected_methods accepted)"
    by (rule development_steering_choice_fields[OF assms(1)]) blast
  then show ?thesis using assms(2,3) development_steering_selected_methods by blast
qed

definition steered_development_result :: "nat \<Rightarrow> native_development_question \<Rightarrow>
    nat\<times>native_development_question\<times>native_development_report\<times>finite_factor_term list option\<times>finite_factor_term list option" where
  "steered_development_result m Q=(let actual=development_producer m Q;
    admission=native_development_admission Q (fst actual) in
    (m,Q,fst actual,snd actual,if snd actual=admission then admission else None))"

theorem steered_development_original_conditions:
  assumes result: "steered_development_result m Q=(m,Q,report,claim,Some accepted)"
    and chosen: "y\<in>set accepted" and original: "C\<in>set (development_conditions Q)"
  shows "development_condition_holds C (development_problem Q) y"
proof -
  have admitted: "native_development_admission Q report=Some accepted"
    using result by (auto simp: steered_development_result_def Let_def split: if_splits)
  show ?thesis by (rule native_development_original_conditions[OF admitted chosen original])
qed

definition native_steered_development where
  "native_steered_development qs requests=(let steering=development_steering_packet qs;
    chosen=development_steering_choice (snd (snd steering)) in
    (requests,steering,chosen,map_option (\<lambda>m. Parallel.map (steered_development_result m) requests) chosen))"

lemma native_steered_development_at:
  assumes chosen: "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
  shows "snd (snd (snd (native_steered_development qs requests)))=Some (map (steered_development_result m) requests)"
  by (simp only: native_steered_development_def Let_def chosen option.simps snd_conv Parallel.map_def)

lemma native_steered_development_preserves_requests:
  "fst (native_steered_development qs requests)=requests"
  by (simp only: native_steered_development_def Let_def fst_conv)

lemma steered_development_preserves_question:
  "fst (snd (steered_development_result m Q))=Q"
  by (simp only: steered_development_result_def Let_def fst_conv snd_conv)

text \<open>The computed native choice now performs subsequent development work.
  Absence or ambiguity yields no chosen producer and no executions. An actual
  singleton selects its declared producer function; requests run independently
  with their original questions. Every returned claim is checked again against
  the original request's closed native admission. The selection's finite prior
  scope does not authorize a result on a new request by itself.\<close>

end
