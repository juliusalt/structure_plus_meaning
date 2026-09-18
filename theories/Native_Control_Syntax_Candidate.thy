theory Native_Control_Syntax_Candidate
  imports Native_Control_Compile_Profile Filtered_Native_Questions
begin

section \<open>Exact finite union with an explicit enumeration boundary\<close>

definition enumerated_union :: "'a::linorder fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "enumerated_union A B=fset_of_list (sorted_list_of_fset A @ sorted_list_of_fset B)"

lemma enumerated_union_exact:
  "enumerated_union A B=A |\<union>| B"
  by (simp add: enumerated_union_def fset_inject[symmetric] fset_of_list.rep_eq)

definition finite_syntax_join_enumerated where
  "finite_syntax_join_enumerated f g U I R S=\<lparr>finite_structure=\<lparr>
    finite_carrier=enumerated_union (enumerated_union U (fimage f (finite_carrier (finite_structure R))))
      (fimage g (finite_carrier (finite_structure S))),
    finite_incidence=enumerated_union
      (enumerated_union I (fimage (\<lambda>(a,p,x). (f a,f p,f x)) (finite_incidence (finite_structure R))))
      (fimage (\<lambda>(a,p,x). (g a,g p,g x)) (finite_incidence (finite_structure S)))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=enumerated_union
      (fimage (\<lambda>(a,v). (f a,v)) (finite_bindings (finite_data R)))
      (fimage (\<lambda>(a,v). (g a,v)) (finite_bindings (finite_data S)))\<rparr>\<rparr>"

lemma finite_syntax_join_enumerated_exact:
  "finite_syntax_join_enumerated f g U I R S=finite_syntax_join f g U I R S"
  by (simp add: finite_syntax_join_enumerated_def finite_syntax_join_def enumerated_union_exact)

section \<open>Complete union observations on the actual seed's pattern carriers\<close>

datatype union_candidate = Original_Union | Enumerated_Union | Left_Projection

fun union_candidate_result :: "union_candidate \<Rightarrow> 'a::linorder fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "union_candidate_result Original_Union A B=A |\<union>| B"
| "union_candidate_result Enumerated_Union A B=enumerated_union A B"
| "union_candidate_result Left_Projection A B=A"

definition union_original_condition where
  "union_original_condition m pairs \<longleftrightarrow>
    (\<forall>(A,B)\<in>set pairs. union_candidate_result m A B=A |\<union>| B)"

definition union_observation where
  "union_observation m pairs=list_all (\<lambda>(A,B).
    union_candidate_result m A B=A |\<union>| B) pairs"

lemma union_observation_exact:
  "union_observation m pairs=union_original_condition m pairs"
  by (simp add: union_observation_def union_original_condition_def list_all_iff)

definition union_candidates where
  "union_candidates=[Original_Union,Enumerated_Union,Left_Projection]"

definition union_question where
  "union_question pairs=filtered_development_question union_candidates
    (\<lambda>m. union_observation m pairs)"

theorem union_admission_original_condition:
  assumes question: "union_question pairs=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  shows "i<length union_candidates \<and> union_original_condition (union_candidates!i) pairs"
  using filtered_development_admission[OF question[unfolded union_question_def] admission selected]
  by (simp only: union_observation_exact)

definition union_subjects where
  "union_subjects xs=(let carriers=map (\<lambda>t.
    finite_carrier (finite_structure (profile_pattern_term t))) xs in
    map (\<lambda>A. (A,{||})) carriers @ map (\<lambda>A. ({||},A)) carriers @ map (\<lambda>A. (A,A)) carriers)"

definition union_execution_question where
  "union_execution_question ignored=union_question (union_subjects (profile_terms ()))"

definition union_execution_value where
  "union_execution_value run=finite_pair_presentation isabelle_context_data
    (finite_steered_development_value finite_development_question_value)
    (development_seed_context,run)"

lemma union_execution_value_injective: "inj union_execution_value"
proof -
  have complete: "inj (finite_pair_presentation isabelle_context_data
      (finite_steered_development_value finite_development_question_value))"
    by (intro finite_pair_presentation_injective isabelle_context_data_injective
      finite_development_values_injective finite_development_question_value_injective)
  show ?thesis
    unfolding union_execution_value_def
    by (rule injI; drule injD[OF complete]; simp)
qed

text \<open>This finite scope tests all eighty actual carriers with empty and
  duplicate operands. The original condition is complete set union, not timing
  or a supplied satisfaction table. The universal equations have no formation
  assumption. Both exact candidates may remain admitted; these observations do
  not choose an algorithm by cost or establish the whole development policy.\<close>

export_code union_execution_question union_execution_value context_execution_summary
  native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Union_Review file_prefix "native_control_union_review"

end
