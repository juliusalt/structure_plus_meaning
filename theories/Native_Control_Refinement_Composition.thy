theory Native_Control_Refinement_Composition
  imports Native_Control_Syntax_Candidate Obligation_Reductions
begin

definition candidate_syntax_join where
  "candidate_syntax_join m f g U I R S=\<lparr>finite_structure=\<lparr>
    finite_carrier=union_candidate_result m
      (union_candidate_result m U (fimage f (finite_carrier (finite_structure R))))
      (fimage g (finite_carrier (finite_structure S))),
    finite_incidence=union_candidate_result m
      (union_candidate_result m I (fimage (\<lambda>(a,p,x). (f a,f p,f x)) (finite_incidence (finite_structure R))))
      (fimage (\<lambda>(a,p,x). (g a,g p,g x)) (finite_incidence (finite_structure S)))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=union_candidate_result m
      (fimage (\<lambda>(a,v). (f a,v)) (finite_bindings (finite_data R)))
      (fimage (\<lambda>(a,v). (g a,v)) (finite_bindings (finite_data S)))\<rparr>\<rparr>"

definition syntax_join_refinement where
  "syntax_join_refinement m \<longleftrightarrow>
    (\<forall>f g U I R S. candidate_syntax_join m f g U I R S=finite_syntax_join f g U I R S)"

lemma syntax_join_refinement_from_union:
  "m\<noteq>Left_Projection \<Longrightarrow> syntax_join_refinement m"
  by (cases m) (simp_all add: syntax_join_refinement_def candidate_syntax_join_def
    finite_syntax_join_def enumerated_union_exact)

lemma syntax_join_refinement_reduction:
  "obligation_reduction UNIV syntax_join_refinement (\<lambda>m. m\<noteq>Left_Projection)
    (\<lambda>m. {((),m)})"
  by (auto simp: obligation_reduction_def rel_ran_def intro: syntax_join_refinement_from_union)

lemma nonempty_right_operand_excludes_projection:
  assumes observed: "union_original_condition m pairs"
    and witness: "({||},B)\<in>set pairs" and nonempty: "B\<noteq>{||}"
  shows "m\<noteq>Left_Projection"
  using assms by (auto simp: union_original_condition_def)

lemma literal_syntax_has_root:
  "[] |\<in>| finite_carrier (finite_structure (finite_literal_syntax t))"
  by (cases t) (simp_all add: finite_external_occurrence_syntax_def)

lemma profile_pattern_has_root:
  "[] |\<in>| finite_carrier (finite_structure (profile_pattern_term t))"
  by (cases t)
    (auto simp: profile_pattern_term_def finite_payload_syntax_def
      finite_bound_pair_syntax_def finite_syntax_join_def literal_syntax_has_root)

lemma union_subjects_have_witness:
  assumes "xs\<noteq>[]"
  obtains B where "({||},B)\<in>set (union_subjects xs)" "B\<noteq>{||}"
proof -
  obtain x ys where xs: "xs=x#ys" using assms by (cases xs) auto
  let ?B="finite_carrier (finite_structure (profile_pattern_term x))"
  have member: "({||},?B)\<in>set (union_subjects xs)"
    by (simp add: union_subjects_def Let_def xs)
  have nonempty: "?B\<noteq>{||}" using profile_pattern_has_root[of x] by auto
  show thesis by (rule that[OF member nonempty])
qed

theorem native_union_admission_refines_syntax:
  assumes question: "union_question (union_subjects xs)=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key union_candidates m)\<in>set accepted"
    and member: "m\<in>set union_candidates"
    and scope: "xs\<noteq>[]"
  shows "syntax_join_refinement m"
proof -
  have condition: "union_original_condition m (union_subjects xs)"
    by (rule union_admission_original_condition[OF question admission selected member])
  obtain B where witness: "({||},B)\<in>set (union_subjects xs)" and nonempty: "B\<noteq>{||}"
    by (rule union_subjects_have_witness[OF scope]) blast
  have leaf: "m\<noteq>Left_Projection"
    by (rule nonempty_right_operand_excludes_projection[OF condition witness nonempty])
  show ?thesis
    by (rule obligation_reduction_discharge[OF syntax_join_refinement_reduction]) (use leaf in auto)
qed

lemma empty_scope_does_not_exclude_projection:
  "union_original_condition Left_Projection []"
  by (simp add: union_original_condition_def)

lemma left_projection_is_not_a_refinement:
  "\<not>syntax_join_refinement Left_Projection"
proof
  assume assumed: "syntax_join_refinement Left_Projection"
  let ?R="finite_payload_syntax []"
  have equal: "candidate_syntax_join Left_Projection id id {||} {||} ?R ?R=
      finite_syntax_join id id {||} {||} ?R ?R"
    using assumed by (auto simp: syntax_join_refinement_def)
  have fields: "finite_carrier (finite_structure
      (candidate_syntax_join Left_Projection id id {||} {||} ?R ?R))=
    finite_carrier (finite_structure (finite_syntax_join id id {||} {||} ?R ?R))"
    by (rule arg_cong[OF equal])
  show False using fields
    by (simp add: candidate_syntax_join_def finite_syntax_join_def finite_payload_syntax_def;
      metis finsert_not_fempty)
qed

lemma seed_union_scope_nonempty: "profile_terms ()\<noteq>[]"
  by (simp only: profile_terms_def map_is_Nil_conv development_seed_context_def isabelle_shared_context_fields
    list.distinct not_False_eq_True)

corollary native_seed_union_refines_syntax:
  assumes question: "union_execution_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (first_occurrence_key union_candidates m)\<in>set accepted"
    and member: "m\<in>set union_candidates"
  shows "syntax_join_refinement m"
  by (rule native_union_admission_refines_syntax[OF question[unfolded union_execution_question_def]
    admission selected member seed_union_scope_nonempty])

text \<open>The receiver instantiates the existing obligation reduction with its
  original whole-constructor equality and the actual selected candidate. A
  nonempty subject scope supplies a concrete right-operand witness, so native
  admission can discharge the leaf in this fixed three-candidate library. An
  empty scope cannot supply it. This does not prove adequacy for a larger
  candidate library or carry an arbitrary encoded HOL theorem into a different
  native program; that checked-context acceptance bridge remains separate.\<close>

end
