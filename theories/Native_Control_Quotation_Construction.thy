theory Native_Control_Quotation_Construction
  imports Native_Control_Artifact_Comparison
begin

lemma finite_data_list_closed:
  "self_contained_term (decode_finite_term (finite_data_list xs)) \<longleftrightarrow>
    list_all (\<lambda>x. self_contained_term (decode_finite_term x)) xs"
  by (induction xs) simp_all

lemma isabelle_position_closed [simp]:
  "self_contained_term (decode_finite_term (isabelle_position_data n))"
  by (simp add: isabelle_position_data_def finite_binary_natural_value_def finite_storage_path_value_def)

lemma isabelle_sort_closed [simp]:
  "self_contained_term (decode_finite_term (isabelle_sort_data xs))"
  by (simp add: isabelle_sort_data_def finite_sequence_presentation_def finite_data_list_closed data_list_term_self_contained list_all_iff comp_def)

lemma isabelle_type_closed [simp]:
  "self_contained_term (decode_finite_term (isabelle_type_data T))"
  by (induction T) (auto simp: finite_data_list_closed data_list_term_self_contained list_all_iff comp_def)

lemma isabelle_term_closed [simp]:
  "self_contained_term (decode_finite_term (isabelle_term_data t))"
  by (induction t) simp_all

lemma isabelle_entity_closed [simp]:
  "self_contained_term (decode_finite_term (isabelle_entity_data e))"
  by (cases e) simp_all

lemma syntax_judgment_data_closed [simp]:
  "self_contained_term (decode_finite_term (syntax_judgment_data s))"
  by (simp add: syntax_judgment_data_def isabelle_context_data_def finite_pair_presentation_def
    isabelle_names_data_def isabelle_name_data_def finite_sequence_presentation_def
    finite_data_list_closed data_list_term_self_contained list_all_iff comp_def)

lemma complete_quote_refuses_two_roots:
  assumes first: "a\<in>rra_carrier (object_structure R) -
      (participation_occurrences (object_structure R) \<union> reached_occurrences (object_structure R))"
    and second: "b\<in>rra_carrier (object_structure R) -
      (participation_occurrences (object_structure R) \<union> reached_occurrences (object_structure R))"
    and different: "a\<noteq>b"
  shows "\<not>complete_data_quoted_at R r t"
proof
  assume quoted: "complete_data_quoted_at R r t"
  have roots: "rra_carrier (object_structure R) -
      (participation_occurrences (object_structure R) \<union> reached_occurrences (object_structure R))={r}"
    by (rule complete_data_quotation_root_boundary[OF quoted])
  have a: "a=r" using first by (simp only: roots singleton_iff)
  have b: "b=r" using second by (simp only: roots singleton_iff)
  show False using different by (simp only: a b not_True_eq_False)
qed

lemma syntax_union_role_projections:
  "participation_occurrences (object_structure (syntax_union R S))=
    Cons 2 ` participation_occurrences (object_structure R) \<union>
    Cons 3 ` participation_occurrences (object_structure S)"
  "reached_occurrences (object_structure (syntax_union R S))=
    Cons 2 ` reached_occurrences (object_structure R) \<union>
    Cons 3 ` reached_occurrences (object_structure S)"
  by (auto simp: syntax_union_def participation_occurrences_def reached_occurrences_def push_structure_def; force)+

lemma detached_data_has_two_roots:
  assumes closed: "self_contained_term t"
  shows "[2]\<in>rra_carrier (object_structure (syntax_union (term_syntax t) (payload_syntax v))) -
      (participation_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))) \<union>
       reached_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))))"
    "[3]\<in>rra_carrier (object_structure (syntax_union (term_syntax t) (payload_syntax v))) -
      (participation_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))) \<union>
       reached_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))))"
proof -
  have unused: "[]\<notin>participation_occurrences (object_structure (term_syntax t)) \<union>
      reached_occurrences (object_structure (term_syntax t))"
    using self_contained_syntax_unreferenced[OF closed] by blast
  have left_carrier: "[]\<in>rra_carrier (object_structure (term_syntax t))" by simp
  have carrier: "rra_carrier (object_structure (syntax_union (term_syntax t) (payload_syntax v)))=
      Cons 2 ` rra_carrier (object_structure (term_syntax t)) \<union> {[3]}"
    by (simp add: syntax_union_def)
  show "[2]\<in>rra_carrier (object_structure (syntax_union (term_syntax t) (payload_syntax v))) -
      (participation_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))) \<union>
       reached_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))))"
    "[3]\<in>rra_carrier (object_structure (syntax_union (term_syntax t) (payload_syntax v))) -
      (participation_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))) \<union>
       reached_occurrences (object_structure (syntax_union (term_syntax t) (payload_syntax v))))"
    using unused left_carrier
    by (simp only: carrier syntax_union_role_projections;
      auto simp: participation_occurrences_def reached_occurrences_def payload_syntax_def)+
qed

lemma detached_data_has_no_complete_body:
  assumes "self_contained_term t"
  shows "\<not>complete_data_quoted_at (syntax_union (term_syntax t) (payload_syntax v)) r x"
  by (rule complete_quote_refuses_two_roots[OF detached_data_has_two_roots[OF assms]]) simp

lemma canonical_judgment_quotation:
  "complete_data_quoted_at (term_syntax (decode_finite_term (syntax_judgment_data s))) []
    (decode_finite_term (syntax_judgment_data s))"
  by (rule complete_data_quotation_total)
    (simp_all add: finite_term_formed_correct[symmetric])

lemma prefixed_judgment_quotation:
  "complete_data_quoted_at (push_object (Cons 7)
      (term_syntax (decode_finite_term (syntax_judgment_data s)))) [7]
    (decode_finite_term (syntax_judgment_data s))"
proof (rule complete_data_quotation_every_addressing[where f="Cons 7", simplified])
  show "term_formed (decode_finite_term (syntax_judgment_data s))"
    by (simp only: finite_term_formed_correct[symmetric] syntax_judgment_data_formed)
  show "self_contained_term (decode_finite_term (syntax_judgment_data s))" by simp
  have source: "exact_formed (term_syntax (decode_finite_term (syntax_judgment_data s)))"
    by (rule term_syntax_formed) (simp add: finite_term_formed_correct[symmetric])
  show "finite_addressing (rra_carrier (object_structure
      (term_syntax (decode_finite_term (syntax_judgment_data s))))) (Cons 7)"
    using source by (auto simp: finite_addressing_def exact_formed_def octets_formed_def)
qed

lemma extra_judgment_quotation:
  "complete_data_quoted_at (term_syntax (Pair_Term (decode_finite_term (syntax_judgment_data s))
      (Payload_Term [9]))) []
    (Pair_Term (decode_finite_term (syntax_judgment_data s)) (Payload_Term [9]))"
  by (rule complete_data_quotation_total)
    (simp_all add: finite_term_formed_correct[symmetric] octets_formed_def)

lemma term_not_its_extra_pair: "t\<noteq>Pair_Term t (Payload_Term [9])"
proof
  assume same: "t=Pair_Term t (Payload_Term [9])"
  have sizes: "size t=size (Pair_Term t (Payload_Term [9]))"
    by (rule arg_cong[OF same, where f="size :: factor_term \<Rightarrow> nat"])
  then show False by simp
qed

lemma canonical_judgment_differs_extra:
  "finite_term_syntax (Finite_Pair (syntax_judgment_data s) (Finite_Payload [9]))\<noteq>
    finite_term_syntax (syntax_judgment_data s)"
proof
  assume same: "finite_term_syntax (Finite_Pair (syntax_judgment_data s) (Finite_Payload [9]))=
    finite_term_syntax (syntax_judgment_data s)"
  have objects: "term_syntax (Pair_Term (decode_finite_term (syntax_judgment_data s)) (Payload_Term [9]))=
    term_syntax (decode_finite_term (syntax_judgment_data s))"
    using arg_cong[OF same, of decode_finite_object] by simp
  have different: "decode_finite_term (syntax_judgment_data s)\<noteq>
    Pair_Term (decode_finite_term (syntax_judgment_data s)) (Payload_Term [9])"
    by (rule term_not_its_extra_pair)
  have extra_at_same: "complete_data_quoted_at
      (term_syntax (decode_finite_term (syntax_judgment_data s))) []
      (Pair_Term (decode_finite_term (syntax_judgment_data s)) (Payload_Term [9]))"
    using extra_judgment_quotation[of s] by (simp only: objects)
  have same_body: "decode_finite_term (syntax_judgment_data s)=
      Pair_Term (decode_finite_term (syntax_judgment_data s)) (Payload_Term [9])"
    by (rule complete_data_quotation_unique[OF canonical_judgment_quotation[of s] extra_at_same])
  show False using same_body different by contradiction
qed

lemma judgment_artifact_constructed_checks:
  "map judgment_artifact_check (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,syntax_judgment_check s,False,False]"
proof -
  let ?t="decode_finite_term (syntax_judgment_data s)"
  have extra: "\<not>complete_data_quoted_at (term_syntax (Pair_Term ?t (Payload_Term [9]))) [] ?t"
  proof
    assume q: "complete_data_quoted_at (term_syntax (Pair_Term ?t (Payload_Term [9]))) [] ?t"
    have same: "Pair_Term ?t (Payload_Term [9])=?t"
      by (rule complete_data_quotation_unique[OF extra_judgment_quotation[of s] q])
    show False using term_not_its_extra_pair[of ?t] same[symmetric] by contradiction
  qed
  show ?thesis
    by (simp only: judgment_artifact_cases_for_def Let_def list.map judgment_artifact_check_exact
      judgment_artifact_condition_def case_prod_conv finite_term_syntax_exact
      finite_artifact_readdress_exact decode_finite_syntax_union decode_finite_payload_syntax
      decode_finite_term.simps canonical_judgment_quotation prefixed_judgment_quotation
      detached_data_has_no_complete_body[OF syntax_judgment_data_closed] extra
      syntax_judgment_check_exact simp_thms)
qed

lemma judgment_artifact_constructed_results:
  "map (judgment_artifact_result Direct_Body_Entry) (judgment_artifact_cases_for s)=[False,False,False,False]"
  "map (judgment_artifact_result Claimed_Body_Only) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,syntax_judgment_check s,syntax_judgment_check s,syntax_judgment_check s]"
  "map (judgment_artifact_result Canonical_Artifact_Only) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,False,False,False]"
  "map (judgment_artifact_result Complete_Artifact_Body) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,syntax_judgment_check s,False,False]"
proof -
  show "map (judgment_artifact_result Direct_Body_Entry) (judgment_artifact_cases_for s)=[False,False,False,False]"
    by (simp add: judgment_artifact_cases_for_def Let_def)
  show "map (judgment_artifact_result Claimed_Body_Only) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,syntax_judgment_check s,syntax_judgment_check s,syntax_judgment_check s]"
    by (simp add: judgment_artifact_cases_for_def Let_def)
  show "map (judgment_artifact_result Canonical_Artifact_Only) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,False,False,False]"
    using canonical_judgment_differs_extra[of s]
    by (simp add: judgment_artifact_cases_for_def Let_def)
  have same: "judgment_artifact_result Complete_Artifact_Body=judgment_artifact_check"
    by (rule ext) simp
  show "map (judgment_artifact_result Complete_Artifact_Body) (judgment_artifact_cases_for s)=
    [syntax_judgment_check s,syntax_judgment_check s,False,False]"
    by (simp only: same judgment_artifact_constructed_checks)
qed

lemma judgment_artifact_constructed_observation:
  "judgment_artifact_observation a (judgment_artifact_cases_for s)=
    (syntax_judgment_check s \<longrightarrow> a=Complete_Artifact_Body)"
proof -
  have mapped: "list_all (\<lambda>q. judgment_artifact_result a q=judgment_artifact_check q)
      (judgment_artifact_cases_for s) \<longleftrightarrow>
    map (judgment_artifact_result a) (judgment_artifact_cases_for s)=
      map judgment_artifact_check (judgment_artifact_cases_for s)"
    by (simp add: list_all_iff)
  show ?thesis
    unfolding judgment_artifact_observation_def mapped
    by (cases a; simp only: judgment_artifact_constructed_results judgment_artifact_constructed_checks;
      cases "syntax_judgment_check s"; simp)
qed

lemma judgment_artifact_reused_observation:
  "judgment_artifact_observation a judgment_artifact_cases=
    list_all (\<lambda>s. syntax_judgment_check s \<longrightarrow> a=Complete_Artifact_Body) syntax_judgment_cases"
  by (simp add: judgment_artifact_cases_def judgment_artifact_observation_def list_all_iff
    judgment_artifact_constructed_observation[unfolded judgment_artifact_observation_def list_all_iff])

text \<open>These equations derive complete original observations from the actual
  constructor inputs and the quotation, uniqueness and complete-carrier
  theorems. The detached material has two structural roots and cannot supply
  any complete body. No observation table or preferred artifact equality
  replaces the original relation. Arbitrary submitted artifacts still require
  the original complete reader; this refinement covers this constructed scope.\<close>

end
