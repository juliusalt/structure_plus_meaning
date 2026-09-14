theory RRA_Generation_Record_Permutations
  imports RRA_Generation_Record_Correctness
begin

locale generation_predecessor_request_equivalence =
  fixes rows qs :: "(local_address option definition_site\<times>finite_generation) list"
  assumes members: "set rows=set qs"
    and multiplicity: "distinct (map snd rows)=distinct (map snd qs)"
begin

lemma projections:
  "set (map fst rows)=set (map fst qs)"
  "fset_of_list (map snd rows)=fset_of_list (map snd qs)"
  by (simp_all only: set_map members fset_inject[symmetric] fset_of_list.rep_eq)

lemma readiness:
  "generation_record_original_ready (E,l,p,c,rows)=generation_record_original_ready (E,l,p,c,qs)"
  by (simp only: generation_record_original_ready_def case_prod_conv members multiplicity)

lemma result_conditions:
  "generation_record_result_condition f (E,l,p,c,rows) result=
    generation_record_result_condition f (E,l,p,c,qs) result"
  by (simp only: generation_record_result_condition_def case_prod_conv projections)

end

lemma generation_record_method_reversed:
  "generation_record_method 1 (E,l,p,c,rows)=generation_record_method 0 (E,l,p,c,rev rows)"
  by (simp add: generation_record_method_def generation_record_mutation_def
    generation_record_variant_def generation_record_base_def split: option.splits)

theorem generation_record_reversed_correct:
  assumes facet: "f<9"
  shows "generation_record_condition f (generation_record_method 1) X"
proof -
  obtain E l p c rows where input: "X=(E,l,p,c,rows)" by (cases X) auto
  interpret reordered: generation_predecessor_request_equivalence rows "rev rows"
    by (unfold_locales) (simp_all add: rev_map[symmetric])
  have same: "generation_record_condition f (generation_record_method 1) (E,l,p,c,rows)=
    generation_record_condition f (generation_record_method 0) (E,l,p,c,rev rows)"
    by (simp only: generation_record_condition_def generation_record_method_reversed
      reordered.readiness reordered.result_conditions)
  show ?thesis by (simp only: input same; rule generation_record_original_correct[OF facet])
qed

text \<open>
  The independent conditions use the complete predecessor request and its
  distinctness boundary. They do not privilege its display order. Reversal
  instantiates the same request-equivalence argument and the existing original
  constructor theorem, including actual cited uses and addresses.
\<close>

end
