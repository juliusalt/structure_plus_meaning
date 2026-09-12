theory Factor_Prefixed_Observation_Contracts
  imports Factor_Prefixed_Observation_Clauses
begin

section \<open>The independent row condition retains every supplied component\<close>

definition prefixed_observation_row :: "bool\<Rightarrow>factor_term\<Rightarrow>factor_term\<Rightarrow>factor_term\<Rightarrow>bool" where
  "prefixed_observation_row first u r v \<longleftrightarrow>
    (\<exists>a d x y. r=Pair_Term (Pair_Term u a) (Pair_Term d (Pair_Term x y)) \<and>
      v=Pair_Term a (Pair_Term d (if first then x else y)) \<and>
      term_formed u \<and> term_formed a \<and> term_formed d \<and> term_formed x \<and> term_formed y)"

locale prefixed_observation_row_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry :: nat and first :: bool
  assumes family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=prefixed_observation_row_schema first"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      term_formed (h 2) \<and> term_formed (h 3) \<and> term_formed (h 4) \<and>
      t=context_relation_argument (h 0)
        (Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (h 3) (h 4))))
        (Pair_Term (h 1) (Pair_Term (h 2) (if first then h 3 else h 4))))"
  by (cases first; subst ordinary_positive_entry_valuation)
    (auto simp: family prefixed_observation_row_schema_def schema_variables_def call)

theorem at_arguments:
  "(entry,context_relation_argument u r v)\<in>positive_meaning P \<longleftrightarrow>
    prefixed_observation_row first u r v"
proof
  assume "(entry,context_relation_argument u r v)\<in>positive_meaning P"
  then show "prefixed_observation_row first u r v"
    by (simp only: valuation factor_term.inject prefixed_observation_row_def) blast
next
  assume "prefixed_observation_row first u r v"
  then obtain a d x y where fields:
    "r=Pair_Term (Pair_Term u a) (Pair_Term d (Pair_Term x y))"
    "v=Pair_Term a (Pair_Term d (if first then x else y))"
    "term_formed u" "term_formed a" "term_formed d" "term_formed x" "term_formed y"
    by (auto simp: prefixed_observation_row_def)
  let ?h="(\<lambda>_::nat. u)(1:=a,2:=d,3:=x,4:=y)"
  show "(entry,context_relation_argument u r v)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h]) (use fields in auto)
qed

end

interpretation prefixed_observation_first:
  prefixed_observation_row_profile prefixed_observation_program 354 True
  by (rule prefixed_observation_row_profile.intro)
    (auto simp: prefixed_observation_clauses_def prefixed_observation_call)

interpretation prefixed_observation_second:
  prefixed_observation_row_profile prefixed_observation_program 355 False
  by (rule prefixed_observation_row_profile.intro)
    (auto simp: prefixed_observation_clauses_def prefixed_observation_call)

interpretation prefixed_observation_first_list: related_list_profile prefixed_observation_program 354 356
  by (rule related_list_profile.intro)
    (auto simp: prefixed_observation_clauses_def prefixed_observation_call)

interpretation prefixed_observation_second_list: related_list_profile prefixed_observation_program 355 357
  by (rule related_list_profile.intro)
    (auto simp: prefixed_observation_clauses_def prefixed_observation_call)

interpretation prefixed_observation_pair:
  paired_context_results_profile prefixed_observation_program 358 356 357
  by (rule paired_context_results_profile.intro)
    (auto simp: prefixed_observation_clauses_def prefixed_observation_call)

section \<open>The paired result contains two complete views of the same sequence\<close>

definition prefixed_observation_result :: "factor_term\<Rightarrow>bool" where
  "prefixed_observation_result t \<longleftrightarrow>
    (\<exists>u rs xs ys. t=paired_context_results_argument u
      (data_list_term rs) (data_list_term xs) (data_list_term ys) \<and>
      term_formed u \<and> list_all2 (prefixed_observation_row True u) rs xs \<and>
      list_all2 (prefixed_observation_row False u) rs ys)"

theorem prefixed_observation_exact:
  "(358,t)\<in>positive_meaning prefixed_observation_program \<longleftrightarrow> prefixed_observation_result t"
  unfolding prefixed_observation_result_def
  by (rule prefixed_observation_pair.related_lists_exact)
    (simp only: prefixed_observation_first_list.exact prefixed_observation_first.at_arguments
      prefixed_observation_second_list.exact prefixed_observation_second.at_arguments)+

corollary prefixed_observation_lists:
  "(358,paired_context_results_argument u (data_list_term rs) (data_list_term xs) (data_list_term ys))
      \<in>positive_meaning prefixed_observation_program \<longleftrightarrow>
    term_formed u \<and> list_all2 (prefixed_observation_row True u) rs xs \<and>
    list_all2 (prefixed_observation_row False u) rs ys"
  by (simp only: prefixed_observation_pair.at_arguments prefixed_observation_first_list.lists
    prefixed_observation_second_list.lists prefixed_observation_first.at_arguments
    prefixed_observation_second.at_arguments; blast)

text \<open>
  Both projections retain each row's complete prefix. In a claim table this
  is the callee; the checked context is the cited definition's owning use.
  The source key, all values, order and repetitions are retained by the
  relation and the two complete traversals. Functional table admission and
  admission of the represented pattern claims remain separate conditions.
\<close>

end
