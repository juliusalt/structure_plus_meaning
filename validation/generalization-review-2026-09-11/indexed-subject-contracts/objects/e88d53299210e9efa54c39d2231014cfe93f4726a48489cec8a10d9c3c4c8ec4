theory Factor_Related_Sets
  imports Factor_Compared_Members Factor_Finite_Set_Readings
begin

section \<open>Both complete traversals retain the same comparison orientation\<close>

definition related_set_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_set_schema forward backward=data_rule (Pattern_Pair data_x data_y)
    {(0,forward,Pattern_Pair data_y data_x),(1,backward,Pattern_Pair data_x data_y)}"

lemma related_set_schema_formed [simp]: "schema_formed (related_set_schema forward backward)"
  by (auto simp: related_set_schema_def schema_formed_def single_valued_def)

lemma related_set_schema_dependencies [simp]:
  "schema_dependencies (related_set_schema forward backward)={forward,backward}"
  by (auto simp: related_set_schema_def schema_dependencies_def rel_ran_image)

locale related_set_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system"
    and member compare forward backward left right entry :: nat
  assumes members: "compared_member_profile P member compare forward backward"
    and left_traversal: "context_list_profile P forward left"
    and right_traversal: "context_list_profile P backward right"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=related_set_schema left right"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

interpretation members: compared_member_profile P member compare forward backward by (rule members)
interpretation left: context_list_profile P forward left by (rule left_traversal)
interpretation right: context_list_profile P backward right by (rule right_traversal)

abbreviation related where
  "related x y \<equiv> (compare,Pair_Term x y)\<in>positive_meaning P"

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      (left,Pair_Term (h 1) (h 0))\<in>positive_meaning P \<and>
      (right,Pair_Term (h 0) (h 1))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family related_set_schema_def schema_variables_def call)

lemma equation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> (left,Pair_Term q p)\<in>positive_meaning P \<and>
      (right,Pair_Term p q)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>p q. t=Pair_Term p q \<and> (left,Pair_Term q p)\<in>positive_meaning P \<and>
      (right,Pair_Term p q)\<in>positive_meaning P" by (simp only: valuation) blast
next
  assume "\<exists>p q. t=Pair_Term p q \<and> (left,Pair_Term q p)\<in>positive_meaning P \<and>
      (right,Pair_Term p q)\<in>positive_meaning P"
  then obtain p q where parts: "t=Pair_Term p q"
    "(left,Pair_Term q p)\<in>positive_meaning P" "(right,Pair_Term p q)\<in>positive_meaning P" by blast
  have formed: "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by auto
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else q"])
      (use parts formed in auto)
qed

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
      data_elements xs \<and> data_elements ys \<and> rel_set related (set xs) (set ys))"
proof -
  have expanded: "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
        (left,Pair_Term (data_list_term ys) (data_list_term xs))\<in>positive_meaning P \<and>
        (right,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P)"
  proof
    assume "(entry,t)\<in>positive_meaning P"
    then obtain p q where parts: "t=Pair_Term p q" "(left,Pair_Term q p)\<in>positive_meaning P"
      "(right,Pair_Term p q)\<in>positive_meaning P" by (simp only: equation) blast
    obtain xs where first: "p=data_list_term xs" using parts(2)
      by (auto simp only: left.exact factor_term.inject)
    obtain ys where second: "q=data_list_term ys" using parts(3)
      by (auto simp only: right.exact factor_term.inject)
    show "\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
        (left,Pair_Term (data_list_term ys) (data_list_term xs))\<in>positive_meaning P \<and>
        (right,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P"
      using parts first second by blast
  next
    assume "\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
        (left,Pair_Term (data_list_term ys) (data_list_term xs))\<in>positive_meaning P \<and>
        (right,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P"
    then show "(entry,t)\<in>positive_meaning P" by (simp only: equation) blast
  qed
  have coverage: "(term_formed (data_list_term xs) \<and> term_formed (data_list_term ys) \<and>
      (\<forall>x\<in>set xs. data_elements ys \<and> (\<exists>y\<in>set ys. related x y)) \<and>
      (\<forall>y\<in>set ys. data_elements xs \<and> (\<exists>x\<in>set xs. related x y))) \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> rel_set related (set xs) (set ys)" for xs ys
    by (cases xs; cases ys) (auto simp: rel_set_def data_list_term_formed octets_formed_def)
  have at_lists: "((left,Pair_Term (data_list_term ys) (data_list_term xs))\<in>positive_meaning P \<and>
      (right,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P) \<longleftrightarrow>
      data_elements xs \<and> data_elements ys \<and> rel_set related (set xs) (set ys)" for xs ys
    using coverage[of xs ys]
    by (simp only: left.lists right.lists members.forward_at members.backward_at) blast
  show ?thesis by (simp only: expanded at_lists)
qed

corollary lists:
  "(entry,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> rel_set related (set xs) (set ys)"
  by (auto simp only: exact factor_term.inject data_list_term_injective)

section \<open>One element contract covers every finite-set output presentation\<close>

theorem comparison_output:
  assumes elements: "presentation_class R D A"
    and source: "data_list_fset_presents R S p"
    and data: "\<And>a t. R a t \<Longrightarrow> term_formed t \<and> self_contained_term t"
    and compare: "\<And>a x y. R a x \<Longrightarrow> related x y \<longleftrightarrow> R a y"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> data_list_fset_presents R S q"
  using data_list_fset_comparison_output[where R=R and S=S and p=p and q=q and C=related, OF elements source] data compare
  by (auto simp only: exact factor_term.inject)

theorem comparison_presentations:
  assumes elements: "presentation_class R D A"
    and first: "data_list_fset_presents R S p" and second: "data_list_fset_presents R T q"
    and data: "\<And>a t. R a t \<Longrightarrow> term_formed t \<and> self_contained_term t"
    and compare: "\<And>a x y. R a x \<Longrightarrow> related x y \<longleftrightarrow> R a y"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> S=T"
  using comparison_output[where R=R and S=S and p=p and q=q, OF elements first] data compare second
    presentation_class.recovery[OF data_list_fset_presentation_class[OF elements]] by blast


theorem presented_identity_contract:
  assumes element: "presented_relation_contract R D A R D A (=) related"
    and data: "\<And>a t. R a t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  shows "presented_relation_contract (data_list_fset_presents R) (\<lambda>S. \<forall>a\<in>fset S. D a)
    (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. A x) \<and> p=data_list_term ps)
    (data_list_fset_presents R) (\<lambda>S. \<forall>a\<in>fset S. D a)
    (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. A x) \<and> p=data_list_term ps)
    (=) (\<lambda>p q. (entry,Pair_Term p q)\<in>positive_meaning P)"
proof -
  interpret element: presented_relation_contract R D A R D A "(=)" related by (rule element)
  have compared: "related x y \<longleftrightarrow> R a y" if "R a x" for a x y
    using element.at_source[OF that] by auto
  have completed_output: "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
      data_list_fset_presents R S q" if "data_list_fset_presents R S p" for S p q
    by (rule comparison_output[where R=R and S=S and p=p and q=q, OF element.left.presentation_class_axioms that])
      (use data compared in blast)+
  have meaning: "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
      presented_relation (data_list_fset_presents R) (data_list_fset_presents R) (=) p q" for p q
  proof
    assume holds: "(entry,Pair_Term p q)\<in>positive_meaning P"
    obtain ps qs where fields: "p=data_list_term ps" "q=data_list_term qs"
      "rel_set related (set ps) (set qs)" using holds by (auto simp only: exact factor_term.inject)
    have covered: "\<forall>x\<in>set ps. \<exists>a. R a x"
      using fields(3) element.exact by (auto simp only: rel_set_def presented_relation_def; blast)
    obtain xs where rows: "list_all2 R xs ps" using covered by (simp only: list_all2_exists_left) blast
    have first: "data_list_fset_presents R (fset_of_list xs) p"
      using rows fields(1) by (auto simp only: data_list_fset_presents_def data_sequence_presents_def)
    have second: "data_list_fset_presents R (fset_of_list xs) q" using holds completed_output[OF first] by blast
    show "presented_relation (data_list_fset_presents R) (data_list_fset_presents R) (=) p q"
      using first second by (auto simp only: presented_relation_def)
  next
    assume "presented_relation (data_list_fset_presents R) (data_list_fset_presents R) (=) p q"
    then show "(entry,Pair_Term p q)\<in>positive_meaning P"
      using completed_output by (auto simp only: presented_relation_def)
  qed
  show ?thesis using data_list_fset_presentation_class[OF element.left.presentation_class_axioms] meaning
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

end

text \<open>
  Each traversal calls the same already established context-list mechanism.
  Every member has a comparison witness in the other complete list. The
  witnesses need not form a bijection between displayed occurrences: several
  displays of one subject member may share a witness. An empty list compares
  only with an empty list. Nonempty coverage checks both complete data lists
  through the actual membership calls, so no redundant admission premise is
  needed at the final clause.

  The all-term law exports the actual element callee under two-sided set
  coverage. The presentation theorem then consumes that callee's complete
  local source contract. It does not turn an external predicate into a
  native definition, or restrict the callee's broader unrelated domain.
\<close>

end
