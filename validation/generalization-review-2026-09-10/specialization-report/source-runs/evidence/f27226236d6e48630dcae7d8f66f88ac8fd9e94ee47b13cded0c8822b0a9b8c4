theory Factor_Context_Filters
  imports Factor_Recursive_Groups Factor_Bag_Difference
begin

section \<open>Filtering follows two explicit complementary element judgments\<close>

definition context_filter_nil_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "context_filter_nil_schema context=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Payload []) (Pattern_Payload [])))
    {(0,context,data_x)}"

definition context_filter_keep_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "context_filter_keep_schema keep recursive=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_y data_w)))
    {(0,keep,Pattern_Pair data_x data_y),
     (1,recursive,Pattern_Pair data_x (Pattern_Pair data_z data_w))}"

definition context_filter_drop_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "context_filter_drop_schema omission_site recursive=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w))
    {(0,omission_site,Pattern_Pair data_x data_y),
     (1,recursive,Pattern_Pair data_x (Pattern_Pair data_z data_w))}"

definition context_filter_clauses :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat\<times>(nat,nat,nat) factor_schema) set" where
  "context_filter_clauses context keep omission_site recursive=
    {(0,context_filter_nil_schema context),(1,context_filter_keep_schema keep recursive),
     (2,context_filter_drop_schema omission_site recursive)}"

locale context_filter_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system"
    and context_site keep_site drop_site filter_site :: nat
    and admitted :: "factor_term \<Rightarrow> bool"
    and element selected :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool"
  assumes formed: "schema_system_formed P"
    and family: "\<And>c S. ((filter_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>context_filter_clauses context_site keep_site drop_site filter_site"
    and call: "\<And>t. schema_call_formed P filter_site t \<longleftrightarrow> term_formed t"
    and context_exact: "\<And>p. (context_site,p)\<in>positive_meaning P \<longleftrightarrow> admitted p"
    and keep_exact: "\<And>t. (keep_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> admitted p \<and> element p x \<and> selected p x)"
    and drop_exact: "\<And>t. (drop_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> admitted p \<and> element p x \<and> \<not>selected p x)"
    and context_formed: "\<And>p. admitted p \<Longrightarrow> term_formed p \<and> self_contained_term p"
    and element_formed: "\<And>p x. admitted p \<Longrightarrow> element p x \<Longrightarrow>
      term_formed x \<and> self_contained_term x"
begin

lemma rule:
  assumes clause: "(c,S)\<in>context_filter_clauses context_site keep_site drop_site filter_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning P"
  shows "(filter_site,evaluate_pattern h (schema_conclusion S))\<in>positive_meaning P"
proof -
  have row: "((filter_site,c),S)\<in>system_clauses P" using clause by (simp only: family)
  have sf: "schema_formed S" using row formed unfolding schema_system_formed_def by blast
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: context_filter_clauses_def context_filter_nil_schema_def
      context_filter_keep_schema_def context_filter_drop_schema_def)
  have tf: "term_formed (evaluate_pattern h (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P filter_site (evaluate_pattern h (schema_conclusion S))"
    using tf by (simp only: call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF row ordinary assignment head support])
qed

theorem sound:
  assumes holds: "(filter_site,t)\<in>positive_meaning P"
  shows "\<exists>p xs. t=Pair_Term p (Pair_Term (data_list_term xs)
    (data_list_term (filter (selected p) xs))) \<and> admitted p \<and> (\<forall>x\<in>set xs. element p x)"
proof -
  let ?Q="\<lambda>t. \<exists>p xs. t=Pair_Term p (Pair_Term (data_list_term xs)
    (data_list_term (filter (selected p) xs))) \<and> admitted p \<and> (\<forall>x\<in>set xs. element p x)"
  have invariant: "filter_site=filter_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=filter_site \<longrightarrow> ?Q t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and head: "schema_call_formed P d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning P \<and>
        (e=filter_site \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=filter_site \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=filter_site"
      then consider (nil) "S=context_filter_nil_schema context_site"
        | (keep) "S=context_filter_keep_schema keep_site filter_site"
        | (drop) "S=context_filter_drop_schema drop_site filter_site"
        using clause by (auto simp: family context_filter_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        have valid: "admitted (h 0)"
          using support by (auto simp: nil context_filter_nil_schema_def context_exact)
        show ?thesis by (intro exI[of _ "h 0"] exI[of _ "[]"])
          (use valid in \<open>simp add: nil context_filter_nil_schema_def\<close>)
      next
        case keep
        have first: "element (h 0) (h 1)" "selected (h 0) (h 1)"
          using support by (auto simp: keep context_filter_keep_schema_def keep_exact)
        obtain xs where tail: "h 2=data_list_term xs"
          "h 3=data_list_term (filter (selected (h 0)) xs)"
          "admitted (h 0)" "\<forall>x\<in>set xs. element (h 0) x"
          using support[rule_format, of 1 filter_site "Pattern_Pair data_x (Pattern_Pair data_z data_w)"]
          by (auto simp: keep context_filter_keep_schema_def)
        show ?thesis by (intro exI[of _ "h 0"] exI[of _ "h 1#xs"])
          (use first tail in \<open>simp add: keep context_filter_keep_schema_def\<close>)
      next
        case drop
        have first: "element (h 0) (h 1)" "\<not>selected (h 0) (h 1)"
          using support by (auto simp: drop context_filter_drop_schema_def drop_exact)
        obtain xs where tail: "h 2=data_list_term xs"
          "h 3=data_list_term (filter (selected (h 0)) xs)"
          "admitted (h 0)" "\<forall>x\<in>set xs. element (h 0) x"
          using support[rule_format, of 1 filter_site "Pattern_Pair data_x (Pattern_Pair data_z data_w)"]
          by (auto simp: drop context_filter_drop_schema_def)
        show ?thesis by (intro exI[of _ "h 0"] exI[of _ "h 1#xs"])
          (use first tail in \<open>simp add: drop context_filter_drop_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem complete:
  assumes "admitted p" "\<forall>x\<in>set xs. element p x"
  shows "(filter_site,Pair_Term p (Pair_Term (data_list_term xs)
    (data_list_term (filter (selected p) xs))))\<in>positive_meaning P"
  using assms
proof (induction xs)
  case Nil
  have ctx: "(context_site,p)\<in>positive_meaning P" using Nil.prems by (simp only: context_exact)
  have result: "(filter_site,evaluate_pattern (\<lambda>_. p)
      (schema_conclusion (context_filter_nil_schema context_site)))\<in>positive_meaning P"
    by (rule rule[where c=0])
      (use ctx context_formed[OF Nil.prems(1)] in
        \<open>auto simp: context_filter_clauses_def context_filter_nil_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: context_filter_nil_schema_def)
next
  case (Cons x xs)
  have ctx: "admitted p" and first: "element p x" and rest: "\<forall>y\<in>set xs. element p y"
    using Cons.prems by auto
  have tail: "(filter_site,Pair_Term p (Pair_Term (data_list_term xs)
      (data_list_term (filter (selected p) xs))))\<in>positive_meaning P"
    by (rule Cons.IH[OF ctx rest])
  have data: "term_formed p" "term_formed x" "data_elements xs"
    using context_formed[OF ctx] element_formed[OF ctx first] element_formed[OF ctx] rest by blast+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then x else if i=2 then data_list_term xs
    else data_list_term (filter (selected p) xs)"
  show ?case
  proof (cases "selected p x")
    case True
    have included: "(keep_site,Pair_Term p x)\<in>positive_meaning P"
      using ctx first True by (auto simp: keep_exact)
    have result: "(filter_site,evaluate_pattern ?h
        (schema_conclusion (context_filter_keep_schema keep_site filter_site)))\<in>positive_meaning P"
      by (rule rule[where c=1])
        (use data included tail in \<open>auto simp: context_filter_clauses_def context_filter_keep_schema_def
          schema_variables_def data_list_term_formed\<close>)
    show ?thesis using result True by (simp add: context_filter_keep_schema_def)
  next
    case False
    have omitted: "(drop_site,Pair_Term p x)\<in>positive_meaning P"
      using ctx first False by (auto simp: drop_exact)
    have result: "(filter_site,evaluate_pattern ?h
        (schema_conclusion (context_filter_drop_schema drop_site filter_site)))\<in>positive_meaning P"
      by (rule rule[where c=2])
        (use data omitted tail in \<open>auto simp: context_filter_clauses_def context_filter_drop_schema_def
          schema_variables_def data_list_term_formed\<close>)
    show ?thesis using result False by (simp add: context_filter_drop_schema_def)
  qed
qed

theorem exact:
  "(filter_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p xs. t=Pair_Term p (Pair_Term (data_list_term xs)
      (data_list_term (filter (selected p) xs))) \<and> admitted p \<and> (\<forall>x\<in>set xs. element p x))"
  using sound complete by blast

theorem at_input:
  "(filter_site,Pair_Term p (Pair_Term (data_list_term xs) q))\<in>positive_meaning P \<longleftrightarrow>
    admitted p \<and> (\<forall>x\<in>set xs. element p x) \<and> q=data_list_term (filter (selected p) xs)"
  by (auto simp: exact data_list_term_injective)

theorem encoded_input:
  assumes admitted_context: "admitted p"
    and elements: "\<And>a. a\<in>set xs \<Longrightarrow> element p (f a)"
    and selection: "\<And>a. a\<in>set xs \<Longrightarrow> selected p (f a) \<longleftrightarrow> keep a"
  shows "(filter_site,Pair_Term p (Pair_Term (data_list_term (map f xs)) q))\<in>positive_meaning P \<longleftrightarrow>
    q=data_list_term (map f (filter keep xs))"
proof -
  have same: "filter (selected p) (map f xs)=map f (filter keep xs)"
    using selection by (induction xs) auto
  show ?thesis using admitted_context elements by (simp add: at_input same)
qed

end

section \<open>Independent relation contracts instantiate the same finite filter\<close>

theorem presented_context_filter_profile:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
    and source_formed: "\<And>a p. R a p \<Longrightarrow> term_formed p \<and> self_contained_term p"
    and element_formed: "\<And>b x. S b x \<Longrightarrow> term_formed x \<and> self_contained_term x"
    and system: "schema_system_formed P"
    and family: "\<And>c T. ((filter_site,c),T)\<in>system_clauses P \<longleftrightarrow>
      (c,T)\<in>context_filter_clauses context_site keep_site drop_site filter_site"
    and call: "\<And>t. schema_call_formed P filter_site t \<longleftrightarrow> term_formed t"
    and admitted_context: "\<And>p. (context_site,p)\<in>positive_meaning P \<longleftrightarrow> A p"
    and keep: "\<And>t. (keep_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> presented_relation R S L p x)"
    and drop: "\<And>t. (drop_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> presented_relation R S (\<lambda>a b. \<not>L a b) p x)"
  shows "context_filter_profile P context_site keep_site drop_site filter_site
    A (\<lambda>p x. B x) (presented_relation R S L)"
proof (rule context_filter_profile.intro[OF system family call admitted_context])
  have boundary: "presented_relation R S L p x \<Longrightarrow> A p \<and> B x" for p x
    using presentation_class.presentation_boundary[OF left]
      presentation_class.presentation_boundary[OF right]
    by (auto simp: presented_relation_def)
  show "(keep_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> A p \<and> B x \<and> presented_relation R S L p x)" for t
    using boundary by (auto simp only: keep)
  show "(drop_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> A p \<and> B x \<and> \<not>presented_relation R S L p x)" for t
    by (simp only: drop presented_relation_complement[OF left right])
  show "A p \<Longrightarrow> term_formed p \<and> self_contained_term p" for p
    using presentation_class.admitted[OF left] source_formed by blast
  show "A p \<Longrightarrow> B x \<Longrightarrow> term_formed x \<and> self_contained_term x" for p x
    using presentation_class.admitted[OF right] element_formed by blast
qed

text \<open>
  The three finite clauses preserve the order and every retained occurrence
  of an actual input list. Each omitted occurrence requires the explicit
  complementary judgment at that same context. The mathematical contract
  proves ordinary list filtering; it introduces no negative native premise.

  Context and element admission, the two complementary meanings, and the
  recursive clause family are proved for the actual combined program. They
  are local proof obligations, not semantic callbacks stored in that program.
  Uses over unordered collections or bags additionally compose with their
  existing exact presentation comparisons.
\<close>

end
