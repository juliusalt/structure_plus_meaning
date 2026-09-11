theory Factor_Binary_Result_Comparison
  imports Factor_Result_Comparison
begin

section \<open>A whole input has one private result and one compared public result\<close>

definition result_comparison_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "result_comparison_schema compute compare=data_rule (Pattern_Pair data_x data_y)
    {(0,compute,Pattern_Pair data_x data_z),(1,compare,Pattern_Pair data_z data_y)}"

lemma result_comparison_formed [simp]: "schema_formed (result_comparison_schema compute compare)"
  by (auto simp: result_comparison_schema_def schema_formed_def single_valued_def)

lemma result_comparison_dependencies [simp]:
  "schema_dependencies (result_comparison_schema compute compare)={compute,compare}"
  by (auto simp: result_comparison_schema_def schema_dependencies_def rel_ran_image)

locale result_comparison_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry compute compare :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=result_comparison_schema compute compare"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (compute,Pair_Term (h 0) (h 2))\<in>positive_meaning P \<and>
      (compare,Pair_Term (h 2) (h 1))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family result_comparison_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q w. t=Pair_Term p q \<and> (compute,Pair_Term p w)\<in>positive_meaning P \<and>
      (compare,Pair_Term w q)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>p q w. t=Pair_Term p q \<and> (compute,Pair_Term p w)\<in>positive_meaning P \<and>
      (compare,Pair_Term w q)\<in>positive_meaning P" by (simp only: valuation) blast
next
  assume "\<exists>p q w. t=Pair_Term p q \<and> (compute,Pair_Term p w)\<in>positive_meaning P \<and>
      (compare,Pair_Term w q)\<in>positive_meaning P"
  then obtain p q w where parts: "t=Pair_Term p q" "(compute,Pair_Term p w)\<in>positive_meaning P"
    "(compare,Pair_Term w q)\<in>positive_meaning P" by blast
  have terms: "term_formed p" "term_formed q" "term_formed w"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else if i=1 then q else w"])
      (use parts terms in auto)
qed

corollary at_input:
  "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>w. (compute,Pair_Term p w)\<in>positive_meaning P \<and> (compare,Pair_Term w q)\<in>positive_meaning P)"
  by (auto simp only: exact factor_term.inject)

lemma at_computed_result:
  assumes computed: "\<And>w. (compute,Pair_Term p w)\<in>positive_meaning P \<longleftrightarrow> admitted \<and> w=result"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    admitted \<and> (compare,Pair_Term result q)\<in>positive_meaning P"
  by (simp only: at_input computed; auto)

theorem presented_contract:
  assumes computation: "presented_function_witness R D A S E B f
      (\<lambda>p q. (compute,Pair_Term p q)\<in>positive_meaning P)"
    and comparison: "\<And>b q r. S b q \<Longrightarrow> ((compare,Pair_Term q r)\<in>positive_meaning P \<longleftrightarrow> S b r)"
  shows "presented_function_contract R D A S E B f (\<lambda>p r. (entry,Pair_Term p r)\<in>positive_meaning P)"
proof -
  have completed: "presented_function_contract R D A S E B f
      (\<lambda>p r. \<exists>q. (compute,Pair_Term p q)\<in>positive_meaning P \<and>
        (compare,Pair_Term q r)\<in>positive_meaning P)"
    by (rule presented_function_witness.completion_by_comparison[OF computation comparison])
  show ?thesis using completed by (simp only: at_input)
qed


theorem presented_exact:
  assumes contract: "presented_function_contract R D A S E B f
    (\<lambda>p q. (entry,Pair_Term p q)\<in>positive_meaning P)"
  shows "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>a p q. t=Pair_Term p q \<and> R a p \<and> S (f a) q)"
proof -
  interpret implemented: presented_function_contract R D A S E B f
    "\<lambda>p q. (entry,Pair_Term p q)\<in>positive_meaning P" by (rule contract)
  have shape: "\<exists>p q. t=Pair_Term p q" if "(entry,t)\<in>positive_meaning P"
    using that by (simp only: exact) blast
  have binary: "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. R a p \<and> S (f a) q)" for p q
    by (simp only: implemented.exact presented_relation_def; blast)
  show ?thesis using shape binary by blast
qed

end

text \<open>
  The complete input remains one term in both the public call and its private
  computation premise. The result comparator has a separate premise socket.
  The existing witness-completion theorem therefore applies directly to an
  arbitrary complete input class, including a record admitted as a whole.
\<close>

end
