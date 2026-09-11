theory Factor_Keyed_Comparison
  imports Factor_Presentation_Classes Factor_List_Profiles
begin

section \<open>A retained key and a compared value have separate native premises\<close>

definition keyed_comparison_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "keyed_comparison_schema key value_site=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_x data_z))
    {(0,key,data_x),(1,value_site,Pattern_Pair data_y data_z)}"

lemma keyed_comparison_schema_formed [simp]: "schema_formed (keyed_comparison_schema key value_site)"
  by (auto simp: keyed_comparison_schema_def schema_formed_def single_valued_def)

lemma keyed_comparison_schema_dependencies [simp]:
  "schema_dependencies (keyed_comparison_schema key value_site)={key,value_site}"
  by (auto simp: keyed_comparison_schema_def schema_dependencies_def rel_ran_image)

locale keyed_comparison_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and key value_site entry :: nat
  assumes formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=keyed_comparison_schema key value_site"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 0) (h 2)) \<and>
      (key,h 0)\<in>positive_meaning P \<and> (value_site,Pair_Term (h 1) (h 2))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family keyed_comparison_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>k p q. t=Pair_Term (Pair_Term k p) (Pair_Term k q) \<and>
      (key,k)\<in>positive_meaning P \<and> (value_site,Pair_Term p q)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>k p q. t=Pair_Term (Pair_Term k p) (Pair_Term k q) \<and>
      (key,k)\<in>positive_meaning P \<and> (value_site,Pair_Term p q)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>k p q. t=Pair_Term (Pair_Term k p) (Pair_Term k q) \<and>
      (key,k)\<in>positive_meaning P \<and> (value_site,Pair_Term p q)\<in>positive_meaning P"
  then obtain k p q where parts: "t=Pair_Term (Pair_Term k p) (Pair_Term k q)"
    "(key,k)\<in>positive_meaning P" "(value_site,Pair_Term p q)\<in>positive_meaning P" by blast
  have terms: "term_formed k" "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then k else if i=1 then p else q"])
      (use parts terms in auto)
qed

corollary at_key:
  "(entry,Pair_Term (Pair_Term k p) q)\<in>positive_meaning P \<longleftrightarrow>
    (key,k)\<in>positive_meaning P \<and>
    (\<exists>r. q=Pair_Term k r \<and> (value_site,Pair_Term p r)\<in>positive_meaning P)"
  by (auto simp only: exact factor_term.inject)

theorem at_presentation:
  assumes source: "factor_pair_presents (\<lambda>a t. D a \<and> t=f a) S (k,v) p"
    and keys: "\<And>a. D a \<Longrightarrow> (key,f a)\<in>positive_meaning P"
    and value_contract: "\<And>a x y. S a x \<Longrightarrow>
      (value_site,Pair_Term x y)\<in>positive_meaning P \<longleftrightarrow> S a y"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    factor_pair_presents (\<lambda>a t. D a \<and> t=f a) S (k,v) q"
proof -
  obtain r where parts: "p=Pair_Term (f k) r" "D k" "S v r"
    using source by (auto simp only: factor_pair_presents_def fst_conv snd_conv)
  show ?thesis using keys[OF parts(2)] value_contract[OF parts(3)] parts(2)
    by (auto simp only: parts(1) at_key factor_pair_presents_def fst_conv snd_conv)
qed

end

text \<open>
  The repeated key variable retains the exact same key term. Its own callee
  admits that key even when the compared values are empty. The value callee
  compares the two complete value presentations. For a key class with one
  encoding per subject, its admission law and the value's comparison law
  determine the complete output class. This theorem does not claim that
  literal key retention compares arbitrary alternative key presentations.
\<close>

end
