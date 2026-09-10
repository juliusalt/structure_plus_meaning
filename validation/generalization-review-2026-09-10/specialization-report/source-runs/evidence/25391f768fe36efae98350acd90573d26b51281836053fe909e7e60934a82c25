theory Factor_Admitted_Pair
  imports Factor_Data_Term_Presentations
begin

section \<open>Each field retains its own native admission\<close>

definition admitted_pair_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "admitted_pair_schema first second=data_rule (Pattern_Pair data_x data_y)
    {(0,first,data_x),(1,second,data_y)}"

lemma admitted_pair_formed [simp]: "schema_formed (admitted_pair_schema first second)"
  by (auto simp: admitted_pair_schema_def schema_formed_def single_valued_def)

lemma admitted_pair_dependencies [simp]: "schema_dependencies (admitted_pair_schema first second)={first,second}"
  by (auto simp: admitted_pair_schema_def schema_dependencies_def rel_ran_image)

lemma admitted_data_pair_schema: "admitted_pair_schema 2 2=data_pair_schema"
  by (simp only: admitted_pair_schema_def data_pair_schema_def)

locale admitted_pair_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry first second :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow> c=0 \<and> S=admitted_pair_schema first second"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (first,h 0)\<in>positive_meaning P \<and> (second,h 1)\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family admitted_pair_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>p q. t=Pair_Term p q \<and> (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>p q. t=Pair_Term p q \<and> (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P"
  then obtain p q where parts: "t=Pair_Term p q" "(first,p)\<in>positive_meaning P" "(second,q)\<in>positive_meaning P" by blast
  have terms: "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by blast+
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else q"])
      (use parts terms in auto)
qed

corollary at_pair:
  "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P"
  by (auto simp only: exact factor_term.inject)

theorem presentation_class:
  assumes left: "presentation_class R D (\<lambda>p. (first,p)\<in>positive_meaning P)"
    and right: "presentation_class S E (\<lambda>q. (second,q)\<in>positive_meaning P)"
  shows "presentation_class (factor_pair_presents R S) (\<lambda>z. D (fst z) \<and> E (snd z))
    (\<lambda>t. (entry,t)\<in>positive_meaning P)"
proof -
  have source: "presentation_class (factor_pair_presents R S) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>t. \<exists>p q. (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF left right])
  have admission: "(\<lambda>t. \<exists>p q. (first,p)\<in>positive_meaning P \<and> (second,q)\<in>positive_meaning P \<and> t=Pair_Term p q)=
      (\<lambda>t. (entry,t)\<in>positive_meaning P)"
    by (rule ext) (simp only: exact; blast)
  show ?thesis using source by (simp only: admission)
qed

end

text \<open>
  The two actual callees admit separate fields at distinct premise sockets.
  Their locally owned classes give the complete pair class without adding
  a relation between its subjects. The existing data-pair clause is the case
  in which both fields call data admission. The same construction applies
  when the two fields have different complete domains.
\<close>

end
