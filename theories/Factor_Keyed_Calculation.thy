theory Factor_Keyed_Calculation
  imports Factor_Related_List_Maps Factor_List_Set_Presentations
begin

section \<open>The selected key is retained beside its actual calculated value\<close>

definition keyed_calculation_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "keyed_calculation_schema calculate=data_rule
    (context_relation_pattern (Pattern_Pair data_x data_y) data_z (Pattern_Pair data_z data_w))
    {(0,calculate,context_relation_pattern (Pattern_Pair data_x data_z) data_y data_w)}"

lemma keyed_calculation_formed [simp]: "schema_formed (keyed_calculation_schema calculate)"
  by (auto simp: keyed_calculation_schema_def schema_formed_def single_valued_def)

lemma keyed_calculation_dependencies [simp]:
  "schema_dependencies (keyed_calculation_schema calculate)={calculate}"
  by (auto simp: keyed_calculation_schema_def schema_dependencies_def rel_ran_image)

locale keyed_calculation_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry calculate :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=keyed_calculation_schema calculate"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=context_relation_argument (Pair_Term (h 0) (h 1)) (h 2) (Pair_Term (h 2) (h 3)) \<and>
      (calculate,context_relation_argument (Pair_Term (h 0) (h 2)) (h 1) (h 3))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family keyed_calculation_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>F T k v. t=context_relation_argument (Pair_Term F T) k (Pair_Term k v) \<and>
      (calculate,context_relation_argument (Pair_Term F k) T v)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>F T k v. t=context_relation_argument (Pair_Term F T) k (Pair_Term k v) \<and>
      (calculate,context_relation_argument (Pair_Term F k) T v)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>F T k v. t=context_relation_argument (Pair_Term F T) k (Pair_Term k v) \<and>
      (calculate,context_relation_argument (Pair_Term F k) T v)\<in>positive_meaning P"
  then obtain F T k v where parts: "t=context_relation_argument (Pair_Term F T) k (Pair_Term k v)"
    "(calculate,context_relation_argument (Pair_Term F k) T v)\<in>positive_meaning P" by blast
  have terms: "term_formed F" "term_formed T" "term_formed k" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by auto
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then F else if i=1 then T else if i=2 then k else v"])
      (use parts terms in auto)
qed

corollary at_key:
  "(entry,context_relation_argument (Pair_Term F T) k q)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>v. q=Pair_Term k v \<and> (calculate,context_relation_argument (Pair_Term F k) T v)\<in>positive_meaning P)"
  by (auto simp only: exact factor_term.inject)

end

section \<open>Complete row classes consume every key and its computed value\<close>

theorem factor_keyed_fset_enumeration:
  assumes keys: "\<And>x. x\<in>set xs \<Longrightarrow> K x (h x)"
    and value_readings: "\<And>x. x\<in>set xs \<Longrightarrow> R (f x) (g x)"
  shows "data_list_fset_presents (factor_pair_presents K R) (fset_of_list (map (\<lambda>x. (x,f x)) xs))
    (data_list_term (map (\<lambda>x. Pair_Term (h x) (g x)) xs))"
proof -
  have rows: "list_all2 (factor_pair_presents K R) (map (\<lambda>x. (x,f x)) xs)
      (map (\<lambda>x. Pair_Term (h x) (g x)) xs)"
    by (simp only: list_all2_map1 list_all2_map2 list_all2_same factor_pair_presents_at)
      (use keys value_readings in blast)
  have sequence: "data_sequence_presents (factor_pair_presents K R) (map (\<lambda>x. (x,f x)) xs)
      (data_list_term (map (\<lambda>x. Pair_Term (h x) (g x)) xs))"
    using rows by (auto simp only: data_sequence_presents_def)
  show ?thesis by (rule data_list_fset_presents_finite_image[OF sequence])
qed

text \<open>
  The native callee receives the selected key in its own context and the
  shared table as its operand. Its result is attached to that same key.
  An outer map can keep the shared context and table while varying the key.
  The row-class theorem retains every enumerated key, including keys whose
  value presentation is empty, and consumes the independent key and value
  presentation laws once for the whole finite set of rows.
\<close>

end
