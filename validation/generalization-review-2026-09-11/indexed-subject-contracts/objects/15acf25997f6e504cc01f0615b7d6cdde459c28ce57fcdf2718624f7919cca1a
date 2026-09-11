theory Factor_Observation_Collection_Contracts
  imports Factor_Keyed_Set_Contracts Factor_Observation_Contracts
begin

section \<open>Profile and loss rows are complete products of their independent fields\<close>

abbreviation observation_keyed_rows_presents where
  "observation_keyed_rows_presents K \<equiv> data_list_fset_presents (factor_pair_presents K observation_values_presents)"

abbreviation observation_keyed_rows_domain where
  "observation_keyed_rows_domain D S \<equiv> \<forall>z\<in>fset S. D (fst z) \<and> observation_values_domain (snd z)"

abbreviation observation_profile_rows_presents where
  "observation_profile_rows_presents \<equiv> observation_keyed_rows_presents observation_datum_presents"

abbreviation observation_loss_rows_presents where
  "observation_loss_rows_presents \<equiv> observation_keyed_rows_presents observation_value_presents"

lemma observation_keyed_row_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (factor_pair_presents K observation_values_presents)
    (\<lambda>z. D (fst z) \<and> observation_values_domain (snd z))
    (\<lambda>p. \<exists>z. factor_pair_presents K observation_values_presents z p)"
  by (rule presentation_class.recovered_admission[OF factor_pair_class[OF keys observation_values_class]])

lemma observation_keyed_rows_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (observation_keyed_rows_presents K) (observation_keyed_rows_domain D)
    (\<lambda>p. \<exists>S. observation_keyed_rows_presents K S p)"
  by (rule presentation_class.recovered_admission[OF
    data_list_fset_presentation_class[OF observation_keyed_row_class[OF keys]]])

theorem observation_profile_rows_class:
  "presentation_class observation_profile_rows_presents (observation_keyed_rows_domain observation_datum)
    (\<lambda>p. \<exists>S. observation_profile_rows_presents S p)"
  by (rule observation_keyed_rows_class[OF observation_datum_class])

theorem observation_loss_rows_class:
  "presentation_class observation_loss_rows_presents (observation_keyed_rows_domain (\<lambda>(c,d). data_elements [c,d]))
    (\<lambda>p. \<exists>S. observation_loss_rows_presents S p)"
  by (rule observation_keyed_rows_class[OF observation_value_class])

section \<open>Owned key and value contracts determine the whole native comparison\<close>

lemma keyed_observation_values_output:
  assumes "observation_values_presents V p"
  shows "(219,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    observation_values_presents V q"
  using observation_values_at_computed[OF assms, of q]
  by (simp only: observation_result_components keyed_set_components)

theorem keyed_observation_rows_output:
  assumes injective: "inj_on f {a. D a}"
    and key_data: "\<And>a. D a \<Longrightarrow> data_term_boundary (f a)"
    and source: "observation_keyed_rows_presents (\<lambda>a t. D a \<and> t=f a) S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    observation_keyed_rows_presents (\<lambda>a t. D a \<and> t=f a) S q"
proof -
  let ?K="\<lambda>a t. D a \<and> t=f a"
  let ?R="factor_pair_presents ?K observation_values_presents"
  have keys: "presentation_class ?K D (\<lambda>p. \<exists>a. D a \<and> p=f a)"
    by (rule injective_presentation_class[OF injective])
  have rows: "presentation_class ?R (\<lambda>z. D (fst z) \<and> observation_values_domain (snd z))
      (\<lambda>p. \<exists>z. ?R z p)" by (rule observation_keyed_row_class[OF keys])
  have key_calls: "(2,f a)\<in>positive_meaning keyed_set_system" if "D a" for a
    using key_data[OF that] by (simp only: keyed_set_components)
  have row_data: "data_term_boundary x" if row_read: "?R z x" for z x
  proof -
    obtain v where parts: "x=Pair_Term (f (fst z)) v" "D (fst z)"
      "observation_values_presents (snd z) v"
      using row_read by (auto simp only: factor_pair_presents_def)
    show ?thesis using key_data[OF parts(2)] observation_values_presented_data[OF parts(3)]
      by (simp only: parts(1) term_formed.simps self_contained_term.simps)
  qed
  have compared: "(312,Pair_Term x y)\<in>positive_meaning keyed_set_system \<longleftrightarrow> ?R z y"
    if compared_source: "?R z x" for z x y
  proof -
    obtain k v where shape: "z=(k,v)" by (cases z) auto
    show ?thesis using keyed_set_rows.at_presentation[where D=D and f=f and S=observation_values_presents
      and k=k and v=v and p=x and q=y, OF compared_source[unfolded shape] key_calls keyed_observation_values_output]
      by (simp only: shape)
  qed
  show ?thesis
  proof (rule keyed_sets.comparison_output[where R="?R", OF rows source])
    fix z x assume "?R z x"
    then show "term_formed x \<and> self_contained_term x" by (rule row_data)
  next
    fix z x y assume "?R z x"
    then show "(312,Pair_Term x y)\<in>positive_meaning keyed_set_system \<longleftrightarrow> ?R z y"
      by (rule compared)
  qed
qed

theorem observation_profile_rows_output:
  assumes "observation_profile_rows_presents S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    observation_profile_rows_presents S q"
proof -
  have injective: "inj_on id {a. observation_datum a}" by simp
  have key_data: "data_term_boundary (id a)" if "observation_datum a" for a using that by simp
  have source: "observation_keyed_rows_presents (\<lambda>a t. observation_datum a \<and> t=id a) S p"
    using assms by simp
  show ?thesis using keyed_observation_rows_output[where f=id and D=observation_datum and S=S and p=p and q=q,
    OF injective key_data source] by simp
qed

theorem observation_loss_rows_output:
  assumes "observation_loss_rows_presents S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    observation_loss_rows_presents S q"
proof -
  let ?D="\<lambda>(c,d). data_elements [c,d]"
  have injective: "inj_on observation_value_term {a. ?D a}"
    by (rule inj_on_subset[OF observation_value_term_injective]) auto
  have key_data: "data_term_boundary (observation_value_term a)" if "?D a" for a
    using that by (cases a) auto
  have source: "observation_keyed_rows_presents (\<lambda>a t. ?D a \<and> t=observation_value_term a) S p"
    using assms by (simp only: observation_value_graph)
  show ?thesis using keyed_observation_rows_output[where f=observation_value_term and D="?D" and S=S and p=p and q=q,
    OF injective key_data source] by (simp only: observation_value_graph)
qed

corollary observation_profile_rows_comparison:
  assumes "observation_profile_rows_presents S p" "observation_profile_rows_presents T q"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow> S=T"
  using observation_profile_rows_output[OF assms(1), of q] assms(2)
    presentation_class.recovery[OF observation_profile_rows_class] by blast

corollary observation_loss_rows_comparison:
  assumes "observation_loss_rows_presents S p" "observation_loss_rows_presents T q"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow> S=T"
  using observation_loss_rows_output[OF assms(1), of q] assms(2)
    presentation_class.recovery[OF observation_loss_rows_class] by blast

text \<open>
  Profile rows pair a candidate with a finite observation profile. Loss rows
  pair an ordered candidate pair with a finite directed loss. These are
  different subject domains, derived through the same product and finite-set
  constructions. At both levels, every allowed displayed order and repetition
  remains admissible, including different presentations of a repeated row.

  The native comparison consumes the already owned value and key equations.
  The output laws cover every target term, and comparisons at two presented
  subjects preserve both equality and inequality. No functional-key condition
  is added to these general row collections. A computed profile or loss graph
  determines that further property through its own function contract.
\<close>

end
