theory Factor_Source_Presentations
  imports Factor_Construction_Presentations Factor_Table_Boundaries Factor_Structural_Collections
begin

section \<open>Whole-artifact literals and complete input occurrences\<close>

abbreviation artifact_literal_presents :: "exact_artifact \<Rightarrow> factor_term \<Rightarrow> bool" where
  "artifact_literal_presents R p \<equiv> exact_formed R \<and> p=Target_Term (Whole_Artifact R)"

lemma artifact_literal_presentation_class:
  "presentation_class artifact_literal_presents exact_formed (\<lambda>p. \<exists>R. artifact_literal_presents R p)"
  by (rule injective_presentation_class) (auto simp: inj_on_def)

abbreviation source_inputs_presents :: "exact_artifact list \<Rightarrow> factor_term \<Rightarrow> bool" where
  "source_inputs_presents xs p \<equiv> (\<forall>R\<in>set xs. exact_formed R) \<and> p=artifact_list_term xs"

lemma source_inputs_presentation_class:
  "presentation_class source_inputs_presents (\<lambda>xs. \<forall>R\<in>set xs. exact_formed R)
    (\<lambda>p. \<exists>xs. source_inputs_presents xs p)"
  by (rule injective_presentation_class) (auto simp: inj_on_def artifact_list_term_exact)

lemma source_input_data_sequence:
  "data_sequence_presents artifact_literal_presents xs p \<longleftrightarrow>
    (\<forall>R\<in>set xs. exact_formed R) \<and> p=data_list_term (map (Target_Term \<circ> Whole_Artifact) xs)"
proof -
  have element: "artifact_literal_presents=(\<lambda>R p. p=(Target_Term \<circ> Whole_Artifact) R \<and> exact_formed R)"
    by (intro ext) auto
  show ?thesis by (simp only: data_sequence_presents_def element list_all2_function_restricted) (auto simp: comp_def)
qed

lemma source_inputs_composition:
  "composed_presentation (data_sequence_presents artifact_literal_presents) enumeration_retermination xs q
    \<longleftrightarrow> source_inputs_presents xs q"
  by (auto simp: composed_presentation_def source_input_data_sequence enumeration_retermination_def
    data_list_term_injective artifact_list_term_def)

section \<open>The complete base table keeps every supplied key and artifact\<close>

abbreviation source_base_presents :: "(local_address\<times>exact_artifact) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "source_base_presents \<equiv>
    composed_presentation (data_table_presents payload_value_presents artifact_literal_presents) enumeration_retermination"

lemma source_base_presentation_class:
  "presentation_class source_base_presents (finite_table_domain octets_formed exact_formed)
    (\<lambda>p. \<exists>B. source_base_presents B p)"
  by (rule reterminated_table_presentation_class[OF payload_value_presentation_class artifact_literal_presentation_class])

lemma source_base_fields:
  "source_base_presents B p \<longleftrightarrow>
    (\<forall>z\<in>B. octets_formed (fst z) \<and> exact_formed (snd z)) \<and>
    finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B p"
  by (rule reterminated_literal_table_boundaries)

lemma source_base_formed:
  assumes "source_base_presents B p"
  shows "term_formed p"
proof -
  have rows: "finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B p"
    using assms by (simp only: source_base_fields; blast)
  have boundary: "\<forall>z\<in>B. octets_formed (fst z) \<and> exact_formed (snd z)"
    using assms by (simp only: source_base_fields; blast)
  show ?thesis by (rule finite_table_presents_formed[OF rows]) (use boundary in auto)
qed

section \<open>The source context is the existing ordered and keyed boundary\<close>

type_synonym construction_source_context = "exact_artifact list\<times>(local_address\<times>exact_artifact) set"

abbreviation source_context_domain :: "construction_source_context \<Rightarrow> bool" where
  "source_context_domain C \<equiv> construction_sources_formed (fst C) (snd C) \<and>
    (\<forall>b R. (b,R)\<in>snd C \<longrightarrow> octets_formed b)"

abbreviation source_context_presents :: "construction_source_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "source_context_presents \<equiv> factor_pair_presents source_inputs_presents source_base_presents"

lemma source_context_presentation_class:
  "presentation_class source_context_presents source_context_domain
    (\<lambda>p. \<exists>C. source_context_presents C p)"
proof -
  have pair: "presentation_class source_context_presents
      (\<lambda>C. (\<forall>R\<in>set (fst C). exact_formed R) \<and> finite_table_domain octets_formed exact_formed (snd C))
      (\<lambda>p. \<exists>x b. (\<exists>xs. source_inputs_presents xs x) \<and>
        (\<exists>B. source_base_presents B b) \<and> p=Pair_Term x b)"
    by (rule factor_pair_class[OF source_inputs_presentation_class source_base_presentation_class])
  have domain: "((\<forall>R\<in>set (fst C). exact_formed R) \<and> finite_table_domain octets_formed exact_formed (snd C))
      \<longleftrightarrow> source_context_domain C" for C
    by (auto simp: construction_sources_formed_def)
  show ?thesis using pair presentation_class.admissible_iff[OF pair]
    by (simp only: presentation_class_def domain; blast)
qed

interpretation source_contexts: presentation_class source_context_presents source_context_domain
  "\<lambda>p. \<exists>C. source_context_presents C p"
  by (rule source_context_presentation_class)

lemma source_context_fields:
  "source_context_presents (xs,B) p \<longleftrightarrow>
    source_context_domain (xs,B) \<and>
    (\<exists>b. finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B b \<and>
      p=Pair_Term (artifact_list_term xs) b)"
proof -
  have boundary: "finite B \<and> single_valued B"
    if "finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B b" for b
    using that finite_collection_presents_finite by (auto simp: finite_table_presents_def)
  show ?thesis using boundary
    by (auto simp: factor_pair_presents_def source_base_fields construction_sources_formed_def)
qed

lemma source_context_formed:
  assumes "source_context_presents C p"
  shows "term_formed p"
  using assms source_base_formed by (auto simp: factor_pair_presents_def artifact_list_term_formed)

section \<open>A source query includes the complete context and an actual source\<close>

type_synonym construction_source_query = "construction_source_context\<times>(nat+local_address)"

abbreviation source_query_domain :: "construction_source_query \<Rightarrow> bool" where
  "source_query_domain z \<equiv> source_context_domain (fst z) \<and>
    (\<exists>R. construction_source_at (fst (fst z)) (snd (fst z)) (snd z) R)"

abbreviation source_query_value :: "construction_source_query \<Rightarrow> exact_artifact" where
  "source_query_value z \<equiv> construction_source_value (fst (fst z)) (snd (fst z)) (snd z)"

definition source_query_presents :: "construction_source_query \<Rightarrow> factor_term \<Rightarrow> bool" where
  "source_query_presents z p \<longleftrightarrow> source_query_domain z \<and>
    factor_pair_presents source_context_presents (\<lambda>j q. q=construction_source_term j) z p"

lemma source_query_presentation_class:
  "presentation_class source_query_presents source_query_domain (\<lambda>p. \<exists>z. source_query_presents z p)"
proof -
  have index: "presentation_class (\<lambda>j q. q=construction_source_term j) (\<lambda>_. True)
      (\<lambda>q. \<exists>j. q=construction_source_term j)"
    using injective_presentation_class[where f=construction_source_term and D="\<lambda>_. True"]
    by (simp add: inj_on_def construction_source_term_exact)
  have pairs: "presentation_class
      (factor_pair_presents source_context_presents (\<lambda>j q. q=construction_source_term j))
      (\<lambda>z. source_context_domain (fst z) \<and> True)
      (\<lambda>p. \<exists>c j. (\<exists>C. source_context_presents C c) \<and>
        (\<exists>k. j=construction_source_term k) \<and> p=Pair_Term c j)"
    by (rule factor_pair_class[OF source_context_presentation_class index])
  show ?thesis unfolding source_query_presents_def
    by (rule presentation_class_subdomain[OF pairs]) simp
qed

interpretation source_queries: presentation_class source_query_presents source_query_domain
  "\<lambda>p. \<exists>z. source_query_presents z p"
  by (rule source_query_presentation_class)

lemma source_query_at:
  "source_query_presents ((xs,B),j) (Pair_Term c k) \<longleftrightarrow>
    source_context_presents (xs,B) c \<and> (\<exists>R. construction_source_at xs B j R) \<and>
    k=construction_source_term j"
  using source_contexts.subject_boundary[of "(xs,B)" c]
  by (auto simp: source_query_presents_def)

lemma source_query_value_formed:
  assumes "source_query_domain z"
  shows "exact_formed (source_query_value z)"
  using assms construction_source_value_at by blast

lemma source_query_formed:
  assumes "source_query_presents z p"
  shows "term_formed p"
proof -
  obtain xs B j c where "context": "source_context_presents (xs,B) c"
    and source: "\<exists>R. construction_source_at xs B j R"
    and shape: "z=((xs,B),j)" "p=Pair_Term c (construction_source_term j)"
    using assms by (cases z; cases "fst z")
      (auto simp: source_query_presents_def factor_pair_presents_def)
  have boundary: "source_context_domain (xs,B)" by (rule source_contexts.subject_boundary[OF "context"])
  have index: "term_formed (construction_source_term j)"
    using source boundary by (cases j) auto
  show ?thesis using source_context_formed[OF "context"] index by (simp add: shape)
qed

text \<open>
  Ordered inputs retain their positions and repetitions. Base sources retain
  every key and exact artifact in every complete table order. Their product
  presents the existing source boundary, including unused members.

  The query is the general product restricted by actual source membership.
  Its value is the existing source function used only on that domain. The
  existing natural and payload constructors distinguish input positions and
  base keys without a new role field. A missing key or an index at the end is
  outside the query domain, including when the requested fragment is empty.

  These classes concern source availability. They do not admit a construction
  policy or prove its global invariance over complete account presentations.
\<close>

end
