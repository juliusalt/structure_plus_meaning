theory Factor_Selection_Presentations
  imports Factor_Source_Presentations Factor_Fragment_Presentations Factor_Table_Maps
begin

section \<open>The existing selection form has a complete component class\<close>

type_synonym construction_selection_value = "(nat+local_address)\<times>local_address set"
type_synonym construction_selection_table = "(local_address\<times>construction_selection_value) set"

lemma construction_selection_presentation_class:
  "presentation_class construction_selection_presents (\<lambda>z. finite (snd z))
    (\<lambda>p. \<exists>z. construction_selection_presents z p)"
proof -
  have indices: "presentation_class (\<lambda>j p. p=construction_source_term j) (\<lambda>_. True)
      (\<lambda>p. \<exists>j. p=construction_source_term j)"
    using injective_presentation_class[where f=construction_source_term and D="\<lambda>_. True"]
    by (simp add: inj_on_def construction_source_term_exact)
  have payloads: "presentation_class (\<lambda>a p. p=Payload_Term a) (\<lambda>_. True)
      (\<lambda>p. \<exists>a. p=Payload_Term a)"
    using injective_presentation_class[where f=Payload_Term and D="\<lambda>_. True"]
    by (simp add: inj_on_def)
  have sets: "presentation_class (finite_set_presents Payload_Term) finite
      (\<lambda>p. \<exists>A. finite_set_presents Payload_Term A p)"
    using finite_collection_presentation_class[OF payloads]
    by (simp add: finite_set_presents_def[abs_def])
  have pair: "presentation_class
      (factor_pair_presents (\<lambda>j p. p=construction_source_term j) (finite_set_presents Payload_Term))
      (\<lambda>z. finite (snd z))
      (\<lambda>p. \<exists>j a. (\<exists>k. j=construction_source_term k) \<and>
        (\<exists>A. finite_set_presents Payload_Term A a) \<and> p=Pair_Term j a)"
    using factor_pair_class[OF indices sets] by simp
  have reading: "factor_pair_presents (\<lambda>j p. p=construction_source_term j)
      (finite_set_presents Payload_Term)=construction_selection_presents"
    by (intro ext) (auto simp: factor_pair_presents_def construction_selection_presents_def)
  show ?thesis using pair presentation_class.admissible_iff[OF pair]
    by (simp only: reading presentation_class_def; blast)
qed

abbreviation selection_valid :: "construction_source_context \<Rightarrow> construction_selection_value \<Rightarrow> bool" where
  "selection_valid C z \<equiv> source_selection_valid (fst C) (snd C) (fst z) (snd z)"

abbreviation selection_presents ::
  "construction_source_context \<Rightarrow> construction_selection_value \<Rightarrow> factor_term \<Rightarrow> bool" where
  "selection_presents C z p \<equiv> selection_valid C z \<and> construction_selection_presents z p"

lemma selection_presentation_class:
  "presentation_class (selection_presents C) (selection_valid C)
    (\<lambda>p. \<exists>z. selection_presents C z p)"
  by (rule presentation_class_subdomain[OF construction_selection_presentation_class])
    (simp add: source_selection_valid_def)

lemma selection_presents_formed:
  assumes "context": "source_context_domain C" and selected: "selection_presents C z p"
  shows "term_formed p"
proof -
  obtain xs B j A where shape: "C=(xs,B)" "z=(j,A)" by (cases C; cases z) auto
  have canonical: "term_formed (construction_selection_term z)"
    using construction_selection_term_formed[of xs B j A] "context" selected
    by (simp add: shape)
  show ?thesis using selected by (intro construction_selection_presents_formed[OF _ canonical]) blast
qed

section \<open>A selected fragment keeps its complete source context\<close>

type_synonym construction_selection_query = "construction_source_context\<times>construction_selection_value"

abbreviation selection_query_domain :: "construction_selection_query \<Rightarrow> bool" where
  "selection_query_domain z \<equiv> source_context_domain (fst z) \<and> selection_valid (fst z) (snd z)"

abbreviation selection_query_fragment :: "construction_selection_query \<Rightarrow> exact_fragment" where
  "selection_query_fragment z \<equiv>
    construction_fragment (fst (fst z)) (snd (fst z)) (fst (snd z)) (snd (snd z))"

definition selection_query_presents :: "construction_selection_query \<Rightarrow> factor_term \<Rightarrow> bool" where
  "selection_query_presents z p \<longleftrightarrow> selection_query_domain z \<and>
    factor_pair_presents source_context_presents construction_selection_presents z p"

lemma selection_query_presentation_class:
  "presentation_class selection_query_presents selection_query_domain
    (\<lambda>p. \<exists>z. selection_query_presents z p)"
proof -
  have pair: "presentation_class (factor_pair_presents source_context_presents construction_selection_presents)
      (\<lambda>z. source_context_domain (fst z) \<and> finite (snd (snd z)))
      (\<lambda>p. \<exists>c s. (\<exists>C. source_context_presents C c) \<and>
        (\<exists>z. construction_selection_presents z s) \<and> p=Pair_Term c s)"
    by (rule factor_pair_class[OF source_context_presentation_class construction_selection_presentation_class])
  show ?thesis unfolding selection_query_presents_def
    by (rule presentation_class_subdomain[OF pair]) (simp add: source_selection_valid_def)
qed

interpretation selection_queries: presentation_class selection_query_presents selection_query_domain
  "\<lambda>p. \<exists>z. selection_query_presents z p"
  by (rule selection_query_presentation_class)

lemma selection_query_at:
  "selection_query_presents (C,z) (Pair_Term c p) \<longleftrightarrow>
    source_context_presents C c \<and> selection_presents C z p"
  using source_contexts.subject_boundary[of C c] by (auto simp: selection_query_presents_def)

lemma selection_query_fragment_formed:
  assumes "selection_query_domain z"
  shows "fragment_formed (selection_query_fragment z)"
  using assms by (intro selected_fragment_formed) auto

lemma selection_query_at_fixed_context:
  assumes "source_context_presents C c"
  shows "selection_query_presents z (Pair_Term c p) \<longleftrightarrow>
    fst z=C \<and> selection_presents C (snd z) p"
proof -
  obtain C' v where shape: "z=(C',v)" by (cases z) auto
  have recover: "C'=C" if "source_context_presents C' c"
    by (rule source_contexts.recovery[OF that assms])
  show ?thesis using assms recover
    by (simp only: shape selection_query_at fst_conv snd_conv; blast)
qed

lemma selection_query_formed:
  assumes "selection_query_presents z p"
  shows "term_formed p"
proof -
  have pair: "factor_pair_presents source_context_presents construction_selection_presents z p"
    and domain: "selection_query_domain z"
    using assms by (simp only: selection_query_presents_def; blast)+
  obtain c s where "context": "source_context_presents (fst z) c"
    and selection: "construction_selection_presents (snd z) s" and shape: "p=Pair_Term c s"
    using factor_pair_presents_def[THEN iffD1, OF pair] by blast
  have formed: "term_formed c" "term_formed s"
    using source_context_formed[OF "context"] selection_presents_formed[of "fst z" "snd z" s]
      domain selection by blast+
  show ?thesis using formed by (simp only: shape term_formed.simps)
qed

abbreviation selection_material :: "construction_source_context \<Rightarrow> construction_selection_value \<Rightarrow> exact_artifact" where
  "selection_material C z \<equiv> fragment_material
    (construction_fragment (fst C) (snd C) (fst z) (snd z))"

lemma selection_material_formed:
  assumes "source_context_domain C" "selection_valid C z"
  shows "exact_formed (selection_material C z)"
  by (rule fragment_material_formed, rule selected_fragment_formed) (use assms in auto)

section \<open>Complete selected tables retain their occurrence slots\<close>

abbreviation selection_table_domain :: "construction_source_context \<Rightarrow> construction_selection_table \<Rightarrow> bool" where
  "selection_table_domain C \<equiv> finite_table_domain octets_formed (selection_valid C)"

abbreviation selection_table_presents ::
  "construction_source_context \<Rightarrow> construction_selection_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "selection_table_presents C \<equiv>
    composed_presentation (data_table_presents payload_value_presents (selection_presents C)) enumeration_retermination"

lemma selection_table_presentation_class:
  "presentation_class (selection_table_presents C) (selection_table_domain C)
    (\<lambda>p. \<exists>Q. selection_table_presents C Q p)"
  by (rule reterminated_table_presentation_class[OF payload_value_presentation_class selection_presentation_class])

lemma selection_table_fields:
  "selection_table_presents C Q p \<longleftrightarrow>
    (\<forall>z\<in>Q. octets_formed (fst z) \<and> selection_valid C (snd z)) \<and>
    finite_table_presents Payload_Term construction_selection_presents Q p"
  by (auto simp: finite_table_retermination composed_presentation_def data_table_presents_constrain)

lemma selection_table_formed:
  assumes "context": "source_context_domain C" and selected: "selection_table_presents C Q p"
  shows "term_formed p"
proof -
  have rows: "finite_table_presents Payload_Term construction_selection_presents Q p"
    and boundary: "\<forall>z\<in>Q. octets_formed (fst z) \<and> selection_valid C (snd z)"
    using selected by (simp only: selection_table_fields; blast)+
  show ?thesis by (rule finite_table_presents_formed[OF rows])
    (use boundary selection_presents_formed[OF "context"] in auto)
qed

type_synonym construction_selection_context = "construction_source_context\<times>construction_selection_table"

abbreviation selection_context_domain :: "construction_selection_context \<Rightarrow> bool" where
  "selection_context_domain z \<equiv> source_context_domain (fst z) \<and> selection_table_domain (fst z) (snd z)"

definition selection_context_presents :: "construction_selection_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "selection_context_presents z p \<longleftrightarrow> selection_context_domain z \<and>
    factor_pair_presents source_context_presents
      (finite_table_presents Payload_Term construction_selection_presents) z p"

lemma selection_context_presentation_class:
  "presentation_class selection_context_presents selection_context_domain
    (\<lambda>p. \<exists>z. selection_context_presents z p)"
proof -
  have tables: "presentation_class (finite_table_presents Payload_Term construction_selection_presents)
      (finite_table_domain (\<lambda>_. True) (\<lambda>z. finite (snd z)))
      (\<lambda>p. \<exists>Q. finite_table_presents Payload_Term construction_selection_presents Q p)"
    by (rule finite_table_presentation_class[OF payload_term_injective construction_selection_presentation_class])
  have pairs: "presentation_class
      (factor_pair_presents source_context_presents (finite_table_presents Payload_Term construction_selection_presents))
      (\<lambda>z. source_context_domain (fst z) \<and>
        finite_table_domain (\<lambda>_. True) (\<lambda>v. finite (snd v)) (snd z))
      (\<lambda>p. \<exists>c s. (\<exists>C. source_context_presents C c) \<and>
        (\<exists>Q. finite_table_presents Payload_Term construction_selection_presents Q s) \<and> p=Pair_Term c s)"
    by (rule factor_pair_class[OF source_context_presentation_class tables])
  show ?thesis unfolding selection_context_presents_def
    by (rule presentation_class_subdomain[OF pairs]) (auto simp: source_selection_valid_def)
qed

interpretation selection_contexts: presentation_class selection_context_presents selection_context_domain
  "\<lambda>p. \<exists>z. selection_context_presents z p"
  by (rule selection_context_presentation_class)

lemma selection_context_at:
  "selection_context_presents (C,Q) (Pair_Term c p) \<longleftrightarrow>
    source_context_presents C c \<and> selection_table_presents C Q p"
  using source_contexts.subject_boundary[of C c]
    presentation_class.subject_boundary[OF selection_table_presentation_class, of C Q p]
  by (auto simp: selection_context_presents_def selection_table_fields)

lemma selection_context_formed:
  assumes "selection_context_presents z p"
  shows "term_formed p"
proof -
  have pair: "factor_pair_presents source_context_presents
      (finite_table_presents Payload_Term construction_selection_presents) z p"
    and domain: "selection_context_domain z"
    using assms by (simp only: selection_context_presents_def; blast)+
  obtain c s where "context": "source_context_presents (fst z) c"
    and table: "finite_table_presents Payload_Term construction_selection_presents (snd z) s"
    and shape: "p=Pair_Term c s"
    using factor_pair_presents_def[THEN iffD1, OF pair] by blast
  have reads: "source_context_presents (fst z) c" "selection_table_presents (fst z) (snd z) s"
    using "context" table domain by (auto simp only: selection_table_fields)
  show ?thesis using source_context_formed[OF reads(1)]
    selection_table_formed[OF source_contexts.subject_boundary[OF reads(1)] reads(2)] by (simp add: shape)
qed

abbreviation selection_context_value :: "construction_selection_context \<Rightarrow> (local_address\<times>exact_artifact) set" where
  "selection_context_value z \<equiv> map_prod id (selection_material (fst z)) ` snd z"

lemma selection_context_value_boundary:
  assumes "selection_context_domain z"
  shows "finite_table_domain octets_formed exact_formed (selection_context_value z)"
  using assms single_valued_value_image selection_material_formed by auto

lemma selection_context_construction_boundary:
  "selection_context_domain ((xs,B),construction_selections W) \<longleftrightarrow>
    construction_selection_formed xs B W \<and> construction_coordinates_formed B W"
  by (auto simp: construction_selection_formed_def construction_coordinates_formed_def; blast)

lemma selection_context_piece_graph:
  "selection_context_value ((xs,B),construction_selections W)=piece_graph (construction_pieces xs B W)"
  by (simp only: construction_pieces_def exact_piece_family.select_convs case_prod_beta' fst_conv snd_conv)

text \<open>
  A raw selection retains the existing source index and every complete order
  of its selected address set. Restriction gives the selections valid at a
  supplied context. The complete query includes that entire context, so an
  empty selection still requires an actual source and all unused sources
  remain visible.

  Tables add the independent piece slots. The context and table classes are
  products restricted by the existing source, selection, and coordinate
  conditions. Their derived value is the standard image that keeps slots and
  maps each selection to its fragment material. The final two equations link
  that image to the original construction witness without adding a stored
  piece family or an output field to its primitive basis.
\<close>

end
