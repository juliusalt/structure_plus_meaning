theory Factor_Term_Sequence_Presentations
  imports Factor_Table_Presentations Factor_Coordinate_Values
begin

section \<open>Sequences retain their actual formed terms\<close>

abbreviation formed_term_presents :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "formed_term_presents x p \<equiv> term_formed x \<and> p=x"

lemma formed_term_presentation_class:
  "presentation_class formed_term_presents term_formed term_formed"
  by (unfold_locales) auto

abbreviation formed_sequence_presents :: "factor_term list \<Rightarrow> factor_term \<Rightarrow> bool" where
  "formed_sequence_presents \<equiv> data_sequence_presents formed_term_presents"

lemma formed_sequence_presents_iff:
  "formed_sequence_presents xs p \<longleftrightarrow>
    (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs"
proof -
  have elements: "list_all2 formed_term_presents xs ps \<longleftrightarrow>
      ps=xs \<and> (\<forall>x\<in>set xs. term_formed x)" for ps
    by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)
  show ?thesis by (auto simp: data_sequence_presents_def elements)
qed

lemma formed_sequence_presentation_class:
  "presentation_class formed_sequence_presents (\<lambda>xs. \<forall>x\<in>set xs. term_formed x)
    (\<lambda>p. \<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs)"
  by (rule data_sequence_presentation_class[OF formed_term_presentation_class])

lemma natural_data_presentation_class:
  "presentation_class (\<lambda>n p. p=natural_data_term n) (\<lambda>_. True)
    (\<lambda>p. \<exists>n. p=natural_data_term n)"
  using injective_presentation_class[where f=natural_data_term and D="\<lambda>_. True"]
    natural_data_term_injective by simp

abbreviation formed_enumeration_presents :: "factor_term list \<Rightarrow> factor_term \<Rightarrow> bool" where
  "formed_enumeration_presents xs p \<equiv> (\<forall>x\<in>set xs. term_formed x) \<and> p=enumeration_term xs"

lemma formed_enumeration_composition:
  "composed_presentation formed_sequence_presents enumeration_retermination xs q \<longleftrightarrow>
    formed_enumeration_presents xs q"
  by (auto simp: composed_presentation_def formed_sequence_presents_iff
    enumeration_retermination_def data_list_term_injective)

lemma formed_enumeration_presentation_class:
  "presentation_class formed_enumeration_presents (\<lambda>xs. \<forall>x\<in>set xs. term_formed x)
    (\<lambda>q. \<exists>xs. formed_enumeration_presents xs q)"
proof -
  let ?A="\<lambda>q. (\<exists>ts. q=enumeration_term ts) \<and>
    (\<exists>p. (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs) \<and>
      enumeration_retermination p q)"
  have combined: "presentation_class (composed_presentation formed_sequence_presents enumeration_retermination)
      (\<lambda>xs. \<forall>x\<in>set xs. term_formed x) ?A"
    by (rule presentation_class_compose_on[OF formed_sequence_presentation_class enumeration_retermination_class]) blast
  have boundary: "?A q \<longleftrightarrow> (\<exists>xs. formed_enumeration_presents xs q)" for q
    using presentation_class.admissible_iff[OF combined, of q]
    by (simp only: formed_enumeration_composition)
  show ?thesis using combined
    by (simp only: presentation_class_def formed_enumeration_composition boundary)
qed

section \<open>A fold retains its seed and the whole input sequence\<close>

abbreviation term_seed_sequence_presents ::
  "(factor_term\<times>factor_term list) \<Rightarrow> (factor_term\<times>factor_term) \<Rightarrow> bool" where
  "term_seed_sequence_presents z p \<equiv>
    formed_term_presents (fst z) (fst p) \<and> formed_sequence_presents (snd z) (snd p)"

abbreviation term_seed_sequence_domain :: "(factor_term\<times>factor_term list) \<Rightarrow> bool" where
  "term_seed_sequence_domain z \<equiv> term_formed (fst z) \<and> (\<forall>x\<in>set (snd z). term_formed x)"

lemma term_seed_sequence_class:
  "presentation_class term_seed_sequence_presents term_seed_sequence_domain
    (\<lambda>p. \<exists>z. term_seed_sequence_presents z p)"
proof -
  have product: "presentation_class term_seed_sequence_presents term_seed_sequence_domain
      (\<lambda>p. term_formed (fst p) \<and>
        (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> snd p=data_list_term xs))"
    by (rule presentation_class_product[OF formed_term_presentation_class formed_sequence_presentation_class])
  have admission: "(\<lambda>p. term_formed (fst p) \<and>
      (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> snd p=data_list_term xs))=
      (\<lambda>p. \<exists>z. term_seed_sequence_presents z p)"
    by (rule ext; rule presentation_class.admissible_iff[OF product])
  show ?thesis using product by (simp only: admission)
qed

section \<open>A position belongs to its complete sequence\<close>

definition term_index_presents ::
  "(factor_term list\<times>nat) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_index_presents z p \<longleftrightarrow> snd z<length (fst z) \<and>
    factor_pair_presents formed_sequence_presents (\<lambda>n q. q=natural_data_term n) z p"

abbreviation term_index_domain :: "(factor_term list\<times>nat) \<Rightarrow> bool" where
  "term_index_domain z \<equiv> (\<forall>x\<in>set (fst z). term_formed x) \<and> snd z<length (fst z)"

lemma term_index_presentation_class:
  "presentation_class term_index_presents term_index_domain (\<lambda>p. \<exists>z. term_index_presents z p)"
proof -
  let ?R="factor_pair_presents formed_sequence_presents (\<lambda>n q. q=natural_data_term n)"
  have pairs: "presentation_class ?R (\<lambda>z. (\<forall>x\<in>set (fst z). term_formed x) \<and> True)
      (\<lambda>p. \<exists>a b. (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> a=data_list_term xs) \<and>
        (\<exists>n. b=natural_data_term n) \<and> p=Pair_Term a b)"
    by (rule factor_pair_class[OF formed_sequence_presentation_class natural_data_presentation_class])
  have restricted: "presentation_class (\<lambda>z p. term_index_domain z \<and> ?R z p)
      term_index_domain (\<lambda>p. \<exists>z. term_index_domain z \<and> ?R z p)"
    by (rule presentation_class_subdomain[OF pairs]) simp
  have reading: "(term_index_domain z \<and> ?R z p) \<longleftrightarrow> term_index_presents z p" for z p
    using presentation_class.subject_boundary[OF pairs, of z p] by (auto simp: term_index_presents_def)
  show ?thesis using restricted by (simp only: reading)
qed

lemma term_index_presents_iff:
  "term_index_presents (xs,n) p \<longleftrightarrow>
    (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and>
    p=Pair_Term (data_list_term xs) (natural_data_term n)"
  by (auto simp: term_index_presents_def factor_pair_presents_def formed_sequence_presents_iff)

text \<open>
  The element subject is the actual formed term. It may contain a target;
  self-containment is a stronger, separate boundary. Sequence identity retains
  order and repetitions. A position is paired with the entire sequence, and
  its domain excludes the end position and every larger index.

  Products and the existing sequence class account for these presentations.
  Fold operands use a mathematical pair of their two actual arguments; no
  extra stored wrapper is required. Literal output contracts below concern
  these term subjects. A different element notion with several presentations
  still needs its own output correspondence.
\<close>

end
