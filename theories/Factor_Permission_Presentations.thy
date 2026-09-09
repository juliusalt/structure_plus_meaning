theory Factor_Permission_Presentations
  imports Factor_Amendment_Values Factor_Continuation_Values Factor_Adoption_Values
    Factor_Judgment_Presentations Presentation_Observation_Contracts
begin

section \<open>The existing argument domains compose without additional fields\<close>

type_synonym adoption_context = "exact_target \<times> generation_core \<times> exact_target"
type_synonym current_frame_context = "judgment_context \<times> site_context"
type_synonym amendment_context = "current_frame_context \<times> generation_core \<times> exact_target"
type_synonym continuation_context =
  "selection_snapshot \<times> structural_transaction \<times> selection_snapshot \<times> site_context"

abbreviation site_context_presents :: "site_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "site_context_presents z t \<equiv> site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t"

abbreviation adoption_context_presents :: "adoption_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "adoption_context_presents \<equiv> factor_pair_presents target_value_presents
    (factor_pair_presents generation_value_presents target_value_presents)"

abbreviation adoption_context_formed :: "adoption_context \<Rightarrow> bool" where
  "adoption_context_formed z \<equiv>
    target_formed (fst z) \<and> generation_formed (fst (snd z)) \<and> target_formed (snd (snd z))"

abbreviation current_frame_context_presents :: "current_frame_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "current_frame_context_presents \<equiv> factor_pair_presents judgment_context_presents site_context_presents"

abbreviation current_frame_context_formed :: "current_frame_context \<Rightarrow> bool" where
  "current_frame_context_formed z \<equiv> judgment_context_formed (fst z) \<and> site_context_formed (snd z)"

abbreviation amendment_context_presents :: "amendment_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "amendment_context_presents \<equiv> factor_pair_presents current_frame_context_presents
    (factor_pair_presents generation_value_presents target_value_presents)"

abbreviation amendment_context_formed :: "amendment_context \<Rightarrow> bool" where
  "amendment_context_formed z \<equiv>
    current_frame_context_formed (fst z) \<and>
    generation_formed (fst (snd z)) \<and> target_formed (snd (snd z))"

abbreviation continuation_context_presents :: "continuation_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "continuation_context_presents \<equiv> factor_pair_presents snapshot_value_presents
    (factor_pair_presents transaction_value_presents
      (factor_pair_presents snapshot_value_presents site_context_presents))"

abbreviation continuation_context_formed :: "continuation_context \<Rightarrow> bool" where
  "continuation_context_formed z \<equiv> snapshot_formed (fst z) \<and>
    transaction_formed (fst (snd z)) \<and> snapshot_formed (fst (snd (snd z))) \<and>
    site_context_formed (snd (snd (snd z)))"

lemma adoption_context_fields:
  "adoption_context_presents (A,G,p) t \<longleftrightarrow> adoption_value_presents A G p t"
  by (auto simp: factor_pair_presents_def adoption_value_presents_def)

lemma current_frame_context_fields:
  "current_frame_context_presents ((E,((pu,pr),(au,ar))),(F,(v,r))) t \<longleftrightarrow>
    current_frame_value_presents E pu pr au ar F v r t"
  by (auto simp: factor_pair_presents_def current_frame_value_presents_def)

lemma amendment_context_fields:
  "amendment_context_presents (((E,((pu,pr),(au,ar))),(F,(v,r))),G,c) t \<longleftrightarrow>
    amendment_value_presents E pu pr au ar F v r G c t"
  by (auto simp: factor_pair_presents_def current_frame_value_presents_def amendment_value_presents_def)

lemma continuation_context_fields:
  "continuation_context_presents (S,T,U,(C,(cu,cr))) t \<longleftrightarrow>
    continuation_value_presents S T U C cu cr t"
  by (auto simp: factor_pair_presents_def continuation_value_presents_def)

theorem adoption_context_presentation_class:
  "presentation_class adoption_context_presents adoption_context_formed
    (\<lambda>t. \<exists>z. adoption_context_presents z t)"
  by (rule presentation_class_reading_admission[OF factor_pair_class[OF target_value_presentation_class
    factor_pair_class[OF generation_value_presentation_class target_value_presentation_class]]])

theorem current_frame_context_presentation_class:
  "presentation_class current_frame_context_presents current_frame_context_formed
    (\<lambda>t. \<exists>z. current_frame_context_presents z t)"
  by (rule presentation_class_reading_admission[OF factor_pair_class[OF judgment_context_presentation_class
    site_presentations.presentation_class_axioms]])

theorem amendment_context_presentation_class:
  "presentation_class amendment_context_presents amendment_context_formed
    (\<lambda>t. \<exists>z. amendment_context_presents z t)"
  by (rule presentation_class_reading_admission[OF factor_pair_class[OF current_frame_context_presentation_class
    factor_pair_class[OF generation_value_presentation_class target_value_presentation_class]]])

theorem continuation_context_presentation_class:
  "presentation_class continuation_context_presents continuation_context_formed
    (\<lambda>t. \<exists>z. continuation_context_presents z t)"
  by (rule presentation_class_reading_admission[OF factor_pair_class[OF snapshot_value_presentation_class
    factor_pair_class[OF transaction_value_presentation_class
      factor_pair_class[OF snapshot_value_presentation_class site_presentations.presentation_class_axioms]]]])

lemma adoption_context_value_formed:
  "adoption_context_presents z t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  using adoption_value_presents_formed
  by (cases z; auto simp: adoption_context_fields split: prod.splits)

lemma current_frame_context_value_formed:
  "current_frame_context_presents z t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  using current_frame_value_presents_formed
  by (cases z; auto simp: current_frame_context_fields split: prod.splits)

lemma amendment_context_value_formed:
  "amendment_context_presents z t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  using amendment_value_presents_formed
  by (cases z; auto simp: amendment_context_fields split: prod.splits)

lemma continuation_context_value_formed:
  "continuation_context_presents z t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  using continuation_value_presents_formed
  by (cases z; auto simp: continuation_context_fields split: prod.splits)

text \<open>
  These products are the already supplied complete arguments. The equations
  identify them with the original value relations, and the existing component
  classes supply coverage and recovery. A current frame retains both actual
  scopes; an amendment adds its candidate and certificate; continuation keeps
  its independent before, transaction, claimed after, and submitted site.

  No derived program, authority, currentness, transaction outcome, permission,
  or evidence validity is stored again. The type synonyms provide mathematical
  argument grouping. They introduce neither a new native grammar nor a
  general datatype of notions.
\<close>

end
