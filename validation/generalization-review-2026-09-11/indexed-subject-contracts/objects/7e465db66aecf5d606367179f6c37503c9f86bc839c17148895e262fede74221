theory Factor_Program_Entry_Presentations
  imports Factor_Program_Entry_Values Factor_Judgment_Presentations
begin

type_synonym program_entry_context = "site_context \<times> local_address option definition_site"

abbreviation program_entry_presents :: "program_entry_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "program_entry_presents z p \<equiv> program_entry_value_presents (fst (fst z))
    (fst (snd (fst z))) (snd (snd (fst z))) (snd z) p"

definition program_entry_context_formed :: "program_entry_context \<Rightarrow> bool" where
  "program_entry_context_formed z \<longleftrightarrow>
    site_context_formed (fst z) \<and> snd z\<in>environment_positions (fst (fst z))"

theorem program_entry_presentation_class:
  "presentation_class program_entry_presents program_entry_context_formed
    (\<lambda>p. \<exists>z. program_entry_presents z p)"
proof -
  let ?site="\<lambda>z p. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) p"
  let ?R="factor_pair_presents ?site site_coordinate_presents"
  let ?A="\<lambda>p. \<exists>s d. (\<exists>E u r. site_value_presents E u r s) \<and>
    (\<exists>q. site_coordinate_presents q d) \<and> p=Pair_Term s d"
  have raw: "presentation_class ?R (\<lambda>z. site_context_formed (fst z)) ?A"
    using factor_pair_class[OF site_presentations.presentation_class_axioms site_coordinate_presentation] by simp
  have constrained: "presentation_class (\<lambda>z p. program_entry_context_formed z \<and> ?R z p)
      program_entry_context_formed (\<lambda>p. \<exists>z. program_entry_context_formed z \<and> ?R z p)"
    by (rule presentation_class_subdomain[OF raw]) (simp add: program_entry_context_formed_def)
  have reading: "program_entry_presents=(\<lambda>z p. program_entry_context_formed z \<and> ?R z p)"
    by (intro ext) (auto simp: program_entry_value_presents_def program_entry_context_formed_def
      factor_pair_presents_def site_value_presents_def dest: environment_value_presents_formed)
  have point: "program_entry_presents z p \<longleftrightarrow> program_entry_context_formed z \<and> ?R z p" for z p
    using fun_cong[OF fun_cong[OF reading, of z], of p] .
  have admission: "(\<lambda>p. \<exists>z. program_entry_context_formed z \<and> ?R z p)=
    (\<lambda>p. \<exists>z. program_entry_presents z p)"
    by (intro ext; simp only: point)
  show ?thesis using constrained by (simp only: reading[symmetric] admission)
qed

interpretation program_entries: presentation_class program_entry_presents program_entry_context_formed
  "\<lambda>p. \<exists>z. program_entry_presents z p"
  by (rule program_entry_presentation_class)

lemma program_entry_presents_fields:
  "program_entry_presents ((E,(u,r)),d) p \<longleftrightarrow>
    (u,r)\<in>environment_positions E \<and> d\<in>environment_positions E \<and>
    (\<exists>e. environment_value_presents E e \<and>
      p=Pair_Term (Pair_Term e (site_data_term u r)) (site_data_term (fst d) (snd d)))"
  by (auto simp: program_entry_value_presents_def site_value_presents_def)

text \<open>
  The existing program-entry value is a product of the complete site class and
  one literal site coordinate, restricted by actual occurrence in the same
  environment. The context contains no stored program or semantic judgment.
  Native package membership and later permission constraints specialize this
  complete class without changing the underlying scope or either site.
\<close>

end
