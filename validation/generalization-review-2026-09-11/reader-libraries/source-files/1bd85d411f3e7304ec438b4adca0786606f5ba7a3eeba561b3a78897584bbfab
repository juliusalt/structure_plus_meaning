theory Factor_Investigation_Input_Presentations
  imports Factor_Observation_Scope_Admission
begin

section \<open>The complete comparison is supplied beside the original declared scope\<close>

definition investigation_input_subject_formed where
  "investigation_input_subject_formed C U F T R \<longleftrightarrow>
    observation_scope_subject_formed C U F T \<and> data_pair_finite_set_domain R"

abbreviation investigation_input_presents where
  "investigation_input_presents \<equiv> factor_pair_presents observation_scope_presents data_pair_finite_set_presents"

abbreviation investigation_input_domain where
  "investigation_input_domain z \<equiv> observation_scope_domain (fst z) \<and> data_pair_finite_set_domain (snd z)"

lemma investigation_input_class:
  "presentation_class investigation_input_presents investigation_input_domain
    (\<lambda>p. \<exists>z. investigation_input_presents z p)"
  by (rule presentation_class.recovered_admission[OF factor_pair_class[OF observation_scope_class data_pair_finite_set_class]])

abbreviation investigation_input_record_presents where
  "investigation_input_record_presents \<equiv> factor_pair_presents observation_scope_record_presents data_pair_finite_set_presents"

abbreviation investigation_input_record_domain where
  "investigation_input_record_domain z \<equiv> observation_scope_record_domain (fst z) \<and> data_pair_finite_set_domain (snd z)"

lemma investigation_input_record_class:
  "presentation_class investigation_input_record_presents investigation_input_record_domain
    (\<lambda>p. \<exists>z. investigation_input_record_presents z p)"
  by (rule presentation_class.recovered_admission[OF factor_pair_class[OF observation_scope_record_class data_pair_finite_set_class]])

lemma investigation_input_restriction:
  "investigation_input_presents z p \<longleftrightarrow>
    investigation_input_domain z \<and> investigation_input_record_presents z p"
proof -
  have boundary: "investigation_input_presents z p \<Longrightarrow> investigation_input_domain z"
    by (rule presentation_class.subject_boundary[OF investigation_input_class])
  show ?thesis using boundary by (auto simp only: factor_pair_presents_def; blast)
qed

lemma investigation_input_subject_lists:
  "investigation_input_subject_formed (fset_of_list C) (fset_of_list U) (fset_of_list F)
      (fset_of_list rows) (fset_of_list relation) \<longleftrightarrow>
    observation_scope_subject_formed (fset_of_list C) (fset_of_list U) (fset_of_list F) (fset_of_list rows) \<and>
    (\<forall>(c,d)\<in>set relation. data_elements [c,d])"
  by (simp only: investigation_input_subject_formed_def fset_of_list.rep_eq)

text \<open>
  The independent input retains the original candidate, available-facet,
  selected-facet, and observation-table scope, together with the complete
  finite comparison relation. Its pair class is the existing complete class
  of pairs of data terms. Endpoint roles come from their positions; the class
  does not require either endpoint to belong to the declared candidate set.
  All displayed rows remain part of the input, including rows outside that
  set. Evaluation subsequently consults the comparison at candidate pairs.
\<close>

end
