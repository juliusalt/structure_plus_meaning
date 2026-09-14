theory Finite_Investigation_Readiness
  imports Finite_Investigation_Interface
begin

definition investigation_ready where
  "investigation_ready cs fs selected rows relation=(let
    report=investigation_basis cs fs selected rows relation
    in fst report \<and> fst (snd report)=[])"

theorem investigation_ready_exact:
  "investigation_ready cs fs selected rows relation \<longleftrightarrow>
    finite_observation_table_formed (fset_of_list cs) (fset_of_list fs) (fset_of_list rows) \<and>
    set selected\<subseteq>set fs \<and>
    comparison_basis (set cs) (\<lambda>c d. (c,d)\<in>set relation) (set selected)
      (finite_table_observations (fset_of_list rows))"
proof -
  have empty: "fst (snd (investigation_basis cs fs selected rows relation))=[] \<longleftrightarrow>
    finite_basis_residual (fset_of_list cs) (fset_of_list selected) (fset_of_list rows)
      (\<lambda>c d. (c,d)\<in>set relation)={||}"
    using investigation_basis_residual[of cs fs selected rows relation]
    by (simp only: fset_inject[symmetric]; auto)
  show ?thesis
    by (simp only: investigation_ready_def Let_def investigation_basis_formation empty
      finite_basis_residual_empty fset_of_list.rep_eq conj_assoc)
qed

definition investigation_revised_ready where
  "investigation_revised_ready cs fs selected rows relation=investigation_ready cs fs
    (fst (snd (snd (snd (investigation_revision cs fs selected rows relation))))) rows relation"

theorem investigation_revised_ready_exact:
  "investigation_revised_ready cs fs selected rows relation \<longleftrightarrow>
    finite_observation_table_formed (fset_of_list cs) (fset_of_list fs) (fset_of_list rows) \<and>
    comparison_failures (set cs) (\<lambda>c d. (c,d)\<in>set relation)
      (sound_observation_facets (set cs) (\<lambda>c d. (c,d)\<in>set relation)
        (set fs) (finite_table_observations (fset_of_list rows)))
      (finite_table_observations (fset_of_list rows))={}"
proof -
  let ?R="\<lambda>c d. (c,d)\<in>set relation"
  let ?O="finite_table_observations (fset_of_list rows)"
  have bound: "revised_observation_selection (set cs) ?R (set fs) (set selected) ?O\<subseteq>set fs"
    using revised_observation_selection_bounds(2)[of "set cs" ?R "set fs" "set selected" ?O]
    by (auto simp: sound_observation_facets_def)
  show ?thesis
    by (simp only: investigation_revised_ready_def investigation_ready_exact
      investigation_revision_selection bound
      revision_is_adequate_exactly_when_the_sound_language_is_adequate simp_thms)
qed

theorem investigation_revised_ready_cong:
  assumes rows: "set rows=set other_rows" and relation: "set relation=set other_relation"
  shows "investigation_revised_ready cs fs selected rows relation=
    investigation_revised_ready cs fs other_selected other_rows other_relation"
proof -
  have tables: "fset_of_list rows=fset_of_list other_rows"
    using rows by (simp only: fset_inject[symmetric] fset_of_list.rep_eq)
  show ?thesis by (simp only: investigation_revised_ready_exact tables relation)
qed

text \<open>
  Readiness means a formed comparison with no residual. After native revision,
  it depends exactly on the complete input table and the remaining failures of
  its full sound language. Different row enumerations and original selections
  preserve this verdict under the stated complete-set correspondence. The
  original selection's availability can be required separately by a workflow.
\<close>

end
