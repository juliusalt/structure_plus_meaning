theory Builtin_Investigation_Presentation
  imports Finite_Presented_Investigations Finite_Term_Words
    Factor_Investigation_Input_Investigation Factor_Observation_Collection_Investigation Factor_Observation_Investigation
    Factor_Observation_Scope_Investigation Factor_Observation_Table_Investigation Factor_Pair_Scope_Investigation
    Factor_Permission_Investigation Factor_Proof_Probe_Investigation Factor_Reasoning_Method_Investigation
    Factor_Schema_Socket_Investigation Factor_Substitution_Investigation Finite_Investigation_Interface
    Observation_Revision_Investigation Presentation_Completion_Investigation
begin

section \<open>A selection report keeps its basis, repairs, extension and revision\<close>

definition investigation_selection_report where
  "investigation_selection_report fs rows relation basis selected=(let B=basis selected;
    cs=map fst (fst (snd (snd B))); R=investigation_repairs cs fs selected rows relation
    in (selected,B,R,investigation_extend selected (fst (snd (snd R))),
      if fst B then Some (investigation_revision cs fs selected rows relation) else None))"

definition finite_investigation_selection_report_value where
  "finite_investigation_selection_report_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_investigation_basis_value (finite_pair_presentation finite_investigation_repairs_value
      (finite_pair_presentation finite_index_sequence_value (finite_option_presentation finite_investigation_revision_value))))"

definition finite_investigation_family_report_value where
  "finite_investigation_family_report_value=finite_pair_presentation (finite_sequence_presentation finite_index_triple_value)
    (finite_pair_presentation (finite_sequence_presentation finite_index_pair_value)
      (finite_sequence_presentation finite_investigation_selection_report_value))"

lemma finite_investigation_selection_values_injective [intro]:
  "inj finite_investigation_selection_report_value" "inj finite_investigation_family_report_value"
  unfolding finite_investigation_selection_report_value_def finite_investigation_family_report_value_def
  by (intro finite_pair_presentation_injective finite_index_values_injective finite_investigation_values_injective
      finite_option_presentation_injective finite_sequence_presentation_injective)+

section \<open>Every registered fixed investigation\<close>

definition builtin_investigation_kinds where
  "builtin_investigation_kinds=[
    ([0,1,2],reasoning_method_investigation_observations,reasoning_method_investigation_relation,
      reasoning_method_investigation),
    ([0,1],input_investigation_observations,input_investigation_relation,input_investigation),
    ([0,1,2,3],revision_investigation_observations,revision_investigation_relation,revision_investigation),
    ([0,1],table_investigation_observations,table_investigation_relation,table_investigation),
    ([0,1],pair_scope_investigation_observations,pair_scope_investigation_relation,pair_scope_investigation),
    ([0,1],collection_investigation_observations,collection_investigation_relation,collection_investigation),
    ([0,1],scope_investigation_observations,scope_investigation_relation,scope_investigation),
    ([0,1],observation_investigation_observations,observation_investigation_relation,observation_investigation),
    ([0,1,2],completion_investigation_observations,completion_investigation_relation,completion_investigation),
    ([0,1],permission_investigation_observations,permission_investigation_relation,permission_investigation),
    ([0,1],pattern_investigation_observations False,pattern_investigation_relation,pattern_investigation False),
    ([0,1],pattern_investigation_observations True,pattern_investigation_relation,pattern_investigation True),
    ([0,1,2],proof_probes_investigation_observations,proof_probes_investigation_relation,proof_probes_investigation),
    ([0,1,2],schema_sockets_investigation_observations,schema_sockets_investigation_relation,
      schema_sockets_investigation)]"

definition builtin_investigation_selections :: "nat list list list" where
  "builtin_investigation_selections=[[[],[0],[0,1,2],[0,1,2,0]],[[],[0],[0,1],[0,1,0]],
    [[],[0],[0,1,2,3],[0,1,2,3,0]],[[],[0],[0,1],[0,1,0]],[[],[0],[0,1],[0,1,0]],[[],[0],[0,1],[0,1,0]],
    [[],[0],[0,1],[0,1,0]],[[],[0],[0,1],[0,1,0]],[[],[0],[0,1,2],[0,1,2,0]],[[],[0],[0,1],[0,1,0]],
    [[],[0],[0,1],[0,1,0]],[[],[0],[0,1],[0,1,0]],[[],[0],[0,1,2],[0,1,2,0]],[[],[0],[0,1,2],[0,1,2,0]]]"

definition builtin_investigation_presented_report where
  "builtin_investigation_presented_report selections=map2 (\<lambda>(fs,rows,relation,basis) chosen.
    (rows,relation,map (investigation_selection_report fs rows relation basis) chosen))
    builtin_investigation_kinds selections"

definition builtin_investigation_report_value where
  "builtin_investigation_report_value selections=finite_sequence_presentation finite_investigation_family_report_value
    (builtin_investigation_presented_report selections)"

theorem builtin_investigation_report_word_exact:
  "finite_term_shared_word (builtin_investigation_report_value ss)=
    finite_term_shared_word (builtin_investigation_report_value ts) \<longleftrightarrow>
    builtin_investigation_presented_report ss=builtin_investigation_presented_report ts"
  by (simp add: finite_term_shared_word_injective builtin_investigation_report_value_def
      inj_eq[OF finite_sequence_presentation_injective[OF finite_investigation_selection_values_injective(2)]])

text \<open>
  Each registered fixed investigation keeps its observations and relation with
  every selection report: the selection, its basis, repairs, extension and, for a
  formed basis, the revision. The candidates are those of the basis profiles and
  the facets are the investigation's own. The two pattern investigations keep
  their distinct and collapsed presentations.
\<close>

end
