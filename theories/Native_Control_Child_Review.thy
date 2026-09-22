theory Native_Control_Child_Review
  imports Native_Control_Selected_Root Certificate_Construction_Review
    Material_Application_Observations Native_Control_Quotation_Code Finite_Presented_Enumeration
begin

type_synonym natural_child_call = "nat \<times> finite_factor_term"
type_synonym natural_child_proofs = "(natural_child_call \<times> (nat,nat,nat) finite_schema_proof) fset"
type_synonym child_schema_subject = "finite_natural_application \<times> nat \<times> nat \<times>
  finite_factor_term \<times> nat \<times> (nat,nat,nat) finite_factor_schema"
type_synonym child_application_prepared = "child_schema_subject \<times>
  ((nat,nat) finite_schema_observation_site \<times> finite_factor_term) fset \<times>
  ((conditional_application_method \<times> conditional_application_facet) \<times> bool) list"

definition cause_child_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "cause_child_program=finite_guard_constructor checked_judgment_rows"

definition cause_child_occurrences :: "finite_natural_application fset \<Rightarrow>
    (finite_natural_application \<times> nat \<times> natural_child_call) fset" where
  "cause_child_occurrences A=ffUnion (fimage (\<lambda>a. case a of (t,V,H) \<Rightarrow>
    fimage (\<lambda>h. (a,h)) H) A)"

lemma cause_child_occurrences_exact:
  "((t,V,H),s,d,x) |\<in>| cause_child_occurrences A \<longleftrightarrow>
    (t,V,H) |\<in>| A \<and> (s,d,x) |\<in>| H"
  by (auto simp: cause_child_occurrences_def finite_union_image_member finite_image_member
    split: prod.splits; force)

ML \<open>val _ = (writeln "cause_child_occurrences_exact_JOIN_BEGIN";
 Thm.consolidate @{thms cause_child_occurrences_exact}; writeln "cause_child_occurrences_exact_JOIN_END");\<close>

definition cause_child_occurrence_value where
  "cause_child_occurrence_value=finite_pair_presentation finite_natural_application_value
    finite_natural_premise_value"

lemma cause_child_occurrence_value_injective: "inj cause_child_occurrence_value"
  unfolding cause_child_occurrence_value_def
  by (intro finite_pair_presentation_injective finite_reasoning_values_injective)

definition cause_child_clause_value where
  "cause_child_clause_value=finite_pair_presentation
    (finite_pair_presentation finite_natural_data finite_natural_data) finite_natural_schema_value"

lemma cause_child_clause_value_injective: "inj cause_child_clause_value"
  unfolding cause_child_clause_value_def
  by (intro finite_pair_presentation_injective finite_natural_data_injective finite_reasoning_values_injective)

definition cause_child_demands :: "finite_natural_application fset \<Rightarrow> natural_child_call fset list" where
  "cause_child_demands A = map (\<lambda>(t,V,H). fimage snd H)
      (finite_presented_enumeration finite_natural_application_value A) @
    map (\<lambda>(a,s,d,x). {|(d,x)|})
      (finite_presented_enumeration cause_child_occurrence_value (cause_child_occurrences A))"

definition cause_certificate_methods where
  "cause_certificate_methods=[Head_Proof_Closure,Head_Proof_Round,Unchecked_Leaves]"
definition cause_certificate_facets where
  "cause_certificate_facets=[Requested_Certificates,Checked_Certificates]"

definition cause_certificate_results :: "natural_child_call fset \<Rightarrow> natural_child_proofs option list" where
  "cause_certificate_results D=certificate_constructor_family cause_certificate_methods cause_child_program D"

definition cause_certificate_prepare where
  "cause_certificate_prepare D=(let results=cause_certificate_results D in
    (D,results,prepare_faceted_observations results cause_certificate_facets
      (certificate_observation cause_child_program D)))"

definition cause_certificate_question where
  "cause_certificate_question prepared results facets=(case prepared of (D,originals,cache) \<Rightarrow>
    prepared_faceted_question (certificate_observation cause_child_program D) cache results facets)"

lemma cause_certificate_question_exact:
  "cause_certificate_question (cause_certificate_prepare D) results facets=
    certificate_result_question cause_child_program D results facets"
  by (simp only: cause_certificate_question_def cause_certificate_prepare_def Let_def prod.case
    prepared_faceted_question_exact certificate_result_question_def)

definition cause_certificate_choice where
  "cause_certificate_choice prepared results facets report =
    keyed_admitted_choice (first_occurrence_key results) results (cause_certificate_question prepared results facets) report"

lemma cause_certificate_choice_exact:
  "cause_certificate_choice (cause_certificate_prepare D) results facets report=
    certificate_result_choice cause_child_program D results facets report"
  by (simp only: cause_certificate_choice_def cause_certificate_question_exact certificate_result_choice_def)

definition cause_certificate_profiles where
  "cause_certificate_profiles prepared=(case prepared of (D,results,cache) \<Rightarrow>
    map (\<lambda>result. map (prepared_faceted_observation (certificate_observation cause_child_program D)
      cache result) cause_certificate_facets) results)"

definition cause_certificate_scopes where
  "cause_certificate_scopes results=[(results,cause_certificate_facets),
    (rev results,cause_certificate_facets),(results@results,cause_certificate_facets),
    (results,[Requested_Certificates]),(results,[Checked_Certificates]),([],cause_certificate_facets)]"

definition cause_certificate_prepare_family where
  "cause_certificate_prepare_family Ds=Parallel.map cause_certificate_prepare Ds"

lemma cause_certificate_prepare_family_exact:
  "cause_certificate_prepare_family Ds=map cause_certificate_prepare Ds"
  by (simp only: cause_certificate_prepare_family_def Parallel.map_def)

definition cause_child_schema_subjects :: "finite_natural_application fset \<Rightarrow>
    (finite_natural_application \<times> nat \<times> nat \<times> finite_factor_term \<times> nat \<times>
      (nat,nat,nat) finite_factor_schema) list" where
  "cause_child_schema_subjects A=concat (map (\<lambda>(a,s,d,x).
    map (\<lambda>((e,c),S). (a,s,d,x,c,S))
      (finite_presented_enumeration cause_child_clause_value
        (ffilter (\<lambda>((e,c),S). e=d) (finite_system_clauses cause_child_program))))
      (finite_presented_enumeration cause_child_occurrence_value (cause_child_occurrences A)))"

lemma cause_child_schema_subjects_exact:
  "(a,s,d,x,c,S)\<in>set (cause_child_schema_subjects A) \<longleftrightarrow>
    (a,s,d,x) |\<in>| cause_child_occurrences A \<and> ((d,c),S) |\<in>| finite_system_clauses cause_child_program"
proof
  assume member: "(a,s,d,x,c,S)\<in>set (cause_child_schema_subjects A)"
  show "(a,s,d,x) |\<in>| cause_child_occurrences A \<and> ((d,c),S) |\<in>| finite_system_clauses cause_child_program"
    using member by (auto simp: cause_child_schema_subjects_def
      finite_presented_enumeration_exact[OF cause_child_clause_value_injective]
      finite_presented_enumeration_exact[OF cause_child_occurrence_value_injective] split: prod.splits)
next
  assume fields: "(a,s,d,x) |\<in>| cause_child_occurrences A \<and>
    ((d,c),S) |\<in>| finite_system_clauses cause_child_program"
  let ?occurrences="finite_presented_enumeration cause_child_occurrence_value (cause_child_occurrences A)"
  let ?clauses="finite_presented_enumeration cause_child_clause_value
    (ffilter (\<lambda>((e,c),S). e=d) (finite_system_clauses cause_child_program))"
  let ?rows="map (\<lambda>((e,c),S). (a,s,d,x,c,S)) ?clauses"
  let ?expand="\<lambda>(a,s,d,x). map (\<lambda>((e,c),S). (a,s,d,x,c,S))
    (finite_presented_enumeration cause_child_clause_value
      (ffilter (\<lambda>((e,c),S). e=d) (finite_system_clauses cause_child_program)))"
  have occurrence: "(a,s,d,x)\<in>set ?occurrences"
    using fields by (simp only: finite_presented_enumeration_exact[OF cause_child_occurrence_value_injective])
  have clause: "((d,c),S)\<in>set ?clauses"
    using fields by (simp add: finite_presented_enumeration_exact[OF cause_child_clause_value_injective])
  have row: "(a,s,d,x,c,S)\<in>set ?rows"
    using imageI[OF clause, of "\<lambda>((e,c),S). (a,s,d,x,c,S)"]
    by (simp only: set_map prod.case)
  have family: "?rows\<in>set (map ?expand ?occurrences)"
    using imageI[OF occurrence, of ?expand] by (simp only: set_map prod.case)
  show "(a,s,d,x,c,S)\<in>set (cause_child_schema_subjects A)"
    unfolding cause_child_schema_subjects_def
    using row family by (simp only: set_concat) blast
qed

ML \<open>val _ = (writeln "cause_child_schema_subjects_exact_JOIN_BEGIN";
 Thm.consolidate @{thms cause_child_schema_subjects_exact}; writeln "cause_child_schema_subjects_exact_JOIN_END");\<close>

definition cause_child_application_prepare :: "child_schema_subject \<Rightarrow> child_application_prepared" where
  "cause_child_application_prepare subject=(case subject of (a,s,d,x,c,S) \<Rightarrow>
    let obs=finite_head_material_observations S x in
    (subject,obs,prepare_faceted_observations cause_root_methods cause_root_facets
      (conditional_application_observation S x obs)))"

definition cause_child_application_question where
  "cause_child_application_question (prepared :: child_application_prepared) methods facets=(case prepared of ((a,s,d,x,c,S),obs,cache) \<Rightarrow>
    prepared_faceted_question (conditional_application_observation S x obs) cache methods facets)"

lemma cause_child_application_question_exact:
  "cause_child_application_question (cause_child_application_prepare (a,s,d,x,c,S)) methods facets =
    faceted_native_question methods facets
      (conditional_application_observation S x (finite_head_material_observations S x))"
  by (simp only: cause_child_application_question_def cause_child_application_prepare_def
    Let_def prod.case prepared_faceted_question_exact)

definition cause_child_application_choice where
  "cause_child_application_choice prepared methods facets report=
    keyed_admitted_choice (first_occurrence_key methods) methods
    (cause_child_application_question prepared methods facets) report"

theorem cause_child_application_choice_original:
  assumes chosen: "cause_child_application_choice (cause_child_application_prepare (a,s,d,x,c,S))
      methods facets report=Some m"
    and facet: "f\<in>set facets"
  shows "conditional_application_requirement S x (finite_head_material_observations S x) m f"
  by (rule conditional_application_admitted[OF _ facet])
    (use chosen in \<open>simp only: cause_child_application_choice_def cause_child_application_question_exact\<close>)

definition cause_child_application_profiles where
  "cause_child_application_profiles (prepared :: child_application_prepared)=(case prepared of ((a,s,d,x,c,S),obs,cache) \<Rightarrow>
    (s,d,c,sorted_list_of_fset (finite_schema_head_missing S),
      map (\<lambda>m. map (prepared_faceted_observation (conditional_application_observation S x obs)
        cache m) cause_root_facets) cause_root_methods))"

definition cause_child_application_prepare_family :: "child_schema_subject list \<Rightarrow> _" where
  "cause_child_application_prepare_family subjects=Parallel.map cause_child_application_prepare subjects"

definition cause_child_proof_summary :: "natural_child_proofs option option \<Rightarrow> nat option option" where
  "cause_child_proof_summary=map_option (map_option fcard)"

definition cause_child_proofs_value :: "natural_child_proofs \<Rightarrow> finite_factor_term" where
  "cause_child_proofs_value=finite_collection_presentation
    (finite_pair_presentation (finite_pair_presentation finite_natural_data id)
      (finite_proof_value finite_natural_data
        (finite_pair_presentation finite_natural_data id) finite_natural_data))"

lemma cause_child_proofs_value_injective: "inj cause_child_proofs_value"
  unfolding cause_child_proofs_value_def
  by (intro finite_collection_presentation_injective finite_pair_presentation_injective
    finite_proof_value_injective finite_natural_data_injective inj_on_id)

definition cause_child_proof_choices_value where
  "cause_child_proof_choices_value=finite_sequence_presentation
    (finite_option_presentation (finite_option_presentation cause_child_proofs_value))"

lemma cause_child_proof_choices_value_injective: "inj cause_child_proof_choices_value"
  unfolding cause_child_proof_choices_value_def
  by (intro finite_sequence_presentation_injective finite_option_presentation_injective
    cause_child_proofs_value_injective)

export_code cause_child_program cause_child_occurrences cause_child_demands cause_child_schema_subjects
  cause_certificate_prepare_family cause_certificate_question cause_certificate_choice
  cause_certificate_profiles cause_certificate_scopes cause_certificate_facets
  cause_child_application_prepare_family cause_child_application_question cause_child_application_choice
  cause_child_application_profiles cause_child_proof_summary cause_child_proof_choices_value
  cause_root_apply_prepared
  native_cause_root_family cause_root_results_value cause_root_results_summary
  cause_root_subject cause_root_prepare cause_root_prepared_question cause_root_methods cause_root_facets
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Child_Review file_prefix "native_control_child_review"

text \<open>Every child occurrence comes from a retained whole root application;
  equal calls at different sockets remain different occurrences. Full root demand
  questions and individual leaf questions are separate. A leaf result cannot
  discharge its siblings. Every clause comes from the original constructed target.
  These natural-coordinate certificates still require the actual installed source,
  full coordinate transport, original replay and certified policy cause.\<close>

end
