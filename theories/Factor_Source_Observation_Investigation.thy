theory Factor_Source_Observation_Investigation
  imports Factor_Finite_Source_Observations Factor_Requirement_Source_Examples_Base Finite_Observation_Contracts
begin

section \<open>Missing and altered source fields are concrete investigation subjects\<close>

definition source_example_subject :: "nat \<Rightarrow> local_address option finite_source_subject" where
  "source_example_subject c=(let P=finite_guard_source_program False;
    Q=(if c=1 then P\<lparr>finite_system_interfaces:={|((None,[1]),Finite_Pattern_Payload [])|}\<rparr>
      else if c=2 then P\<lparr>finite_system_clauses:={||}\<rparr>
      else if c=3 then P\<lparr>finite_system_interfaces:=finsert ((Some [],[]),Finite_Variable []) (finite_system_interfaces P)\<rparr>
      else if c=4 \<or> c=5 then finite_guard_source_program True else P);
    E=(if c=6 then \<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>
      else finite_guard_source (c=5))
    in (E,None,[0],Q))"

definition source_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "source_investigation_observations=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,if finite_source_observation f (source_example_subject c) then 1 else 0)) [0,1,2,3])
      [0,1,2,3,4,5,6])"

definition source_investigation_relation :: "(nat\<times>nat) list" where
  "source_investigation_relation=filter (\<lambda>(c,d).
    finite_source_subject_matches (source_example_subject c)=finite_source_subject_matches (source_example_subject d))
      (investigation_pairs [0,1,2,3,4,5,6])"

lemma source_investigation_relation_exact:
  "(c,d)\<in>set source_investigation_relation \<longleftrightarrow>
    c\<in>{0,1,2,3,4,5,6} \<and> d\<in>{0,1,2,3,4,5,6} \<and>
    native_source_subject_matches (source_example_subject c)=native_source_subject_matches (source_example_subject d)"
  by (simp only: source_investigation_relation_def set_filter investigation_pairs_exact
    mem_Collect_eq case_prod_conv list.set finite_source_subject_matches_correct; blast)

definition source_investigation where
  "source_investigation selected=investigation_basis [0,1,2,3,4,5,6] [0,1,2,3] selected
    source_investigation_observations source_investigation_relation"

definition source_candidate_subjects where
  "source_candidate_subjects=fimage (\<lambda>c. (c,source_example_subject c)) {|0::nat,1,2,3,4,5,6|}"

definition source_operation_subjects :: "(nat\<times>(local_address option finite_source_subject\<Rightarrow>bool)) fset" where
  "source_operation_subjects=fimage (\<lambda>f. (f,native_source_observation f)) {|0::nat,1,2,3|}"

definition source_value_subjects where
  "source_value_subjects=fimage (\<lambda>w. (w,w=1)) {|0::nat,1|}"

lemma source_subject_maps_formed:
  "finite_observation_subjects_formed source_candidate_subjects source_operation_subjects source_value_subjects"
  unfolding source_candidate_subjects_def source_operation_subjects_def source_value_subjects_def
  by (rule finite_observation_function_graphs_formed)

lemma source_observations_derived:
  "fset_of_list source_investigation_observations=
    finite_derived_observations source_candidate_subjects source_operation_subjects
      source_value_subjects (\<lambda>operation subject value. value=operation subject)"
  unfolding source_candidate_subjects_def source_operation_subjects_def source_value_subjects_def
  apply (rule finite_table_derived_from_function_graphs)
  by (simp only: fset_of_list.rep_eq source_investigation_observations_def indexed_value_rows_member
    finite_source_observation_correct; auto split: if_splits)

theorem source_observation_at_subject:
  assumes "(c,subject) |\<in>| source_candidate_subjects"
    "(f,operation) |\<in>| source_operation_subjects"
    "(w,value) |\<in>| source_value_subjects"
  shows "(f,c,w)\<in>set source_investigation_observations \<longleftrightarrow> value=operation subject"
  using finite_derived_observation_at_subject[OF source_subject_maps_formed assms,
    where P="\<lambda>operation subject value. value=operation subject"]
  by (simp only: source_observations_derived[symmetric] fset_of_list.rep_eq)

theorem source_comparison_at_subject:
  assumes "(c,subject) |\<in>| source_candidate_subjects"
    "(d,other) |\<in>| source_candidate_subjects"
  shows "(c,d)\<in>set source_investigation_relation \<longleftrightarrow>
    native_source_subject_matches subject=native_source_subject_matches other"
  using assms by (auto simp: source_candidate_subjects_def fimage.rep_eq source_investigation_relation_exact)

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm source_investigation_def},
   equation = @{thm source_observations_derived},
   formation = @{thm source_subject_maps_formed},
   observation = @{thm source_observation_at_subject},
   comparison = @{thm source_comparison_at_subject}}\<close>

definition source_example_report where
  "source_example_report c=(let X=source_example_subject c in
    (X,case X of (E,u,r,P) \<Rightarrow> (finite_native_package_readings E u r,
      finite_source_subject_matches X,map (\<lambda>f. (f,finite_source_observation f X)) [0,1,2,3])))"

lemma source_example_report_subject [simp]:
  "fst (source_example_report c)=source_example_subject c"
  by (simp add: source_example_report_def Let_def)

text \<open>
  The seven subjects include the actual source, an altered interface, missing
  clauses, an extra definition, a changed clause at the same source site, the
  corresponding different actual source, and an absent source. Candidate and
  operation indices are connected to those complete inputs by functional maps.
  The comparison groups subjects by their independently stated native reading
  condition. It therefore criticizes observations that distinguish negative
  inputs without helping to determine that condition, as well as missed source
  mismatches. The computed revisions concern this scope; the whole observation's
  universal source equation is established separately.

  The separate field profile distinguishes some rejected inputs from each
  other. Its failure at this truth comparison does not show that the conjunction
  of complete interface and clause equality is insufficient. The whole
  observation computes exactly that conjunction on each recovered program.
\<close>

end
