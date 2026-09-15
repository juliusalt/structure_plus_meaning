theory RRA_Lookup_Generation_Checking
  imports RRA_Lookup_Generation_Fields RRA_Finite_Generation_Construction
begin

definition lookup_generation_child_rows where
  "lookup_generation_child_rows locations u M checks=ffUnion (fimage (\<lambda>(G,check).
    fimage (\<lambda>(s,d). (s,G)) (ffilter (\<lambda>(s,d).
      fBex (locations u d) (\<lambda>(v,a). check v a)) M)) checks)"

lemma lookup_generation_child_rows_member:
  "(s,G) |\<in>| lookup_generation_child_rows locations u M (fimage (\<lambda>H. (H,check H)) P) \<longleftrightarrow>
    G |\<in>| P \<and> (\<exists>d. (s,d) |\<in>| M \<and>
      (\<exists>v a. (v,a) |\<in>| locations u d \<and> check G v a))"
  by (auto simp: lookup_generation_child_rows_def finite_union_image_member
    finite_image_member split_paired_Ex split: prod.splits; force)

function (sequential) lookup_check_generation :: "finite_generation\<Rightarrow>
    (local_address option\<Rightarrow>finite_exact_artifact fset)\<Rightarrow>
    (local_address option\<Rightarrow>local_address\<Rightarrow>local_address option fset)\<Rightarrow>
    local_address option\<Rightarrow>local_address\<Rightarrow>bool" where
  "lookup_check_generation (Generation l P p c) artifacts bindings u r=
    fBex (lookup_generation_field_readings artifacts bindings u r) (\<lambda>(l',M,p',c').
      l=l' \<and> p=p' \<and> c=c' \<and>
      finite_bijective_relation (fimage fst M) P
        (lookup_generation_child_rows (lookup_located_values artifacts bindings) u M
          (fimage (\<lambda>H. (H,lookup_check_generation H artifacts bindings)) P)))"
  by pat_completeness auto

termination
  apply (relation "measure (size \<circ> fst)")
   apply (rule wf_measure)
  apply (simp only: in_measure comp_apply fst_conv)
  apply (rule predecessor_size_decreases)
  apply (simp add: predecessor_edges_def)
  done

definition lookup_generation_record_ready where
  "lookup_generation_record_ready artifacts bindings l p c rows=
    (finite_target_formed l \<and> finite_target_formed p \<and> finite_target_formed c \<and>
      distinct (map snd rows) \<and> list_all (\<lambda>(d,G).
        lookup_check_generation G artifacts bindings (fst d) (snd d)) rows)"

context environment_lookup_reading
begin

theorem generation_check_exact:
  assumes formed: "finite_environment_formed E"
  shows "lookup_check_generation G artifacts bindings u r=finite_check_generation G E u r"
proof (induction G arbitrary: u r)
  case (Generation l P p c)
  have recursive: "lookup_check_generation H artifacts bindings v a=finite_check_generation H E v a"
    if "H |\<in>| P" for H v a using Generation.IH that by blast
  have rows: "lookup_generation_child_rows (lookup_located_values artifacts bindings) u M
      (fimage (\<lambda>H. (H,lookup_check_generation H artifacts bindings)) P)=
    finite_generation_child_rows E u M (fimage (\<lambda>H. (H,finite_check_generation H)) P)" for M
    by (rule fset_inject[THEN iffD1], rule set_eqI, rename_tac row, case_tac row)
      (simp only: lookup_generation_child_rows_member finite_generation_child_rows_member
        located_values_exact recursive cong: conj_cong)
  show ?case by (simp only: lookup_check_generation.simps finite_check_generation.simps
    generation_fields_exact[OF formed] rows)
qed

theorem generation_readiness_exact:
  "finite_environment_formed E \<Longrightarrow>
    lookup_generation_record_ready artifacts bindings l p c rows=finite_generation_record_ready E l p c rows"
  by (simp only: lookup_generation_record_ready_def finite_generation_record_ready_def
    generation_check_exact simp_thms)

end

export_code lookup_check_generation lookup_generation_record_ready checking SML

text \<open>
  Recursive checks follow the supplied complete generation core and the actual
  predecessor locations. A formed environment and its complete lookup relation
  establish equality to the original checker and record-readiness predicate.
  No supplied truth table or whole environment reconstruction is executed.
\<close>

end
