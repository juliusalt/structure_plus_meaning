theory RRA_Finite_Syntax_Bodies
  imports RRA_Executable_Records
begin

definition finite_payload_leaf_body where
  "finite_payload_leaf_body C a v=(finite_headed_incidence (finite_structure C) a={||} \<and>
    finite_payload_at C a v)"

lemma finite_payload_leaf_guard:
  "finite_payload_leaf_at C a v \<longleftrightarrow> finite_object_formed C \<and> finite_payload_leaf_body C a v"
  by (simp only: finite_payload_leaf_at_def finite_payload_leaf_body_def)

definition finite_record_body where
  "finite_record_body C r ps xs=(r |\<in>| finite_carrier (finite_structure C) \<and>
    ((ps=[] \<and> xs=[] \<and> finite_headed_incidence (finite_structure C) r={||}) \<or>
     (finite_record_path (finite_structure C) r ps xs \<and>
       finite_headed_incidence (finite_structure C) r=fset_of_list (zip ps xs))) \<and>
    finite_data_empty_on C (finsert r (fset_of_list ps)))"

lemma finite_record_guard:
  "finite_record_at C r ps xs \<longleftrightarrow> finite_object_formed C \<and> finite_record_body C r ps xs"
  by (simp only: finite_record_at_def finite_record_body_def)

definition finite_record_body_candidates where
  "finite_record_body_candidates C r n=(let H=finite_headed_incidence (finite_structure C) r in
    if fcard H=n then ffilter (\<lambda>(ps,xs). finite_record_body C r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_lists_of_length n H)) else {||})"

lemma finite_record_body_candidates_exact:
  assumes "finite_object_formed C"
  shows "finite_record_body_candidates C r n=finite_record_candidates C r n"
  using assms by (simp only: finite_record_body_candidates_def finite_record_candidates_def
    finite_record_guard simp_thms)

text \<open>
  These bodies contain the original local incidence and data conditions.
  They represent full leaf and record recognition only with the separate
  original object-formation premise. Callers must establish that premise from
  the actual complete source before using the body equations.
\<close>

end
