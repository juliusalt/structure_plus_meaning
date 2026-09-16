theory Factor_Development_Steering
  imports Factor_Development_Subjects Factor_Finite_Development_Questions
begin

definition development_method_row :: "nat \<Rightarrow> finite_factor_term" where
  "development_method_row m=Finite_Pair (Finite_Payload []) (Finite_Payload [m])"

lemma development_method_row_function:
  "development_method_row=(\<lambda>m. Finite_Pair (Finite_Payload []) (Finite_Payload [m]))"
  by (rule ext) (simp only: development_method_row_def)

definition development_criterion_rows where
  "development_criterion_rows table nquestions f=map development_method_row
    (filter (\<lambda>m. development_table_condition table nquestions m f) development_methods)"

lemma development_criterion_rows_exact:
  assumes method: "m\<in>set development_methods"
  shows "Finite_Pair (Finite_Payload []) (Finite_Payload [m])\<in>
      set (development_criterion_rows (development_subject_table qs) (length qs) f) \<longleftrightarrow>
    (\<forall>Q\<in>set qs. development_producer_condition f (development_producer m) Q)"
  using method by (auto simp: development_criterion_rows_def development_method_row_def
    development_table_condition_exact)

definition development_criterion_values where
  "development_criterion_values table nquestions f=map (\<lambda>m. Finite_Payload [m])
    (filter (\<lambda>m. development_table_condition table nquestions m f) development_methods)"

definition development_steering_question_from where
  "development_steering_question_from table nquestions=(if nquestions=0 then None else
    finite_development_question (map (\<lambda>m. Finite_Payload [m]) development_methods)
      (map (development_criterion_values table nquestions) development_facets))"

lemma development_steering_question_from_equation:
  "development_steering_question_from table nquestions=(let source=finite_ground_source (map development_method_row development_methods);
    cs=map (\<lambda>f. finite_ground_condition (development_criterion_rows table nquestions f)) development_facets in
    if nquestions=0 \<or> \<not>list_all (\<lambda>C. C\<noteq>None) cs then None else
      case source of None \<Rightarrow> None | Some (d,F,u) \<Rightarrow>
        Some \<lparr>development_source=F,development_source_use=u,development_source_root=[],development_generator_entry=d,
          development_problem=Finite_Payload [],development_conditions=map the cs,
          development_scope_criticism=development_scope_condition True,development_selected_facets=[]\<rparr>)"
  by (auto simp: development_steering_question_from_def finite_development_question_def
    finite_development_source_def finite_development_rows_def development_criterion_values_def
    development_criterion_rows_def development_method_row_function development_methods_def
    development_facets_def Let_def comp_def split: option.splits prod.splits if_splits)

definition development_steering_question where
  "development_steering_question qs=development_steering_question_from (development_subject_table qs) (length qs)"

lemma development_steering_original_criterion:
  assumes constructed: "development_steering_question qs=Some Q" and facet: "f\<in>set development_facets"
  obtains C where "C\<in>set (development_conditions Q)" "development_problem Q=Finite_Payload []"
    "finite_ground_condition (development_criterion_rows (development_subject_table qs) (length qs) f)=Some C"
proof -
  let ?cs="map (\<lambda>f. finite_ground_condition (development_criterion_rows (development_subject_table qs) (length qs) f)) development_facets"
  have complete: "list_all (\<lambda>C. C\<noteq>None) ?cs"
    and conditions: "development_conditions Q=map the ?cs"
    and problem: "development_problem Q=Finite_Payload []"
    using constructed by (auto simp: development_steering_question_def development_steering_question_from_equation
      Let_def split: if_splits option.splits prod.splits)
  have present: "finite_ground_condition (development_criterion_rows (development_subject_table qs) (length qs) f)\<noteq>None"
    using complete facet by (auto simp: list_all_iff)
  obtain C where source: "finite_ground_condition (development_criterion_rows (development_subject_table qs) (length qs) f)=Some C"
    using present by auto
  have in_cs: "Some C\<in>set ?cs"
    using facet by (metis imageI set_map source)
  have member: "C\<in>set (development_conditions Q)"
    using imageI[OF in_cs, of the] by (simp only: conditions set_map option.sel)
  show thesis by (rule that[OF member problem source])
qed

theorem development_steering_original_conditions:
  assumes constructed: "development_steering_question qs=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and chosen: "Finite_Payload [m]\<in>set accepted" and method: "m\<in>set development_methods"
    and facet: "f\<in>set development_facets" and original: "q\<in>set qs"
  shows "development_producer_condition f (development_producer m) q"
proof -
  obtain C where member: "C\<in>set (development_conditions Q)" and problem: "development_problem Q=Finite_Payload []"
    and source: "finite_ground_condition (development_criterion_rows (development_subject_table qs) (length qs) f)=Some C"
    by (rule development_steering_original_criterion[OF constructed facet]) blast
  have holds: "development_condition_holds C (development_problem Q) (Finite_Payload [m])"
    by (rule native_development_original_conditions[OF admitted chosen member])
  have included: "Finite_Pair (Finite_Payload []) (Finite_Payload [m])\<in>
    set (development_criterion_rows (development_subject_table qs) (length qs) f)"
    using holds by (simp only: problem finite_ground_condition_exact[OF source])
  show ?thesis using included development_criterion_rows_exact[OF method] original by blast
qed

definition development_selected_methods where
  "development_selected_methods accepted=filter (\<lambda>m. Finite_Payload [m]\<in>set accepted) development_methods"

corollary development_steering_selected_methods:
  assumes "development_steering_question qs=Some Q" "native_development_admission Q report=Some accepted"
    "m\<in>set (development_selected_methods accepted)" "f\<in>set development_facets" "q\<in>set qs"
  shows "development_producer_condition f (development_producer m) q"
  using assms by (auto simp: development_selected_methods_def intro: development_steering_original_conditions)

definition development_steering_packet where
  "development_steering_packet qs=(let table=development_subject_table qs;
    original=development_steering_question_from table (length qs) in
    (qs,table,map_option (\<lambda>Q. let report=construct_native_development Q;
      accepted=native_development_admission Q report in
      (Q,report,accepted,map_option development_selected_methods accepted)) original))"

lemma development_steering_packet_question:
  "development_steering_packet qs=(let table=development_subject_table qs in
    (qs,table,map_option (\<lambda>Q. let report=construct_native_development Q;
      accepted=native_development_admission Q report in
      (Q,report,accepted,map_option development_selected_methods accepted)) (development_steering_question qs)))"
  by (simp only: development_steering_packet_def development_steering_question_def Let_def)

text \<open>This is a closed computed-observation use. Complete original questions
  produce actual method results, independent original-goal references and all
  five criterion observations. The resulting native source clauses are derived
  internally from that complete computation. The public boundary receives no
  satisfaction table. The theorem connects every admitted method to every
  original question and condition, rather than granting facts from source
  formation or a clause table alone. The outer packet retains those questions
  and complete computations; its empty inner argument carries no such claim.
  The selected identifiers map exactly to the declared actual producer functions.
  This finite ten-producer comparison does not establish broader candidate or
  problem coverage, mathematical-proof admission, or the genesis handoff.\<close>

end
