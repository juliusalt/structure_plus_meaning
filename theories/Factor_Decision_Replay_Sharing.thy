theory Factor_Decision_Replay_Sharing
  imports Factor_Decision_Replay_Investigation Factor_Native_Replay_Relation_Caches
    Finite_Assessment_Projections
begin

definition decision_replay_result_queries where
  "decision_replay_result_queries result=(case result of None \<Rightarrow> {||}
    | Some (Z,R) \<Rightarrow> fimage (\<lambda>(c,replay). (decision_certificate_subject Z c,replay)) R)"

definition decision_replay_context_queries where
  "decision_replay_context_queries C=(case C of None \<Rightarrow> {||}
    | Some (X,(reference,details),bases) \<Rightarrow> ffUnion (fimage (\<lambda>m.
      decision_replay_result_queries (decision_replay_prepared m X bases))
        (fset_of_list [0,1,2,3,4,5,6,7,8,9,10,11])))"

definition decision_replay_shared_context where
  "decision_replay_shared_context w=(let C=decision_replay_context w in
    (C,native_replay_relation_caches (decision_replay_context_queries C)))"

definition decision_replay_shared_row where
  "decision_replay_shared_row caches Z row=(case row of (c,result) \<Rightarrow>
    let X=decision_certificate_subject Z c in
    (X,native_replay_relation_assessment caches X result))"

lemma decision_replay_shared_row_exact:
  "decision_replay_shared_row (native_replay_relation_caches rows) Z row=
    decision_replay_row_assessment Z row"
  by (cases row)
    (simp only: decision_replay_shared_row_def decision_replay_row_assessment_def Let_def
      case_prod_conv native_replay_relation_assessment_exact
      native_replay_original_def[symmetric] native_replay_assessment_def)

definition decision_replay_shared_family where
  "decision_replay_shared_family caches Z R=(finite_decision_certificates Z,
    fimage fst R=finite_decision_certificates Z \<and> finite_relation_functional R,
    finite_inspection_rows (decision_replay_shared_row caches Z) R)"

lemma decision_replay_shared_family_exact:
  "decision_replay_shared_family (native_replay_relation_caches rows) Z R=
    decision_replay_family_assessment Z R"
  by (simp only: decision_replay_shared_family_def decision_replay_family_assessment_def
    decision_replay_shared_row_exact[abs_def])

definition decision_replay_shared_assessment where
  "decision_replay_shared_assessment caches X reference result=(
    requirement_decision_assessment_from X reference (map_option fst result),
    map_option (\<lambda>(Z,R). decision_replay_shared_family caches Z R) result)"

lemma decision_replay_shared_assessment_exact:
  "decision_replay_shared_assessment (native_replay_relation_caches rows) X reference result=
    decision_replay_assessment_from X reference result"
  by (simp only: decision_replay_shared_assessment_def decision_replay_assessment_from_def
    decision_replay_shared_family_exact)

definition decision_replay_shared_cell where
  "decision_replay_shared_cell m CC=(case CC of (C,caches) \<Rightarrow>
    map_option (\<lambda>(X,(reference,details),bases). let result=decision_replay_prepared m X bases in
      (X,reference,result,decision_replay_shared_assessment caches X reference result)) C)"

lemma decision_replay_shared_cell_exact:
  "decision_replay_shared_cell m (decision_replay_shared_context w)=
    decision_replay_cell m (decision_replay_context w)"
  by (simp only: decision_replay_shared_cell_def decision_replay_shared_context_def
    decision_replay_cell_def Let_def case_prod_conv decision_replay_shared_assessment_exact)

definition decision_replay_shared_table where
  "decision_replay_shared_table ws=project_assessment_contexts fst
    (context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      decision_replay_shared_context decision_replay_shared_cell)"

theorem decision_replay_shared_table_exact:
  "decision_replay_shared_table ws=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
    decision_replay_context decision_replay_cell"
  unfolding decision_replay_shared_table_def
proof (rule context_assessment_table_projection)
  show "fst (decision_replay_shared_context w)=decision_replay_context w" for w
    by (simp only: decision_replay_shared_context_def Let_def fst_conv)
  show "decision_replay_shared_cell c (decision_replay_shared_context w)=
    decision_replay_cell c (decision_replay_context w)" for c w
    by (rule decision_replay_shared_cell_exact)
qed

definition decision_replay_shared_packet where
  "decision_replay_shared_packet ws selections=(let table=decision_replay_shared_table ws;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws table
      decision_replay_cell_inspect
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
      (fst comparison) (fst (snd comparison))) selections))"

theorem decision_replay_shared_packet_exact:
  "decision_replay_shared_packet ws selections=decision_replay_packet ws selections"
  by (simp only: decision_replay_shared_packet_def decision_replay_packet_def decision_replay_shared_table_exact)

declare decision_replay_packet_def[code del]

lemma decision_replay_packet_shared [code]:
  "decision_replay_packet ws selections=decision_replay_shared_packet ws selections"
  by (rule decision_replay_shared_packet_exact[symmetric])

text \<open>
  The complete original public contexts, results, assessments, comparison and
  every revision field remain equal. The internal shared context contains only
  derived actual reader values. Its explicit projection has the complete table
  contract; no public result field is omitted or replaced. Native execution
  and full result comparison remain prerequisites for adopting this proposal.
\<close>

end
