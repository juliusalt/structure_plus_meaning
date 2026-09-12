theory Factor_Admission_Sequence_Exact
  imports Factor_Admission_Sequence_Clauses
begin

theorem admission_sequence_sound:
  assumes holds: "(361,z)\<in>positive_meaning admission_sequence_system"
  shows "admission_sequence_result z"
proof -
  have invariant: "(361::nat)=361 \<longrightarrow> admission_sequence_result z"
  proof (rule positive_valuation_induct[OF holds,
      where property="\<lambda>d t. d=361 \<longrightarrow> admission_sequence_result t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses admission_sequence_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and head: "schema_call_formed admission_sequence_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning admission_sequence_system \<and>
        (e=361 \<longrightarrow> admission_sequence_result (evaluate_pattern h p))"
    show "d=361 \<longrightarrow> admission_sequence_result (evaluate_pattern h (schema_conclusion S))"
    proof
      assume root: "d=361"
      consider (nil) "S=admission_sequence_nil_schema" | (step) "S=admission_sequence_step_schema"
        using clause root by (auto simp: admission_sequence_clauses_def)
      then show "admission_sequence_result (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        obtain n where counter: "h 0=admission_counter n"
          using support by (auto simp: nil admission_sequence_nil_schema_def admission_sequence_components)
        show ?thesis unfolding admission_sequence_result_def
          by (rule exI[of _ "[]"], rule exI[of _ n], rule exI[of _ "[]"],
            rule exI[of _ n], rule exI[of _ "[]"])
            (simp add: nil admission_sequence_nil_schema_def counter)
      next
        case step
        have first: "admission_plan_result (admission_plan_argument (h 0) (h 2) (h 3) (h 7) (h 8))"
          and rest: "admission_sequence_result (admission_plan_argument (h 1) (h 7) (h 4) (h 5) (h 9))"
          and join: "(46,collection_join_argument (h 8) (h 9) (h 6))\<in>positive_meaning data_append_system"
          using support by (auto simp: step admission_sequence_step_schema_def admission_sequence_components)
        obtain g n a m xs where left: "admission_plan g n=(a,m,xs)"
          "h 0=admission_goal_value g" "h 2=admission_counter n" "h 3=admission_counter a"
          "h 7=admission_counter m" "h 8=data_list_term (map admission_instruction_value xs)"
          using first by (simp only: admission_plan_result_def factor_term.inject) blast
        obtain gs ds k ys where right: "admission_sequence gs m=(ds,k,ys)"
          "h 1=data_list_term (map admission_goal_value gs)"
          "h 4=data_list_term (map admission_counter ds)" "h 5=admission_counter k"
          "h 9=data_list_term (map admission_instruction_value ys)"
          using rest by (simp only: admission_sequence_result_def left(5) factor_term.inject
            admission_counter_injective) blast
        have final: "h 6=data_list_term (map admission_instruction_value (xs@ys))"
          using join by (simp only: left(6) right(5) data_append_at_lists map_append)
        show ?thesis unfolding admission_sequence_result_def
          by (rule exI[of _ "g#gs"], rule exI[of _ n], rule exI[of _ "a#ds"],
            rule exI[of _ k], rule exI[of _ "xs@ys"])
            (use left right final in \<open>simp add: step admission_sequence_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem admission_sequence_complete:
  assumes sequence: "admission_sequence gs n=(ds,k,cs)"
  shows "(361,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning admission_sequence_system"
  using sequence
proof (induction gs arbitrary: n ds k cs)
  case Nil
  have fields: "ds=[]" "k=n" "cs=[]" using Nil.prems by auto
  have result: "(361,evaluate_pattern (\<lambda>_. admission_counter n)
      (schema_conclusion admission_sequence_nil_schema))\<in>positive_meaning admission_sequence_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (auto simp: admission_sequence_clauses_def admission_sequence_nil_schema_def
        schema_variables_def admission_sequence_call admission_sequence_components octets_formed_def)
  show ?case using result by (simp add: fields admission_sequence_nil_schema_def)
next
  case (Cons g gs)
  obtain a m xs where left: "admission_plan g n=(a,m,xs)"
    by (cases "admission_plan g n") auto
  obtain es l ys where right: "admission_sequence gs m=(es,l,ys)"
    by (cases "admission_sequence gs m") auto
  have fields: "ds=a#es" "k=l" "cs=xs@ys"
    using Cons.prems by (auto simp: left right)
  let ?xs="data_list_term (map admission_instruction_value xs)"
  let ?ys="data_list_term (map admission_instruction_value ys)"
  let ?cs="data_list_term (map admission_instruction_value cs)"
  have child: "(341,admission_plan_argument (admission_goal_value g) (admission_counter n)
      (admission_counter a) (admission_counter m) ?xs)\<in>positive_meaning admission_sequence_system"
    by (simp only: admission_sequence_components(2) admission_plan_result_def)
      (use left in blast)
  have tail: "(361,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter m)
      (data_list_term (map admission_counter es)) (admission_counter l) ?ys)
      \<in>positive_meaning admission_sequence_system"
    by (rule Cons.IH[OF right])
  have join: "(46,collection_join_argument ?xs ?ys ?cs)\<in>positive_meaning admission_sequence_system"
    by (simp only: admission_sequence_components(3) data_append_lists)
      (auto simp: fields octets_formed_def)
  let ?h="\<lambda>i::nat. if i=0 then admission_goal_value g
    else if i=1 then data_list_term (map admission_goal_value gs)
    else if i=2 then admission_counter n else if i=3 then admission_counter a
    else if i=4 then data_list_term (map admission_counter es) else if i=5 then admission_counter l
    else if i=6 then ?cs else if i=7 then admission_counter m else if i=8 then ?xs else ?ys"
  have result: "(361,evaluate_pattern ?h (schema_conclusion admission_sequence_step_schema))
      \<in>positive_meaning admission_sequence_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use child tail join in \<open>auto simp: admission_sequence_clauses_def admission_sequence_step_schema_def
        schema_variables_def admission_sequence_call data_list_term_formed octets_formed_def\<close>)
  show ?case using result by (simp add: fields admission_sequence_step_schema_def)
qed

theorem admission_sequence_exact:
  "(361,z)\<in>positive_meaning admission_sequence_system \<longleftrightarrow> admission_sequence_result z"
  using admission_sequence_sound admission_sequence_complete by (auto simp: admission_sequence_result_def)

export_code admission_sequence checking SML

end
