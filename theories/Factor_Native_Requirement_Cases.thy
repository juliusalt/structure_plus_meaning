theory Factor_Native_Requirement_Cases
  imports Factor_Native_Requirement_Plans Factor_Native_Requirement_Source_Models
begin

section \<open>Recursive collection plans retain the actual source distinction\<close>

definition source_requirement_goal :: "bool\<Rightarrow>admission_goal" where
  "source_requirement_goal paired=(if paired then
    Paired_Admission (Existing_Admission 0) (Collected_Admission (Existing_Admission 0))
    else Collected_Admission (Existing_Admission 0))"

definition source_requirement_sequence where
  "source_requirement_sequence paired=(if paired then
    ([2],3,[List_Admission_Instruction 1 0,Pair_Admission_Instruction 2 0 1])
    else ([1],2,[List_Admission_Instruction 1 0]))"

lemma source_requirement_checked:
  "checked_admission_sequence (system_definitions (nat_guard_source_model b))
    [source_requirement_goal paired] 1=Some (source_requirement_sequence paired)"
  by (cases paired; simp add: source_requirement_goal_def source_requirement_sequence_def
    checked_admission_sequence_def admission_request_supported_def admission_source_floor_def)

lemma source_requirement_native_plan:
  assumes sequence: "source_requirement_sequence paired=(ds,k,cs)"
  shows "(367,admission_plan_argument (data_list_term (map admission_goal_value [source_requirement_goal paired]))
    (admission_counter 1) (data_list_term (map admission_counter ds)) (admission_counter k)
    (data_list_term (map admission_instruction_value cs)))
      \<in>positive_meaning (admission_request_system (system_definitions (nat_guard_source_model b)))"
  by (simp only: checked_admission_sequence_at_values[OF system_definitions_finite[OF nat_guard_source_model_formed]]
    source_requirement_checked sequence; simp)

theorem source_requirement_native_installation:
  assumes sequence: "source_requirement_sequence paired=(ds,k,cs)"
  shows "\<exists>F h v T. environment_formed F \<and>
    environment_included (decode_finite_environment (finite_guard_source b)) F \<and>
    native_package_at F None [0] (decode_finite_system (finite_guard_source_program b)) \<and>
    native_package_at F v [] T \<and> h 0=(None,[Suc 0]) \<and>
    system_alpha_variant (rename_system h (required_admission_system (nat_guard_source_model b) ds k cs)) T \<and>
    h k\<in>system_definitions T \<and> fst (h k)\<notin>environment_uses (decode_finite_environment (finite_guard_source b)) \<and>
    (\<forall>t. (h k,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
      admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired) t)"
proof -
  have planned: "(367,admission_plan_argument (data_list_term (map admission_goal_value [source_requirement_goal paired]))
    (admission_counter 1) (data_list_term (map admission_counter ds)) (admission_counter k)
    (data_list_term (map admission_instruction_value cs)))
      \<in>positive_meaning (admission_request_system (system_definitions (nat_guard_source_model b)))"
    by (rule source_requirement_native_plan[OF sequence])
  obtain F h v T where built: "environment_formed F"
    "environment_included (decode_finite_environment (finite_guard_source b)) F"
    "native_package_at F None [0] (decode_finite_system (finite_guard_source_program b))"
    "native_package_at F v [] T"
    "\<forall>d\<in>system_definitions (nat_guard_source_model b). h d=native_guard_source_coordinate d"
    "system_alpha_variant (rename_system h (required_admission_system (nat_guard_source_model b) ds k cs)) T"
    "h k\<in>system_definitions T"
    "fst (h k)\<notin>environment_uses (decode_finite_environment (finite_guard_source b))"
    "\<forall>t. (h k,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
      (\<forall>q\<in>set [source_requirement_goal paired]. admission_goal_holds
        {(d,x). d\<in>system_definitions (nat_guard_source_model b) \<and>
          (native_guard_source_coordinate d,x)\<in>positive_meaning (decode_finite_system (finite_guard_source_program b))} q t)"
    using native_checked_requirement_package_total[OF finite_guard_source_package[where b=b]
      nat_guard_source_model_formed nat_guard_source_coordinate_injective nat_guard_source_model_variant planned]
    by (elim exE conjE) blast
  have coordinate: "h 0=(None,[Suc 0])" using built(5) by (simp add: native_guard_source_coordinate_def)
  have meaning: "\<forall>t. (h k,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
    admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired) t"
    using built(9) by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ h], rule exI[of _ v], rule exI[of _ T])
    (use built(1-4,6-8) coordinate meaning in blast)
qed

definition source_requirement_plan_report where
  "source_requirement_plan_report b paired=(
    checked_admission_sequence (system_definitions (nat_guard_source_model b)) [source_requirement_goal paired] 1,
    map (admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired))
      [Payload_Term [],Pair_Term (Payload_Term []) (Payload_Term []),
        Pair_Term (Pair_Term (Payload_Term []) (Payload_Term [])) (Payload_Term [])])"

lemma source_requirement_plan_report_code [code]:
  "source_requirement_plan_report b paired=(Some (source_requirement_sequence paired),[\<not>paired,b,True])"
proof -
  have checked: "checked_admission_sequence (system_definitions (nat_guard_source_model b))
    [source_requirement_goal paired] 1=Some (source_requirement_sequence paired)"
    by (rule source_requirement_checked)
  have leaf: "(0,Payload_Term [])\<in>positive_meaning (nat_guard_source_model b) \<longleftrightarrow> b"
    by (simp only: nat_guard_source_model_meaning; simp add: octets_formed_def)
  have diagonal: "(0,Pair_Term (Payload_Term []) (Payload_Term []))\<in>positive_meaning (nat_guard_source_model b)"
    by (simp only: nat_guard_source_model_meaning; simp add: octets_formed_def)
  show ?thesis
    by (simp only: source_requirement_plan_report_def checked; cases paired;
      simp only: list.map nat_guard_source_model_basis[symmetric]
        source_requirement_goal_def if_True if_False admission_paired_holds admission_collected_pair
        admission_collected_empty admission_goal_holds.simps(1)
        admission_goal_holds.simps(2)[where t="Payload_Term []"] leaf diagonal; simp)
qed

text \<open>
  The four cases combine two complete actual source artifacts with collection
  and nonempty-collection requirements. Their native plans contain the existing
  recursive list clause family and, when requested, the pair constructor.
  The installation theorem retains the original package and its address.

  The executed report observes the actual source requirement at three concrete
  terms and retains the complete computed instruction sequence. Its equation
  follows from the complete source correspondence and the owned goal equations.
  The installation theorem connects those observations to every constructed
  target. These observations do not execute the existential native constructor.
\<close>

end
