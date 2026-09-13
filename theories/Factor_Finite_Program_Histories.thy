theory Factor_Finite_Program_Histories
  imports Factor_Finite_Program_Evaluation Finite_Inference_Histories
begin

section \<open>Original clauses and complete bindings accompany each inference step\<close>

lemma finite_program_evaluation_demand_included:
  assumes original: "finite_program_evaluation P D=Some A"
    and expanded: "finite_program_evaluation P E=Some B" and demand: "D |\<subseteq>| E"
  shows "A |\<subseteq>| B"
  using finite_program_evaluation_exact(2)[OF original] finite_program_evaluation_exact(2)[OF expanded] demand
  by (auto simp: less_eq_fset.rep_eq)

definition finite_program_activation where
  "finite_program_activation P D X=
    finite_inference_witnesses finite_program_application_rule (finite_program_applications P D) X"

lemma finite_program_activation_member:
  "(d,c,t,V,H) |\<in>| finite_program_activation P D X \<longleftrightarrow>
    (d,c,t,V,H) |\<in>| finite_program_applications P D \<and> fimage snd H |\<subseteq>| X"
proof -
  have functional: "finite_premise_functional H"
    if member: "(d,c,t,V,H) |\<in>| finite_program_applications P D"
  proof -
    have rule: "((d,t),H) |\<in>| finite_program_rule_table P D"
      using member by (auto simp: finite_program_rule_member)
    show ?thesis
      using finite_program_rule_functional[OF rule] by (simp only: finite_premise_functional_exact)
  qed
  show ?thesis using functional
    by (simp only: finite_program_activation_def finite_inference_witness_member finite_program_application_rule.simps
      case_prod_conv; blast)
qed

theorem finite_program_activation_sound:
  assumes member: "(d,c,t,V,H) |\<in>| finite_program_activation P D X"
  shows "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises H)"
    "fimage snd H |\<subseteq>| X"
    "(d,t) |\<in>| D"
  using member by (auto simp: finite_program_activation_member finite_program_application_member
    finite_admitted_schema_instance_correct)

theorem finite_program_activation_exact:
  assumes covered: "finite_program_head_covered P D"
  shows "(d,c,t,V,H) |\<in>| finite_program_activation P D X \<longleftrightarrow>
    (d,t) |\<in>| D \<and>
    admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises H) \<and> fimage snd H |\<subseteq>| X"
  by (simp only: finite_program_activation_member finite_program_application_exact[OF covered]
    finite_admitted_schema_instance_correct conj_assoc)

theorem finite_program_activation_complete:
  assumes inst: "admitted_schema_instance (decode_finite_system P) d c V (decode_finite_term t) H"
    and demand: "(d,t) |\<in>| D" and covered: "finite_program_head_covered P D"
    and support: "rel_ran H\<subseteq>image decode_finite_call_term (fset X)"
  shows "\<exists>B G. (d,c,t,B,G) |\<in>| finite_program_activation P D X \<and>
    decode_finite_term_bindings B=V \<and> decode_finite_premises G=H"
proof -
  obtain B G where application: "(d,c,t,B,G) |\<in>| finite_program_applications P D"
    and fields: "decode_finite_term_bindings B=V" "decode_finite_premises G=H"
    using finite_program_application_complete[OF inst demand covered] by blast
  have ready: "fimage snd G |\<subseteq>| X"
    using support by (simp only: fields(2)[symmetric] decode_finite_premises_def
      finite_relation_values_support[OF decode_finite_call_inj(2)])
  show ?thesis
    using application ready fields by (simp only: finite_program_activation_member; blast)
qed

definition finite_program_history where
  "finite_program_history P D=(if finite_program_evaluation_ready P D then
    finite_inference_labelled_history finite_program_application_rule (finite_program_applications P D) {||}
    else None)"

lemma finite_program_history_conditions:
  "finite_program_history P D=Some (A,Hs) \<longleftrightarrow>
    finite_program_evaluation_ready P D \<and>
    (\<exists>Xs. finite_inference_history (finite_program_rule_table P D) {||}=Some (A,Xs) \<and>
      Hs=map (\<lambda>X. (X,finite_program_activation P D X)) Xs)"
  by (auto simp: finite_program_history_def finite_inference_labelled_history_conditions
    finite_program_rule_table_def finite_program_activation_def split: if_splits)

theorem finite_program_history_total:
  "(\<exists>A Hs. finite_program_history P D=Some (A,Hs)) \<longleftrightarrow>
    finite_system_formed P \<and> finite_program_head_covered P D \<and> finite_program_demand_closed P D"
  using finite_inference_history_total[of "finite_program_rule_table P D" "{||}"]
  by (auto simp: finite_program_history_conditions finite_program_evaluation_ready_def)

theorem finite_program_history_answer:
  assumes result: "finite_program_history P D=Some (A,Hs)"
  shows "finite_program_evaluation P D=Some A"
proof -
  obtain Xs where ready: "finite_program_evaluation_ready P D"
    and history: "finite_inference_history (finite_program_rule_table P D) {||}=Some (A,Xs)"
    using result by (simp only: finite_program_history_conditions; blast)
  have closure: "fset A=finite_inference_result (finite_program_rule_table P D) {||}"
    using finite_inference_history_correct(1)[OF history] by (simp only: finite_inference_result_exact)
  have heads: "image fst (fset (finite_program_rule_table P D))\<subseteq>fset D"
    using finite_program_rule_head[of _ _ P D] by auto
  have inside: "fset A\<subseteq>fset D"
    using finite_inference_history_bound(1)[OF history] heads by auto
  have included: "A |\<subseteq>| fimage id D"
    using inside by (simp add: less_eq_fset.rep_eq)
  have filtered: "ffilter (\<lambda>q. q\<in>finite_inference_result (finite_program_rule_table P D) {||}) D=A"
    using finite_image_restriction[OF included] by (simp add: closure[symmetric])
  show ?thesis by (simp only: finite_program_evaluation_def ready if_True Let_def filtered)
qed

theorem finite_program_history_projection:
  "map_option fst (finite_program_history P D)=finite_program_evaluation P D"
proof (cases "finite_program_history P D")
  case None
  have "\<not>(\<exists>A Hs. finite_program_history P D=Some (A,Hs))" by (simp only: None) simp
  then have "\<not>(\<exists>A. finite_program_evaluation P D=Some A)"
    using finite_program_history_total[of P D] finite_program_evaluation_conditions[of P D] by blast
  then show ?thesis by (simp add: None)
next
  case (Some result)
  obtain A Hs where fields: "result=(A,Hs)" by (cases result) auto
  show ?thesis using finite_program_history_answer[OF Some[unfolded fields]]
    by (simp only: Some fields option.simps fst_conv)
qed

theorem finite_program_history_state_sound:
  assumes result: "finite_program_history P D=Some (A,Hs)"
    and state: "(X,W)\<in>set Hs" and member: "q |\<in>| X"
  shows "q |\<in>| D" "decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  obtain Xs where history: "finite_inference_history (finite_program_rule_table P D) {||}=Some (A,Xs)"
    and labels: "Hs=map (\<lambda>X. (X,finite_program_activation P D X)) Xs"
    using result by (simp only: finite_program_history_conditions; blast)
  have before: "X\<in>set Xs" using state by (auto simp: labels)
  have subset: "X |\<subseteq>| A"
    using finite_inference_history_states_subset[OF history] before by blast
  have admitted: "q |\<in>| A" using subset member by auto
  have evaluation: "finite_program_evaluation P D=Some A"
    by (rule finite_program_history_answer[OF result])
  show "q |\<in>| D" "decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    using admitted finite_program_evaluation_exact(2)[OF evaluation] by auto
qed

export_code finite_program_history checking SML

text \<open>
  Every activation retains the actual clause and its complete binding and
  premise relations. The computation starts with no supplied true calls.
  Its answer projection equals the existing evaluator on every input,
  including requests whose decision prerequisites are unavailable.
  Constructing and placing native proof graphs from these histories remains
  a separate requirement, as does checking native mathematical proofs.
\<close>

end
