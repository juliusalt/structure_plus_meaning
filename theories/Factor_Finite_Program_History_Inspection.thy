theory Factor_Finite_Program_History_Inspection
  imports Factor_Finite_Program_Histories
begin

definition finite_program_history_steps where
  "finite_program_history_steps P D A Hs=(
    iteration_prefix (\<lambda>X. finite_inference_next (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_next (finite_program_rule_table P D) {||}) {||} (map fst Hs) A \<and>
    finite_inference_next (finite_program_rule_table P D) {||} A=A)"

definition program_history_steps where
  "program_history_steps P D A Hs=(
    iteration_prefix (\<lambda>X. finite_inference_round (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_round (finite_program_rule_table P D) {||}) {}
      (map (\<lambda>(X,W). fset X) Hs) (fset A) \<and>
    finite_inference_round (finite_program_rule_table P D) {||} (fset A)=fset A)"

lemma finite_program_history_steps_exact:
  "finite_program_history_steps P D A Hs=program_history_steps P D A Hs"
proof -
  have injective: "inj fset" by (simp add: inj_on_def fset_inject)
  have path: "iteration_prefix
      (\<lambda>X. finite_inference_round (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_round (finite_program_rule_table P D) {||}) (fset {||})
      (map fset (map fst Hs)) (fset A) \<longleftrightarrow>
    iteration_prefix
      (\<lambda>X. finite_inference_next (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_next (finite_program_rule_table P D) {||}) {||} (map fst Hs) A"
    by (rule iteration_prefix_map[OF injective])
      (rule finite_inference_next_test, rule finite_inference_next_correct)
  show ?thesis
    using path by (simp add: finite_program_history_steps_def program_history_steps_def
      finite_inference_next_fixed comp_def split_def)
qed

definition finite_program_history_witnesses where
  "finite_program_history_witnesses P D Hs=
    list_all (\<lambda>(X,W). W=finite_program_activation P D X) Hs"

definition program_history_witnesses where
  "program_history_witnesses P D Hs=(\<forall>(X,W)\<in>set Hs. \<forall>d c t V H.
    (d,c,t,V,H) |\<in>| W \<longleftrightarrow>
      (d,t) |\<in>| D \<and>
      admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
        (decode_finite_term t) (decode_finite_premises H) \<and>
      fimage snd H |\<subseteq>| X)"

lemma finite_program_history_witnesses_exact:
  assumes "finite_program_head_covered P D"
  shows "finite_program_history_witnesses P D Hs=program_history_witnesses P D Hs"
proof -
  have each: "W=finite_program_activation P D X \<longleftrightarrow>
      (\<forall>d c t V H. (d,c,t,V,H) |\<in>| W \<longleftrightarrow> (d,t) |\<in>| D \<and>
        admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
          (decode_finite_term t) (decode_finite_premises H) \<and> fimage snd H |\<subseteq>| X)" for X W
    by (simp only: fset_eq_iff split_paired_All finite_program_activation_exact[OF assms])
  show ?thesis
    by (auto simp only: finite_program_history_witnesses_def program_history_witnesses_def
      list_all_iff each split: prod.splits)
qed

theorem finite_program_history_inspection:
  assumes result: "finite_program_history P D=Some (A,Hs)"
  shows "finite_program_history_steps P D A Hs"
    "finite_program_history_witnesses P D Hs"
proof -
  obtain Xs where history: "finite_inference_history (finite_program_rule_table P D) {||}=Some (A,Xs)"
    and labels: "Hs=map (\<lambda>X. (X,finite_program_activation P D X)) Xs"
    using result by (simp only: finite_program_history_conditions; blast)
  show "finite_program_history_steps P D A Hs"
    using finite_inference_history_correct(2,3)[OF history]
    by (simp add: finite_program_history_steps_def labels comp_def)
  show "finite_program_history_witnesses P D Hs"
    by (simp add: finite_program_history_witnesses_def labels list_all_iff)
qed

definition finite_program_history_step_review where
  "finite_program_history_step_review P D A Hs=
    iteration_review (\<lambda>X. finite_inference_next (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_next (finite_program_rule_table P D) {||}) {||} (map fst Hs) A"

lemma finite_program_history_step_review_exact:
  "iteration_review_holds (finite_program_history_step_review P D A Hs)=finite_program_history_steps P D A Hs"
  by (simp add: finite_program_history_step_review_def iteration_review_exact finite_program_history_steps_def)

definition finite_program_history_witness_review where
  "finite_program_history_witness_review P D Hs=
    finite_inference_witness_review finite_program_application_rule (finite_program_applications P D) Hs"

lemma finite_program_history_witness_review_exact:
  "finite_inference_witness_review_holds (finite_program_history_witness_review P D Hs)=
    finite_program_history_witnesses P D Hs"
  by (simp only: finite_program_history_witness_review_def finite_inference_witness_review_exact
    finite_program_history_witnesses_def finite_program_activation_def)

export_code finite_program_history_steps finite_program_history_witnesses
  finite_program_history_step_review finite_program_history_witness_review checking SML

end
