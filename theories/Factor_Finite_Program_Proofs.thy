theory Factor_Finite_Program_Proofs
  imports Factor_Finite_Application_Proofs Finite_Iteration_Folds
begin

lemma finite_program_activation_heads:
  "fimage (\<lambda>(d,c,t,V,H). (d,t)) (finite_program_activation P D X)=
    finite_inference_next (finite_program_rule_table P D) {||} X"
proof -
  have projection: "fimage finite_program_application_rule (finite_program_activation P D X)=
    finite_inference_enabled (finite_program_rule_table P D) (fset X)"
    by (simp only: finite_program_activation_def finite_inference_witness_projection finite_program_rule_table_def)
  have heads: "fimage fst (fimage finite_program_application_rule (finite_program_activation P D X))=
    fimage fst (finite_inference_enabled (finite_program_rule_table P D) (fset X))"
    by (simp only: projection)
  show ?thesis using heads by (simp add: finite_inference_next_def finite_program_application_rule_head
    fimage_fimage comp_def split_def)
qed

lemma finite_program_proof_step_projection:
  assumes state: "fimage fst T=X"
  shows "fimage fst (finite_application_proofs (finite_program_activation P D X) T)=
    finite_inference_next (finite_program_rule_table P D) {||} X"
proof -
  have support: "fimage snd H |\<subseteq>| fimage fst T"
    if "(d,c,t,V,H) |\<in>| finite_program_activation P D X" for d c t V H
    using that by (simp only: finite_program_activation_member state; blast)
  show ?thesis by (simp only: finite_application_proofs_domain[OF support] finite_program_activation_heads)
qed

definition finite_program_proofs where
  "finite_program_proofs P D=map_option (\<lambda>(A,Hs).
    (A,fold (\<lambda>(X,W) T. finite_application_proofs W T) Hs {||})) (finite_program_history P D)"

lemma finite_program_history_proofs_domain:
  assumes history: "finite_program_history P D=Some (A,Hs)"
  shows "fimage fst (fold (\<lambda>(X,W) T. finite_application_proofs W T) Hs {||})=A"
proof -
  obtain Xs where path: "finite_inference_history (finite_program_rule_table P D) {||}=Some (A,Xs)"
    and labels: "Hs=map (\<lambda>X. (X,finite_program_activation P D X)) Xs"
    using history by (simp only: finite_program_history_conditions; blast)
  have prefix: "iteration_prefix (\<lambda>X. finite_inference_next (finite_program_rule_table P D) {||} X\<noteq>X)
      (finite_inference_next (finite_program_rule_table P D) {||}) {||} Xs A"
    by (rule finite_inference_history_correct(2)[OF path])
  have projected: "fimage fst (fold (\<lambda>X T. finite_application_proofs (finite_program_activation P D X) T) Xs {||})=A"
    apply (rule iteration_prefix_fold_projection[where project="fimage fst", OF prefix])
     apply simp
    by (rule finite_program_proof_step_projection; assumption)
  show ?thesis using projected by (simp only: labels fold_map comp_def case_prod_conv)
qed

lemma finite_program_history_proofs_sound:
  assumes history: "finite_program_history P D=Some (A,Hs)"
  shows "finite_proofs_sound P (fold (\<lambda>(X,W) T. finite_application_proofs W T) Hs {||})"
proof -
  obtain Xs where labels: "Hs=map (\<lambda>X. (X,finite_program_activation P D X)) Xs"
    using history by (simp only: finite_program_history_conditions; blast)
  have applications: "\<forall>d c t V H. (d,c,t,V,H) |\<in>| snd x \<longrightarrow> finite_admitted_schema_instance P d c V t H"
    if "x\<in>set Hs" for x
    using that by (auto simp: labels finite_program_activation_member finite_program_application_member)
  have initial: "finite_proofs_sound P {||}" by (simp add: finite_proofs_sound_def)
  have step: "finite_proofs_sound P ((\<lambda>(X,W) T. finite_application_proofs W T) x T)"
    if apps: "\<forall>d c t V H. (d,c,t,V,H) |\<in>| snd x \<longrightarrow> finite_admitted_schema_instance P d c V t H"
      and proofs: "finite_proofs_sound P T" for x T
    by (cases x) (auto intro!: finite_application_proofs_sound[OF _ proofs] intro: apps[rule_format])
  show ?thesis by (rule fold_invariant[where P="finite_proofs_sound P", OF applications initial step])
qed

theorem finite_program_proofs_projection:
  "map_option fst (finite_program_proofs P D)=finite_program_evaluation P D"
  by (simp add: finite_program_proofs_def option.map_comp comp_def split_def
    finite_program_history_projection[symmetric])

theorem finite_program_proofs_correct:
  assumes result: "finite_program_proofs P D=Some (A,T)"
  shows "finite_program_evaluation P D=Some A" "fimage fst T=A" "finite_proofs_sound P T"
proof -
  obtain Hs where history: "finite_program_history P D=Some (A,Hs)"
    and proofs: "T=fold (\<lambda>(X,W) T. finite_application_proofs W T) Hs {||}"
    using result by (auto simp: finite_program_proofs_def split: option.splits prod.splits)
  show "finite_program_evaluation P D=Some A" by (rule finite_program_history_answer[OF history])
  show "fimage fst T=A" by (simp only: proofs; rule finite_program_history_proofs_domain[OF history])
  show "finite_proofs_sound P T" by (simp only: proofs; rule finite_program_history_proofs_sound[OF history])
qed

theorem finite_program_proofs_complete:
  assumes result: "finite_program_proofs P D=Some (A,T)"
  shows "(d,t) |\<in>| D \<and> (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system P)
    \<longleftrightarrow> (\<exists>p. ((d,t),p) |\<in>| T)"
proof -
  have meaning: "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    by (rule finite_program_evaluation_exact(2)[OF finite_program_proofs_correct(1)[OF result]])
  have original: "(d,t) |\<in>| A \<longleftrightarrow>
    (d,t) |\<in>| D \<and> (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system P)"
    by (simp only: meaning mem_Collect_eq decode_finite_call_pair)
  have domain: "fimage fst T=A" by (rule finite_program_proofs_correct(2)[OF result])
  have constructed: "(d,t) |\<in>| A \<longleftrightarrow> (\<exists>p. ((d,t),p) |\<in>| T)"
    by (simp only: domain[symmetric] finite_first_projection_member)
  show ?thesis using original constructed by blast
qed

text \<open>
  The original finite inference history controls the construction depth.
  Every answered call has an actual complete certificate, and every generated
  certificate satisfies the original proof checker. Positive cycles may have
  infinitely many distinct certificates; this operation constructs a sufficient
  finite family and does not iterate certificate families to a fixed point.
  Native placement, replay and mathematical-proof admission remain separate.
\<close>

end
