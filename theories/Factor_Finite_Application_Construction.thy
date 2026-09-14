theory Factor_Finite_Application_Construction
  imports Factor_Finite_Application_Encoding Factor_Finite_Native_Sources
    Factor_Executable_Calls RRA_Finite_Environment_Preservation
begin

definition finite_application_target where
  "finite_application_target E d=finite_singleton_option
    (ffilter (\<lambda>R. snd d |\<in>| finite_carrier (finite_structure R)) (finite_artifacts_at E (fst d)))"

lemma finite_application_target_member:
  assumes formed: "finite_environment_formed E"
  shows "finite_application_target E d=Some R \<longleftrightarrow>
    (fst d,R) |\<in>| finite_environment_artifacts E \<and> snd d |\<in>| finite_carrier (finite_structure R)"
proof -
  let ?T="ffilter (\<lambda>R. snd d |\<in>| finite_carrier (finite_structure R)) (finite_artifacts_at E (fst d))"
  have unique: "x=y" if "x |\<in>| ?T" "y |\<in>| ?T" for x y
    using formed that
    by (auto simp: finite_environment_formed_def finite_relation_functional_correct
      single_valued_def finite_artifacts_at_member)
  have selected: "finite_singleton_option ?T=Some R \<longleftrightarrow> R |\<in>| ?T"
    by (rule finite_singleton_option_member[OF unique])
  show ?thesis using selected
    by (auto simp only: finite_application_target_def ffmember_filter finite_artifacts_at_member)
qed

definition finite_application_ready where
  "finite_application_ready E d t=(finite_environment_formed E \<and>
    d |\<in>| finite_environment_positions E \<and> finite_term_formed t)"

lemma finite_application_ready_exact:
  "finite_application_ready E d t=(environment_formed (decode_finite_environment E) \<and>
    d\<in>environment_positions (decode_finite_environment E) \<and> term_formed (decode_finite_term t))"
  by (simp only: finite_application_ready_def finite_environment_formed_correct
    finite_environment_positions_correct finite_term_formed_correct)

definition finite_extend_native_application where
  "finite_extend_native_application E d t=(if finite_application_ready E d t then
    map_option (\<lambda>R. let q=Finite_Pair (Finite_Target (Finite_Anchor R (snd d))) t in
      (finite_future_call_environment E (fst d) R (snd d) t,finite_future_call_use E (fst d),
        finite_term_syntax_interior q,fimage fst (finite_term_literal_bindings q)))
      (finite_application_target E d) else None)"

theorem finite_extend_native_application_domain:
  "(\<exists>F u I K. finite_extend_native_application E d t=Some (F,u,I,K)) \<longleftrightarrow>
    finite_application_ready E d t"
proof (cases "finite_application_ready E d t")
  case False
  then show ?thesis by (simp only: finite_extend_native_application_def if_False option.distinct; blast)
next
  case True
  have formed: "finite_environment_formed E" and position: "d |\<in>| finite_environment_positions E"
    using True by (simp only: finite_application_ready_def; blast)+
  obtain R where artifact: "(fst d,R) |\<in>| finite_environment_artifacts E"
    and address: "snd d |\<in>| finite_carrier (finite_structure R)"
    using position by (cases d) (auto simp: finite_environment_positions_correct environment_positions_def)
  have target: "finite_application_target E d=Some R"
    using artifact address by (simp only: finite_application_target_member[OF formed]; blast)
  show ?thesis by (simp add: finite_extend_native_application_def True target Let_def)
qed

theorem finite_extend_native_application_correct:
  assumes extended: "finite_extend_native_application E d t=Some (F,u,I,K)"
  shows "finite_application_ready E d t"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "((d,t),I,K) |\<in>| finite_application_readings F u []"
proof -
  have ready: "finite_application_ready E d t"
    using extended finite_extend_native_application_domain[of E d t] by blast
  have ef: "environment_formed (decode_finite_environment E)"
    and argument: "term_formed (decode_finite_term t)"
    using ready by (simp only: finite_application_ready_exact; blast)+
  have finite_ef: "finite_environment_formed E"
    using ef by (simp only: finite_environment_formed_correct)
  obtain R where target: "finite_application_target E d=Some R"
    and fields: "F=finite_future_call_environment E (fst d) R (snd d) t"
      "u=finite_future_call_use E (fst d)"
      "I=finite_term_syntax_interior (Finite_Pair (Finite_Target (Finite_Anchor R (snd d))) t)"
      "K=fimage fst (finite_term_literal_bindings (Finite_Pair (Finite_Target (Finite_Anchor R (snd d))) t))"
    using extended ready by (auto simp: finite_extend_native_application_def Let_def split: option.splits)
  have art: "artifact_at (decode_finite_environment E) (fst d) (decode_finite_object R)"
    and anchor: "anchor_formed (decode_finite_object R,snd d)"
    using target finite_ef
    by (auto simp: finite_application_target_member[OF finite_ef] finite_environment_formed_def
      anchor_formed_def finite_exact_formed_correct)
  show "finite_application_ready E d t" by (rule ready)
  show "finite_environment_formed F"
    using future_call_environment_formed[OF ef art anchor argument]
    by (simp only: fields finite_environment_formed_correct finite_future_call_environment_exact)
  show "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: fields finite_future_call_environment_exact; rule future_call_includes_existing)
  show "u\<notin>fset (finite_environment_uses E)"
    by (simp only: fields finite_future_call_use_exact finite_environment_uses_correct;
      rule future_call_use_fresh[OF ef])
  show "finite_environment_agrees_on E F (finite_environment_uses E)"
    using future_call_existing_artifacts[OF ef art anchor argument]
      future_call_existing_bindings[OF ef]
    by (auto simp only: fields finite_environment_agrees_on_correct finite_environment_uses_correct
      finite_future_call_environment_exact)
  let ?q="Pair_Term (Target_Term (Occurrence_Anchor (decode_finite_object R,snd d))) (decode_finite_term t)"
  have slots: "fset K=rel_dom (term_literal_bindings ?q)"
    by (simp only: fields(4) finite_term_literal_domain decode_finite_term.simps decode_finite_target.simps)
  have exact: "native_application_at (decode_finite_environment F) u [] d (decode_finite_term t) (fset I) (fset K)"
    using future_call_application[OF ef art anchor argument]
    by (simp only: fields(1-3) finite_future_call_environment_exact finite_future_call_use_exact
      finite_term_syntax_interior_exact decode_finite_term.simps decode_finite_target.simps slots prod.collapse)
  show "((d,t),I,K) |\<in>| finite_application_readings F u []"
    using exact by (simp only: finite_application_readings_correct)
qed

export_code finite_extend_native_application checking SML

end
