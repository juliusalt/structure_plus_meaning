theory Factor_Finite_Source_Decision_Replay
  imports Factor_Finite_Source_Decisions Factor_Finite_Certificate_Replay_Families
begin

definition finite_decision_certificates where
  "finite_decision_certificates Z=(case Z of (d,F,u,Q,D,A,T,Ys) \<Rightarrow>
    ffilter (\<lambda>((e,t),p). e=d \<and> t |\<in>| Ys) T)"

definition finite_decision_replay_body where
  "finite_decision_replay_body Z=(case Z of (d,F,u,Q,D,A,T,Ys) \<Rightarrow>
    (Z,finite_certificate_replays F u [] (finite_decision_certificates Z)))"

definition finite_source_decision_replay where
  "finite_source_decision_replay supported C E u r Xs=
    map_option finite_decision_replay_body (finite_source_decision supported C E u r Xs)"

theorem finite_source_decision_replay_projection:
  "map_option fst (finite_source_decision_replay supported C E u r Xs)=
    finite_source_decision supported C E u r Xs"
  by (cases "finite_source_decision supported C E u r Xs")
    (auto simp: finite_source_decision_replay_def finite_decision_replay_body_def split: prod.splits)

theorem finite_source_decision_replay_result:
  "finite_source_decision_replay supported C E u r Xs=Some ((d,F,v,Q,D,A,T,Ys),R) \<longleftrightarrow>
    finite_source_decision supported C E u r Xs=Some (d,F,v,Q,D,A,T,Ys) \<and>
    R=finite_certificate_replays F v [] (finite_decision_certificates (d,F,v,Q,D,A,T,Ys))"
  by (cases d) (auto simp: finite_source_decision_replay_def finite_decision_replay_body_def
    split: option.splits prod.splits)

theorem finite_source_decision_replay_available:
  assumes result: "finite_source_decision_replay supported C E u r Xs=
      Some ((d,F,v,Q,D,A,T,Ys),R)"
    and row: "(c,replay) |\<in>| R"
  shows "replay\<noteq>None"
proof -
  have decision: "finite_source_decision supported C E u r Xs=Some (d,F,v,Q,D,A,T,Ys)"
    and family: "R=finite_certificate_replays F v [] (finite_decision_certificates (d,F,v,Q,D,A,T,Ys))"
    using result by (simp only: finite_source_decision_replay_result; blast)+
  have source: "finite_native_source F v []=Some Q"
    and certificates: "finite_native_program_proofs F v [] D=Some (Q,A,T)"
    using decision by (simp only: finite_source_decision_conditions; blast)+
  have sound: "finite_proofs_sound Q T"
    by (rule finite_native_program_proofs_correct(3)[OF certificates])
  have selected: "finite_proofs_sound Q (finite_decision_certificates (d,F,v,Q,D,A,T,Ys))"
    using sound by (auto simp: finite_decision_certificates_def finite_proofs_sound_def)
  show ?thesis by (rule finite_certificate_replays_available[OF source selected row[unfolded family]])
qed

context finite_native_source_constructor
begin

theorem finite_source_decision_replay_terms:
  assumes result: "finite_source_decision_replay supported C E u r Xs=
      Some ((d,F,v,Q,D,A,T,Ys),R)"
    and original: "finite_native_source E u r=Some P"
  shows "fset Ys={t\<in>fset Xs. expected P (decode_finite_term t)}"
    "t |\<in>| Ys \<Longrightarrow> \<exists>p A' M root G au I K B.
      (((d,t),p),Some (A',M,root,G,au,I,K,B)) |\<in>| R"
proof -
  have decision: "finite_source_decision supported C E u r Xs=Some (d,F,v,Q,D,A,T,Ys)"
    and family: "R=finite_certificate_replays F v [] (finite_decision_certificates (d,F,v,Q,D,A,T,Ys))"
    using result by (simp only: finite_source_decision_replay_result; blast)+
  show "fset Ys={t\<in>fset Xs. expected P (decode_finite_term t)}"
    by (rule finite_source_decision_exact(1)[OF decision original])
  show "t |\<in>| Ys \<Longrightarrow> \<exists>p A' M root G au I K B.
    (((d,t),p),Some (A',M,root,G,au,I,K,B)) |\<in>| R"
  proof -
    assume admitted: "t |\<in>| Ys"
    obtain p where certificate: "((d,t),p) |\<in>| T"
      using finite_source_decision_exact(4)[OF decision original admitted] by blast
    have selected: "((d,t),p) |\<in>| finite_decision_certificates (d,F,v,Q,D,A,T,Ys)"
      using certificate admitted by (simp only: finite_decision_certificates_def case_prod_conv ffilter.rep_eq Set.filter_eq; simp)
    have member: "(((d,t),p),finite_certificate_replay F v [] ((d,t),p)) |\<in>| R"
      by (simp only: family finite_certificate_replays_member selected simp_thms)
    have available: "finite_certificate_replay F v [] ((d,t),p)\<noteq>None"
      by (rule finite_source_decision_replay_available[OF result member])
    then obtain A' M root G au I K B where shape:
      "finite_certificate_replay F v [] ((d,t),p)=Some (A',M,root,G,au,I,K,B)"
      by (cases "finite_certificate_replay F v [] ((d,t),p)") auto
    show "\<exists>p A' M root G au I K B. (((d,t),p),Some (A',M,root,G,au,I,K,B)) |\<in>| R"
      using member by (simp only: shape; blast)
  qed
qed

end

text \<open>
  The original complete decision is preserved exactly. Its admitted terms
  determine the required target certificates; every such certificate receives
  its actual native replay. Empty admitted families remain successful empty
  replay families. Missing original decisions remain unavailable.

  Each native replay is checked against the installed decision source.
  The original constructor contract still determines what that entry means
  about the original subject. Replay alone does not establish that contract
  or justify omitting any original requirement.
\<close>

end
