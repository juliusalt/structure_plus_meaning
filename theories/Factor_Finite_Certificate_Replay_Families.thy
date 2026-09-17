theory Factor_Finite_Certificate_Replay_Families
  imports Factor_Finite_Native_Certificate_Replay Factor_Finite_Application_Proofs
    Finite_Function_Graphs
begin

definition finite_certificate_replay where
  "finite_certificate_replay E u r c=(case c of ((d,t),p) \<Rightarrow>
    finite_native_certificate_replay E u r p d t)"

definition finite_certificate_replays where
  "finite_certificate_replays E u r T=fimage (\<lambda>c. (c,finite_certificate_replay E u r c)) T"

theorem finite_certificate_replays_exact:
  "fset (finite_certificate_replays E u r T)=graph_map (fset T) (finite_certificate_replay E u r)"
  by (simp only: finite_certificate_replays_def finite_function_graph)

theorem finite_certificate_replays_member:
  "(c,R) |\<in>| finite_certificate_replays E u r T \<longleftrightarrow>
    c |\<in>| T \<and> R=finite_certificate_replay E u r c"
  by (simp only: finite_certificate_replays_exact graph_map_member)

theorem finite_certificate_replays_available:
  assumes source: "finite_native_source E u r=Some P"
    and sound: "finite_proofs_sound P T"
    and member: "(c,R) |\<in>| finite_certificate_replays E u r T"
  shows "R\<noteq>None"
proof -
  obtain d t p where shape: "c=((d,t),p)" by (cases c) auto
  have original: "((d,t),p) |\<in>| T"
    and actual: "R=finite_native_certificate_replay E u r p d t"
    using member by (simp only: shape finite_certificate_replays_member
      finite_certificate_replay_def case_prod_conv; blast)+
  have checked: "finite_checks_schema_proof P p d t"
    using sound original by (simp only: finite_proofs_sound_def finite_checks_schema_proof_exact; blast)
  have available: "\<exists>A M root G au I K B.
    finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)"
    using source checked by (simp only: finite_native_certificate_replay_domain; blast)
  show ?thesis using available by (simp only: actual; blast)
qed

text \<open>
  A complete certificate family determines a functional family of actual
  native replay results. Its keys retain each complete claim and proof.
  Every sound certificate at the stated original source has an available
  replay result. Each result keeps its own complete extending and retained
  environments; this family does not merge private installations.
\<close>

end
