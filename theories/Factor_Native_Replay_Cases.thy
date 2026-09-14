theory Factor_Native_Replay_Cases
  imports Factor_Native_Replay_Assessment Factor_Native_Graph_Cases Factor_Native_Certificate_Identity_Cases
begin

definition native_replay_base :: "native_replay_subject\<Rightarrow>native_replay_result" where
  "native_replay_base X=(case X of (E,u,r,p,d,t) \<Rightarrow> finite_native_certificate_replay E u r p d t)"

definition native_replay_apply :: "nat\<Rightarrow>native_replay_subject\<Rightarrow>native_replay_result\<Rightarrow>native_replay_result" where
  "native_replay_apply m X base=(if m=1 then None else case X of (E,u,r,p,d,t) \<Rightarrow>
    case base of None \<Rightarrow> (if m=2 then Some (E,{||},(u,r),
      \<lparr>finite_graph_inferences={||},finite_graph_discharges={||}\<rparr>,u,{||},{||},E) else None)
    | Some (A,M,root,G,au,I,K,B) \<Rightarrow>
      if m=3 then Some (A,{||},root,G,au,I,K,B)
      else if m=4 then Some (A,fimage (\<lambda>(n,s). (n,root)) M,root,G,au,I,K,B)
      else if m=5 then Some (A,M,root,G\<lparr>finite_graph_discharges:={||}\<rparr>,au,I,K,B)
      else if m=6 then Some (A,M,(Some [255],[]),G,au,I,K,B)
      else if m=7 then Some (native_graph_remove_use (fst root) A,M,root,G,au,I,K,B)
      else if m=8 then Some (E,M,root,G,au,I,K,B)
      else if m=9 then Some (A,M,root,G,au,{||},{||},B)
      else if m=10 then Some (A,M,root,G,u,I,K,B)
      else if m=11 then Some (A,M,root,G,au,I,K,A)
      else if m=12 then Some (A,M,root,G,au,I,K,native_node_empty_environment)
      else if m=13 then Some (B,M,root,G,au,I,K,B) else base)"

definition native_replay_method where
  "native_replay_method m X=native_replay_apply m X (native_replay_base X)"

lemma native_replay_method_original:
  "native_replay_method 0 X=native_replay_base X"
  by (cases X; cases "native_replay_base X") (simp_all add: native_replay_method_def native_replay_apply_def)

definition native_replay_methods :: "nat list" where
  "native_replay_methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13]"

definition native_replay_subject_family where
  "native_replay_subject_family w=(case (if w=26 then native_certificate_identity_query else native_history_problem w) of None \<Rightarrow> {||}
    | Some (E,u,r,D) \<Rightarrow> (case native_derivation_base (E,u,r,D) of None \<Rightarrow> {||}
      | Some (P,A,T) \<Rightarrow> fimage (\<lambda>((d,t),p). (E,u,r,p,d,t)) T))"

definition native_replay_problem :: "nat\<Rightarrow>native_replay_subject fset" where
  "native_replay_problem w=(if w<27 then native_replay_subject_family w else
    fimage (\<lambda>(E,u,r,p,d,t).
      (if w=28 then native_node_empty_environment else if w=29 then E\<lparr>finite_environment_artifacts:=
        finsert (Some [250],finite_empty_artifact) (finite_environment_artifacts E)\<rparr> else E,
        u,r,if w=27 then native_derivation_alter_root 4 p else p,d,t)) (native_replay_subject_family 0))"

definition native_replay_indices :: "nat list" where
  "native_replay_indices=[0,8,17,26,27,28,29]"

export_code native_replay_method native_replay_methods native_replay_subject_family native_replay_problem native_replay_indices checking SML

text \<open>
  Actual native sources and generated certificates supply proposed complete
  replay subjects. The finite family retains every proof without ordering proof
  values. Candidate operations alter actual maps, graph fields, source artifacts,
  call positions, claimed interiors and retained environments. Each remains
  subject to the complete independent assessment and native execution.
\<close>

end
