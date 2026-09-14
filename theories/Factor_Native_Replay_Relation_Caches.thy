theory Factor_Native_Replay_Relation_Caches
  imports Factor_Native_Replay_Caches Finite_Evaluation_Relations
begin

definition native_replay_result_requests where
  "native_replay_result_requests X result=(case X of (E,u,r,p,d,t) \<Rightarrow>
    case result of None \<Rightarrow> ({||},{||},{||},{||},{||})
    | Some (A,M,root,G,au,I,K,B) \<Rightarrow>
      ({|(A,u,r),(B,u,r)|},{|(A,root),(B,root)|},{|(A,au,[]),(B,au,[])|},
        {|(A,u,r,au,[],G)|},{|(B,u,r,au,[],root)|}))"

definition native_replay_relation_caches where
  "native_replay_relation_caches rows=(let
    requests=fimage (\<lambda>(X,result). native_replay_result_requests X result) rows;
    sources=ffUnion (fimage fst requests);
    graphs=ffUnion (fimage (fst\<circ>snd) requests);
    apps=ffUnion (fimage (fst\<circ>snd\<circ>snd) requests);
    boundaries=ffUnion (fimage (fst\<circ>snd\<circ>snd\<circ>snd) requests);
    replays=ffUnion (fimage (snd\<circ>snd\<circ>snd\<circ>snd) requests)
    in (finite_inspection_rows native_replay_reference (fimage fst rows),
      finite_inspection_rows native_replay_source_query sources,
      finite_inspection_rows native_replay_graph_query graphs,
      finite_inspection_rows native_replay_application_query apps,
      finite_inspection_rows native_replay_boundary_query boundaries,
      finite_inspection_rows native_replay_closed_query replays))"

definition native_replay_relation_result_assessment where
  "native_replay_relation_result_assessment caches X P result=(case caches of
    (references,sources,graphs,apps,boundaries,replays) \<Rightarrow>
    native_replay_result_assessment_by
      (\<lambda>E root. finite_relation_cached_evaluation native_replay_graph_query graphs (E,root))
      (\<lambda>E u r. finite_relation_cached_evaluation native_replay_source_query sources (E,u,r))
      (\<lambda>E u r. finite_relation_cached_evaluation native_replay_application_query apps (E,u,r))
      (\<lambda>E u r au ar G. finite_relation_cached_evaluation native_replay_boundary_query boundaries (E,u,r,au,ar,G))
      (\<lambda>E u r au ar root. finite_relation_cached_evaluation native_replay_closed_query replays (E,u,r,au,ar,root))
      X P result)"

theorem native_replay_relation_result_assessment_exact:
  "native_replay_relation_result_assessment (native_replay_relation_caches rows) X P result=
    native_replay_result_assessment X P result"
  by (simp add: native_replay_relation_caches_def native_replay_relation_result_assessment_def
    Let_def finite_relation_cached_evaluation_exact native_replay_source_query_def native_replay_graph_query_def
    native_replay_application_query_def native_replay_boundary_query_def native_replay_closed_query_def
    native_replay_result_assessment_def)

definition native_replay_relation_assessment where
  "native_replay_relation_assessment caches X result=(let
    reference=finite_relation_cached_evaluation native_replay_reference (fst caches) X;
    original=(case reference of None \<Rightarrow> None | Some (P,checked) \<Rightarrow> if checked then Some P else None)
    in (reference,(original\<noteq>None,
      (case original of None \<Rightarrow> None | Some P \<Rightarrow>
        native_replay_relation_result_assessment caches X P result),result=None)))"

theorem native_replay_relation_assessment_exact:
  "native_replay_relation_assessment (native_replay_relation_caches rows) X result=
    (native_replay_reference X,native_replay_assessment X result)"
proof -
  have reference: "finite_relation_cached_evaluation native_replay_reference
      (fst (native_replay_relation_caches rows)) X=native_replay_reference X"
    by (simp only: native_replay_relation_caches_def Let_def fst_conv finite_relation_cached_evaluation_exact)
  show ?thesis by (simp only: native_replay_relation_assessment_def reference Let_def
    native_replay_relation_result_assessment_exact native_replay_original_def[symmetric]
    native_replay_assessment_def native_replay_assessment_from_def)
qed

text \<open>
  Complete subject/result pairs supply every actual request to six existing
  readers. Reference sharing retains the actual program and complete proof
  check. The other five operations are the original package, graph, call,
  least-boundary and closed-replay readers. Exactness covers arbitrary query
  families and queried subjects, with the complete original assessment value.
\<close>

end
