theory Factor_Native_Replay_Caches
  imports Factor_Native_Replay_Assessment Finite_Evaluation_Caches
begin

definition native_replay_source_query where
  "native_replay_source_query q=(case q of (E,u,r) \<Rightarrow> finite_native_package_readings E u r)"
definition native_replay_graph_query where
  "native_replay_graph_query q=(case q of (E,root) \<Rightarrow> finite_native_graph_readings E root)"
definition native_replay_application_query where
  "native_replay_application_query q=(case q of (E,u,r) \<Rightarrow> finite_application_readings E u r)"
definition native_replay_boundary_query where
  "native_replay_boundary_query q=(case q of (E,u,r,au,ar,G) \<Rightarrow> finite_native_replay_environment E u r au ar G)"
definition native_replay_closed_query where
  "native_replay_closed_query q=(case q of (E,u,r,au,ar,root) \<Rightarrow> finite_native_replay_readings E u r au ar root)"

definition native_replay_caches where
  "native_replay_caches X results=(case X of (E,u,r,p,d,t) \<Rightarrow>
    let present=List.map_filter id results;
      sources=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,u,r),(B,u,r)]) present);
      graphs=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,root),(B,root)]) present);
      apps=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,au,[]),(B,au,[])]) present);
      boundaries=map (\<lambda>(A,M,root,G,au,I,K,B). (A,u,r,au,[],G)) present;
      replays=map (\<lambda>(A,M,root,G,au,I,K,B). (B,u,r,au,[],root)) present
    in (finite_evaluation_cache native_replay_source_query sources,
      finite_evaluation_cache native_replay_graph_query graphs,
      finite_evaluation_cache native_replay_application_query apps,
      finite_evaluation_cache native_replay_boundary_query boundaries,
      finite_evaluation_cache native_replay_closed_query replays))"

definition native_replay_cached_result_assessment where
  "native_replay_cached_result_assessment caches X P result=(case caches of (sources,graphs,apps,boundaries,replays) \<Rightarrow>
    native_replay_result_assessment_by
      (\<lambda>E root. finite_cached_evaluation native_replay_graph_query graphs (E,root))
      (\<lambda>E u r. finite_cached_evaluation native_replay_source_query sources (E,u,r))
      (\<lambda>E u r. finite_cached_evaluation native_replay_application_query apps (E,u,r))
      (\<lambda>E u r au ar G. finite_cached_evaluation native_replay_boundary_query boundaries (E,u,r,au,ar,G))
      (\<lambda>E u r au ar root. finite_cached_evaluation native_replay_closed_query replays (E,u,r,au,ar,root))
      X P result)"

theorem native_replay_cached_result_assessment_exact:
  "native_replay_cached_result_assessment (native_replay_caches X results) X P result=
    native_replay_result_assessment X P result"
  by (cases X)
    (simp add: native_replay_cached_result_assessment_def native_replay_caches_def Let_def
      finite_cached_evaluation_exact native_replay_source_query_def native_replay_graph_query_def
      native_replay_application_query_def native_replay_boundary_query_def native_replay_closed_query_def
      native_replay_result_assessment_def)

definition native_replay_cached_assessment_from where
  "native_replay_cached_assessment_from caches X original result=(original\<noteq>None,
    (case original of None \<Rightarrow> None | Some P \<Rightarrow> native_replay_cached_result_assessment caches X P result),result=None)"

theorem native_replay_cached_assessment_from_exact:
  "native_replay_cached_assessment_from (native_replay_caches X results) X original result=
    native_replay_assessment_from X original result"
  by (simp only: native_replay_cached_assessment_from_def native_replay_assessment_from_def
    native_replay_cached_result_assessment_exact)

text \<open>
  Actual candidate outputs determine the complete requests to five original
  native operations. Every request retains its entire environment and roots;
  the replay-boundary request also retains its complete graph. These tables
  preserve every original result and all reader evidence, even for a candidate
  outside the prepared family. Sharing changes neither observation conditions
  nor candidate results. A complete execution comparison remains required.
\<close>

end
