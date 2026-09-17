theory Parallel_Replay_Readers
 imports Parallel_Inspection_Caches Factor_Native_Replay_Relation_Caches
begin

declare native_replay_relation_caches_def[code del]

lemma native_replay_relation_caches_parallel_code [code]:
 "native_replay_relation_caches rows=(let
    requests=fimage (\<lambda>(X,result). native_replay_result_requests X result) rows;
    sources=ffUnion (fimage fst requests);
    graphs=ffUnion (fimage (fst\<circ>snd) requests);
    apps=ffUnion (fimage (fst\<circ>snd\<circ>snd) requests);
    boundaries=ffUnion (fimage (fst\<circ>snd\<circ>snd\<circ>snd) requests);
    replays=ffUnion (fimage (snd\<circ>snd\<circ>snd\<circ>snd) requests)
    in (parallel_inspection_rows native_replay_reference (fimage fst rows),
      parallel_inspection_rows native_replay_source_query sources,
      parallel_inspection_rows native_replay_graph_query graphs,
      parallel_inspection_rows native_replay_application_query apps,
      parallel_inspection_rows native_replay_boundary_query boundaries,
      parallel_inspection_rows native_replay_closed_query replays))"
 by (simp only: parallel_inspection_rows_exact native_replay_relation_caches_def)

declare native_replay_caches_def[code del]

lemma native_replay_caches_parallel_code [code]:
 "native_replay_caches X results=(case X of (E,u,r,p,d,t) \<Rightarrow>
    let present=List.map_filter id results;
      sources=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,u,r),(B,u,r)]) present);
      graphs=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,root),(B,root)]) present);
      apps=concat (map (\<lambda>(A,M,root,G,au,I,K,B). [(A,au,[]),(B,au,[])]) present);
      boundaries=map (\<lambda>(A,M,root,G,au,I,K,B). (A,u,r,au,[],G)) present;
      replays=map (\<lambda>(A,M,root,G,au,I,K,B). (B,u,r,au,[],root)) present
    in (parallel_evaluation_cache native_replay_source_query sources,
      parallel_evaluation_cache native_replay_graph_query graphs,
      parallel_evaluation_cache native_replay_application_query apps,
      parallel_evaluation_cache native_replay_boundary_query boundaries,
      parallel_evaluation_cache native_replay_closed_query replays))"
 by (simp only: parallel_evaluation_cache_exact native_replay_caches_def)

end
