theory Factor_Recovered_Graph_Sharing
  imports Factor_Executable_Replay_Retention Established_Premises
begin

section \<open>Recovered graphs read their proof rows and closures once\<close>

text \<open>
  These code equations instantiate the loop-invariant sharing of
  Factor_Invariant_Evaluation_Sharing and the formation-once readings of
  Factor_Formation_Once_Readings for native graph recovery. A recovered graph
  previously evaluated its proof sites, and therefore every proof-node reading
  of the environment and the complete edge closure, once for each proof row.
  Each equation returns exactly the original value.
\<close>

declare finite_recovered_graph_def[code del]

lemma finite_recovered_graph_shared_code [code]:
  "finite_recovered_graph E root=(let rows=finite_proof_node_rows E;
      edges=ffUnion (fimage (\<lambda>(n,(N,D),I,K). fimage (\<lambda>(s,m). (m,n)) D) rows);
      sites=finsert root (fimage fst (ffilter (\<lambda>(m,n). n=root) (finite_edge_closure edges)));
      R=ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| sites) rows
    in \<lparr>finite_graph_inferences=fimage (\<lambda>(n,(N,D),I,K). (n,N)) R,
        finite_graph_discharges=ffUnion (fimage (\<lambda>(n,(N,D),I,K). fimage (\<lambda>(s,m). ((n,s),m)) D) R)\<rparr>)"
  by (simp only: finite_recovered_graph_def finite_native_proof_sites_def finite_native_proof_edges_def Let_def)

declare finite_native_definition_graph_def[code del]

lemma finite_native_definition_graph_shared_code [code]:
  "finite_native_definition_graph E roots=(let rows=finite_native_definition_rows E;
      edges=ffUnion (fimage (\<lambda>(d,p,F). ffUnion (fimage (\<lambda>(c,S). fimage (Pair d) (finite_schema_dependencies S)) F)) rows);
      sites=roots |\<union>| fimage snd (ffilter (\<lambda>(d,e). d |\<in>| roots) (finite_edge_closure edges))
    in ffilter (\<lambda>(d,p,F). d |\<in>| sites) rows)"
  by (simp only: finite_native_definition_graph_def finite_native_definition_sites_def
      finite_native_definition_edges_def Let_def)

section \<open>Proof-node rows establish environment formation once\<close>

definition finite_proof_node_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_node_readings_formed E u r=ffUnion (fimage (\<lambda>C.
      (if ([],[]) |\<in>| finite_record_candidates C r 0
       then {|((Finite_Assertion,{||}),{|r|},{||})|} else {||}) |\<union>|
      finite_three_field_record C r (finite_proof_inference_readings E u r))
      (finite_artifacts_at E u))"

text \<open>
  A proof-node reading is an instance of the first notion of @{text Established_Premises}: its
  definition checks the environment's formation at its entry, so its guard is the entry law, stated at
  the environment's arity. The rows and the graph's demands hoist that check through each reading
  (@{thm [source] checked_premise.checked_through}) and out of the union over the family
  (@{thm [source] checked_union}).
\<close>

lemma finite_proof_node_readings_checked_premise:
  "checked_premise finite_proof_node_readings finite_environment_formed finite_proof_node_readings_formed
    (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case
    by (intro ext) (simp only: finite_proof_node_readings_def finite_proof_node_readings_formed_def 1 if_True)
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_proof_node_readings_def 2 if_False)
qed

lemma finite_proof_node_readings_formed_guard:
  "finite_proof_node_readings E=
    (if finite_environment_formed E then finite_proof_node_readings_formed E else (\<lambda>u r. {||}))"
  by (rule checked_premise.checked_at_entry[OF finite_proof_node_readings_checked_premise])

declare finite_proof_node_rows_def[code del]

lemma finite_proof_node_rows_formed_once_code [code]:
  "finite_proof_node_rows E=(if finite_environment_formed E then ffUnion (fimage (\<lambda>n.
      fimage (Pair n) (finite_proof_node_readings_formed E (fst n) (snd n))) (finite_environment_positions E))
    else {||})"
proof -
  have each: "fimage (Pair n) (finite_proof_node_readings E (fst n) (snd n))=
      (if finite_environment_formed E then fimage (Pair n) (finite_proof_node_readings_formed E (fst n) (snd n))
       else {||})" for n
    by (simp only: checked_premise.checked_through[OF finite_proof_node_readings_checked_premise,
      where t="\<lambda>f. fimage (Pair n) (f (fst n) (snd n))"] fimage_fempty)
  show ?thesis by (simp only: finite_proof_node_rows_def each checked_union)
qed

definition finite_native_node_slots_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow>
    ('u definition_site,'u definition_site) finite_schema_graph_node \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) fset \<Rightarrow> local_address fset" where
  "finite_native_node_slots_formed E n N D=finite_reading_slots
    (ffilter (\<lambda>((M,F),I,K). M=N \<and> F=D) (finite_proof_node_readings_formed E (fst n) (snd n)))"

declare finite_native_graph_demands_def[code del]

lemma finite_native_graph_demands_checked_premise:
  "checked_premise finite_native_graph_demands finite_environment_formed
    (\<lambda>E G. ffUnion (fimage (\<lambda>(n,N).
      fimage (Pair (fst n)) (finite_native_node_slots_formed E n N (finite_graph_premises G n)))
        (finite_graph_inferences G)))
    (\<lambda>E G. {||})"
proof -
  have empty: "finite_reading_slots (ffilter Q {||})={||}" for Q
    by (auto simp: finite_reading_slots_def fset_eq_iff ffUnion.rep_eq fimage.rep_eq ffilter.rep_eq)
  have each: "fimage (Pair (fst n)) (finite_native_node_slots E n N D)=
      (if finite_environment_formed E then fimage (Pair (fst n)) (finite_native_node_slots_formed E n N D)
       else {||})" for E n N D
    by (simp only: finite_native_node_slots_def finite_native_node_slots_formed_def
      checked_premise.checked_through[OF finite_proof_node_readings_checked_premise,
        where t="\<lambda>f. fimage (Pair (fst n))
          (finite_reading_slots (ffilter (\<lambda>((M,F),I,K). M=N \<and> F=D) (f (fst n) (snd n))))"]
      empty fimage_fempty)
  have joined: "finite_native_graph_demands E G=(if finite_environment_formed E then ffUnion (fimage (\<lambda>(n,N).
      fimage (Pair (fst n)) (finite_native_node_slots_formed E n N (finite_graph_premises G n)))
        (finite_graph_inferences G)) else {||})" for E G
    by (simp only: finite_native_graph_demands_def case_prod_unfold each checked_union)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 E)
    show ?case by (intro ext) (simp only: joined 1 if_True)
  next
    case (2 E)
    show ?case by (intro ext) (simp only: joined 2 if_False)
  qed
qed

lemma finite_native_graph_demands_formed_once_code [code]:
  "finite_native_graph_demands E G=(if finite_environment_formed E then ffUnion (fimage (\<lambda>(n,N).
      fimage (Pair (fst n)) (finite_native_node_slots_formed E n N (finite_graph_premises G n)))
        (finite_graph_inferences G))
    else {||})"
  by (rule checked_premise.checked_through[OF finite_native_graph_demands_checked_premise, where t="\<lambda>f. f G"])

section \<open>Graph formation and read environments share their invariant sets\<close>

declare finite_graph_formed_def[code del]

lemma finite_graph_formed_shared_code [code]:
  "finite_graph_formed G root=(let N=finite_graph_nodes G; Ed=finite_graph_edges G; C=finite_edge_closure Ed in
    finite_relation_functional (finite_graph_inferences G) \<and>
    finite_relation_functional (finite_graph_discharges G) \<and>
    finite_relation_functional (finite_assertion_uses G) \<and>
    root |\<in>| N \<and>
    fBall Ed (\<lambda>(m,n). m |\<in>| N \<and> n |\<in>| N) \<and>
    fBall N (\<lambda>n. n=root \<or> (n,root) |\<in>| C) \<and>
    fBall C (\<lambda>(x,y). x\<noteq>y))"
  by (simp only: finite_graph_formed_def finite_edge_reaches_def finite_edge_wellfounded_def Let_def)

declare finite_read_environment_def[code del]

lemma finite_read_environment_shared_code [code]:
  "finite_read_environment E U D=(let W=finite_read_environment_uses E U D in
    \<lparr>finite_environment_artifacts=ffilter (\<lambda>entry. fst entry |\<in>| W) (finite_environment_artifacts E),
     finite_environment_bindings=ffilter (\<lambda>entry. fst entry |\<in>| D) (finite_environment_bindings E)\<rparr>)"
  by (simp only: finite_read_environment_def Let_def)

text \<open>
  A recovered proof graph and a native definition graph now read the rows of
  their environment once, close their edges once and filter the same rows by the
  resulting sites.
  Unformed environments keep every original empty reading; formed environments
  keep every original row, demand and discharge. Graph formation computes its
  nodes, edges and closure once for all edge, reachability and acyclicity
  checks, and a read environment computes its retained uses once.
\<close>

end
