theory Factor_Native_Replay_Assessment
  imports Factor_Finite_Native_Certificate_Replay Factor_Finite_Native_Graph_Assessment Factor_Native_Derivation_Cases
begin

type_synonym native_replay_subject =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    native_derivation_tree\<times>local_address option definition_site\<times>finite_factor_term"
type_synonym native_replay_node =
  "(local_address,local_address,local_address option definition_site,local_address) finite_instantiated_proof_node"
type_synonym native_replay_result =
  "(local_address option finite_artifact_environment\<times>
    (native_replay_node\<times>local_address option definition_site) fset\<times>
    local_address option definition_site\<times>local_address option finite_native_derivation_graph\<times>
    local_address option\<times>local_address fset\<times>local_address fset\<times>
    local_address option finite_artifact_environment) option"

definition native_replay_reference :: "native_replay_subject\<Rightarrow>(local_address option finite_native_system\<times>bool) option" where
  "native_replay_reference X=(case X of (E,u,r,p,d,t) \<Rightarrow>
    map_option (\<lambda>P. (P,finite_checks_schema_proof P p d t)) (finite_native_source E u r))"

definition native_replay_original where
  "native_replay_original X=(case native_replay_reference X of None \<Rightarrow> None
    | Some (P,checked) \<Rightarrow> if checked then Some P else None)"

theorem native_replay_original_exact:
  "native_replay_original (E,u,r,p,d,t)=Some P \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
proof -
  have finite: "native_replay_original (E,u,r,p,d,t)=Some P \<longleftrightarrow>
    finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t"
    by (auto simp: native_replay_original_def native_replay_reference_def split: option.splits if_splits)
  show ?thesis by (simp only: finite finite_native_source_correct finite_checks_schema_proof_exact)
qed

definition native_replay_result_condition :: "nat\<Rightarrow>native_replay_subject\<Rightarrow>
    local_address option finite_native_system\<Rightarrow>native_replay_result\<Rightarrow>bool" where
  "native_replay_result_condition f X P result=(case X of (E,u,r,p,d,t) \<Rightarrow>
    case result of None \<Rightarrow> False | Some (A,M,root,G,au,I,K,B) \<Rightarrow>
      if f<5 then finite_native_graph_result_condition f E (finite_source_proof_graph P (p,d,t))
        (p,d,t) (Some (A,M,root,G))
      else if f=5 then native_package_at (decode_finite_environment A) u r (decode_finite_system P) \<and>
        native_application_at (decode_finite_environment A) au [] d (decode_finite_term t) (fset I) (fset K)
      else if f=6 then decode_finite_environment B=
        native_replay_environment (decode_finite_environment A) u r au [] (decode_finite_graph G)
      else if f=7 then environment_formed (decode_finite_environment B) \<and>
        environment_included (decode_finite_environment B) (decode_finite_environment A) \<and>
        native_package_at (decode_finite_environment B) u r (decode_finite_system P) \<and>
        native_schema_graph_at (decode_finite_environment B) root (decode_finite_graph G) \<and>
        native_application_at (decode_finite_environment B) au [] d (decode_finite_term t) (fset I) (fset K)
      else if f=8 then native_replay_at (decode_finite_environment B) u r au [] root {} else False)"

definition native_replay_result_assessment_by where
  "native_replay_result_assessment_by read_graph read_source read_app read_boundary read_replay X P result=(case X of (E,u,r,p,d,t) \<Rightarrow>
    map_option (\<lambda>(A,M,root,G,au,I,K,B). let
      graph=finite_native_graph_result_assessment_by read_graph E (finite_source_proof_graph P (p,d,t)) (p,d,t) (Some (A,M,root,G));
      source=read_source A u r; app=read_app A au [];
      expected=read_boundary A u r au [] G;
      kept_source=read_source B u r; kept_app=read_app B au [];
      kept_graph=read_graph B root; replay=read_replay B u r au [] root
      in (graph,(source,app,expected,kept_source,kept_app,kept_graph,replay),
        P |\<in>| source \<and> ((d,t),I,K) |\<in>| app,
        B=expected,
        finite_environment_formed B \<and> finite_environment_included B A \<and>
          P |\<in>| kept_source \<and> G |\<in>| kept_graph \<and> ((d,t),I,K) |\<in>| kept_app,
        {||} |\<in>| replay)) result)"

definition native_replay_result_assessment :: "native_replay_subject\<Rightarrow>
    local_address option finite_native_system\<Rightarrow>native_replay_result\<Rightarrow>_" where
  "native_replay_result_assessment X P result=native_replay_result_assessment_by
    finite_native_graph_readings finite_native_package_readings finite_application_readings
    finite_native_replay_environment finite_native_replay_readings X P result"

definition native_replay_result_inspect where
  "native_replay_result_inspect A (f::nat)=(case A of None \<Rightarrow> False
    | Some (graph,readings,source,boundary,retained,closed) \<Rightarrow>
      if f<5 then finite_native_graph_result_inspect graph f else if f=5 then source
      else if f=6 then boundary else if f=7 then retained else if f=8 then closed else False)"

theorem native_replay_result_assessment_exact:
  "native_replay_result_inspect (native_replay_result_assessment X P result) f=
    native_replay_result_condition f X P result"
proof -
  obtain E u r p d t where input: "X=(E,u,r,p,d,t)" by (cases X) auto
  have boundary: "B=finite_native_replay_environment A u r au [] G \<longleftrightarrow>
    decode_finite_environment B=native_replay_environment (decode_finite_environment A) u r au [] (decode_finite_graph G)"
    for A au G B
    by (simp only: finite_native_replay_environment_correct[symmetric] decode_finite_environment_injective)
  show ?thesis
    by (cases result)
      (auto simp: input native_replay_result_assessment_def native_replay_result_assessment_by_def
        finite_native_graph_result_assessment_def[symmetric] native_replay_result_inspect_def
        native_replay_result_condition_def Let_def finite_native_graph_result_assessment_exact
        finite_native_package_readings_correct finite_application_readings_correct boundary
        finite_environment_formed_correct finite_environment_included_correct finite_native_graph_readings_correct
        finite_native_replay_readings_correct split: prod.splits)
qed

definition native_replay_condition where
  "native_replay_condition (f::nat) method X=(let original=native_replay_original X in
    if f=9 then (original=None \<longrightarrow> method X=None)
    else if f<9 then (original\<noteq>None \<longrightarrow>
      (case original of None \<Rightarrow> False | Some P \<Rightarrow> native_replay_result_condition f X P (method X))) else False)"

definition native_replay_assessment_from where
  "native_replay_assessment_from X original result=(original\<noteq>None,
    (case original of None \<Rightarrow> None | Some P \<Rightarrow> native_replay_result_assessment X P result),result=None)"

definition native_replay_assessment where
  "native_replay_assessment X result=native_replay_assessment_from X (native_replay_original X) result"

definition native_replay_inspect where
  "native_replay_inspect A (f::nat)=(case A of (ready,body,rejected) \<Rightarrow>
    if f=9 then (\<not>ready \<longrightarrow> rejected) else if f<9 then (ready \<longrightarrow> native_replay_result_inspect body f) else False)"

theorem native_replay_assessment_exact:
  "native_replay_inspect (native_replay_assessment X (method X)) f=native_replay_condition f method X"
  by (cases "native_replay_original X")
    (auto simp: native_replay_assessment_def native_replay_assessment_from_def native_replay_inspect_def
      native_replay_condition_def native_replay_result_assessment_exact Let_def)

export_code native_replay_reference native_replay_assessment native_replay_inspect checking SML

text \<open>
  The complete original source and supplied certificate determine readiness.
  Every result is assessed through the returned full environment, complete map,
  graph, actual call position and interior/binding sets, and retained environment.
  Full extension, exact least retention, recovery of the original source, graph
  and call, and closed native replay remain separate conditions. Actual complete
  reader results accompany the booleans. Closed replay alone cannot establish
  a claimed correspondence or preservation of unrelated original artifacts.
\<close>

end
