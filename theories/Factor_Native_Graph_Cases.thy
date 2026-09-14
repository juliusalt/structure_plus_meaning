theory Factor_Native_Graph_Cases
  imports Factor_Finite_Graph_Construction Factor_Finite_Graph_Mappings Factor_Native_Node_Cases
begin

type_synonym native_graph_input =
  "(local_address option definition_site,local_address option definition_site,
    local_address option definition_site,local_address) finite_derivation_graph"
type_synonym native_graph_problem =
  "local_address option finite_artifact_environment\<times>native_graph_input\<times>local_address"
type_synonym native_graph_mapping = "(local_address\<times>local_address option definition_site) fset"
type_synonym native_graph_result =
  "(local_address option finite_artifact_environment\<times>native_graph_mapping\<times>
    local_address option definition_site\<times>local_address option finite_native_derivation_graph) option"

definition native_graph_star :: "native_node_problem\<Rightarrow>bool\<Rightarrow>native_graph_problem" where
  "native_graph_star X assertions=(case X of (E,N,D) \<Rightarrow>
    let leaves=fimage snd D; h=finite_binder_coordinates leaves;
      G=\<lparr>finite_graph_inferences=finsert ([],N)
        (fimage (\<lambda>n. (h n,if assertions then Finite_Assertion else N)) leaves),
        finite_graph_discharges=fimage (\<lambda>(s,n). (([],s),h n)) D\<rparr>
    in (E,G,[]))"

definition native_graph_problem :: "nat\<Rightarrow>native_graph_problem" where
  "native_graph_problem i=(if i<26 then native_graph_star (native_node_problem i) False
    else if i=26 \<or> i=27 then native_graph_star (native_node_problem (if i=26 then 8 else 9)) True
    else let (E,N,D)=native_node_problem 2; s=(Some [1],[26]); t=(None,[4]);
      nodes=(if i=28 then {||}
        else if i=29 then {|([],N),([1],N)|}
        else if i=30 then {|([],N)|}
        else if i=31 then {|([],N),([],Finite_Assertion)|}
        else if i=32 then {|([],N),([1],N),([2],N)|}
        else if i=33 then {|([],N),([1],N),([2],native_node_erase_bindings N)|}
        else if i=34 then {|([],N),([1],N),([2],N)|}
        else if i=35 then {|([],N),([1],N),([2],N),([3],N)|}
        else {|([256],Finite_Assertion)|});
      edges=(if i=30 then {|(([],s),[])|}
        else if i=32 then {|(([],s),[1]),(([],s),[2])|}
        else if i=33 then {|(([],s),[1]),(([],t),[2])|}
        else if i=34 then {|(([],s),[1]),(([1],s),[2])|}
        else if i=35 then {|(([],s),[1]),(([],t),[2]),(([1],s),[3]),(([2],s),[3])|}
        else {||})
    in (E,\<lparr>finite_graph_inferences=nodes,finite_graph_discharges=edges\<rparr>,if i=36 then [256] else []))"

definition native_graph_base :: "native_graph_problem\<Rightarrow>native_graph_result" where
  "native_graph_base X=(case X of (E,G,root) \<Rightarrow> finite_extend_native_graph E G root)"

definition native_graph_change_metadata where
  "native_graph_change_metadata f G=G\<lparr>finite_graph_inferences:=fimage (map_prod id f) (finite_graph_inferences G)\<rparr>"

definition native_graph_remove_use where
  "native_graph_remove_use u F=F\<lparr>
    finite_environment_artifacts:=ffilter (\<lambda>(v,A). v\<noteq>u) (finite_environment_artifacts F),
    finite_environment_bindings:=ffilter (\<lambda>((v,k),w). v\<noteq>u) (finite_environment_bindings F)\<rparr>"

definition native_graph_relocate where
  "native_graph_relocate h E G root=map_option (\<lambda>(F,M,r,H).
    (F,finite_edge_compose (fimage (\<lambda>n. (n,h n)) (finite_graph_nodes G)) M,r,H))
    (finite_extend_native_graph E (finite_rename_graph h G) (h root))"

definition native_graph_existing :: "native_graph_problem\<Rightarrow>native_graph_result" where
  "native_graph_existing X=(case X of (E,G,root) \<Rightarrow>
    let r=(Some [240],[]) in map_option (\<lambda>H. (E,{|(root,r)|},r,H))
      (finite_singleton_option (finite_native_graph_readings E r)))"

definition native_graph_original_apply ::
    "nat\<Rightarrow>native_graph_problem\<Rightarrow>native_graph_result\<Rightarrow>native_graph_result" where
  "native_graph_original_apply m X base=(case X of (E,G,root) \<Rightarrow>
    if m=4 then None else case base of None \<Rightarrow>
      (if m=10 then Some (native_node_empty_environment,{||},(None,[]),
        \<lparr>finite_graph_inferences={||},finite_graph_discharges={||}\<rparr>) else None)
    | Some (F,M,r,H) \<Rightarrow>
      if m=1 then finite_extend_native_graph E (native_graph_change_metadata native_node_erase_bindings G) root
      else if m=2 then finite_extend_native_graph E (native_graph_change_metadata native_node_change_clause G) root
      else if m=3 then finite_extend_native_graph E
        \<lparr>finite_graph_inferences=ffilter (\<lambda>(n,N). n=root) (finite_graph_inferences G),
          finite_graph_discharges={||}\<rparr> root
      else if m=5 then Some (native_graph_remove_use (fst r) F,M,r,H)
      else if m=6 then (case sorted_list_of_fset (fminus (finite_graph_nodes H) {|r|}) of
        [] \<Rightarrow> base | other#rest \<Rightarrow> Some (F,M,other,H))
      else if m=7 then Some (native_node_erase_unused F,M,r,H)
      else if m=8 then Some (F,{||},r,H)
      else if m=9 then native_graph_relocate (\<lambda>n. if n=[] then [] else ([6]::local_address)) E G root
      else if m=11 then native_graph_relocate (\<lambda>n. if n=[] then [255] else 254#n) E G root
      else if m=12 then native_graph_existing X else base)"

definition native_graph_apply ::
    "nat\<Rightarrow>native_graph_problem\<Rightarrow>native_graph_result\<Rightarrow>native_graph_result" where
  "native_graph_apply m X base=(if m=13 then
      (case native_graph_original_apply 12 X base of None \<Rightarrow> base
        | Some (F,M,r,H) \<Rightarrow> (case X of (E,G,root) \<Rightarrow>
          if finite_graph_mapping M G root H r then Some (F,M,r,H) else base))
    else if m=14 then (case native_graph_original_apply 9 X base of None \<Rightarrow> base | Some v \<Rightarrow> Some v)
    else native_graph_original_apply m X base)"

lemma native_graph_apply_original_indices:
  assumes "m<13"
  shows "native_graph_apply m X base=native_graph_original_apply m X base"
proof -
  have "m\<noteq>13" "m\<noteq>14" using assms by arith+
  then show ?thesis by (simp only: native_graph_apply_def if_False)
qed

definition native_graph_method :: "nat\<Rightarrow>native_graph_problem\<Rightarrow>native_graph_result" where
  "native_graph_method m X=native_graph_apply m X (native_graph_base X)"

lemma native_graph_method_original:
  "native_graph_method 0 (E,G,root)=finite_extend_native_graph E G root"
  by (simp add: native_graph_method_def native_graph_apply_def native_graph_original_apply_def native_graph_base_def split: option.splits)

definition native_graph_methods :: "nat list" where
  "native_graph_methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]"
definition native_graph_indices :: "nat list" where "native_graph_indices=[0..<37]"

export_code native_graph_problem native_graph_method native_graph_methods native_graph_indices checking SML

text \<open>
  Every subject is the complete original environment, finite graph and root.
  Stars reuse actual node metadata and source sockets. Their private leaf
  identities distinguish actual target values without requiring those values
  to be existing source positions: the constructor allocates new graph nodes.
  Further subjects retain shared inference targets, distinct and shared
  assertions, missing roots, detached nodes, cycles, contradictory rows,
  unequal leaf metadata, a chain, a diamond and a non-octet private key.

  Candidate operations return actual environments, complete maps and graphs.
  Metadata changes keep original availability. A merging candidate composes
  the full original map, and an alternative injective placement changes the
  private order before allocation. Reading an existing native graph exposes
  freshness independently of recovery. No inspection result is supplied.

  Further controls retain the valid original construction when a proposed
  reuse does not recover the entire original graph, or when merging returns
  no result. Their successful alternatives still carry the actual complete
  map and graph. The original thirteen operations remain unchanged, and the
  expanded scope can separate freshness and injectivity from other failures.
\<close>

end
