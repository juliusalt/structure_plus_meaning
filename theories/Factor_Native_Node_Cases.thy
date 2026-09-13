theory Factor_Native_Node_Cases
  imports Factor_Finite_Proof_Node_Installation Retained_Clause_Execution
begin

type_synonym native_node_metadata =
  "(local_address option definition_site,local_address option definition_site) finite_schema_graph_node"
type_synonym native_node_targets =
  "(local_address option definition_site\<times>local_address option definition_site) fset"
type_synonym native_node_problem =
  "local_address option finite_artifact_environment\<times>native_node_metadata\<times>native_node_targets"
type_synonym native_node_result =
  "(local_address option finite_artifact_environment\<times>local_address option) option"

definition native_node_empty_environment :: "local_address option finite_artifact_environment" where
  "native_node_empty_environment=\<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>"

definition native_node_source :: "local_address option finite_artifact_environment" where
  "native_node_source=finite_fresh_reference_sequence (finite_guard_environment False) [Some [240],Some [241]]
    (\<lambda>_. finite_block_artifact (finite_assertion_node_block :: local_address option finite_syntax_block)) (\<lambda>_. {||}) (\<lambda>_. {||})"

definition native_node_problem :: "nat\<Rightarrow>native_node_problem" where
  "native_node_problem i=(let
    c=(if i=4 then (Some [242],[]) else (Some [1],[7]));
    a=(if i=5 then (Some [242],[]) else (Some [1],[10]));
    t=(if i=6 then Finite_Payload [256]
      else if i=24 then Finite_Pair (Finite_Payload [])
        (Finite_Pair (Finite_Target (Finite_Whole (finite_payload_syntax [42])))
          (Finite_Target (Finite_Anchor (finite_payload_syntax [42]) [])))
      else if i=20 then Finite_Target (Finite_Whole (finite_payload_syntax [42]))
      else if i=21 then Finite_Target (Finite_Anchor (finite_payload_syntax [42]) []) else Finite_Payload []);
    V=(if i=1 then {||} else if i=3 then {|(a,t),(a,Finite_Payload [1])|}
      else if i=25 then {|(a,t),((None,[4]),Finite_Payload [1])|}
      else if i=22 then {|(a,t),((None,[4]),t)|} else {|(a,t)|});
    s=(Some [1],[26]); v=(Some [240],[]); w=(Some [241],[]);
    D=(if i=7 \<or> i=14 then {|(s,v)|}
      else if i=8 then {|(s,v),((None,[4]),v)|}
      else if i=9 then {|(s,v),((None,[4]),w)|}
      else if i=10 then {|(s,v),(s,w)|}
      else if i=11 then {|(s,(Some [242],[]))|}
      else if i=12 then {|(s,(Some [240],[256]))|}
      else if i=13 then {|((Some [242],[]),v)|}
      else if i=19 then {|(s,(Some [250],[]))|} else {||});
    E=(if i=16 then native_node_empty_environment
      else if i=15 then native_node_source\<lparr>finite_environment_artifacts:=finsert
        (Some [255],finite_payload_syntax [256]) (finite_environment_artifacts native_node_source)\<rparr>
      else if i=17 \<or> i=18 \<or> i=19 \<or> i=23 then
        native_node_source\<lparr>finite_environment_artifacts:=finsert
          (Some [250],finite_payload_syntax (if i=18 then [256] else [42]))
          (finite_environment_artifacts native_node_source)\<rparr> else native_node_source)
    in (E,if i=0 \<or> i=14 \<or> i=16 \<or> i=23 then Finite_Assertion else Finite_Inference c V,D))"

fun native_node_erase_bindings :: "native_node_metadata\<Rightarrow>native_node_metadata" where
  "native_node_erase_bindings Finite_Assertion=Finite_Assertion"
| "native_node_erase_bindings (Finite_Inference c V)=Finite_Inference c {||}"

fun native_node_change_clause :: "native_node_metadata\<Rightarrow>native_node_metadata" where
  "native_node_change_clause Finite_Assertion=Finite_Assertion"
| "native_node_change_clause (Finite_Inference c V)=Finite_Inference (None,[4]) V"

definition native_node_erase_unused where
  "native_node_erase_unused F=F\<lparr>finite_environment_artifacts:=
    ffilter (\<lambda>(v,A). v\<noteq>Some [250]) (finite_environment_artifacts F)\<rparr>"

definition native_node_method :: "nat\<Rightarrow>native_node_problem\<Rightarrow>native_node_result" where
  "native_node_method m X=(case X of (E,N,D) \<Rightarrow>
    if m=1 then finite_extend_proof_node E Finite_Assertion {||}
    else if m=2 then finite_extend_proof_node E (native_node_erase_bindings N) D
    else if m=3 then finite_extend_proof_node E N {||}
    else if m=4 then Some (E,Some [240])
    else if m=5 then map_option (\<lambda>(F,u). (native_node_erase_unused F,u)) (finite_extend_proof_node E N D)
    else if m=6 then None
    else if m=7 then finite_extend_proof_node native_node_empty_environment Finite_Assertion {||}
    else if m=8 then (if finite_proof_node_installable E N D then
      finite_extend_proof_node E (native_node_erase_bindings N) D else None)
    else if m=9 then (if finite_proof_node_installable E N D then
      finite_extend_proof_node E N {||} else None)
    else if m=10 then (if finite_proof_node_installable E N D then
      finite_extend_proof_node E (native_node_change_clause N) D else None)
    else finite_extend_proof_node E N D)"

lemma native_node_method_original:
  "native_node_method 0 (E,N,D)=finite_extend_proof_node E N D"
  by (simp add: native_node_method_def)

definition native_node_methods :: "nat list" where "native_node_methods=[0,1,2,3,4,5,6,7,8,9,10]"
definition native_node_indices :: "nat list" where "native_node_indices=[0..<26]"

export_code native_node_problem native_node_method native_node_methods native_node_indices checking SML

text \<open>
  The source contains the actual guard artifacts and two existing assertion
  nodes. Inputs vary complete binding and target families, conflicting keys,
  absent positions, malformed values, shared targets, recursively paired terms,
  distinct and repeated binding values, and unused material. Three additional
  candidates first check the original prerequisites, then alter only metadata.
  Correct refusal cannot substitute for inspecting that metadata.
  All candidate operations receive the original complete input. They construct
  actual environments or change their fields; no recovery flag is supplied.
  These cases concern metadata and installation, including unsupported inputs.
  The metadata guard does not claim that an arbitrary target family validates
  the original clause application.
\<close>

end
