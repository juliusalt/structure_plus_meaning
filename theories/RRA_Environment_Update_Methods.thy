theory RRA_Environment_Update_Methods
  imports RRA_Environment_Update_References
begin

fun indexed_environment_update where
  "indexed_environment_update I (Install_Artifact u R)=indexed_insert_artifact I u R"
| "indexed_environment_update I (Install_Binding u k v)=indexed_insert_binding I u k v"

fun stored_environment_update where
  "stored_environment_update I (Install_Artifact u R)=environment_store_add_artifact I u R"
| "stored_environment_update I (Install_Binding u k v)=environment_store_add_binding I u k v"

fun environment_update_guard where
  "environment_update_guard (m::nat) I (Install_Artifact u R)=(
    (m=3 \<or> m=4 \<or> indexed_environment_artifacts I u={||}) \<and>
    (m=3 \<or> m=5 \<or> finite_exact_formed R))"
| "environment_update_guard m I (Install_Binding u k v)=(
    (m=3 \<or> m=6 \<or> indexed_environment_artifacts I v\<noteq>{||}) \<and>
    (m=3 \<or> m=7 \<or> fBex (indexed_environment_artifacts I u) (\<lambda>R. k |\<in>| finite_carrier (finite_structure R))) \<and>
    (m=3 \<or> m=8 \<or> indexed_environment_bindings I u k={||}))"

definition environment_update_option :: "nat\<Rightarrow>environment_update_subject\<Rightarrow>
    local_address option finite_artifact_environment option" where
  "environment_update_option m X=(case X of (A,B,op) \<Rightarrow>
    if m=0 then (case load_environment_store A B of None \<Rightarrow> None | Some I \<Rightarrow>
      map_option (\<lambda>J. indexed_environment_view (raw_environment_store J)) (stored_environment_update I op))
    else let E=finite_enumerated_environment A B;I=index_environment_rows A B in
      if m=9 then None else if m=10 then Some E else
      if (m=2 \<or> finite_environment_formed E) \<and> environment_update_guard m I op
        then Some (indexed_environment_view (indexed_environment_update I op)) else None)"

definition environment_update_method where
  "environment_update_method m X=finite_optional_image id {|environment_update_option m X|}"

definition environment_update_condition where
  "environment_update_condition f method X=relation_reader_condition (environment_update_relation X) f (method X)"

definition environment_update_context where
  "environment_update_context X=(X,environment_update_reference X)"

definition environment_update_assessment where
  "environment_update_assessment m context=(case context of (X,reference) \<Rightarrow>
    (environment_update_method m X,reference))"

definition environment_update_inspect ::
  "(local_address option finite_artifact_environment fset\<times>local_address option finite_artifact_environment fset)
    \<Rightarrow>nat\<Rightarrow>bool" where
  "environment_update_inspect=finite_reader_inspect"

theorem environment_update_assessment_exact:
  "environment_update_inspect (environment_update_assessment m (environment_update_context X)) f=
    environment_update_condition f (environment_update_method m) X"
  by (simp only: environment_update_inspect_def environment_update_assessment_def
    environment_update_context_def case_prod_conv environment_update_condition_def
    finite_reader_inspect_exact[OF environment_update_reference_exact])

definition environment_update_case :: "nat\<Rightarrow>environment_update_subject" where
  "environment_update_case w=(let A=finite_payload_syntax [7];B=finite_payload_syntax [8];bad=finite_payload_syntax [256] in
    if w=0 then ([],[],Install_Artifact None A)
    else if w=1 then ([(None,A)],[],Install_Artifact (Some []) B)
    else if w=2 then ([(None,A),(None,A)],[],Install_Artifact (Some []) B)
    else if w=3 then ([(None,A),(None,B)],[],Install_Artifact (Some []) B)
    else if w=4 then ([(None,bad)],[],Install_Artifact (Some []) B)
    else if w=5 then ([(None,A)],[],Install_Artifact None B)
    else if w=6 then ([(None,A)],[],Install_Artifact (Some []) bad)
    else if w=7 then ([(None,A),(Some [],B)],[],Install_Binding None [] (Some []))
    else if w=8 then ([(None,A),(Some [],B)],[],Install_Binding None [7] (Some []))
    else if w=9 then ([(None,A)],[],Install_Binding None [] (Some []))
    else if w=10 then ([(None,A),(Some [],B)],[((None,[]),Some [])],Install_Binding None [] (Some []))
    else if w=11 then ([(None,A)],[((None,[]),Some [9])],Install_Artifact (Some []) B)
    else if w=12 then ([(None,A)],[],Install_Binding None [] None)
    else if w=13 then ([(Some [300],A)],[],Install_Binding (Some [300]) [] (Some [300]))
    else if w=14 then (map (\<lambda>i. (Some [i,1],B)) [0..<32] @ [(None,A)],[],Install_Artifact (Some []) B)
    else (map (\<lambda>i. (Some [i,1],B)) [0..<128] @ [(None,A)],[],Install_Binding None [] None))"

definition environment_update_chain where
  "environment_update_chain n=foldl (\<lambda>current i. case current of None \<Rightarrow> None
    | Some I \<Rightarrow> environment_store_add_artifact I (Some [i,1]) (finite_payload_syntax [8]))
      (environment_store_add_artifact empty_environment_store None (finite_payload_syntax [7])) [0..<n]"

definition environment_update_chain_report where
  "environment_update_chain_report n=map_option (\<lambda>I.
    let raw=raw_environment_store I;tree=indexed_artifact_store raw
    in (indexed_environment_view raw,indexed_environment_artifacts raw None,
      counted_store_lookup tree (use_binary_path None))) (environment_update_chain n)"

text \<open>
  Eleven actual operations include the closed store API, the full raw guard,
  each omitted prerequisite, refusal and a no-op. Their full returned
  environments are compared with the independently stated original update;
  returning a value is not enough. A separate chain initializes once and
  extends that same store through every operation. Its full final environment,
  fixed lookup and structural path count remain available for criticism.
\<close>

end
