theory RRA_Artifact_Lookup_Methods
  imports RRA_Indexed_Artifact_Lookup RRA_Finite_Syntax_Construction
    Finite_Relation_Reader_Assessments Finite_Singleton_Selection
begin

type_synonym artifact_lookup_subject =
  "(local_address option\<times>finite_exact_artifact) list\<times>local_address option"

definition artifact_lookup_reference :: "artifact_lookup_subject\<Rightarrow>finite_exact_artifact fset" where
  "artifact_lookup_reference X=(case X of (rows,u) \<Rightarrow>
    finite_artifacts_at (finite_enumerated_environment rows []) u)"

definition artifact_lookup_relation where
  "artifact_lookup_relation X C=(case X of (rows,u) \<Rightarrow>
    artifact_at (decode_finite_environment (finite_enumerated_environment rows [])) u (decode_finite_object C))"

lemma artifact_lookup_reference_exact:
  "C |\<in>| artifact_lookup_reference X \<longleftrightarrow> artifact_lookup_relation X C"
  by (cases X) (auto simp only: artifact_lookup_reference_def artifact_lookup_relation_def
    case_prod_conv finite_artifacts_at_member decode_finite_environment_entry decode_finite_object_injective)

definition artifact_lookup_method :: "nat\<Rightarrow>artifact_lookup_subject\<Rightarrow>finite_exact_artifact fset" where
  "artifact_lookup_method m X=(case X of (rows,u) \<Rightarrow>
    let tree=artifact_relation_store rows; actual=indexed_artifacts_at tree u in
    if m=0 then artifact_lookup_reference X
    else if m=1 then actual
    else if m=2 then (case finite_singleton_option actual of None \<Rightarrow> {||} | Some C \<Rightarrow> {|C|})
    else if m=3 then (if case u of None \<Rightarrow> True | Some word \<Rightarrow> octets_formed word then actual else {||})
    else if m=4 then {||}
    else if m=5 then indexed_artifacts_at tree (case u of None \<Rightarrow> Some [] | Some _ \<Rightarrow> None)
    else ffilter finite_exact_formed actual)"

definition artifact_lookup_condition where
  "artifact_lookup_condition f method X=relation_reader_condition (artifact_lookup_relation X) f (method X)"

lemma artifact_lookup_original:
  "artifact_lookup_method 0 X=artifact_lookup_reference X"
  by (cases X) (simp add: artifact_lookup_method_def Let_def)

lemma artifact_lookup_indexed:
  "artifact_lookup_method 1 X=artifact_lookup_reference X"
  by (cases X) (simp add: artifact_lookup_method_def Let_def artifact_lookup_reference_def indexed_artifacts_at_exact)

lemma artifact_lookup_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> f\<in>{0,1} \<Longrightarrow>
    artifact_lookup_condition f (artifact_lookup_method m) X"
  by (auto simp: artifact_lookup_condition_def relation_reader_condition_def
    artifact_lookup_original artifact_lookup_indexed[unfolded One_nat_def] artifact_lookup_reference_exact)

definition artifact_lookup_context where
  "artifact_lookup_context X=(X,artifact_lookup_reference X)"

definition artifact_lookup_assessment where
  "artifact_lookup_assessment m context=(case context of (X,reference) \<Rightarrow>
    (if m=0 then reference else artifact_lookup_method m X,reference))"

definition artifact_lookup_inspect :: "(finite_exact_artifact fset\<times>finite_exact_artifact fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "artifact_lookup_inspect=finite_reader_inspect"

lemma artifact_lookup_assessment_exact:
  "artifact_lookup_inspect (artifact_lookup_assessment m (artifact_lookup_context X)) f=
    artifact_lookup_condition f (artifact_lookup_method m) X"
  by (simp add: artifact_lookup_inspect_def artifact_lookup_assessment_def artifact_lookup_context_def
    artifact_lookup_condition_def artifact_lookup_original finite_reader_inspect_exact[OF artifact_lookup_reference_exact]
    split: if_splits)

definition artifact_lookup_case :: "nat\<Rightarrow>artifact_lookup_subject" where
  "artifact_lookup_case w=(let A=finite_payload_syntax [7];B=finite_payload_syntax [8] in
    if w=0 then ([],None)
    else if w=1 then ([(None,A),(Some [],B)],None)
    else if w=2 then ([(None,A),(Some [],B)],Some [])
    else if w=3 then ([(Some [0],A),(Some [0],A)],Some [0])
    else if w=4 then ([(Some [0],A),(Some [0],B)],Some [0])
    else if w=5 then ([(Some [300],A)],Some [300])
    else if w=6 then ([(Some [0,1],A)],Some [1,0])
    else if w=7 then ([(Some [0],finite_payload_syntax [256])],Some [0])
    else if w=8 then (map (\<lambda>i. (Some [i,1],B)) [0..<32] @ [(None,A)],None)
    else (map (\<lambda>i. (Some [i,1],B)) [0..<128] @ [(None,A)],None))"

definition artifact_lookup_path_report where
  "artifact_lookup_path_report X=(case X of (rows,u) \<Rightarrow>
    let tree=artifact_relation_store rows; path=use_binary_path u;
      reading=counted_store_lookup tree path;
      updated=counted_store_update tree path (Some {|finite_payload_syntax [9]|})
    in (path,reading,snd updated,indexed_artifacts_at (fst updated) u,
      map (\<lambda>(v,C). (v,indexed_artifacts_at tree v,indexed_artifacts_at (fst updated) v)) rows))"

text \<open>
  Original artifact membership supplies the independent condition. Actual
  cases distinguish None from a present empty word, repeated rows from
  conflicting values, unbounded natural use words, missing coordinates and
  malformed artifact payloads. Two larger sources add unrelated entries.
  Structural path counts and all before/after lookups are retained separately
  from the soundness and completeness comparison. Index preparation and the
  complete physical decision cost remain outside this scoped count.
\<close>

end
