theory Factor_Native_Certificate_Assessment
  imports Factor_Native_Certificate_Cases Finite_Inspection_Rows
begin

definition native_certificate_family :: "native_certificate_row fset\<Rightarrow>native_derivation_family" where
  "native_certificate_family R=fimage (\<lambda>(n,paths,M,G). (snd n,fst n)) R"

definition native_certificate_row_condition where
  "native_certificate_row_condition (f::nat) P row=(case row of ((p,d,t),R,M,G) \<Rightarrow>
    if f=0 then fset (fimage (map_prod id decode_finite_instantiated_node) R)=
      indexed_path_family (schema_proof_children (decode_finite_system P)) (decode_finite_instantiated_node (p,d,t))
    else if f=1 then schema_graph_mapping (fset M)
      (decode_finite_graph (finite_schema_proof_graph P (p,d,t))) (p,d,t) (decode_finite_graph G) []
    else if f=2 then (\<forall>(n,ss)\<in>fset M. (ss,decode_finite_instantiated_node n)\<in>
      indexed_path_family (schema_proof_children (decode_finite_system P)) (decode_finite_instantiated_node (p,d,t)))
    else False)"

definition native_certificate_row_assessment where
  "native_certificate_row_assessment P row=(case row of ((p,d,t),R,M,G) \<Rightarrow>
    let paths=finite_schema_proof_paths P p d t; graph=finite_schema_proof_graph P (p,d,t)
    in (paths,graph,R=paths,finite_graph_mapping M graph (p,d,t) G [],
      fBall M (\<lambda>(n,ss). (ss,n) |\<in>| paths)))"

definition native_certificate_row_inspect where
  "native_certificate_row_inspect A (f::nat)=(case A of (paths,graph,exact,mapping,coordinates) \<Rightarrow>
    if f=0 then exact else if f=1 then mapping else if f=2 then coordinates else False)"

lemma native_certificate_row_assessment_exact:
  "native_certificate_row_inspect (native_certificate_row_assessment P row) f=native_certificate_row_condition f P row"
proof -
  obtain p d t R M G where shape: "row=((p,d,t),R,M,G)" by (cases row) auto
  show ?thesis
    by (simp only: shape native_certificate_row_assessment_def native_certificate_row_inspect_def
      native_certificate_row_condition_def case_prod_conv Let_def finite_schema_proof_paths_equal
      finite_graph_mapping_exact finite_schema_proof_paths_decoded_member)
qed

definition native_certificate_result_condition where
  "native_certificate_result_condition (f::nat) original result=(case original of None \<Rightarrow> False
    | Some (P,A,T) \<Rightarrow> (case result of None \<Rightarrow> False | Some (Q,B,R) \<Rightarrow>
      if f=0 then B=A else if f=1 then Q=P
      else if f=2 then single_valued (fset R) \<and> native_certificate_family R=T
      else if f<6 then (\<forall>row\<in>fset R. native_certificate_row_condition (f-3) P row) else False))"

definition native_certificate_condition_on where
  "native_certificate_condition_on (f::nat) original result=(
    if f=6 then (original=None \<longrightarrow> result=None)
    else if f<6 then (original\<noteq>None \<longrightarrow> native_certificate_result_condition f original result)
    else False)"

definition native_certificate_condition where
  "native_certificate_condition f method X=native_certificate_condition_on f (native_certificate_original X) (method X)"

definition native_certificate_assessment_from where
  "native_certificate_assessment_from original result=(original\<noteq>None,
    (case original of None \<Rightarrow> None | Some (P,A,T) \<Rightarrow>
      map_option (\<lambda>(Q,B,R). (B=A,Q=P,
        finite_relation_functional R \<and> native_certificate_family R=T,
        finite_inspection_rows (native_certificate_row_assessment P) R)) result),result=None)"

definition native_certificate_assessment where
  "native_certificate_assessment X result=native_certificate_assessment_from (native_certificate_original X) result"

definition native_certificate_inspect where
  "native_certificate_inspect A (f::nat)=(case A of (ready,body,rejected) \<Rightarrow>
    if f=6 then (\<not>ready \<longrightarrow> rejected) else if f<6 then (ready \<longrightarrow>
      (case body of None \<Rightarrow> False | Some (answers,source,family,rows) \<Rightarrow>
        if f=0 then answers else if f=1 then source else if f=2 then family
        else fBall rows (\<lambda>(row,a). native_certificate_row_inspect a (f-3)))) else False)"

theorem native_certificate_assessment_from_exact:
  "native_certificate_inspect (native_certificate_assessment_from original result) f=
    native_certificate_condition_on f original result"
  by (cases original; cases result)
    (auto simp: native_certificate_assessment_from_def native_certificate_inspect_def
      native_certificate_condition_on_def native_certificate_result_condition_def
      finite_relation_functional_correct finite_inspection_rows_def native_certificate_row_assessment_exact
      Let_def split: prod.splits)

theorem native_certificate_assessment_exact:
  "native_certificate_inspect (native_certificate_assessment X (method X)) f=native_certificate_condition f method X"
  by (simp only: native_certificate_assessment_def native_certificate_assessment_from_exact native_certificate_condition_def)

export_code native_certificate_assessment native_certificate_inspect checking SML

text \<open>
  The original source-derived answer and complete certificate family remain
  the reference. Every offered graph row is inspected against its full original
  certificate and call. Exact paths use the independent indexed-path relation;
  complete graph correspondence uses the existing arbitrary-map contract.
  Chosen coordinates must be actual source paths, without requiring the least
  path. Checked certificates then distinguish nodes sharing neither a complete
  proof-and-call identity nor an endpoint. Native source positioning, artifact
  placement, replay and complete development admission remain separate.
\<close>

end
