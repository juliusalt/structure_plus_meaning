theory Factor_Native_Certificate_Cases
  imports Factor_Finite_Proof_Coordinate_Graphs Factor_Native_Derivation_Cases
begin

type_synonym native_certificate_node =
  "(local_address,local_address,local_address option definition_site,local_address) finite_instantiated_proof_node"
type_synonym native_certificate_paths = "(local_address list\<times>native_certificate_node) fset"
type_synonym native_certificate_mapping = "(native_certificate_node\<times>local_address list) fset"
type_synonym native_certificate_graph = "(local_address,local_address,local_address,local_address list) finite_derivation_graph"
type_synonym native_certificate_row =
  "native_certificate_node\<times>native_certificate_paths\<times>native_certificate_mapping\<times>native_certificate_graph"
type_synonym native_certificate_result =
  "(local_address option finite_native_system\<times>native_history_call fset\<times>native_certificate_row fset) option"
type_synonym native_certificate_problem = "native_history_problem option"

definition native_certificate_original :: "native_certificate_problem\<Rightarrow>native_derivation_result" where
  "native_certificate_original X=(case X of None \<Rightarrow> None | Some Y \<Rightarrow> native_derivation_base Y)"

definition native_certificate_nodes :: "native_derivation_family\<Rightarrow>native_certificate_node fset" where
  "native_certificate_nodes T=fimage (\<lambda>((d,t),p). (p,d,t)) T"

definition native_certificate_node_result :: "local_address option finite_native_system\<Rightarrow>
    native_certificate_node\<Rightarrow>native_certificate_paths\<times>native_certificate_mapping\<times>native_certificate_graph" where
  "native_certificate_node_result P n=(case n of (p,d,t) \<Rightarrow>
    (finite_schema_proof_paths P p d t,finite_schema_proof_coordinates P (p,d,t),
      finite_schema_coordinate_graph P (p,d,t)))"

definition native_certificate_rows :: "local_address option finite_native_system\<Rightarrow>
    native_derivation_family\<Rightarrow>native_certificate_row fset" where
  "native_certificate_rows P T=fimage (\<lambda>n. (n,native_certificate_node_result P n)) (native_certificate_nodes T)"

lemma native_certificate_rows_direct:
  "native_certificate_rows P T=fimage (\<lambda>((d,t),p). ((p,d,t),
    finite_schema_proof_paths P p d t,finite_schema_proof_coordinates P (p,d,t),
    finite_schema_coordinate_graph P (p,d,t))) T"
  by (simp add: native_certificate_rows_def native_certificate_nodes_def native_certificate_node_result_def
    fimage_fimage comp_def case_prod_unfold)

definition native_certificate_base_from where
  "native_certificate_base_from original=map_option (\<lambda>(P,A,T). (P,A,native_certificate_rows P T)) original"

definition native_certificate_base where
  "native_certificate_base X=native_certificate_base_from (native_certificate_original X)"

definition native_certificate_prefix :: "local_address list\<Rightarrow>local_address list" where
  "native_certificate_prefix ss=(if ss=[] then [] else []#ss)"

definition native_certificate_merge_proof :: "native_certificate_mapping\<Rightarrow>native_certificate_mapping" where
  "native_certificate_merge_proof M=fimage (\<lambda>(n,ss). (n,
    case finite_relation_least_key (fimage (\<lambda>(q,tt). (tt,fst q)) M) (fst n)
      of None \<Rightarrow> ss | Some tt \<Rightarrow> tt)) M"

definition native_certificate_merge_call :: "native_certificate_mapping\<Rightarrow>native_certificate_mapping" where
  "native_certificate_merge_call M=fimage (\<lambda>(n,ss). (n,
    case finite_relation_least_key (fimage (\<lambda>(q,tt). (tt,snd q)) M) (snd n)
      of None \<Rightarrow> ss | Some tt \<Rightarrow> tt)) M"

fun native_certificate_erase_bindings ::
    "(local_address,local_address) finite_schema_graph_node\<Rightarrow>(local_address,local_address) finite_schema_graph_node" where
  "native_certificate_erase_bindings Finite_Assertion=Finite_Assertion"
| "native_certificate_erase_bindings (Finite_Inference c V)=Finite_Inference c {||}"

definition native_certificate_alter_row :: "nat\<Rightarrow>local_address option finite_native_system\<Rightarrow>
    native_certificate_row\<Rightarrow>native_certificate_row" where
  "native_certificate_alter_row m P row=(case row of (n,R,M,G) \<Rightarrow>
    let U=(if m=7 then {||} else if m=11 then fimage (map_prod id native_certificate_prefix) M
      else if m=12 then native_certificate_merge_proof M else if m=13 then native_certificate_merge_call M else M);
      H=(if m=8 then G\<lparr>finite_graph_discharges:={||}\<rparr>
        else if m=9 then G\<lparr>finite_graph_inferences:=fimage (map_prod id native_certificate_erase_bindings) (finite_graph_inferences G)\<rparr>
        else if m=10 then G\<lparr>finite_graph_inferences:=ffilter (\<lambda>(ss,N). ss=[]) (finite_graph_inferences G)\<rparr>
        else if m=11 then finite_rename_graph native_certificate_prefix G
        else if m=12 \<or> m=13 then finite_mapped_graph U (finite_schema_proof_graph P n) else G)
    in (n,if m=5 then {||} else if m=6 then {|([],n)|} else R,U,H))"

definition native_certificate_variant where
  "native_certificate_variant m v=(case v of (P,A,R) \<Rightarrow>
    (if m=3 then native_history_empty_program else P,if m=2 then {||} else A,
      if m=1 then {||} else if m=15 then R |\<union>| fimage (native_certificate_alter_row 5 P) R
      else fimage (native_certificate_alter_row m P) R))"

definition native_certificate_apply :: "nat\<Rightarrow>native_certificate_result\<Rightarrow>native_certificate_result" where
  "native_certificate_apply m base=(if m=4 then None else case base of None \<Rightarrow>
    (if m=14 then Some (native_history_empty_program,{||},{||}) else None)
    | Some v \<Rightarrow> Some (native_certificate_variant m v))"

definition native_certificate_method where
  "native_certificate_method m X=native_certificate_apply m (native_certificate_base X)"

lemma native_certificate_row_original:
  "native_certificate_alter_row 0 P row=row"
  by (cases row) (simp add: native_certificate_alter_row_def Let_def)

lemma native_certificate_row_identity:
  "native_certificate_alter_row 0 P=id"
  by (rule ext) (simp only: native_certificate_row_original id_apply)

lemma native_certificate_variant_original:
  "native_certificate_variant 0 v=v"
  by (cases v) (simp add: native_certificate_variant_def native_certificate_row_identity)

lemma native_certificate_method_original:
  "native_certificate_method 0 X=native_certificate_base X"
  by (simp add: native_certificate_method_def native_certificate_apply_def
    native_certificate_variant_original split: option.splits)

definition native_certificate_methods :: "nat list" where
  "native_certificate_methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]"
definition native_certificate_indices :: "nat list" where
  "native_certificate_indices=native_history_indices"
definition native_certificate_problem :: "nat\<Rightarrow>native_certificate_problem" where
  "native_certificate_problem w=native_history_problem w"

text \<open>
  Complete original native sources and requests supply the already constructed
  certificate families. Every certificate retains its full required call.
  Candidates retain or alter actual path families, coordinate maps and complete
  graphs, including proof-only and call-only merging and conflicting outputs.
  Source positioning and native artifact placement remain separate operations.
  These are proposed candidates; execution and complete criticism are required
  before selection within this declared construction problem.
\<close>

end
