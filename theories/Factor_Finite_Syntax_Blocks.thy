theory Factor_Finite_Syntax_Blocks
  imports Factor_Finite_Reference_Forests RRA_Finite_Syntax_Construction Factor_Record_Syntax
begin

type_synonym 'u finite_syntax_block =
  "finite_exact_artifact\<times>(local_address\<times>finite_exact_artifact) fset\<times>
    (local_address\<times>'u definition_site) fset"

fun finite_block_artifact :: "'u finite_syntax_block\<Rightarrow>finite_exact_artifact" where
  "finite_block_artifact (R,L,C)=R"
fun finite_block_literals :: "'u finite_syntax_block\<Rightarrow>(local_address\<times>finite_exact_artifact) fset" where
  "finite_block_literals (R,L,C)=L"
fun finite_block_callees :: "'u finite_syntax_block\<Rightarrow>(local_address\<times>'u definition_site) fset" where
  "finite_block_callees (R,L,C)=C"

definition finite_block_slots where
  "finite_block_slots B=fimage fst (finite_block_literals B) |\<union>| fimage fst (finite_block_callees B)"
definition finite_block_interior where
  "finite_block_interior B=finite_carrier (finite_structure (finite_block_artifact B)) |-| finite_block_slots B"

lemma finite_block_slots_exact:
  "fset (finite_block_slots B)=
    rel_dom (map_relation_values decode_finite_object (fset (finite_block_literals B))) \<union>
    rel_dom (fset (finite_block_callees B))"
  by (simp add: finite_block_slots_def map_relation_values_domain rel_dom_image
    map_relation_values_domain[unfolded rel_dom_image])

lemma finite_block_boundary:
  assumes carrier: "rra_carrier (object_structure (decode_finite_object (finite_block_artifact B)))=I\<union>K"
    and separate: "I\<inter>K={}"
    and references: "rel_dom (map_relation_values decode_finite_object (fset (finite_block_literals B))) \<union>
      rel_dom (fset (finite_block_callees B))=K"
  shows "fset (finite_block_slots B)=K" "fset (finite_block_interior B)=I"
proof -
  show slots: "fset (finite_block_slots B)=K" by (simp only: finite_block_slots_exact references)
  show "fset (finite_block_interior B)=I"
    using carrier separate by (auto simp: finite_block_interior_def slots)
qed

definition finite_block_forest :: "'u finite_syntax_block list\<Rightarrow>'u finite_syntax_block" where
  "finite_block_forest Bs=(finite_syntax_forest (map finite_block_artifact Bs),
    finite_syntax_forest_table (map finite_block_literals Bs),
    finite_syntax_forest_table (map finite_block_callees Bs))"

definition finite_frame_block :: "(finite_exact_artifact\<Rightarrow>finite_exact_artifact)\<Rightarrow>
    'u finite_syntax_block\<Rightarrow>'u finite_syntax_block" where
  "finite_frame_block frame B=(frame (finite_block_artifact B),finite_block_literals B,finite_block_callees B)"

definition finite_record_block where
  "finite_record_block Bs=finite_frame_block (\<lambda>R.
    finite_record_wrapper R [] (family_ports (length Bs))
      (map (\<lambda>i. syntax_branch i []) [0..<length Bs])) (finite_block_forest Bs)"

definition finite_table_block where
  "finite_table_block Bs=finite_frame_block (\<lambda>R.
    finite_family_wrapper R [] (fset_of_list (zip (family_ports (length Bs))
      (map (\<lambda>i. syntax_branch i []) [0..<length Bs])))) (finite_block_forest Bs)"

lemma finite_block_forest_fields:
  "decode_finite_object (finite_block_artifact (finite_block_forest Bs))=
    syntax_forest (map (\<lambda>B. decode_finite_object (finite_block_artifact B)) Bs)"
  "map_relation_values decode_finite_object (fset (finite_block_literals (finite_block_forest Bs)))=
    syntax_forest_table (map (\<lambda>B. map_relation_values decode_finite_object (fset (finite_block_literals B))) Bs)"
  "fset (finite_block_callees (finite_block_forest Bs))=
    syntax_forest_table (map (\<lambda>B. fset (finite_block_callees B)) Bs)"
  by (simp_all add: finite_block_forest_def syntax_forest_value_map comp_def)

lemma finite_frame_block_fields [simp]:
  "finite_block_artifact (finite_frame_block frame B)=frame (finite_block_artifact B)"
  "finite_block_literals (finite_frame_block frame B)=finite_block_literals B"
  "finite_block_callees (finite_frame_block frame B)=finite_block_callees B"
  by (simp_all add: finite_frame_block_def)

lemma finite_table_block_fields:
  "decode_finite_object (finite_block_artifact (finite_table_block Bs))=
    family_wrapper (syntax_forest (map (\<lambda>B. decode_finite_object (finite_block_artifact B)) Bs)) []
      (set (zip (family_ports (length Bs)) (map (\<lambda>i. syntax_branch i []) [0..<length Bs])))"
  "map_relation_values decode_finite_object (fset (finite_block_literals (finite_table_block Bs)))=
    syntax_forest_table (map (\<lambda>B. map_relation_values decode_finite_object (fset (finite_block_literals B))) Bs)"
  "fset (finite_block_callees (finite_table_block Bs))=
    syntax_forest_table (map (\<lambda>B. fset (finite_block_callees B)) Bs)"
  by (simp_all add: finite_table_block_def finite_block_forest_fields fset_of_list.rep_eq)

lemma finite_record_block_fields:
  "decode_finite_object (finite_block_artifact (finite_record_block Bs))=
    record_wrapper (syntax_forest (map (\<lambda>B. decode_finite_object (finite_block_artifact B)) Bs)) []
      (family_ports (length Bs)) (map (\<lambda>i. syntax_branch i []) [0..<length Bs])"
  "map_relation_values decode_finite_object (fset (finite_block_literals (finite_record_block Bs)))=
    syntax_forest_table (map (\<lambda>B. map_relation_values decode_finite_object (fset (finite_block_literals B))) Bs)"
  "fset (finite_block_callees (finite_record_block Bs))=
    syntax_forest_table (map (\<lambda>B. fset (finite_block_callees B)) Bs)"
  by (simp_all add: finite_record_block_def finite_block_forest_fields)

export_code finite_block_artifact finite_block_literals finite_block_callees finite_block_slots
  finite_block_interior finite_record_block finite_table_block checking SML

text \<open>
  A block retains the actual syntax artifact and complete literal and callee
  references. Its slots and interior are derived fields. Both record and table
  framing reuse the same complete private forest and reference traversal.
  Formation and native recovery require the corresponding original contracts.
\<close>

end
