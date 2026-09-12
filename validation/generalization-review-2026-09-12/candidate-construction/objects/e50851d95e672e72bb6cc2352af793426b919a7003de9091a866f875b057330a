theory Factor_Executable_Positions
  imports Factor_Executable_Packages Factor_Program_Positions
begin

section \<open>Finite program coordinates retain their owning semantic use\<close>

lemma decode_finite_pattern_map:
  "decode_finite_pattern (map_finite_term_pattern f p) = rename_pattern f (decode_finite_pattern p)"
  by (induction p) (simp_all add: rename_pattern_def)

definition finite_rename_material ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a finite_material_pattern \<Rightarrow> 'b finite_material_pattern" where
  "finite_rename_material f M =
    \<lparr>finite_material_source=map_finite_term_pattern f (finite_material_source M),
     finite_material_atoms=map_finite_term_pattern f (finite_material_atoms M),
     finite_material_edges=map_finite_term_pattern f (finite_material_edges M),
     finite_material_counts=map_finite_term_pattern f (finite_material_counts M),
     finite_material_functions=map_finite_term_pattern f (finite_material_functions M)\<rparr>"

lemma finite_rename_material_correct:
  "decode_finite_material (finite_rename_material f M) = rename_material_pattern f (decode_finite_material M)"
  by (simp add: finite_rename_material_def decode_finite_material_def rename_material_pattern_def decode_finite_pattern_map)

definition finite_rename_schema ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('d \<Rightarrow> 'e) \<Rightarrow>
    ('a,'s,'d) finite_factor_schema \<Rightarrow> ('b,'t,'e) finite_factor_schema" where
  "finite_rename_schema f h g S =
    \<lparr>finite_schema_conclusion=map_finite_term_pattern f (finite_schema_conclusion S),
     finite_schema_premises=fimage (\<lambda>(s,d,p). (h s,g d,map_finite_term_pattern f p)) (finite_schema_premises S),
     finite_schema_materials=fimage (\<lambda>(s,M). (h s,finite_rename_material f M)) (finite_schema_materials S)\<rparr>"

lemma finite_rename_schema_correct:
  "decode_finite_schema (finite_rename_schema f h g S) = rename_schema f h g (decode_finite_schema S)"
  by (simp add: finite_rename_schema_def decode_finite_schema_def rename_schema_def map_socket_graph_def
      map_relation_values_def fimage.rep_eq image_image case_prod_unfold decode_finite_call_pattern_def
      map_prod_def decode_finite_pattern_map finite_rename_material_correct)

definition finite_positioned_program ::
  "'u finite_native_system \<Rightarrow>
    ('u definition_site,'u definition_site,'u definition_site,'u definition_site) finite_schema_system" where
  "finite_positioned_program P =
    \<lparr>finite_system_interfaces=fimage (\<lambda>(d,p). (d,map_finite_term_pattern (Pair (fst d)) p)) (finite_system_interfaces P),
     finite_system_clauses=fimage (\<lambda>((d,c),S). ((d,(fst d,c)),
       finite_rename_schema (Pair (fst d)) (Pair (fst d)) id S)) (finite_system_clauses P)\<rparr>"

theorem finite_positioned_program_correct:
  "decode_finite_system (finite_positioned_program P) = positioned_program (decode_finite_system P)"
  by (simp add: finite_positioned_program_def decode_finite_system_def positioned_program_def
      map_relation_values_def fimage.rep_eq image_image case_prod_unfold
      decode_finite_pattern_map finite_rename_schema_correct)

corollary finite_positioned_program_formed:
  assumes "finite_system_formed P"
  shows "finite_system_formed (finite_positioned_program P)"
  using positioned_program_formed[of "decode_finite_system P"] assms
  by (simp add: finite_system_formed_correct finite_positioned_program_correct)

export_code finite_positioned_program checking SML

text \<open>
  Local binder, socket, and clause coordinates are paired with the owning
  definition's use. The transformation maps every pattern operand and every
  identified row, while preserving target values and definition references.
  It computes exactly the existing positioned program view on all finite
  inputs and preserves formation. Native proof metadata can therefore be
  checked against the recovered program in the same occurrence coordinates.
\<close>

end
