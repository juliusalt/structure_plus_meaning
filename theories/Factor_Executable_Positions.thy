theory Factor_Executable_Positions
  imports Factor_Executable_Packages Factor_Program_Positions Factor_Finite_Schema_Renaming
begin

section \<open>Finite program coordinates retain their owning semantic use\<close>

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
