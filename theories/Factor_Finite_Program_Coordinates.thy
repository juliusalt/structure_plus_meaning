theory Factor_Finite_Program_Coordinates
  imports Factor_Fresh_Program_Coordinates Factor_Finite_Pattern_Syntax RRA_Finite_Environment_Construction
begin

section \<open>Computed definition positions instantiate the existing extension map\<close>

definition finite_program_coordinates :: "local_address option finite_artifact_environment\<Rightarrow>
    'd::linorder fset\<Rightarrow>'d fset\<Rightarrow>('d\<Rightarrow>local_address option definition_site)\<Rightarrow>
    'd\<Rightarrow>local_address option definition_site" where
  "finite_program_coordinates E U V g d=(if d |\<in>| U then g d else
    (finite_fresh_use_map (finite_environment_uses E) None (Some (finite_binder_coordinates (V |-| U) d)),[]))"

lemma finite_program_coordinates_correct:
  "finite_program_coordinates E U V g=program_coordinate_extension (decode_finite_environment E)
    (fset U) g (finite_binder_coordinates (V |-| U))"
  by (rule ext) (simp add: finite_program_coordinates_def program_coordinate_extension_def
    finite_fresh_use_map_exact finite_environment_uses_correct)

theorem finite_program_coordinates_properties:
  assumes environment: "finite_environment_formed E"
    and injective: "inj_on g (fset U)" and positions: "image g (fset U)\<subseteq>environment_positions (decode_finite_environment E)"
  shows "let h=finite_program_coordinates E U V g in
    inj_on h (fset V) \<and> (\<forall>d\<in>fset U. h d=g d) \<and>
    (\<forall>d\<in>fset V-fset U. snd (h d)=[]) \<and>
    image fst (image h (fset V-fset U))\<inter>fset (finite_environment_uses E)={}"
proof -
  have ef: "environment_formed (decode_finite_environment E)"
    using environment by (simp only: finite_environment_formed_correct)
  have addressing: "finite_addressing (fset V-fset U) (finite_binder_coordinates (V |-| U))"
    using finite_binder_coordinates_properties[of "V |-| U"] by (simp add: binder_addressing_def)
  show ?thesis using program_coordinate_extension_properties[OF ef injective positions addressing]
    by (simp only: Let_def finite_program_coordinates_correct finite_environment_uses_correct; blast)
qed

export_code finite_program_coordinates checking SML

end
