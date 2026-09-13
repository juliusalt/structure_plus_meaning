theory Factor_Finite_Citation_Syntax
  imports RRA_Finite_Syntax_Construction Factor_Prospective_Encoding
begin

lemma decode_finite_external_occurrence_syntax [simp]:
  "decode_finite_object (finite_external_occurrence_syntax a)=external_occurrence_syntax a"
  by (simp add: finite_external_occurrence_syntax_def external_occurrence_syntax_def
    decode_finite_object_def decode_finite_structure_def)

end
