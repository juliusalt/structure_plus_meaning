theory Factor_Finite_Material_Arguments
  imports Factor_Executable_Artifact_Values Factor_Executable_Instances Factor_Finite_Exact_Patterns
begin

section \<open>Construct every material operand from the actual artifact\<close>

abbreviation finite_enumeration_term where
  "finite_enumeration_term xs \<equiv> foldr Finite_Pair xs (Finite_Target (Finite_Whole finite_empty_artifact))"

lemma decode_finite_enumeration_term [simp]:
  "decode_finite_term (finite_enumeration_term xs)=enumeration_term (map decode_finite_term xs)"
  by (induction xs) simp_all

definition finite_occurrence_term where
  "finite_occurrence_term C a=Finite_Target (Finite_Anchor C a)"
definition finite_atom_term where
  "finite_atom_term C a=Finite_Pair (Finite_Payload a) (finite_occurrence_term C a)"
definition finite_incidence_term where
  "finite_incidence_term C q=(case q of (a,b,c) \<Rightarrow>
    Finite_Pair (finite_occurrence_term C a) (Finite_Pair (finite_occurrence_term C b) (finite_occurrence_term C c)))"
definition finite_attachment_term where
  "finite_attachment_term C q=(case q of (a,p) \<Rightarrow>
    Finite_Pair (finite_occurrence_term C a) (Finite_Payload p))"

lemma finite_material_entry_decodings [simp]:
  "decode_finite_term (finite_occurrence_term C a)=occurrence_term (decode_finite_object C) a"
  "decode_finite_term (finite_atom_term C a)=atom_term (decode_finite_object C) a"
  "decode_finite_term (finite_incidence_term C e)=incidence_term (decode_finite_object C) e"
  "decode_finite_term (finite_attachment_term C p)=attachment_term (decode_finite_object C) p"
  by (simp_all add: finite_occurrence_term_def finite_atom_term_def finite_incidence_term_def finite_attachment_term_def
    occurrence_term_def atom_term_def incidence_term_def attachment_term_def split: prod.splits)

definition finite_material_arguments where
  "finite_material_arguments C=(case finite_artifact_rows C of (A,E,B,F) \<Rightarrow>
    (Finite_Target (Finite_Whole C),finite_enumeration_term (map (finite_atom_term C) A),
      finite_enumeration_term (map (finite_incidence_term C) E),
      finite_enumeration_term (map (finite_attachment_term C) B),
      finite_enumeration_term (map (finite_attachment_term C) F)))"

lemma finite_artifact_rows_enumeration:
  assumes rows: "finite_artifact_rows C=(A,E,B,F)"
  shows "artifact_enumeration (decode_finite_object C) A E B F \<longleftrightarrow> finite_exact_formed C"
  using finite_artifact_rows_value_exact[of "decode_finite_object C" C]
  by (simp only: rows artifact_rows_term_def case_prod_conv artifact_value_presents_data; simp)

theorem finite_material_arguments_exact:
  assumes args: "finite_material_arguments C=(s,a,e,b,f)"
  shows "finite_material_observation s a e b f \<longleftrightarrow> finite_exact_formed C"
proof -
  obtain A E B F where rows: "finite_artifact_rows C=(A,E,B,F)" by (cases "finite_artifact_rows C") auto
  have fields: "s=Finite_Target (Finite_Whole C)"
    "a=finite_enumeration_term (map (finite_atom_term C) A)"
    "e=finite_enumeration_term (map (finite_incidence_term C) E)"
    "b=finite_enumeration_term (map (finite_attachment_term C) B)"
    "f=finite_enumeration_term (map (finite_attachment_term C) F)"
    using args by (simp_all add: finite_material_arguments_def rows)
  show ?thesis
    by (simp add: fields finite_material_observation_correct map_map comp_def
      material_observation_exact finite_artifact_rows_enumeration[OF rows])
qed

definition finite_literal_material where
  "finite_literal_material C=(case finite_material_arguments C of (s,a,e,b,f) \<Rightarrow>
    \<lparr>finite_material_source=finite_exact_term_pattern s,finite_material_atoms=finite_exact_term_pattern a,
      finite_material_edges=finite_exact_term_pattern e,finite_material_counts=finite_exact_term_pattern b,
      finite_material_functions=finite_exact_term_pattern f\<rparr>)"

lemma finite_literal_material_satisfied:
  "finite_material_satisfied V (finite_literal_material C) \<longleftrightarrow> finite_exact_formed C"
proof -
  obtain s a e b f where args: "finite_material_arguments C=(s,a,e,b,f)"
    by (cases "finite_material_arguments C") auto
  have observation: "material_observation (decode_finite_term s) (decode_finite_term a)
    (decode_finite_term e) (decode_finite_term b) (decode_finite_term f) \<longleftrightarrow> finite_exact_formed C"
    using finite_material_arguments_exact[OF args] by (simp only: finite_material_observation_correct)
  show ?thesis
    using material_observation_formed[of "decode_finite_term s" "decode_finite_term a"
      "decode_finite_term e" "decode_finite_term b" "decode_finite_term f"]
    by (auto simp: finite_material_satisfied_correct finite_literal_material_def args decode_finite_material_def
      material_pattern_satisfied_def material_pattern_instance_def observation)
qed

text \<open>
  The existing complete artifact-row constructor supplies every carrier entry,
  incidence and attachment occurrence. The material operands retain exact
  occurrence anchors to that same source. Their empty enumeration is the
  existing whole empty artifact; a payload-and-pair data-list terminator does
  not present that enumeration. Literal patterns for these complete operands
  satisfy the original material condition exactly when the source is formed.
\<close>

end
