theory Material_Application_Observations
  imports Conditional_Application_Review Factor_Finite_Material_Arguments
begin

definition finite_material_site_observations where
  "finite_material_site_observations s C = (case finite_material_arguments C of (x,a,e,b,f) \<Rightarrow>
    fset_of_list [(Finite_Material_Source_Site s,x),(Finite_Material_Atoms_Site s,a),
      (Finite_Material_Edges_Site s,e),(Finite_Material_Counts_Site s,b),
      (Finite_Material_Functions_Site s,f)])"

lemma finite_material_site_observations_fields:
  assumes arguments: "finite_material_arguments C=(x,a,e,b,f)"
  shows "finite_material_site_observations s C =
    {|(Finite_Material_Source_Site s,x),(Finite_Material_Atoms_Site s,a),
      (Finite_Material_Edges_Site s,e),(Finite_Material_Counts_Site s,b),
      (Finite_Material_Functions_Site s,f)|}"
    "material_observation (decode_finite_term x) (decode_finite_term a)
      (decode_finite_term e) (decode_finite_term b) (decode_finite_term f)
      \<longleftrightarrow> finite_exact_formed C"
proof -
  show "finite_material_site_observations s C =
    {|(Finite_Material_Source_Site s,x),(Finite_Material_Atoms_Site s,a),
      (Finite_Material_Edges_Site s,e),(Finite_Material_Counts_Site s,b),
      (Finite_Material_Functions_Site s,f)|}"
    by (simp add: finite_material_site_observations_def arguments)
  show "material_observation (decode_finite_term x) (decode_finite_term a)
      (decode_finite_term e) (decode_finite_term b) (decode_finite_term f)
      \<longleftrightarrow> finite_exact_formed C"
    using finite_material_arguments_exact[OF arguments]
    by (simp only: finite_material_observation_correct)
qed

fun finite_literal_site_observations where
  "finite_literal_site_observations s (Finite_Target (Finite_Whole C)) =
    finite_material_site_observations s C"
| "finite_literal_site_observations s t = {||}"

definition finite_head_material_observations where
  "finite_head_material_observations S q = (let V=finite_matching_bindings (finite_schema_conclusion S) q in
    finsert (Finite_Conclusion_Site,q)
      (ffUnion (fimage (\<lambda>(s,M). ffUnion (fimage (finite_literal_site_observations s)
        (finite_pattern_instances V (finite_material_source M)))) (finite_schema_materials S))))"

lemma finite_head_material_keeps_request:
  "(Finite_Conclusion_Site,q) |\<in>| finite_head_material_observations S q"
  by (simp add: finite_head_material_observations_def Let_def)

theorem finite_head_material_application_original:
  assumes result: "(t,V,H) |\<in>| finite_observed_schema_applications S (finite_head_material_observations S q)"
  shows "schema_instance (decode_finite_schema S) (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises H)"
    "schema_material_satisfied (decode_finite_schema S) (decode_finite_term_bindings V)"
  using finite_observed_schema_application_sound(2,3)[OF result]
  by (simp_all only: finite_schema_instance_correct finite_schema_material_satisfied_correct)

text \<open>Head matching locates actual literal material sources. Their complete
  operands are computed from those artifacts by the existing material constructor,
  then matched through the original schema roles. Original instance and material
  checks remain mandatory. This operation neither asserts ordinary premise calls
  nor claims that head-locatable sources cover every future schema.\<close>

ML \<open>val _ = (writeln "Material_Application_Observations_JOIN_BEGIN";
  Thm.consolidate @{thms finite_material_site_observations_fields finite_head_material_application_original};
  writeln "Material_Application_Observations_JOIN_END");\<close>

end
