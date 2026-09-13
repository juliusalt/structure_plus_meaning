theory Factor_Requested_Application_Readings
  imports Factor_Requested_Applications
begin

section \<open>Complete requested applications also cover the original abstract instances\<close>

lemma finite_requested_instance_reading:
  fixes S :: "('a,'s,'d) finite_factor_schema"
  assumes inst: "schema_instance (decode_finite_schema S) V (decode_finite_term t) H"
    and covered: "finite_schema_head_missing S={||}"
  defines "B \<equiv> finite_matching_bindings (finite_schema_conclusion S) t"
  shows "decode_finite_term_bindings B=V"
    "decode_finite_premises (finite_instantiated_premises S B)=H"
    "finite_schema_instance S B t (finite_instantiated_premises S B)"
proof -
  have finite_scope: "finite_schema_variables S=finite_pattern_variables (finite_schema_conclusion S)"
    using covered by (auto simp: finite_schema_head_missing_def finite_schema_variables_def)
  have scope: "schema_variables (decode_finite_schema S)=
      pattern_variables (decode_finite_pattern (finite_schema_conclusion S))"
    by (simp only: finite_schema_variables_correct[symmetric] finite_scope finite_pattern_variables_correct)
  have bindings: "term_bindings_formed
      (pattern_variables (decode_finite_pattern (finite_schema_conclusion S))) V"
    and head: "pattern_instance V (decode_finite_pattern (finite_schema_conclusion S)) (decode_finite_term t)"
    using inst by (auto simp: schema_instance_def scope)
  have subset: "decode_finite_term_bindings B\<subseteq>V"
    and domain: "rel_dom (decode_finite_term_bindings B)=
      pattern_variables (decode_finite_pattern (finite_schema_conclusion S))"
    using finite_matching_bindings_complete[OF head] unfolding B_def by blast+
  have reverse: "V\<subseteq>decode_finite_term_bindings B"
  proof
    fix z assume member: "z\<in>V"
    obtain a x where shape: "z=(a,x)" by (cases z) auto
    have key: "a\<in>rel_dom (decode_finite_term_bindings B)"
      using member bindings domain by (auto simp: shape term_bindings_formed_def rel_dom_def)
    obtain y where recovered: "(a,y)\<in>decode_finite_term_bindings B"
      using key by (auto simp: rel_dom_def)
    have same: "x=y" using subset recovered member bindings
      by (auto simp: shape term_bindings_formed_def single_valued_def)
    show "z\<in>decode_finite_term_bindings B" using recovered by (simp only: shape same)
  qed
  show same: "decode_finite_term_bindings B=V" using subset reverse by blast
  show body: "decode_finite_premises (finite_instantiated_premises S B)=H"
    by (rule finite_instantiated_premises_correct) (simp only: same; rule inst)
  show "finite_schema_instance S B t (finite_instantiated_premises S B)"
    by (simp only: finite_schema_instance_correct same body; rule inst)
qed

theorem finite_requested_application_reading:
  assumes inst: "schema_instance (decode_finite_schema S) V (decode_finite_term t) H"
    and material: "schema_material_satisfied (decode_finite_schema S) V"
    and covered: "finite_schema_head_missing S={||}"
  shows "\<exists>B G. (t,B,G) |\<in>| finite_requested_schema_applications S t \<and>
    decode_finite_term_bindings B=V \<and> decode_finite_premises G=H"
proof -
  let ?B="finite_matching_bindings (finite_schema_conclusion S) t"
  let ?G="finite_instantiated_premises S ?B"
  have fields: "decode_finite_term_bindings ?B=V" "decode_finite_premises ?G=H"
    "finite_schema_instance S ?B t ?G"
    using finite_requested_instance_reading[OF inst covered] by simp_all
  have satisfied: "finite_schema_material_satisfied S ?B"
    using material by (simp only: finite_schema_material_satisfied_correct fields(1))
  show ?thesis by (rule exI[of _ ?B], rule exI[of _ ?G])
    (simp only: finite_requested_schema_applications_exact[OF covered] fields satisfied; simp)
qed

text \<open>
  The abstract binding and premise relations are recovered from the actual
  requested head and original schema. Complete head scope is an explicit
  prerequisite. No separately chosen binding values or premise table enter
  the application constructor.
\<close>

end
