theory Conditional_Application_Review
  imports Faceted_Native_Questions Factor_Observed_Applications Factor_Requested_Applications
begin

section \<open>Constructing an application does not discharge its premises\<close>

datatype conditional_application_method = Requested_Head | Observed_Parts | Erased_Premises
datatype conditional_application_facet = Requested_Result | Original_Rule

fun conditional_application_run where
  "conditional_application_run Requested_Head S q obs = finite_requested_schema_applications S q"
| "conditional_application_run Observed_Parts S q obs = finite_observed_schema_applications S obs"
| "conditional_application_run Erased_Premises S q obs =
    fimage (\<lambda>(t,V,H). (t,V,{||})) (finite_observed_schema_applications S obs)"

fun conditional_application_observation where
  "conditional_application_observation S q obs m Requested_Result =
    (let A=conditional_application_run m S q obs in
      A\<noteq>{||} \<and> fBall A (\<lambda>(t,V,H). t=q))"
| "conditional_application_observation S q obs m Original_Rule =
    fBall (conditional_application_run m S q obs)
      (\<lambda>(t,V,H). finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V)"

fun conditional_application_requirement where
  "conditional_application_requirement S q obs m Requested_Result =
    (let A=conditional_application_run m S q obs in
      fset A\<noteq>{} \<and> (\<forall>(t,V,H)\<in>fset A. decode_finite_term t=decode_finite_term q))"
| "conditional_application_requirement S q obs m Original_Rule =
    (\<forall>(t,V,H)\<in>fset (conditional_application_run m S q obs).
      schema_instance (decode_finite_schema S) (decode_finite_term_bindings V)
        (decode_finite_term t) (decode_finite_premises H) \<and>
      schema_material_satisfied (decode_finite_schema S) (decode_finite_term_bindings V))"

lemma conditional_application_observation_exact:
  "conditional_application_observation S q obs m f =
    conditional_application_requirement S q obs m f"
  by (cases f) (auto simp: Let_def Ball_def finite_schema_instance_correct
    finite_schema_material_satisfied_correct split: prod.splits)

lemma requested_application_missing_variable:
  assumes required: "a |\<in>| finite_schema_variables S"
    and missing: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion S)"
  shows "finite_requested_schema_applications S q={||}"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| finite_requested_schema_applications S q \<longleftrightarrow> x |\<in>| {||}"
  proof
    assume member: "x |\<in>| finite_requested_schema_applications S q"
    obtain t V H where shape: "x=(t,V,H)" by (cases x) auto
    have bindings: "V=finite_matching_bindings (finite_schema_conclusion S) q"
      and inst: "finite_schema_instance S V t H"
      using member by (auto simp: shape finite_requested_schema_applications_def Let_def split: if_splits)
    have domain: "fimage fst V=finite_schema_variables S"
      using inst by (simp add: finite_schema_instance_def finite_term_bindings_formed_def)
    obtain v where bound: "(a,v) |\<in>| V" using required domain by force
    have "a |\<in>| finite_pattern_variables (finite_schema_conclusion S)"
      by (rule finite_matching_binding_variable) (use bound in \<open>simp only: bindings\<close>)
    then show "x |\<in>| {||}" using missing by contradiction
  next
    assume "x |\<in>| {||}" then show "x |\<in>| finite_requested_schema_applications S q" by simp
  qed
qed

theorem conditional_application_admitted:
  assumes chosen: "native_admitted_choice methods
      (faceted_native_question methods facets (conditional_application_observation S q obs)) report = Some m"
    and facet: "f\<in>set facets"
  shows "conditional_application_requirement S q obs m f"
  using faceted_native_choice[OF chosen facet]
  by (simp only: conditional_application_observation_exact)

lemma observed_application_original:
  "conditional_application_observation S q obs Observed_Parts Original_Rule"
  using finite_observed_schema_application_sound(2,3)
  by (auto simp: Ball_def split: prod.splits)

text \<open>The two original requirements concern production of the requested
  conditional application and preservation of its complete original rule.
  Matching observations supplies bindings, never truth for the reconstructed
  ordinary premise calls. Their discharge, certificate construction, placement,
  replay and policy cause remain separate operations.\<close>

end
