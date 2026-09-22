theory Faceted_Native_Questions
  imports Native_Control_Admitted_Selection
begin

text \<open>
  A faceted question of actual subjects is the keyed question at the first-occurrence key of its own
  subject list: each candidate is the path of the binary digits of a subject's first position there, a
  path of shapes that no clause reads as octets. The name carries no contract of its own; its users take
  the keyed question's contracts and consumers (@{thm [source] keyed_faceted_admission_at},
  @{thm [source] keyed_admitted_choice_condition}) with the key's injectivity on the subjects
  (@{thm [source] first_occurrence_key_inj_on}). Equal subjects at two positions have one key, as they
  are one subject.
\<close>

abbreviation faceted_native_question where
  "faceted_native_question subjects facets observe \<equiv>
    keyed_faceted_question (first_occurrence_key subjects) subjects facets observe"

end
