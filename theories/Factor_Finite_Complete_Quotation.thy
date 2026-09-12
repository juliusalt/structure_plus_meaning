theory Factor_Finite_Complete_Quotation
  imports Factor_Executable_Quotation Factor_Complete_Data_Recognition
begin

definition finite_singleton_environment :: "finite_exact_artifact \<Rightarrow> unit finite_artifact_environment" where
  "finite_singleton_environment C=finite_enumerated_environment [((),C)] []"

lemma decode_finite_singleton_environment [simp]:
  "decode_finite_environment (finite_singleton_environment C)=singleton_environment (decode_finite_object C)"
  by (simp add: finite_singleton_environment_def singleton_environment_def map_relation_values_def)

definition finite_complete_data_roots ::
  "finite_exact_artifact \<Rightarrow> finite_factor_term \<Rightarrow> local_address fset" where
  "finite_complete_data_roots C t=(if finite_exact_formed C then
    ffilter (\<lambda>r. (t,finite_carrier (finite_structure C),{||}) |\<in>|
      finite_term_readings (finite_singleton_environment C) () r)
      (finite_carrier (finite_structure C)) else {||})"

theorem finite_complete_data_roots_exact:
  "r |\<in>| finite_complete_data_roots C t \<longleftrightarrow>
    complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)"
proof (cases "finite_exact_formed C")
  case True
  have formed: "exact_formed (decode_finite_object C)"
    using True by (simp only: finite_exact_formed_correct)
  have environment: "environment_formed (singleton_environment (decode_finite_object C))"
    using singleton_environment_closed[OF formed] by (simp add: environment_closed_def)
  have source: "artifact_at (singleton_environment (decode_finite_object C)) () (decode_finite_object C)"
    by (simp add: singleton_environment_def artifact_at_def)
  have root: "r\<in>fset (finite_carrier (finite_structure C))"
    if "complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)"
    using complete_data_quotation_root_boundary[OF that] by auto
  show ?thesis
    by (simp only: finite_complete_data_roots_def True if_True ffmember_filter
      finite_term_readings_correct decode_finite_singleton_environment
      decode_finite_object_carrier bot_fset.rep_eq
      complete_data_quotation_at_source[OF environment source, simplified decode_finite_object_carrier, symmetric])
      (use root in blast)
next
  case False
  have absent: "\<not>complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)"
    using complete_data_quotation_formed[where C="decode_finite_object C" and r=r and t="decode_finite_term t"] False
    by (simp only: finite_exact_formed_correct; blast)
  show ?thesis by (simp add: finite_complete_data_roots_def False absent)
qed

export_code finite_complete_data_roots checking SML

text \<open>
  Every possible root comes from the actual finite carrier. The existing
  quotation reader must account for that complete carrier with an empty
  external-slot boundary. Extra structure, attached data, malformed artifacts,
  and non-data quotation candidates receive the same all-input contract.
\<close>

end
