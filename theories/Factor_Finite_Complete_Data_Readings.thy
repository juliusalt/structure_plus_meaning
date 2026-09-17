theory Factor_Finite_Complete_Data_Readings
  imports Factor_Finite_Complete_Quotation
begin

definition finite_complete_data_readings ::
  "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> finite_factor_term fset" where
  "finite_complete_data_readings C r=(if finite_exact_formed C \<and>
    r |\<in>| finite_carrier (finite_structure C) then
    fimage fst (ffilter (\<lambda>(t,I,K). I=finite_carrier (finite_structure C) \<and> K={||})
      (finite_term_readings (finite_singleton_environment C) () r)) else {||})"

lemma finite_complete_data_readings_roots:
  "t |\<in>| finite_complete_data_readings C r \<longleftrightarrow> r |\<in>| finite_complete_data_roots C t"
proof -
  have projection:
    "t |\<in>| fimage fst (ffilter (\<lambda>(t,I,K). I=finite_carrier (finite_structure C) \<and> K={||})
      (finite_term_readings (finite_singleton_environment C) () r)) \<longleftrightarrow>
      (t,finite_carrier (finite_structure C),{||}) |\<in>|
        finite_term_readings (finite_singleton_environment C) () r"
    by (simp only: finite_first_projection_member ffmember_filter split_paired_Ex case_prod_conv; blast)
  show ?thesis
    by (cases "finite_exact_formed C"; cases "r |\<in>| finite_carrier (finite_structure C)")
      (simp only: finite_complete_data_readings_def finite_complete_data_roots_def
        simp_thms if_True if_False projection ffmember_filter; auto)+
qed

theorem finite_complete_data_readings_exact:
  "t |\<in>| finite_complete_data_readings C r \<longleftrightarrow>
    complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)"
  by (simp only: finite_complete_data_readings_roots finite_complete_data_roots_exact)

lemma finite_complete_data_readings_complete:
  assumes "complete_data_quoted_at (decode_finite_object C) r t"
  shows "\<exists>T. T |\<in>| finite_complete_data_readings C r \<and> decode_finite_term T=t"
proof -
  have formed: "term_formed t" using complete_data_quotation_formed[OF assms] by blast
  have decode: "decode_finite_term (finite_term_of t)=t" by (rule decode_finite_term_of[OF formed])
  show ?thesis by (rule exI[of _ "finite_term_of t"])
    (use assms decode in \<open>simp add: finite_complete_data_readings_exact\<close>)
qed

text \<open>
  The existing actual quotation reader recovers the term and checks its whole
  interior and empty external boundary. The root query and value query select
  opposite coordinates of that same relation; neither restricts quotation to
  one chosen layout.
\<close>

end
