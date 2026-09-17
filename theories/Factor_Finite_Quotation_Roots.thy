theory Factor_Finite_Quotation_Roots
  imports RRA_Finite_Role_Projections Factor_Finite_Prepared_Data_Readings
begin

definition finite_complete_data_root_candidates where
  "finite_complete_data_root_candidates C=finite_unreferenced_positions (finite_structure C)"

lemma finite_complete_data_root_candidates_exact:
  assumes quoted: "complete_data_quoted_at (decode_finite_object C) r t"
  shows "finite_complete_data_root_candidates C={|r|}"
  using complete_data_quotation_root_boundary[OF quoted]
  by (simp add: finite_complete_data_root_candidates_def fset_inject[symmetric]
    finite_unreferenced_positions_exact)

definition finite_complete_data_readings_at_roots where
  "finite_complete_data_readings_at_roots C r=(if r |\<in>| finite_complete_data_root_candidates C
    then finite_complete_data_readings_prepared C r else {||})"

theorem finite_complete_data_readings_at_roots_exact:
  "finite_complete_data_readings_at_roots C r=finite_complete_data_readings C r"
proof -
  have required: "r |\<in>| finite_complete_data_root_candidates C"
    if "t |\<in>| finite_complete_data_readings C r" for t
    using finite_complete_data_root_candidates_exact[OF that[unfolded finite_complete_data_readings_exact]] by simp
  show ?thesis by (rule fset_inject[THEN iffD1])
    (use required in \<open>auto simp: finite_complete_data_readings_at_roots_def finite_complete_data_readings_prepared_exact\<close>)
qed

text \<open>
  The existing complete-quotation theorem identifies its root as exactly the
  carrier positions that occur in neither the participation nor reached role.
  This selector uses that original structural boundary on every input. It adds
  no preferred root coordinate and admits every original complete quotation.
\<close>

end
