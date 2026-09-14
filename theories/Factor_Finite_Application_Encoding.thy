theory Factor_Finite_Application_Encoding
  imports Factor_Finite_Term_Encoding RRA_Finite_Environment_Construction Factor_Future_Applications
begin

definition finite_term_environment where
  "finite_term_environment t=finite_literal_environment (finite_term_syntax t) (finite_term_literal_bindings t)"

lemma finite_term_environment_exact:
  "decode_finite_environment (finite_term_environment t)=term_environment (decode_finite_term t)"
  by (simp only: finite_term_environment_def decode_finite_literal_environment
    finite_term_syntax_exact finite_term_literal_bindings_exact term_environment_def)

definition finite_call_environment where
  "finite_call_environment R a t=finite_rename_environment call_use
    (finite_term_environment (Finite_Pair (Finite_Target (Finite_Anchor R a)) t))"

lemma finite_call_environment_exact:
  "decode_finite_environment (finite_call_environment R a t)=
    call_environment (decode_finite_object R) a (decode_finite_term t)"
  by (simp only: finite_call_environment_def decode_finite_rename_environment
    finite_term_environment_exact decode_finite_term.simps decode_finite_target.simps call_environment_def)

definition finite_future_call_environment where
  "finite_future_call_environment E u R a t=finite_graft_environment E u (finite_call_environment R a t)"

lemma finite_future_call_environment_exact:
  "decode_finite_environment (finite_future_call_environment E u R a t)=
    future_call_environment (decode_finite_environment E) u (decode_finite_object R) a (decode_finite_term t)"
  by (simp only: finite_future_call_environment_def decode_finite_graft_environment
    finite_call_environment_exact future_call_environment_def)

definition finite_future_call_use where
  "finite_future_call_use E u=finite_fresh_use_map (finite_environment_uses E) u (Some [])"

lemma finite_future_call_use_exact:
  "finite_future_call_use E u=future_call_use (decode_finite_environment E) u"
  by (simp only: finite_future_call_use_def finite_fresh_use_map_exact finite_environment_uses_correct future_call_use_def)

export_code finite_term_environment finite_call_environment finite_future_call_environment finite_future_call_use checking SML

text \<open>
  Whole native call construction instantiates the existing quotation, use
  permutation and environment grafting operations. Exact environment equality
  supplies all literal references and the original designated callee artifact.
  Formation and source membership remain the constructor's separate boundary.
\<close>

end
