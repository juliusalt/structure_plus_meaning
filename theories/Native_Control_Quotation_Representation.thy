theory Native_Control_Quotation_Representation
  imports Factor_Request_Quotation_Base Factor_Executable_Systems Finite_Set_Encoding
    Isabelle_Entity_Export
begin

section \<open>Executable constructors are reduced from the complete checked program\<close>

definition finite_request_quotation_program where
  "finite_request_quotation_program=finite_system_of (request_quotation_system {})"

lemma finite_request_quotation_program_exact:
  "decode_finite_system finite_request_quotation_program=request_quotation_system {}"
  unfolding finite_request_quotation_program_def
  by (rule decode_finite_system_of[OF request_quotation_formed])

lemma finite_request_quotation_program_formed:
  "finite_system_formed finite_request_quotation_program"
  by (simp only: finite_system_formed_correct finite_request_quotation_program_exact request_quotation_formed)


end
