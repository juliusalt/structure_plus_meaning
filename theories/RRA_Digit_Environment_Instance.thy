theory RRA_Digit_Environment_Instance
  imports RRA_Unary_Environment_Instance RRA_Digit_Use_Paths
begin

interpretation digit_environment: environment_key_codec digit_use_path digit_address_path
    read_digit_use_path read_digit_address_path
  by (unfold_locales) (auto simp: inj_on_def)

text \<open>
  The digit codec instantiates the complete environment-store contract for
  arbitrary original uses and slots. Formation and local update proofs are
  inherited from the generic lookup transfer. No old rows are traversed by
  local lookup, insertion or guard operations.
\<close>

end
