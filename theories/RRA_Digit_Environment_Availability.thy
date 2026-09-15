theory RRA_Digit_Environment_Availability
  imports RRA_Digit_Environment_Loading
begin

theorem load_digit_environment_domain:
  "load_digit_environment E\<noteq>None \<longleftrightarrow> finite_environment_formed E"
  using arg_cong[OF load_digit_environment_exact[of E], where f="\<lambda>result. result=None"]
  by (auto simp: map_option_is_None split: if_splits)

end
