theory RRA_Finite_Generation_Monotonicity
  imports RRA_Finite_Generation_Checking RRA_Finite_Environment_Preservation RRA_Generation_Transport
begin

theorem finite_check_generation_included:
  assumes checked: "finite_check_generation G E u r"
    and included: "finite_environment_included E F" and formed: "finite_environment_formed F"
  shows "finite_check_generation G F u r"
  using generation_at_included[OF checked[unfolded finite_check_generation_exact]
    included[unfolded finite_environment_included_correct]
    formed[unfolded finite_environment_formed_correct]]
  by (simp only: finite_check_generation_exact)

end
