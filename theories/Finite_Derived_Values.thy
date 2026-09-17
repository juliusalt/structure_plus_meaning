theory Finite_Derived_Values
 imports Finite_Presented_Coordinates
begin

definition finite_derived_value where
 "finite_derived_value present derived x=Finite_Pair (present x) (derived x)"
lemma finite_derived_value_injective [intro]:
 "inj present \<Longrightarrow> inj (finite_derived_value present derived)"
 by (auto simp: inj_def finite_derived_value_def)
text \<open>An actual derived observation accompanies its entire original value.
 The first projection retains the original identity; the derivation supplies no
 assumed condition. A caller still owes the original-subject law of an inspection.\<close>
end
