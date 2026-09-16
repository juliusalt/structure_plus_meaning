theory Projected_Identity_Execution
  imports Main
begin

definition observed_identity where
  "observed_identity observe complete x y=(observe x=observe y \<and> complete x=complete y)"

theorem observed_identity_exact:
  assumes complete: "\<And>x y. complete x=complete y \<longleftrightarrow> x=y"
  shows "observed_identity observe complete x y \<longleftrightarrow> x=y"
  by (auto simp: observed_identity_def complete)

text \<open>A cheap actual observation may rule out identity. Agreement of that
  observation never supplies identity: the complete injective view remains the
  final comparison. No formation premise, supplied discriminator, digest or
  pointer identity grants equality. The equation applies to arbitrary values.\<close>

end
