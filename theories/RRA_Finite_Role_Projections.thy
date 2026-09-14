theory RRA_Finite_Role_Projections
  imports RRA_Executable_Syntax
begin

definition finite_participation_occurrences where
  "finite_participation_occurrences S=fimage (\<lambda>(r,p,x). p) (finite_incidence S)"

definition finite_reached_occurrences where
  "finite_reached_occurrences S=fimage (\<lambda>(r,p,x). x) (finite_incidence S)"

lemma finite_role_projections_exact:
  "fset (finite_participation_occurrences S)=participation_occurrences (decode_finite_structure S)"
  "fset (finite_reached_occurrences S)=reached_occurrences (decode_finite_structure S)"
  by (auto simp: finite_participation_occurrences_def finite_reached_occurrences_def
    participation_occurrences_def reached_occurrences_def fimage.rep_eq; force)+

definition finite_unreferenced_positions where
  "finite_unreferenced_positions S=finite_carrier S |-| (finite_participation_occurrences S |\<union>|
    finite_reached_occurrences S)"

lemma finite_unreferenced_positions_exact:
  "fset (finite_unreferenced_positions S)=rra_carrier (decode_finite_structure S) -
    (participation_occurrences (decode_finite_structure S) \<union> reached_occurrences (decode_finite_structure S))"
  by (simp add: finite_unreferenced_positions_def finite_role_projections_exact)

end
