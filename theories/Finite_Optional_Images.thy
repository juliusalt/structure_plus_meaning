theory Finite_Optional_Images
  imports "HOL-Library.FSet"
begin

definition finite_optional_image where
  "finite_optional_image f A=ffUnion (fimage (\<lambda>x. case f x of None \<Rightarrow> {||} | Some y \<Rightarrow> {|y|}) A)"

theorem finite_optional_image_exact:
  "y |\<in>| finite_optional_image f A \<longleftrightarrow> (\<exists>x. x |\<in>| A \<and> f x=Some y)"
  by (auto simp: finite_optional_image_def ffUnion.rep_eq fimage.rep_eq split: option.splits; force)

end
