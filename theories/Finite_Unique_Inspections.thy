theory Finite_Unique_Inspections
  imports "HOL-Library.FSet"
begin

lemma finite_unique_inspection_conjunction:
  assumes unique: "\<And>x y. x |\<in>| R \<Longrightarrow> y |\<in>| R \<Longrightarrow> x=y"
  shows "fBex R P \<and> fBex R Q \<longleftrightarrow> fBex R (\<lambda>x. P x \<and> Q x)"
  using unique by blast

text \<open>
  Separate field inspections of one unique complete reading share the same
  witness. Uniqueness is an explicit prerequisite; independent existential
  field witnesses cannot otherwise establish a complete joint reading.
\<close>

end
