theory Finite_Supported_Images
  imports Finite_Set_Composition
begin

lemma finite_union_image_supported:
  assumes inside: "\<And>x. x |\<in>| S \<Longrightarrow> x |\<in>| A"
    and supported: "\<And>x y. x |\<in>| A \<Longrightarrow> y |\<in>| f x \<Longrightarrow> x |\<in>| S"
  shows "ffUnion (fimage f S)=ffUnion (fimage f A)"
  by (rule fset_inject[THEN iffD1], rule set_eqI)
    (simp only: finite_union_image_member; use inside supported in blast)

end
