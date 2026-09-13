theory Finite_Set_Encoding
  imports "HOL-Library.FSet"
begin

section \<open>Finite set constructors retain their abstract representation\<close>

lemma finite_set_empty_encoding [simp]: "Abs_fset {}={||}"
  by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)

lemma finite_set_insert_encoding [simp]:
  "finite A \<Longrightarrow> Abs_fset (insert a A)=finsert a (Abs_fset A)"
  by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)

end
