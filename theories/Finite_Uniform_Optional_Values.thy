theory Finite_Uniform_Optional_Values
  imports Finite_Singleton_Selection
begin

definition finite_uniform_optional_value where
  "finite_uniform_optional_value rows=(case finite_singleton_option (fimage snd rows) of
    None \<Rightarrow> None | Some value \<Rightarrow> value)"

lemma finite_uniform_optional_value_exact:
  "finite_uniform_optional_value rows=Some value \<longleftrightarrow>
    fimage snd rows={|Some value|}"
  by (auto simp: finite_uniform_optional_value_def finite_singleton_option_some
    split: option.splits)

text \<open>
  A nonempty keyed family supplies one value only when every position supplies
  that same value. Empty families, failed positions and conflicting values
  remain unavailable. The complete keyed family can be retained independently.
\<close>

end
