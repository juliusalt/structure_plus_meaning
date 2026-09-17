theory Finite_Inspected_Values
 imports Finite_Presented_Assessments
begin

definition finite_inspected_value where
 "finite_inspected_value present inspect facets x=Finite_Pair (present x)
   (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_boolean_data)
     (map (\<lambda>f. (f,inspect x f)) facets))"

lemma finite_inspected_value_injective [intro]:
 "inj present \<Longrightarrow> inj (finite_inspected_value present inspect facets)"
 by (auto simp: inj_def finite_inspected_value_def)

lemma finite_inspected_value_original:
 "finite_inspected_value present inspect facets x=finite_inspected_value present inspect facets y
   \<Longrightarrow> present x=present y"
 by (simp add: finite_inspected_value_def)

text \<open>The complete original value is accompanied by actual inspections,
 with the exact ordered facet occurrences. No inspection result is assumed.
 Original-condition claims still need the inspector's subject equation.\<close>
end
