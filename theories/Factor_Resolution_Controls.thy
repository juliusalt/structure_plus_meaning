theory Factor_Resolution_Controls
  imports Factor_Material_Resolution Factor_Distinct_Payloads Factor_Substitution
begin

text \<open>
  The resolver's controls, one lemma proved by one evaluation; no library theory imports this theory.

  Site 1 concludes its payload list from the premise of site 0 at the pair of its variables 1 and 0 and
  the material premise @{const distinct_payloads_material}. At a ground list of payloads, resolving site
  0 by its two clauses binds variable 1 to the enumeration of the pairs of each payload and a fresh
  variable; those fresh variables are 3, 4, \<dots> here. The material premise's fields are then the
  pattern below, whose decoding is @{const distinct_payloads_material} with its variable 1 replaced by
  that enumeration pattern, and its skeleton is ground.
\<close>

definition site_one_atoms :: "octets list \<Rightarrow> nat finite_term_pattern" where
  "site_one_atoms as = foldr (\<lambda>(i,a) p. Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable (3+i))) p)
    (zip [0..<length as] as) (Finite_Pattern_Target (Finite_Whole finite_empty_artifact))"

definition site_one_material :: "octets list \<Rightarrow> nat finite_material_pattern" where
  "site_one_material as = \<lparr>finite_material_source=Finite_Variable 2, finite_material_atoms=site_one_atoms as,
    finite_material_edges=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_counts=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_functions=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)\<rparr>"

lemma site_one_material_decoded:
  "decode_finite_material (site_one_material as) =
    material_pattern_substitute (\<lambda>v. if v=1 then decode_finite_pattern (site_one_atoms as) else Pattern_Variable v)
      distinct_payloads_material"
  by (simp add: site_one_material_def decode_finite_material_def distinct_payloads_material_def
    material_pattern_substitute_def)

text \<open>
  At [[1],[2]] the premise has one solution: the source is the whole artifact with carrier {[1],[2]}, no
  incidence and no data, and each fresh variable its occurrence. At [[1],[1]] it has none, the addresses
  not being distinct. At the empty list its solution is the empty artifact. At [[1]] with its edges
  field a payload, the skeleton holds no variable and has no reading: no solution, whatever the source.
\<close>

lemma site_one_material_controls:
  "finite_material_resolution (site_one_material [[1],[2]]) = Material_Solutions
      {|{|(2,Finite_Target (Finite_Whole (finite_enumerated_artifact [[1],[2]] [] [] []))),
          (3,Finite_Target (Finite_Anchor (finite_enumerated_artifact [[1],[2]] [] [] []) [1])),
          (4,Finite_Target (Finite_Anchor (finite_enumerated_artifact [[1],[2]] [] [] []) [2]))|}|} \<and>
    finite_material_resolution (site_one_material [[1],[1]]) = Material_Solutions {||} \<and>
    finite_material_resolution (site_one_material []) =
      Material_Solutions {|{|(2,Finite_Target (Finite_Whole finite_empty_artifact))|}|} \<and>
    finite_material_resolution ((site_one_material [[1]])\<lparr>finite_material_edges:=Finite_Pattern_Payload []\<rparr>) =
      Material_Solutions {||}"
  by eval

end
