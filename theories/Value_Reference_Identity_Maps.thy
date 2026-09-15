theory Value_Reference_Identity_Maps
  imports Complete_Value_References
begin

lemma value_reference_index_identity_map:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "value_reference_index (encode x) (map encode table)=value_reference_index x table"
  by (induction table) (simp_all add: each)

lemma value_reference_step_identity_map:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "map_prod id (map encode) (value_reference_step x table)=
    value_reference_step (encode x) (map encode table)"
  by (simp add: value_reference_step_def value_reference_index_identity_map[OF each]
      split: option.splits)

lemma value_reference_read_map:
  "value_reference_read (map encode table) i=map_option encode (value_reference_read table i)"
  by (simp add: value_reference_read_def)

text \<open>Referencing an original value and then applying an injective
  complete presentation produces the same index and presented table as
  referencing that presentation directly. Earlier reference order and all
  original table entries remain, including duplicate initial entries.\<close>

end
