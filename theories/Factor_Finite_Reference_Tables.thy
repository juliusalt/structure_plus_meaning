theory Factor_Finite_Reference_Tables
  imports Factor_Premise_Construction RRA_Finite_Artifacts
begin

section \<open>Finite reference operations retain every complete row\<close>

lemma slot_keys_value_map [simp]:
  "map_relation_values g (map_slot_keys f M)=map_slot_keys f (map_relation_values g M)"
  by (simp add: map_slot_keys_def map_relation_values_def image_image split_def)

lemma reference_value_union [simp]:
  "map_relation_values f (M\<union>N)=map_relation_values f M\<union>map_relation_values f N"
  by (simp add: map_relation_values_def image_Un)

definition finite_slot_keys :: "(local_address\<Rightarrow>local_address) \<Rightarrow>
    (local_address\<times>'a) fset \<Rightarrow> (local_address\<times>'a) fset" where
  "finite_slot_keys f M=fimage (\<lambda>(k,v). (f k,v)) M"

lemma finite_slot_keys_exact [simp]:
  "fset (finite_slot_keys f M)=map_slot_keys f (fset M)"
  by (simp add: finite_slot_keys_def map_slot_keys_def fimage.rep_eq)

lemma finite_slot_keys_values:
  "map_relation_values g (fset (finite_slot_keys f M))=
    map_slot_keys f (map_relation_values g (fset M))"
  by simp

lemma finite_reference_union_values:
  "map_relation_values f (fset (M |\<union>| N))=
    map_relation_values f (fset M)\<union>map_relation_values f (fset N)"
  by simp

text \<open>
  Rekeying moves each actual reference socket and preserves its value.
  Decoding commutes with rekeying and union. These operations preserve the
  complete literal and callee tables used by the syntax constructors.
\<close>

end
