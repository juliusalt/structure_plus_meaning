theory Factor_Finite_Syntax_Accumulation
  imports Factor_Finite_Artifact_Enumeration RRA_Finite_Syntax_Construction
    "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

type_synonym finite_syntax_rows =
  "local_address list \<times> (local_address \<times> local_address \<times> local_address) list \<times>
    (local_address \<times> octets) list"

definition finite_syntax_rows_object :: "finite_syntax_rows \<Rightarrow> finite_exact_artifact" where
  "finite_syntax_rows_object X=(case X of (U,I,B) \<Rightarrow> finite_enumerated_artifact U I [] B)"

definition finite_syntax_accumulate ::
  "local_address \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_syntax_accumulate p C A=finite_syntax_join (append p) id {||} {||} C A"

definition finite_syntax_rows_payload ::
  "local_address \<Rightarrow> octets \<Rightarrow> finite_syntax_rows \<Rightarrow> finite_syntax_rows" where
  "finite_syntax_rows_payload p v X=(case X of (U,I,B) \<Rightarrow> (p#U,I,(p,v)#B))"

definition finite_syntax_rows_pair ::
  "local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow>
    finite_syntax_rows \<Rightarrow> finite_syntax_rows" where
  "finite_syntax_rows_pair r p q a b X=(case X of (U,I,B) \<Rightarrow>
    (r#p#q#U,(r,p,a)#(r,q,b)#(p,p,q)#I,B))"

lemma finite_syntax_rows_payload_object:
  "finite_syntax_rows_object (finite_syntax_rows_payload p v X)=
    finite_syntax_accumulate p (finite_payload_syntax v) (finite_syntax_rows_object X)"
  by (cases X) (simp add: finite_syntax_rows_payload_def finite_syntax_rows_object_def
      finite_syntax_accumulate_def finite_syntax_join_def finite_payload_syntax_def
      finite_payload_basis_def finite_enumerated_artifact_def id_def)

lemma finite_syntax_rows_pair_object:
  "finite_syntax_rows_object (finite_syntax_rows_pair r p q a b X)=
    finite_attach_structure (finite_syntax_rows_object X)
      \<lparr>finite_carrier={|r,p,q|},finite_incidence={|(r,p,a),(r,q,b),(p,p,q)|}\<rparr>"
  by (cases X) (auto simp: finite_syntax_rows_pair_def finite_syntax_rows_object_def
      finite_enumerated_artifact_def finite_attach_structure_def
      funion_commute funion_left_commute funion_assoc)

lemma append_empty_function:
  "append []=(\<lambda>q. q)"
  by (rule ext) simp

lemma finite_syntax_accumulate_empty:
  assumes "finite_bag (finite_data C)={#}"
  shows "finite_syntax_accumulate [] C (finite_syntax_rows_object ([],[],[]))=C"
  using assms
  by (cases C; cases "finite_structure C"; cases "finite_data C")
    (simp add: finite_syntax_accumulate_def finite_syntax_join_def finite_syntax_rows_object_def
      finite_enumerated_artifact_def append_empty_function id_def)

text \<open>The row accumulator preserves the complete syntax join. A pair node's rows
  are stated by its root, its two ports and the roots of its two children, so every
  addressing of the syntax accumulates through the same rows. Its empty counted
  component is explicit, as in the original syntax constructors; it is not an
  operation for discarding counts from an arbitrary artifact.\<close>

lemma finite_syntax_rows_object_listed:
  "finite_syntax_rows_object (case X of (U,I,B) \<Rightarrow>
      (sorted_list_of_set (set U),sorted_list_of_set (set I),sorted_list_of_set (set B)))=
    finite_syntax_rows_object X"
  by (cases X) (simp add: finite_syntax_rows_object_def finite_enumerated_artifact_def fset_of_list.abs_eq)

text \<open>Accumulated rows are a listing of each row family in construction order. Listed again
  in its canonical order, each family presents the same finite set, so the object is unchanged;
  a set presented by its canonical listing is recognized by one pass wherever it is listed,
  compared or checked later (\<open>Finite_Sorted_Set_Execution\<close>), instead of being sorted again
  at every such use.\<close>

end
