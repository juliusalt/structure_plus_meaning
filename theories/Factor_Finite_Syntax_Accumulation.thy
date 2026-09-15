theory Factor_Finite_Syntax_Accumulation
  imports Factor_Finite_Artifact_Enumeration RRA_Finite_Syntax_Construction
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
  "local_address \<Rightarrow> finite_syntax_rows \<Rightarrow> finite_syntax_rows" where
  "finite_syntax_rows_pair p X=(case X of (U,I,B) \<Rightarrow>
    (p#(p@[0])#(p@[1])#U,
     (p,p@[0],p@[2])#(p,p@[1],p@[3])#(p@[0],p@[0],p@[1])#I,B))"

lemma finite_syntax_rows_payload_object:
  "finite_syntax_rows_object (finite_syntax_rows_payload p v X)=
    finite_syntax_accumulate p (finite_payload_syntax v) (finite_syntax_rows_object X)"
  by (cases X) (simp add: finite_syntax_rows_payload_def finite_syntax_rows_object_def
      finite_syntax_accumulate_def finite_syntax_join_def finite_payload_syntax_def
      finite_payload_basis_def finite_enumerated_artifact_def id_def)

lemma finite_syntax_rows_pair_object:
  "finite_syntax_rows_object (finite_syntax_rows_pair p X)=
    finite_attach_structure (finite_syntax_rows_object X)
      \<lparr>finite_carrier={|p,p@[0],p@[1]|},
        finite_incidence={|(p,p@[0],p@[2]),(p,p@[1],p@[3]),(p@[0],p@[0],p@[1])|}\<rparr>"
  by (cases X) (auto simp: finite_syntax_rows_pair_def finite_syntax_rows_object_def
      finite_enumerated_artifact_def finite_attach_structure_def
      funion_commute funion_left_commute funion_assoc)

lemma append_singleton_function:
  "append (p@[n])=(\<lambda>q. p@(n#q))"
  by (rule ext) simp

lemma append_empty_function:
  "append []=(\<lambda>q. q)"
  by (rule ext) simp

lemma finite_syntax_accumulate_pair:
  "finite_attach_structure
      (finite_syntax_accumulate (p@[2]) R (finite_syntax_accumulate (p@[3]) S A))
      \<lparr>finite_carrier={|p,p@[0],p@[1]|},
        finite_incidence={|(p,p@[0],p@[2]),(p,p@[1],p@[3]),(p@[0],p@[0],p@[1])|}\<rparr>
    =finite_syntax_accumulate p (finite_pair_syntax R S) A"
  by (simp add: finite_syntax_accumulate_def finite_syntax_join_def finite_pair_syntax_def
      finite_attach_structure_def fimage_funion fimage_fimage fun_eq_iff id_def
      comp_def case_prod_unfold append_singleton_function
      funion_commute funion_left_commute funion_assoc)

lemma finite_syntax_accumulate_empty:
  assumes "finite_bag (finite_data C)={#}"
  shows "finite_syntax_accumulate [] C (finite_syntax_rows_object ([],[],[]))=C"
  using assms
  by (cases C; cases "finite_structure C"; cases "finite_data C")
    (simp add: finite_syntax_accumulate_def finite_syntax_join_def finite_syntax_rows_object_def
      finite_enumerated_artifact_def append_empty_function id_def)

text \<open>The row accumulator preserves the complete original syntax join. Its
  empty counted component is explicit, as in the original syntax constructors;
  it is not an operation for discarding counts from an arbitrary artifact.\<close>

end
