theory RRA_Graft_Observations
  imports RRA_Finite_Embedded_Grafts Finite_Map_Observations
begin

type_synonym graft_subject =
  "local_address option finite_artifact_environment\<times>local_address option\<times>
    local_address option finite_artifact_environment"
type_synonym graft_result =
  "(local_address option\<Rightarrow>local_address option)\<times>local_address option finite_artifact_environment"
type_synonym graft_assessment =
  "graft_subject\<times>(local_address option\<times>local_address option) fset\<times>
    local_address option finite_artifact_environment\<times>local_address option finite_artifact_environment"

definition graft_input_uses where
  "graft_input_uses X=(case X of (E,u,F) \<Rightarrow> finsert None (finite_environment_uses F))"

definition graft_mapping_condition where
  "graft_mapping_condition (f::nat) X x y=(case X of (E,u,F) \<Rightarrow>
    if f=0 then (x=None \<longrightarrow> y=u)
    else if f=2 then (x\<noteq>None \<longrightarrow> y\<notin>insert u (environment_uses (decode_finite_environment E)))
    else if f=4 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> use_word_length y=Suc (length a))
    else False)"

definition graft_condition where
  "graft_condition (f::nat) method X=(case (X,method X) of ((E,u,F),(h,G)) \<Rightarrow>
    if f=1 then inj_on h (fset (graft_input_uses X))
    else if f=3 then decode_finite_environment G=embedded_graft_environment h
      (decode_finite_environment E) (decode_finite_environment F)
    else (\<forall>x\<in>fset (graft_input_uses X). graft_mapping_condition f X x (h x)))"

definition graft_mapping_check where
  "graft_mapping_check (f::nat) X x y=(case X of (E,u,F) \<Rightarrow>
    if f=0 then (x=None \<longrightarrow> y=u)
    else if f=2 then (x\<noteq>None \<longrightarrow> \<not>(y |\<in>| finsert u (finite_environment_uses E)))
    else if f=4 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> use_word_length y=Suc (length a))
    else False)"

lemma graft_mapping_check_exact:
  "graft_mapping_check f X x y=graft_mapping_condition f X x y"
  by (cases X) (simp add: graft_mapping_check_def graft_mapping_condition_def finite_environment_uses_correct)

definition graft_assess where
  "graft_assess method X=(case (X,method X) of ((E,u,F),(h,G)) \<Rightarrow>
    (X,finite_map_rows (graft_input_uses X) h,G,finite_embedded_graft h E F))"

definition graft_inspect :: "graft_assessment\<Rightarrow>nat\<Rightarrow>bool" where
  "graft_inspect report f=(case report of (X,rows,G,reference) \<Rightarrow>
    if f=1 then finite_map_injective rows
    else if f=3 then G=reference
    else finite_map_preserves rows (graft_mapping_check f X))"

theorem graft_assessment_exact:
  "graft_inspect (graft_assess method X) f=graft_condition f method X"
  by (cases X; cases "method X")
    (simp add: graft_inspect_def graft_assess_def graft_condition_def finite_map_injective_exact
      finite_map_preserves_exact graft_mapping_check_exact finite_embedded_graft_exact[symmetric])

lemma graft_condition_from_embedding:
  assumes method: "method (E,u,F)=(h,G)"
    and embedding: "boundary_use_embedding (environment_uses (decode_finite_environment E)) u h"
    and whole: "decode_finite_environment G=embedded_graft_environment h
      (decode_finite_environment E) (decode_finite_environment F)"
    and facet: "f\<in>{0,1,2,3}"
  shows "graft_condition f method (E,u,F)"
proof -
  have injection: "inj_on h (fset (graft_input_uses (E,u,F)))"
    using embedding by (auto simp: boundary_use_embedding_def inj_on_def)
  show ?thesis using embedding whole facet injection
    by (auto simp: graft_condition_def method graft_mapping_condition_def boundary_use_embedding_def)
qed

definition graft_view_formed :: "local_address option finite_artifact_environment\<Rightarrow>bool" where
  "graft_view_formed E=finite_environment_formed E"

text \<open>
  The complete original environments, boundary, actual use mapping and whole
  output determine each observation. Exact output equality is against the
  original merge and rename constructors. Formation of the displayed results
  is observed separately; an unformed input or conflicting boundary does not
  become an admitted transition merely because its raw merge was reproduced.
\<close>

end
