theory RRA_Use_Allocation_Observations
  imports RRA_Finite_Compact_Uses Finite_Map_Observations
begin

type_synonym use_allocation_subject =
  "local_address option fset\<times>local_address option\<times>local_address fset"

definition use_allocation_inputs where
  "use_allocation_inputs X=(case X of (U,u,V) \<Rightarrow> finsert None (fimage Some V))"

definition use_allocation_row_condition where
  "use_allocation_row_condition (f::nat) X x y=(case X of (U,u,V) \<Rightarrow>
    if f=0 then (x=None \<longrightarrow> y=u)
    else if f=1 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> y\<notin>insert u (fset U))
    else if f=3 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> (\<exists>p. y=Some (p@a)))
    else if f=4 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> use_word_length y=Suc (length a))
    else False)"

definition use_allocation_condition where
  "use_allocation_condition (f::nat) method X=(if f=2 then
    inj_on (method X) (fset (use_allocation_inputs X))
    else (\<forall>x\<in>fset (use_allocation_inputs X). use_allocation_row_condition f X x (method X x)))"

definition use_allocation_row_check where
  "use_allocation_row_check (f::nat) X x y=(case X of (U,u,V) \<Rightarrow>
    if f=0 then (x=None \<longrightarrow> y=u)
    else if f=1 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> \<not>(y |\<in>| finsert u U))
    else if f=3 then (case x of None \<Rightarrow> True | Some a \<Rightarrow>
      (case y of None \<Rightarrow> False | Some b \<Rightarrow> list_suffix_check a b))
    else if f=4 then (case x of None \<Rightarrow> True | Some a \<Rightarrow> use_word_length y=Suc (length a))
    else False)"

lemma use_allocation_row_check_exact:
  "use_allocation_row_check f X x y=use_allocation_row_condition f X x y"
  by (cases X; cases x; cases y)
    (auto simp: use_allocation_row_check_def use_allocation_row_condition_def list_suffix_check_exact)

definition use_allocation_assess where
  "use_allocation_assess method X=(X,finite_map_rows (use_allocation_inputs X) (method X))"

definition use_allocation_inspect where
  "use_allocation_inspect report (f::nat)=(case report of (X,rows) \<Rightarrow>
    if f=2 then finite_map_injective rows
    else finite_map_preserves rows (use_allocation_row_check f X))"

theorem use_allocation_assessment_exact:
  "use_allocation_inspect (use_allocation_assess method X) f=use_allocation_condition f method X"
  by (simp add: use_allocation_assess_def use_allocation_inspect_def use_allocation_condition_def
    finite_map_injective_exact finite_map_preserves_exact use_allocation_row_check_exact)

lemma prefix_allocation_semantics:
  assumes fresh: "prefix_avoids_uses (fset U) u prefix" and facet: "f\<in>{0,1,2,3}"
  shows "use_allocation_condition f (\<lambda>_. prefix_use_map prefix u) (U,u,V)"
proof -
  have injection: "inj (prefix_use_map prefix u)" by (rule prefix_use_map_injective[OF fresh])
  have local_injection: "inj_on (prefix_use_map prefix u) (fset (use_allocation_inputs (U,u,V)))"
    by (rule inj_on_subset[OF injection]) simp
  have outside: "\<And>a. prefix_use_map prefix u (Some a)\<notin>insert u (fset U)"
    by (rule prefix_use_map_outside[OF fresh])
  show ?thesis using facet local_injection outside
    by (auto simp: use_allocation_condition_def use_allocation_row_condition_def split: option.splits)
qed

text \<open>
  Boundary identity, freshness, injectivity and original suffix preservation
  are independent conditions on actual mappings. A fifth condition records
  one added word coordinate. Each subject retains its complete reserved uses,
  supplied boundary and requested word set; absent input is always inspected.
  A scoped execution does not establish coverage of every possible request.
\<close>

end
