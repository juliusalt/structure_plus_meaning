theory Ordered_Finite_Rows
  imports Finite_Investigation_Interface Ordered_Member_Trees "HOL-Library.Product_Lexorder"
begin

section \<open>Rows are selected through the ordered index of a complete set\<close>

definition ordered_investigation_select :: "'a::linorder list \<Rightarrow> 'a fset \<Rightarrow> 'a list" where
  "ordered_investigation_select xs A=(let T=ordered_member_tree A in
    filter (\<lambda>x. RBT.lookup T x\<noteq>None) (ordered_remdups xs))"

theorem ordered_investigation_select_exact:
  "ordered_investigation_select xs A=investigation_select xs A"
  by (simp add: ordered_investigation_select_def investigation_select_def Let_def
    ordered_remdups_exact ordered_member_tree_some)

text \<open>
  The ordered index records exactly the rows already retained. Each input row
  is inspected once, and the last occurrence order of the original list is
  returned. Membership reads the complete finite set through its canonical
  ordered list. No row, repetition boundary or selected value changes.
\<close>

end
