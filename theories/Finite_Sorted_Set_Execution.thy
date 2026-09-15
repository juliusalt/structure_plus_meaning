theory Finite_Sorted_Set_Execution
  imports Main
begin

lemma sorted_remdups_adj_distinct:
  "sorted (xs::'a::linorder list) \<Longrightarrow> distinct (remdups_adj xs)"
  by (induction xs rule: remdups_adj.induct)
    (auto simp: sorted_simps dest: order.antisym)

declare sorted_list_of_set_sort_remdups[code del]

lemma sorted_list_of_set_after_sort_code [code]:
  "sorted_list_of_set (set xs)=remdups_adj (sort xs)"
  by (rule sorted_distinct_set_unique)
    (simp_all add: sorted_remdups_adj_distinct)

text \<open>
  Sorting puts equal values next to each other. Removing adjacent repetitions
  then returns the same complete canonical set list, including for empty lists
  and arbitrary repeated inputs. The equation changes no multiset operation
  or counted occurrence. Every artifact field and original comparison retains
  the original canonical value. Physical execution time is measured separately.
\<close>

end
