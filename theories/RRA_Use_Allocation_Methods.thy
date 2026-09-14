theory RRA_Use_Allocation_Methods
  imports RRA_Use_Allocation_Observations
begin

definition use_allocation_previous_method ::
  "nat\<Rightarrow>use_allocation_subject\<Rightarrow>local_address option\<Rightarrow>local_address option" where
  "use_allocation_previous_method m X=(case X of (U,u,V) \<Rightarrow>
    let head=finite_compact_use_head U u in
    if m=0 then finite_fresh_use_map U u
    else if m=1 then finite_compact_use_map U u
    else if m=2 then prefix_use_map [0] u
    else if m=3 then prefix_use_map [head] None
    else if m=4 then (\<lambda>x. case x of None \<Rightarrow> u | Some a \<Rightarrow> Some [head])
    else if m=5 then (\<lambda>x. case x of None \<Rightarrow> u | Some a \<Rightarrow> Some (head#rev a))
    else if m=6 then prefix_use_map [head mod 256] u
    else if m=7 then id
    else (\<lambda>_. None))"


definition use_allocation_method where
  "use_allocation_method (m::nat) X=(if m=9 then (case X of (U,u,V) \<Rightarrow>
    prefix_use_map [finite_compact_use_head U None] u) else use_allocation_previous_method m X)"

lemma use_allocation_previous_methods:
  "m<9 \<Longrightarrow> use_allocation_method m X=use_allocation_previous_method m X"
  by (simp add: use_allocation_method_def)

lemma use_allocation_original:
  "use_allocation_method 0 (U,u,V)=prefix_use_map (fresh_use_prefix (fset U) u) u"
  by (simp add: use_allocation_method_def use_allocation_previous_method_def Let_def finite_fresh_use_map_exact original_fresh_use_prefix)

lemma use_allocation_compact:
  "use_allocation_method 1 (U,u,V)=prefix_use_map (compact_use_prefix (fset U) u) u"
  by (simp add: use_allocation_method_def use_allocation_previous_method_def Let_def finite_compact_use_map_exact compact_use_map_def)

theorem use_allocation_correct_semantics:
  assumes method: "m\<in>{0,1}" and facet: "f\<in>{0,1,2,3}"
  shows "use_allocation_condition f (use_allocation_method m) X"
proof -
  obtain U u V where shape: "X=(U,u,V)" by (cases X) auto
  have original: "prefix_avoids_uses (fset U) u (fresh_use_prefix (fset U) u)"
    by (rule original_prefix_avoids_uses) simp
  have compact: "prefix_avoids_uses (fset U) u (compact_use_prefix (fset U) u)"
    by (rule compact_use_prefix_avoids) simp
  show ?thesis using method prefix_allocation_semantics[OF original facet, of V]
      prefix_allocation_semantics[OF compact facet, of V]
    by (auto simp: shape use_allocation_condition_def use_allocation_original
      use_allocation_compact[unfolded One_nat_def])
qed

theorem use_allocation_compact_growth:
  "use_allocation_condition 4 (use_allocation_method 1) X"
  by (cases X)
    (auto simp: use_allocation_condition_def use_allocation_row_condition_def
      use_allocation_compact[unfolded One_nat_def] compact_use_prefix_def split: option.splits)

definition use_allocation_previous_case :: "nat\<Rightarrow>use_allocation_subject" where
  "use_allocation_previous_case w=(let V={|[],[0],[1,2]|} in
    if w=0 then ({||},None,{|[]|})
    else if w=1 then ({||},Some [],V)
    else if w=2 then ({|None,Some [0],Some [0,0]|},Some [7],V)
    else if w=3 then (fset_of_list (map (\<lambda>i. Some [i]) [0..<256]),Some [],V)
    else if w=4 then ({|Some [300]|},None,{|[],[1,0],[300]|})
    else if w=5 then ({|Some (replicate 32 0)|},None,V)
    else if w=6 then ({|Some (replicate 128 0)|},None,V)
    else if w=7 then (fset_of_list (map (\<lambda>i. Some [i,1]) [0..<128]),None,V)
    else if w=8 then ({||},Some [999],V)
    else if w=9 then ({|Some [0]|},Some [],{|[0],[0,0]|})
    else if w=10 then ({|Some []|},Some [300],{||})
    else ({|None,Some []|},Some [300],V))"


definition use_allocation_case where
  "use_allocation_case (w::nat)=(if w=12 then ({||},Some [0],{|[],[1,2]|})
    else if w=13 then ({||},Some [1],{|[],[1,2]|}) else use_allocation_previous_case w)"

lemma use_allocation_previous_cases:
  "w<12 \<Longrightarrow> use_allocation_case w=use_allocation_previous_case w"
  by (simp add: use_allocation_case_def)

end
