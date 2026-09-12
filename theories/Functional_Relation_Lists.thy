theory Functional_Relation_Lists
  imports Functional_Relation_Joins
begin

section \<open>An ordered link list enumerates its complete functional join\<close>

definition joined_relation_rows :: "('n\<times>'v) set\<Rightarrow>('s\<times>'n) list\<Rightarrow>('s\<times>'v) list" where
  "joined_relation_rows J ds=map (\<lambda>(s,n). (s,rel_value J n)) ds"

lemma joined_relation_rows_keys:
  "map fst (joined_relation_rows J ds)=map fst ds"
  by (simp add: joined_relation_rows_def comp_def case_prod_unfold)

theorem joined_relation_rows_set:
  assumes functional: "single_valued J" and covered: "rel_ran (set ds)\<subseteq>rel_dom J"
  shows "set (joined_relation_rows J ds)=set ds O J"
proof -
  have selected: "(n,rel_value J n)\<in>J" if row: "(s,n)\<in>set ds" for s n
  proof -
    have key: "n\<in>rel_dom J" using covered rel_ranI[OF row] by blast
    obtain v where selected_value: "(n,v)\<in>J" using key by (auto simp: rel_dom_def)
    show ?thesis using selected_value rel_value_eq[OF functional selected_value] by simp
  qed
  have lower: "set (joined_relation_rows J ds)\<subseteq>set ds O J"
  proof
    fix z assume member: "z\<in>set (joined_relation_rows J ds)"
    obtain a n where row: "(a,n)\<in>set ds" and result: "z=(a,rel_value J n)"
      using member unfolding joined_relation_rows_def by auto
    have joined: "(a,rel_value J n)\<in>set ds O J"
      by (rule relcompI[OF row selected[OF row]])
    show "z\<in>set ds O J" using joined by (simp only: result)
  qed
  have upper: "set ds O J\<subseteq>set (joined_relation_rows J ds)"
  proof
    fix z assume member: "z\<in>set ds O J"
    obtain s n v where shape: "z=(s,v)" and row: "(s,n)\<in>set ds" and target: "(n,v)\<in>J"
      using member by auto
    have chosen: "rel_value J n=v" by (rule rel_value_eq[OF functional target])
    have mapped: "(s,rel_value J n)\<in>set (joined_relation_rows J ds)"
      unfolding joined_relation_rows_def set_map by (rule image_eqI[OF _ row]) simp
    show "z\<in>set (joined_relation_rows J ds)" using mapped by (simp only: shape chosen)
  qed
  show ?thesis by (rule equalityI[OF lower upper])
qed


section \<open>Complete functional relations quantify over the same identified rows\<close>

theorem functional_relations_all_values:
  assumes left: "single_valued N" and right: "single_valued J" and domain: "rel_dom J=rel_dom N"
  shows "(\<forall>k v. (k,v)\<in>J \<longrightarrow> (\<exists>a. (k,a)\<in>N \<and> R k a v)) \<longleftrightarrow>
    (\<forall>k a. (k,a)\<in>N \<longrightarrow> R k a (rel_value J k))"
proof
  assume row_condition: "\<forall>k v. (k,v)\<in>J \<longrightarrow> (\<exists>a. (k,a)\<in>N \<and> R k a v)"
  show "\<forall>k a. (k,a)\<in>N \<longrightarrow> R k a (rel_value J k)"
  proof (intro allI impI)
    fix k a assume row: "(k,a)\<in>N"
    have key: "k\<in>rel_dom J" using rel_domI[OF row] domain by simp
    obtain v where selected_value: "(k,v)\<in>J" using key by (auto simp: rel_dom_def)
    obtain b where actual: "(k,b)\<in>N" "R k b v" using row_condition selected_value by blast
    have same: "b=a" by (rule single_valued_outputs[OF left actual(1) row])
    have selected: "rel_value J k=v" by (rule rel_value_eq[OF right selected_value])
    show "R k a (rel_value J k)" using actual(2) by (simp only: same selected)
  qed
next
  assume nodes: "\<forall>k a. (k,a)\<in>N \<longrightarrow> R k a (rel_value J k)"
  show "\<forall>k v. (k,v)\<in>J \<longrightarrow> (\<exists>a. (k,a)\<in>N \<and> R k a v)"
  proof (intro allI impI)
    fix k v assume row: "(k,v)\<in>J"
    have key: "k\<in>rel_dom N" using rel_domI[OF row] domain by simp
    obtain a where node: "(k,a)\<in>N" using key by (auto simp: rel_dom_def)
    have selected: "rel_value J k=v" by (rule rel_value_eq[OF right row])
    show "\<exists>a. (k,a)\<in>N \<and> R k a v" using nodes node selected by blast
  qed
qed

lemma finite_filter_order:
  assumes finite: "finite A" and order: "distinct ys" and exact: "set ys={x\<in>A. F x}"
  obtains xs where "set xs=A" "distinct xs" "filter F xs=ys"
proof -
  have rest_finite: "finite (A-set ys)" using finite by simp
  obtain zs where rest: "set zs=A-set ys" "distinct zs"
    using finite_distinct_list[OF rest_finite] by blast
  have all_selected: "\<forall>y\<in>set ys. F y" using exact by blast
  have selected: "filter F ys=ys" using all_selected by (induction ys) auto
  have excluded: "filter F zs=[]" using exact rest(1) by (auto simp: filter_empty_conv)
  have complete: "set (ys@zs)=A" using exact rest(1) by auto
  have distinct: "distinct (ys@zs)" using order rest by auto
  show thesis by (rule that[OF complete distinct]) (simp add: selected excluded)
qed


lemma functional_filter_order:
  assumes finite: "finite J" and functional: "single_valued J" and order: "distinct hs"
    and boundary: "set hs={z\<in>J. F z}"
  obtains xs where "set xs=J" "distinct (map fst xs)" "filter F xs=hs"
proof -
  obtain xs where rows: "set xs=J" "distinct xs" "filter F xs=hs"
    by (rule finite_filter_order[OF finite order boundary]) (rule that; assumption)
  have keys: "distinct (map fst xs)" using rows(1,2) functional by (simp only: distinct_keys_iff; blast)
  show thesis by (rule that[OF rows(1) keys rows(3)])
qed

text \<open>
  The list preserves every link occurrence and its order. The relation equation
  requires a value at every target. Sharing a target and repeated link rows
  remain possible; neither is removed by the construction.
\<close>

end
