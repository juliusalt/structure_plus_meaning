theory Factor_Reference_Forests
  imports Factor_Reference_Tables RRA_Syntax_Families
begin

section \<open>Reference tables for disjoint copies of complete blocks\<close>

lemma map_slot_keys_composition:
  "map_slot_keys f (map_slot_keys g M) = map_slot_keys (f \<circ> g) M"
  by (simp add: map_slot_keys_def image_image split_def comp_def)

text \<open>
  The forest's reference table is each child's table under that child's branch, as the forest is
  each child placed at its branch: it is the placed table (@{text RRA_Placed_Forests}) at the family
  of the syntax branches, and its facts follow from the notion's member equation and the branch's
  contracts alone.
\<close>

definition syntax_forest_table :: "(local_address \<times> 'a) set list \<Rightarrow> (local_address \<times> 'a) set" where
  "syntax_forest_table Ms = placed_table syntax_branch Ms"

lemma syntax_forest_table_eq:
  "syntax_forest_table Ms = (\<Union>i<length Ms. map_slot_keys (syntax_branch i) (Ms!i))"
  by (simp add: syntax_forest_table_def placed_table_eq)

lemma syntax_forest_table_Nil [simp]: "syntax_forest_table [] = {}"
  by (simp add: syntax_forest_table_def)

lemma syntax_forest_empty_tables [simp]:
  "syntax_forest_table (replicate n {}) = {}"
  by (auto simp: syntax_forest_table_def placed_table_member)

lemma syntax_forest_table_member:
  assumes index: "i < length Ms" and member: "(k,x) \<in> Ms!i"
  shows "(syntax_branch i k,x) \<in> syntax_forest_table Ms"
  unfolding syntax_forest_table_def placed_table_member using index member by blast

lemma syntax_forest_table_origin:
  assumes "(k,x) \<in> syntax_forest_table Ms"
  shows "\<exists>i<length Ms. \<exists>a. (a,x) \<in> Ms!i \<and> k=syntax_branch i a"
  using assms unfolding syntax_forest_table_def placed_table_member by blast

lemma syntax_forest_table_child:
  assumes index: "i < length Ms"
  shows "map_slot_keys (syntax_branch i) (Ms!i) \<subseteq> syntax_forest_table Ms"
  using syntax_forest_table_member[OF index] by (auto simp: map_slot_keys_def)

lemma syntax_forest_table_range:
  "rel_ran (syntax_forest_table Ms) = (\<Union>M\<in>set Ms. rel_ran M)"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> rel_ran (syntax_forest_table Ms)"
  then have "\<exists>k. (k,x) \<in> syntax_forest_table Ms" by (simp only: rel_ran_def mem_Collect_eq)
  then obtain k where "(k,x) \<in> syntax_forest_table Ms" ..
  then show "x \<in> (\<Union>M\<in>set Ms. rel_ran M)"
    by (elim syntax_forest_table_origin[elim_format] exE conjE) (rule UN_I[OF nth_mem rel_ranI])
next
  fix x assume "x \<in> (\<Union>M\<in>set Ms. rel_ran M)"
  then obtain M where M0: "M \<in> set Ms" "x \<in> rel_ran M" by (rule UN_E)
  have "\<exists>k. (k,x) \<in> M" using M0(2) by (simp only: rel_ran_def mem_Collect_eq)
  then obtain k where "(k,x) \<in> M" ..
  with M0 have M: "M \<in> set Ms" "(k,x) \<in> M" by simp_all
  obtain i where i: "i < length Ms" "Ms!i = M" using M(1) by (auto simp: in_set_conv_nth)
  have "(syntax_branch i k,x) \<in> syntax_forest_table Ms"
    by (rule syntax_forest_table_member) (use i M in auto)
  then show "x \<in> rel_ran (syntax_forest_table Ms)" by (rule rel_ranI)
qed

lemma syntax_forest_table_domain:
  "rel_dom (syntax_forest_table Ms) = syntax_forest_positions (map rel_dom Ms)"
proof (rule set_eqI, rule iffI)
  fix k assume member: "k \<in> rel_dom (syntax_forest_table Ms)"
  obtain x where entry: "(k,x) \<in> syntax_forest_table Ms" using member by (auto simp: rel_dom_def)
  obtain i a where origin: "i < length Ms" "(a,x) \<in> Ms!i" "k=syntax_branch i a"
    using syntax_forest_table_origin[OF entry] by blast
  have key: "a \<in> rel_dom (Ms!i)" by (rule rel_domI[OF origin(2)])
  show "k \<in> syntax_forest_positions (map rel_dom Ms)"
    unfolding syntax_forest_position_member
    by (rule exI[of _ i]) (use origin(1,3) key in auto)
next
  fix k assume member: "k \<in> syntax_forest_positions (map rel_dom Ms)"
  obtain i a where origin: "i < length Ms" "a \<in> rel_dom (Ms!i)" "k=syntax_branch i a"
    using member by (auto simp: syntax_forest_position_member)
  obtain x where entry: "(a,x) \<in> Ms!i" using origin(2) by (auto simp: rel_dom_def)
  have copied: "(syntax_branch i a,x) \<in> syntax_forest_table Ms"
    by (rule syntax_forest_table_member[OF origin(1) entry])
  show "k \<in> rel_dom (syntax_forest_table Ms)" using rel_domI[OF copied] origin(3) by simp
qed

lemma syntax_forest_table_bounds:
  assumes len: "length Ms = length Rs"
    and bounds: "\<forall>i<length Rs. rel_dom (Ms!i) \<subseteq> rra_carrier (object_structure (Rs!i))"
  shows "rel_dom (syntax_forest_table Ms) \<subseteq> rra_carrier (object_structure (syntax_forest Rs))"
proof
  fix k assume member: "k \<in> rel_dom (syntax_forest_table Ms)"
  obtain x where entry: "(k,x) \<in> syntax_forest_table Ms" using member by (auto simp: rel_dom_def)
  obtain i a where origin: "i < length Ms" "(a,x) \<in> Ms!i" "k=syntax_branch i a"
    using syntax_forest_table_origin[OF entry] by blast
  have index: "i < length Rs" using origin(1) len by simp
  have inside: "a \<in> rra_carrier (object_structure (Rs!i))"
    using bounds index rel_domI[OF origin(2)] by blast
  show "k \<in> rra_carrier (object_structure (syntax_forest Rs))"
    using syntax_forest_child_inside[OF index inside] origin(3) by simp
qed

lemma reference_table_disjoint_copies:
  assumes first: "reference_table_formed L C" and second: "reference_table_formed A B"
  shows "reference_table_formed
    (map_slot_keys (Cons 2) L \<union> map_slot_keys (Cons 3) A)
    (map_slot_keys (Cons 2) C \<union> map_slot_keys (Cons 3) B)"
proof -
  have left: "reference_table_formed (map_slot_keys (Cons 2) L) (map_slot_keys (Cons 2) C)"
    by (rule reference_table_map[OF first]) (simp add: inj_def)
  have right: "reference_table_formed (map_slot_keys (Cons 3) A) (map_slot_keys (Cons 3) B)"
    by (rule reference_table_map[OF second]) (simp add: inj_def)
  have separate: "(rel_dom (map_slot_keys (Cons 2) L) \<union> rel_dom (map_slot_keys (Cons 2) C)) \<inter>
    (rel_dom (map_slot_keys (Cons 3) A) \<union> rel_dom (map_slot_keys (Cons 3) B)) = {}"
    by (auto simp: map_slot_keys_domain)
  show ?thesis by (rule reference_table_union[OF left right separate])
qed

lemma reference_table_forest:
  assumes len: "length Ls = length Cs"
    and profiles: "\<forall>i<length Ls. reference_table_formed (Ls!i) (Cs!i)"
  shows "reference_table_formed (syntax_forest_table Ls) (syntax_forest_table Cs)"
  unfolding syntax_forest_table_def
  by (rule reference_table_placed[OF len profiles syntax_branch_injective syntax_branch_disjoint])

text \<open>
  A forest reference has exactly one source block and copied source slot.
  Its target value or callee site is unchanged. Literal and callee slots from
  different blocks are disjoint, so the combined tables remain finite and
  functional. Every resulting slot belongs to the complete forest carrier.
\<close>

end
