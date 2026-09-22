theory RRA_Syntax_Forests
  imports RRA_Syntax_Construction RRA_Placed_Forests
begin

section \<open>Disjoint copies of complete private syntax scopes\<close>

definition syntax_union :: "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact" where
  "syntax_union R S =
    \<lparr>object_structure =
      \<lparr>rra_carrier = Cons 2 ` rra_carrier (object_structure R) \<union> Cons 3 ` rra_carrier (object_structure S),
       rra_incidence = rra_incidence (push_structure (Cons 2) (object_structure R)) \<union>
          rra_incidence (push_structure (Cons 3) (object_structure S))\<rparr>,
     object_data = object_data (pair_syntax R S)\<rparr>"

lemma syntax_union_no_counts [simp]: "bag_count (object_data (syntax_union R S)) = (\<lambda>_. 0)"
  by (simp add: syntax_union_def)

lemma syntax_union_formed:
  assumes rf: "exact_formed R" and sf: "exact_formed S"
  shows "exact_formed (syntax_union R S)"
proof -
  have sources: "object_formed R" "object_formed S" using rf sf by (auto simp: exact_formed_def)
  have formed: "object_formed (syntax_union R S)"
    using sources by (auto simp: syntax_union_def pair_syntax_def object_formed_def rra_formed_def
        push_structure_def basis_formed_def single_valued_def bag_support_def)
  have payloads: "\<And>a v. (a,v) \<in> functional_bindings (object_data R) \<union>
    functional_bindings (object_data S) \<Longrightarrow> octets_formed v"
  proof -
    fix a v assume member: "(a,v) \<in> functional_bindings (object_data R) \<union> functional_bindings (object_data S)"
    have "v \<in> basis_values (object_data R) \<union> basis_values (object_data S)"
      using member by (force simp: basis_values_def)
    then show "octets_formed v" using rf sf by (auto simp: exact_formed_def)
  qed
  have addresses: "\<And>a. a \<in> rra_carrier (object_structure R) \<union> rra_carrier (object_structure S) \<Longrightarrow> octets_formed a"
    using rf sf by (auto simp: exact_formed_def)
  show ?thesis using formed payloads addresses
    by (auto simp: exact_formed_def syntax_union_def pair_syntax_def basis_values_def bag_support_def octets_formed_def; blast)
qed

lemma syntax_union_reads_left:
  assumes "bag_count (object_data R) = (\<lambda>_. 0)"
  shows "object_reads_agree (push_object (Cons 2) R) (syntax_union R S) (Cons 2 ` rra_carrier (object_structure R))"
  using pair_syntax_reads_left[OF assms, of S]
  by (auto simp: object_reads_agree_def syntax_union_def pair_syntax_def headed_incidence_def push_structure_def)

lemma syntax_union_reads_right:
  assumes "bag_count (object_data S) = (\<lambda>_. 0)"
  shows "object_reads_agree (push_object (Cons 3) S) (syntax_union R S) (Cons 3 ` rra_carrier (object_structure S))"
  using pair_syntax_reads_right[OF assms, of R]
  by (auto simp: object_reads_agree_def syntax_union_def pair_syntax_def headed_incidence_def push_structure_def)

section \<open>The branch of a forest child and its contracts\<close>

fun syntax_branch :: "nat \<Rightarrow> local_address \<Rightarrow> local_address" where
  "syntax_branch 0 a = 2#a"
| "syntax_branch (Suc n) a = 3#syntax_branch n a"

lemma syntax_branch_zero: "syntax_branch 0 = Cons 2" by (rule ext) simp

lemma syntax_branch_prefix: "syntax_branch i a = syntax_branch i [] @ a"
  by (induction i) simp_all

lemma syntax_branch_top_prefix: "\<exists>b. syntax_branch i a = 2#b \<or> syntax_branch i a = 3#b"
  by (cases i) simp_all

lemma syntax_branch_injective: "inj (syntax_branch n)"
  by (induction n) (auto simp: inj_def)

lemma syntax_branch_formed:
  assumes "octets_formed a"
  shows "octets_formed (syntax_branch n a)"
  using assms by (induction n) (simp_all add: octets_formed_def)

lemma syntax_branch_addressing:
  assumes formed: "exact_formed R"
  shows "finite_addressing (rra_carrier (object_structure R)) (syntax_branch n)"
proof -
  have injective: "inj_on (syntax_branch n) (rra_carrier (object_structure R))"
    using syntax_branch_injective[of n] by (auto simp: inj_on_def)
  have addresses: "\<forall>a\<in>rra_carrier (object_structure R). octets_formed (syntax_branch n a)"
    using formed syntax_branch_formed by (auto simp: exact_formed_def)
  show ?thesis using injective addresses by (simp add: finite_addressing_def)
qed

lemma syntax_branch_disjoint:
  assumes "i \<noteq> j"
  shows "range (syntax_branch i) \<inter> range (syntax_branch j) = {}"
  using assms
proof (induction i arbitrary: j)
  case 0
  then show ?case by (cases j) auto
next
  case (Suc i)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by auto
  next
    case (Suc n)
    have disjoint: "range (syntax_branch i) \<inter> range (syntax_branch n) = {}"
      by (rule Suc.IH) (use Suc.prems Suc in simp)
    show ?thesis using disjoint by (auto simp: Suc)
  qed
qed

text \<open>
  Two branch positions are one exactly when their children and addresses are: injectivity and
  disjointness together, stated once so that a consumer comparing positions reads no layout.
\<close>
lemma syntax_branch_eq_iff [simp]: "syntax_branch i a = syntax_branch j b \<longleftrightarrow> i = j \<and> a = b"
proof
  assume same: "syntax_branch i a = syntax_branch j b"
  have "i = j"
  proof (rule ccontr)
    assume "i \<noteq> j"
    then have "range (syntax_branch i) \<inter> range (syntax_branch j) = {}" by (rule syntax_branch_disjoint)
    then show False using same by blast
  qed
  then show "i = j \<and> a = b" using same syntax_branch_injective[of j] by (simp add: inj_eq)
qed simp

text \<open>
  The contracts above are all that is read of the branch: its equations leave the simpset here, so no
  proof after them computes a position, and a change of the layout changes this theory alone.
\<close>
declare syntax_branch.simps [simp del]

section \<open>The forest is its children placed at their branches\<close>

text \<open>
  The syntax forest is the placed forest (@{text RRA_Placed_Forests}) at the family of the syntax
  branches, whose placements never meet (@{thm [source] syntax_branch_disjoint}); its positions are
  the placed positions at the same family. Formation and child reads are the notion's, discharged by
  the branch's contracts; what is stated here of the branch alone (its top prefix, the absent empty
  and other prefixes) is read through the placed forest's carrier member.
\<close>

definition syntax_forest_positions :: "local_address set list \<Rightarrow> local_address set" where
  "syntax_forest_positions As = placed_positions syntax_branch As"

lemma syntax_forest_positions_eq:
  "syntax_forest_positions As = (\<Union>i<length As. syntax_branch i ` (As!i))"
  by (simp add: syntax_forest_positions_def placed_positions_def)

lemma syntax_forest_position_member:
  "a \<in> syntax_forest_positions As \<longleftrightarrow>
    (\<exists>i<length As. \<exists>b\<in>As!i. a=syntax_branch i b)"
  by (simp add: syntax_forest_positions_def placed_positions_member)

lemma syntax_forest_positions_list:
  "\<Union>(set (map (\<lambda>i. syntax_branch i ` (As!i)) [0..<length As])) = syntax_forest_positions As"
  by (auto simp: syntax_forest_positions_eq)

lemma syntax_forest_three_positions:
  "syntax_forest_positions [A,B,C] =
    image (syntax_branch 0) A \<union> image (syntax_branch 1) B \<union> image (syntax_branch 2) C"
  by (auto simp: syntax_forest_positions_eq less_Suc_eq numeral_2_eq_2)

lemma syntax_forest_positions_disjoint:
  assumes len: "length As=length Bs" and separate: "\<forall>i<length As. As!i \<inter> Bs!i = {}"
  shows "syntax_forest_positions As \<inter> syntax_forest_positions Bs = {}"
proof (rule equals0I)
  fix a assume member: "a \<in> syntax_forest_positions As \<inter> syntax_forest_positions Bs"
  obtain i b where left: "i < length As" "b \<in> As!i" "a=syntax_branch i b"
    using member by (auto simp: syntax_forest_position_member)
  obtain j c where right: "j < length As" "c \<in> Bs!j" "a=syntax_branch j c"
    using member len by (auto simp: syntax_forest_position_member)
  show False
  proof (cases "i=j")
    case True
    have same: "b=c" using syntax_branch_injective[of i] left(3) right(3) True
      by (auto simp: inj_def)
    show False using separate left right True same by blast
  next
    case False
    have disjoint: "range (syntax_branch i) \<inter> range (syntax_branch j) = {}"
      by (rule syntax_branch_disjoint[OF False])
    show False using disjoint left(3) right(3) by blast
  qed
qed

text \<open>
  Each child is copied once, by its own branch: the forest's carrier is the positions of the
  children's carriers, its incidence and functional bindings are each child's pushed by its branch,
  and it holds no counted data. Nothing below reads the branch's equations; every fact follows from
  its contracts (injective, disjoint, formed, the top prefix and the prefix form).
\<close>

definition syntax_forest :: "exact_artifact list \<Rightarrow> exact_artifact" where
  "syntax_forest Rs = placed_forest syntax_branch Rs"

lemma syntax_forest_Nil: "syntax_forest [] = empty_artifact"
  by (simp add: syntax_forest_def)

lemma syntax_forest_carrier_member:
  "a \<in> rra_carrier (object_structure (syntax_forest Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b\<in>rra_carrier (object_structure (Rs!i)). a=syntax_branch i b)"
  by (simp only: syntax_forest_def placed_forest_carrier_member)

lemma syntax_forest_pushed:
  "rra_carrier (object_structure (syntax_forest Rs)) =
    (\<Union>i<length Rs. rra_carrier (object_structure (push_object (syntax_branch i) (Rs!i))))"
  "rra_incidence (object_structure (syntax_forest Rs)) =
    (\<Union>i<length Rs. rra_incidence (object_structure (push_object (syntax_branch i) (Rs!i))))"
  "functional_bindings (object_data (syntax_forest Rs)) =
    (\<Union>i<length Rs. functional_bindings (object_data (push_object (syntax_branch i) (Rs!i))))"
  by (simp_all add: syntax_forest_def placed_forest_def placed_positions_def push_object_def push_basis_def
      cong: SUP_cong_simp)

lemma syntax_forest_pieces_separate:
  assumes "a \<in> rra_carrier (object_structure (push_object (syntax_branch i) R))"
    and "a \<in> rra_carrier (object_structure (push_object (syntax_branch j) S))"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then have "range (syntax_branch i) \<inter> range (syntax_branch j) = {}" by (rule syntax_branch_disjoint)
  then show False using assms by (auto simp: push_object_def)
qed

lemma syntax_forest_piece_formed:
  assumes "exact_formed R"
  shows "exact_formed (push_object (syntax_branch i) R)"
  by (rule exact_push_formed[OF assms syntax_branch_addressing[OF assms]])

lemma syntax_forest_no_counts [simp]: "bag_count (object_data (syntax_forest Rs)) = (\<lambda>_. 0)"
  by (simp add: syntax_forest_def)

lemma syntax_forest_formed:
  assumes formed: "\<forall>R\<in>set Rs. exact_formed R"
  shows "exact_formed (syntax_forest Rs)"
  unfolding syntax_forest_def
proof (rule placed_forest_formed[OF formed])
  fix i assume index: "i < length Rs"
  have child: "exact_formed (Rs!i)" using formed nth_mem[OF index] by blast
  show "finite_addressing (rra_carrier (object_structure (Rs!i))) (syntax_branch i)"
    by (rule syntax_branch_addressing[OF child])
next
  fix i j a b
  assume "i < length Rs" "j < length Rs" "i \<noteq> j" "a \<in> rra_carrier (object_structure (Rs!i))"
    "b \<in> rra_carrier (object_structure (Rs!j))" "syntax_branch i a = syntax_branch j b"
  then show "silent_at (Rs!i) a \<and> silent_at (Rs!j) b" by simp
qed

lemma syntax_forest_empty_absent [simp]:
  "[] \<notin> rra_carrier (object_structure (syntax_forest Rs))"
proof
  assume "[] \<in> rra_carrier (object_structure (syntax_forest Rs))"
  then obtain i b where eq: "[] = syntax_branch i b" unfolding syntax_forest_carrier_member by blast
  obtain c where "syntax_branch i b = 2#c \<or> syntax_branch i b = 3#c" using syntax_branch_top_prefix by blast
  then show False using eq by auto
qed

lemma syntax_forest_prefix_absent [simp]:
  assumes "n \<noteq> 2" "n \<noteq> 3"
  shows "n#a \<notin> rra_carrier (object_structure (syntax_forest Rs))"
proof
  assume "n#a \<in> rra_carrier (object_structure (syntax_forest Rs))"
  then obtain i b where eq: "n#a = syntax_branch i b" unfolding syntax_forest_carrier_member by blast
  obtain c where "syntax_branch i b = 2#c \<or> syntax_branch i b = 3#c" using syntax_branch_top_prefix by blast
  then show False using eq assms by auto
qed

lemma syntax_forest_top_prefix:
  assumes "a \<in> rra_carrier (object_structure (syntax_forest Rs))"
  shows "\<exists>b. a=2#b \<or> a=3#b"
proof -
  obtain i b where eq: "a = syntax_branch i b" using assms unfolding syntax_forest_carrier_member by blast
  show ?thesis using syntax_branch_top_prefix[of i b] eq by blast
qed

lemma syntax_forest_child_inside:
  assumes index: "i < length Rs" and atom: "a \<in> rra_carrier (object_structure (Rs!i))"
  shows "syntax_branch i a \<in> rra_carrier (object_structure (syntax_forest Rs))"
  unfolding syntax_forest_carrier_member using index atom by blast

lemma syntax_forest_atom_origin:
  assumes "a \<in> rra_carrier (object_structure (syntax_forest Rs))"
  shows "\<exists>i<length Rs. \<exists>b\<in>rra_carrier (object_structure (Rs!i)). a=syntax_branch i b"
  using assms unfolding syntax_forest_carrier_member .

lemma syntax_forest_child_reads:
  assumes formed: "\<forall>R\<in>set Rs. exact_formed R"
    and counts: "\<forall>R\<in>set Rs. bag_count (object_data R) = (\<lambda>_. 0)"
    and index: "i < length Rs"
  shows "object_reads_agree (push_object (syntax_branch i) (Rs!i)) (syntax_forest Rs)
    (syntax_branch i ` rra_carrier (object_structure (Rs!i)))"
proof -
  have zero: "bag_count (object_data (Rs!i)) = (\<lambda>_. 0)" using counts nth_mem[OF index] by blast
  show ?thesis unfolding syntax_forest_def
    by (rule placed_forest_reads[OF index syntax_branch_injective zero subset_refl]) simp
qed

lemma syntax_forest_positions_bound:
  assumes len: "length As=length Rs"
    and bounds: "\<forall>i<length Rs. As!i \<subseteq> rra_carrier (object_structure (Rs!i))"
  shows "syntax_forest_positions As \<subseteq> rra_carrier (object_structure (syntax_forest Rs))"
proof
  fix a assume member: "a \<in> syntax_forest_positions As"
  obtain i b where index: "i < length Rs" "b \<in> As!i" "a=syntax_branch i b"
    using member len by (auto simp: syntax_forest_position_member)
  have inside: "b \<in> rra_carrier (object_structure (Rs!i))" using bounds index(1,2) by blast
  show "a \<in> rra_carrier (object_structure (syntax_forest Rs))"
    using syntax_forest_child_inside[OF index(1) inside] index(3) by simp
qed

lemma syntax_forest_carrier_partition:
  assumes alen: "length As=length Rs" and blen: "length Bs=length Rs"
    and cover: "\<forall>i<length Rs. rra_carrier (object_structure (Rs!i)) = As!i \<union> Bs!i"
  shows "rra_carrier (object_structure (syntax_forest Rs)) =
    syntax_forest_positions As \<union> syntax_forest_positions Bs"
proof
  show "rra_carrier (object_structure (syntax_forest Rs)) \<subseteq>
    syntax_forest_positions As \<union> syntax_forest_positions Bs"
  proof
    fix a assume member: "a \<in> rra_carrier (object_structure (syntax_forest Rs))"
    obtain i b where index: "i < length Rs" "b \<in> rra_carrier (object_structure (Rs!i))" "a=syntax_branch i b"
      using syntax_forest_atom_origin[OF member] by blast
    have inside: "b \<in> As!i \<union> Bs!i" using cover index(1,2) by blast
    show "a \<in> syntax_forest_positions As \<union> syntax_forest_positions Bs"
      using index(1,3) inside alen blen by (auto simp: syntax_forest_position_member)
  qed
  have left: "syntax_forest_positions As \<subseteq> rra_carrier (object_structure (syntax_forest Rs))"
    by (rule syntax_forest_positions_bound[OF alen]) (use cover in blast)
  have right: "syntax_forest_positions Bs \<subseteq> rra_carrier (object_structure (syntax_forest Rs))"
    by (rule syntax_forest_positions_bound[OF blen]) (use cover in blast)
  show "syntax_forest_positions As \<union> syntax_forest_positions Bs \<subseteq>
    rra_carrier (object_structure (syntax_forest Rs))" using left right by blast
qed

text \<open>
  Complete scopes are copied with every occurrence, including each private
  binder. The copies are disjoint and the forest adds no occurrence or
  constructor header. Every forest occurrence has a source child. The native
  syntax constructors have zero counted data; that condition is explicit when
  claiming complete child-read preservation. Arbitrary artifact values cited
  by the code retain both native data components.
\<close>

end
