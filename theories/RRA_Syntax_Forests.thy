theory RRA_Syntax_Forests
  imports RRA_Syntax_Construction
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

definition syntax_forest_positions :: "local_address set list \<Rightarrow> local_address set" where
  "syntax_forest_positions As = (\<Union>i<length As. syntax_branch i ` (As!i))"

lemma syntax_forest_position_member:
  "a \<in> syntax_forest_positions As \<longleftrightarrow>
    (\<exists>i<length As. \<exists>b\<in>As!i. a=syntax_branch i b)"
  by (auto simp: syntax_forest_positions_def)

lemma syntax_forest_positions_list:
  "\<Union>(set (map (\<lambda>i. syntax_branch i ` (As!i)) [0..<length As])) = syntax_forest_positions As"
  by (auto simp: syntax_forest_positions_def)

lemma syntax_forest_three_positions:
  "syntax_forest_positions [A,B,C] =
    image (syntax_branch 0) A \<union> image (syntax_branch 1) B \<union> image (syntax_branch 2) C"
  by (auto simp: syntax_forest_positions_def less_Suc_eq numeral_2_eq_2)

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
  "syntax_forest Rs =
    \<lparr>object_structure =
      \<lparr>rra_carrier = syntax_forest_positions (map (\<lambda>R. rra_carrier (object_structure R)) Rs),
       rra_incidence = (\<Union>i<length Rs. rra_incidence (push_structure (syntax_branch i) (object_structure (Rs!i))))\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0),
       functional_bindings = (\<Union>i<length Rs. (\<lambda>(a,v). (syntax_branch i a,v)) ` functional_bindings (object_data (Rs!i)))\<rparr>\<rparr>"

lemma syntax_forest_Nil: "syntax_forest [] = empty_artifact"
  by (simp add: syntax_forest_def syntax_forest_positions_def empty_artifact_def empty_basis_def)

lemma syntax_forest_carrier_member:
  "a \<in> rra_carrier (object_structure (syntax_forest Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b\<in>rra_carrier (object_structure (Rs!i)). a=syntax_branch i b)"
  by (simp add: syntax_forest_def syntax_forest_position_member cong: conj_cong)

lemma syntax_forest_pushed:
  "rra_carrier (object_structure (syntax_forest Rs)) =
    (\<Union>i<length Rs. rra_carrier (object_structure (push_object (syntax_branch i) (Rs!i))))"
  "rra_incidence (object_structure (syntax_forest Rs)) =
    (\<Union>i<length Rs. rra_incidence (object_structure (push_object (syntax_branch i) (Rs!i))))"
  "functional_bindings (object_data (syntax_forest Rs)) =
    (\<Union>i<length Rs. functional_bindings (object_data (push_object (syntax_branch i) (Rs!i))))"
  by (simp_all add: syntax_forest_def syntax_forest_positions_def push_object_def push_basis_def cong: SUP_cong_simp)

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
proof -
  let ?P = "\<lambda>i. push_object (syntax_branch i) (Rs!i)"
  let ?U = "rra_carrier (object_structure (syntax_forest Rs))"
  let ?F = "functional_bindings (object_data (syntax_forest Rs))"
  have piece: "exact_formed (?P i)" if index: "i < length Rs" for i
  proof -
    have child: "exact_formed (Rs!i)" using formed nth_mem[OF index] by blast
    show ?thesis by (rule syntax_forest_piece_formed[OF child])
  qed
  have piece_rra: "rra_formed (object_structure (?P i))" if "i < length Rs" for i
    using piece[OF that] unfolding exact_formed_def object_formed_def by blast
  have piece_basis: "basis_formed (rra_carrier (object_structure (?P i))) (object_data (?P i))"
    if "i < length Rs" for i
    using piece[OF that] unfolding exact_formed_def object_formed_def by blast
  have piece_addresses: "\<forall>a\<in>rra_carrier (object_structure (?P i)). octets_formed a" if "i < length Rs" for i
    using piece[OF that] unfolding exact_formed_def by blast
  have piece_values: "\<forall>v\<in>basis_values (object_data (?P i)). octets_formed v" if "i < length Rs" for i
    using piece[OF that] unfolding exact_formed_def by blast
  have finite_carrier: "finite ?U"
    unfolding syntax_forest_pushed
  proof (rule finite_UN_I[OF finite_lessThan])
    fix i assume "i \<in> {..<length Rs}"
    then have "i < length Rs" by (simp only: lessThan_iff)
    then show "finite (rra_carrier (object_structure (?P i)))" using piece_rra unfolding rra_formed_def by blast
  qed
  have finite_incidence: "finite (rra_incidence (object_structure (syntax_forest Rs)))"
    unfolding syntax_forest_pushed
  proof (rule finite_UN_I[OF finite_lessThan])
    fix i assume "i \<in> {..<length Rs}"
    then have "i < length Rs" by (simp only: lessThan_iff)
    then show "finite (rra_incidence (object_structure (?P i)))" using piece_rra unfolding rra_formed_def by blast
  qed
  have endpoints: "\<forall>r p x. (r,p,x) \<in> rra_incidence (object_structure (syntax_forest Rs)) \<longrightarrow>
      r \<in> ?U \<and> p \<in> ?U \<and> x \<in> ?U"
  proof (intro allI impI)
    fix r p x assume "(r,p,x) \<in> rra_incidence (object_structure (syntax_forest Rs))"
    then obtain i where i: "i < length Rs" "(r,p,x) \<in> rra_incidence (object_structure (?P i))"
      unfolding syntax_forest_pushed by blast
    have "r \<in> rra_carrier (object_structure (?P i)) \<and> p \<in> rra_carrier (object_structure (?P i)) \<and>
        x \<in> rra_carrier (object_structure (?P i))"
      using piece_rra[OF i(1)] i(2) unfolding rra_formed_def by blast
    then show "r \<in> ?U \<and> p \<in> ?U \<and> x \<in> ?U" using i(1) unfolding syntax_forest_pushed by blast
  qed
  have no_bag: "bag_support (object_data (syntax_forest Rs)) = {}"
    by (simp add: bag_support_def)
  have finite_bindings: "finite ?F"
    unfolding syntax_forest_pushed
  proof (rule finite_UN_I[OF finite_lessThan])
    fix i assume "i \<in> {..<length Rs}"
    then have "i < length Rs" by (simp only: lessThan_iff)
    then show "finite (functional_bindings (object_data (?P i)))"
      using piece_basis unfolding basis_formed_def by blast
  qed
  have origin: "\<exists>i<length Rs. (a,v) \<in> functional_bindings (object_data (?P i)) \<and>
      a \<in> rra_carrier (object_structure (?P i))" if entry: "(a,v) \<in> ?F" for a v
  proof -
    have "(a,v) \<in> (\<Union>i<length Rs. functional_bindings (object_data (?P i)))"
      using entry by (simp only: syntax_forest_pushed)
    then obtain i where member: "i \<in> {..<length Rs}" "(a,v) \<in> functional_bindings (object_data (?P i))"
      by (rule UN_E)
    have index: "i < length Rs" using member(1) by (simp only: lessThan_iff)
    have "a \<in> rra_carrier (object_structure (?P i))"
      by (rule functional_attachment_in_carrier[OF piece_basis[OF index] member(2)])
    then show ?thesis using index member(2) by blast
  qed
  have single: "single_valued ?F"
    unfolding single_valued_def
  proof (intro allI impI)
    fix a v w assume first: "(a,v) \<in> ?F" and second: "(a,w) \<in> ?F"
    obtain i where i: "i < length Rs" "(a,v) \<in> functional_bindings (object_data (?P i))"
      "a \<in> rra_carrier (object_structure (?P i))" using origin[OF first] by blast
    obtain j where j: "j < length Rs" "(a,w) \<in> functional_bindings (object_data (?P j))"
      "a \<in> rra_carrier (object_structure (?P j))" using origin[OF second] by blast
    have same: "i = j" by (rule syntax_forest_pieces_separate[OF i(3) j(3)])
    have sv: "single_valued (functional_bindings (object_data (?P i)))"
      using piece_basis[OF i(1)] unfolding basis_formed_def by blast
    show "v = w" by (rule single_valued_outputs[OF sv i(2)]) (use j(2) same in simp)
  qed
  have bindings_inside: "?F \<subseteq> ?U \<times> UNIV"
  proof
    fix z assume entry: "z \<in> ?F"
    obtain a v where z: "z=(a,v)" by (cases z)
    obtain i where i: "i < length Rs" "a \<in> rra_carrier (object_structure (?P i))"
      using origin[of a v] entry z by blast
    have "a \<in> ?U" using i unfolding syntax_forest_pushed by blast
    then show "z \<in> ?U \<times> UNIV" using z by simp
  qed
  have addresses: "\<forall>a\<in>?U. octets_formed a"
  proof
    fix a assume "a \<in> ?U"
    then obtain i where i: "i < length Rs" "a \<in> rra_carrier (object_structure (?P i))"
      unfolding syntax_forest_pushed by blast
    show "octets_formed a" using piece_addresses[OF i(1)] i(2) by blast
  qed
  have payloads: "\<forall>v\<in>basis_values (object_data (syntax_forest Rs)). octets_formed v"
  proof
    fix v assume "v \<in> basis_values (object_data (syntax_forest Rs))"
    then obtain a where entry: "(a,v) \<in> ?F" using no_bag by (auto simp: basis_values_def)
    obtain i where i: "i < length Rs" "(a,v) \<in> functional_bindings (object_data (?P i))"
      using origin[OF entry] by blast
    have "v \<in> basis_values (object_data (?P i))" using i(2) by (force simp: basis_values_def)
    then show "octets_formed v" using piece_values[OF i(1)] by blast
  qed
  have incidence_formed: "rra_formed (object_structure (syntax_forest Rs))"
    unfolding rra_formed_def using finite_carrier finite_incidence endpoints by blast
  have basis: "basis_formed ?U (object_data (syntax_forest Rs))"
    unfolding basis_formed_def using no_bag finite_bindings single bindings_inside by simp
  show ?thesis unfolding exact_formed_def object_formed_def using incidence_formed basis addresses payloads by blast
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
  let ?P = "\<lambda>j. push_object (syntax_branch j) (Rs!j)"
  let ?I = "syntax_branch i ` rra_carrier (object_structure (Rs!i))"
  have piece_formed: "object_formed (?P j)" if "j < length Rs" for j
  proof -
    have "exact_formed (Rs!j)" using formed nth_mem[OF that] by blast
    then show ?thesis using syntax_forest_piece_formed[of "Rs!j" j] unfolding exact_formed_def by blast
  qed
  have carrier: "rra_carrier (object_structure (?P i)) = ?I" by (simp add: push_object_def)
  have inside: "?I \<subseteq> rra_carrier (object_structure (syntax_forest Rs))"
    using syntax_forest_child_inside[OF index] by blast
  have headed: "\<forall>a\<in>?I. headed_incidence (object_structure (?P i)) a =
      headed_incidence (object_structure (syntax_forest Rs)) a"
  proof
    fix a assume a: "a \<in> ?I"
    show "headed_incidence (object_structure (?P i)) a = headed_incidence (object_structure (syntax_forest Rs)) a"
    proof
      show "headed_incidence (object_structure (?P i)) a \<subseteq> headed_incidence (object_structure (syntax_forest Rs)) a"
      proof (rule subrelI)
        fix p x assume "(p,x) \<in> headed_incidence (object_structure (?P i)) a"
        then have inc: "(a,p,x) \<in> rra_incidence (object_structure (?P i))" by simp
        have "(a,p,x) \<in> (\<Union>j<length Rs. rra_incidence (object_structure (?P j)))"
          by (rule UN_I[where B="\<lambda>j. rra_incidence (object_structure (?P j))", OF _ inc])
            (simp only: lessThan_iff index)
        then show "(p,x) \<in> headed_incidence (object_structure (syntax_forest Rs)) a"
          by (simp only: headed_incidence_member syntax_forest_pushed)
      qed
      show "headed_incidence (object_structure (syntax_forest Rs)) a \<subseteq> headed_incidence (object_structure (?P i)) a"
      proof (rule subrelI)
        fix p x assume "(p,x) \<in> headed_incidence (object_structure (syntax_forest Rs)) a"
        then have "(a,p,x) \<in> (\<Union>j<length Rs. rra_incidence (object_structure (?P j)))"
          by (simp only: headed_incidence_member syntax_forest_pushed)
        then obtain j where j0: "j \<in> {..<length Rs}" "(a,p,x) \<in> rra_incidence (object_structure (?P j))"
          by (rule UN_E)
        have j: "j < length Rs" "(a,p,x) \<in> rra_incidence (object_structure (?P j))"
          using j0 by (simp_all only: lessThan_iff)
        have "a \<in> rra_carrier (object_structure (?P j))"
          using piece_formed[OF j(1)] j(2) unfolding object_formed_def rra_formed_def by blast
        moreover have "a \<in> rra_carrier (object_structure (?P i))" using a carrier by simp
        ultimately have "j = i" by (rule syntax_forest_pieces_separate)
        then show "(p,x) \<in> headed_incidence (object_structure (?P i)) a" using j(2) by simp
      qed
    qed
  qed
  have zero: "bag_count (object_data (?P i)) = (\<lambda>_. 0)"
  proof -
    have child: "bag_count (object_data (Rs!i)) = (\<lambda>_. 0)" using counts nth_mem[OF index] by blast
    show ?thesis
      by (simp add: push_object_def push_basis_def pushed_count_def child fun_eq_iff split: prod.split)
  qed
  have data: "restrict_basis ?I (object_data (?P i)) = restrict_basis ?I (object_data (syntax_forest Rs))"
  proof (rule basis_identity[THEN iffD2], rule conjI)
    show "bag_count (restrict_basis ?I (object_data (?P i))) =
      bag_count (restrict_basis ?I (object_data (syntax_forest Rs)))"
    proof -
      have same: "bag_count (object_data (?P i)) = bag_count (object_data (syntax_forest Rs))"
        using zero by simp
      show ?thesis by (simp only: restrict_basis_def same) simp
    qed
    show "functional_bindings (restrict_basis ?I (object_data (?P i))) =
      functional_bindings (restrict_basis ?I (object_data (syntax_forest Rs)))"
    proof (simp only: functional_bindings_restrict, rule set_eqI, rule iffI)
      fix av assume "av \<in> {av \<in> functional_bindings (object_data (?P i)). fst av \<in> ?I}"
      then have entry: "av \<in> functional_bindings (object_data (?P i))" and key: "fst av \<in> ?I" by simp_all
      have "av \<in> (\<Union>j<length Rs. functional_bindings (object_data (?P j)))"
        by (rule UN_I[where B="\<lambda>j. functional_bindings (object_data (?P j))", OF _ entry])
          (simp only: lessThan_iff index)
      then show "av \<in> {av \<in> functional_bindings (object_data (syntax_forest Rs)). fst av \<in> ?I}"
        using key by (simp only: syntax_forest_pushed mem_Collect_eq simp_thms)
    next
      fix av assume member: "av \<in> {av \<in> functional_bindings (object_data (syntax_forest Rs)). fst av \<in> ?I}"
      have key: "fst av \<in> ?I" using member by simp
      have "av \<in> (\<Union>j<length Rs. functional_bindings (object_data (?P j)))"
        using member by (simp only: syntax_forest_pushed mem_Collect_eq)
      then obtain j where j0: "j \<in> {..<length Rs}" "av \<in> functional_bindings (object_data (?P j))"
        by (rule UN_E)
      have j: "j < length Rs" "av \<in> functional_bindings (object_data (?P j))" using j0 by (simp_all only: lessThan_iff)
      have "fst av \<in> rra_carrier (object_structure (?P j))"
        using piece_formed[OF j(1)] functional_attachment_in_carrier[of _ "object_data (?P j)" "fst av" "snd av"] j(2)
        by (simp add: object_formed_def)
      moreover have "fst av \<in> rra_carrier (object_structure (?P i))" using key carrier by simp
      ultimately have "j = i" by (rule syntax_forest_pieces_separate)
      then show "av \<in> {av \<in> functional_bindings (object_data (?P i)). fst av \<in> ?I}" using j(2) key by simp
    qed
  qed
  show ?thesis using carrier inside headed data by (simp add: object_reads_agree_def)
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
