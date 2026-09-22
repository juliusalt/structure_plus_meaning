theory Factor_Pattern_Forests
  imports Factor_Pattern_Encoding RRA_Bound_Forests RRA_Syntax_Forests
begin

section \<open>A child is placed at its branch, its binders fixed\<close>

text \<open>
  Bodies that share one declared scope are placed as the forest places its children: the i-th at
  the branch @{const syntax_branch} i, except its binder occurrences, which every body shares and
  which stay where they are, as @{const syntax_prefix} keeps them. Every fact below follows from the
  branch's contracts and the binder addresses' own facts; none reads the branch's equations.
\<close>

definition bound_branch :: "nat \<Rightarrow> local_address \<Rightarrow> local_address" where
  "bound_branch i a = (if a \<in> binder_addresses then a else syntax_branch i a)"

lemma bound_branch_code [code]:
  "bound_branch i a = (if a \<noteq> [] \<and> hd a = 6 then a else syntax_branch i a)"
  by (cases a) (auto simp: bound_branch_def binder_addresses_def)

lemma syntax_branch_not_binder [simp]: "syntax_branch i a \<notin> binder_addresses"
  using syntax_branch_top_prefix[of i a] by (auto simp: binder_addresses_def)

lemma syntax_branch_not_binder_cons [simp]: "syntax_branch i a \<noteq> 6#b" "6#b \<noteq> syntax_branch i a"
  using syntax_branch_top_prefix[of i a] by auto


lemma bound_branch_binder: "a \<in> binder_addresses \<Longrightarrow> bound_branch i a = a"
  by (simp add: bound_branch_def)

lemma bound_branch_other: "a \<notin> binder_addresses \<Longrightarrow> bound_branch i a = syntax_branch i a"
  by (simp add: bound_branch_def)

lemma bound_branch_root [simp]: "bound_branch i [] = syntax_branch i []"
  by (simp add: bound_branch_def binder_addresses_def image_iff)

lemma bound_branch_boundary: "bound_branch i a \<in> binder_addresses \<longleftrightarrow> a \<in> binder_addresses"
  by (simp add: bound_branch_def)

lemma bound_branch_injective: "inj (bound_branch i)"
proof (rule injI)
  fix a b assume same: "bound_branch i a = bound_branch i b"
  show "a = b"
  proof (cases "a \<in> binder_addresses"; cases "b \<in> binder_addresses")
    assume "a \<in> binder_addresses" "b \<in> binder_addresses"
    then show ?thesis using same by (simp add: bound_branch_def)
  next
    assume "a \<in> binder_addresses" "b \<notin> binder_addresses"
    then have "a = syntax_branch i b" using same by (simp add: bound_branch_def)
    then show ?thesis using \<open>a \<in> binder_addresses\<close> by simp
  next
    assume "a \<notin> binder_addresses" "b \<in> binder_addresses"
    then have "syntax_branch i a = b" using same by (simp add: bound_branch_def)
    then show ?thesis using \<open>b \<in> binder_addresses\<close> by (metis syntax_branch_not_binder)
  next
    assume "a \<notin> binder_addresses" "b \<notin> binder_addresses"
    then have "syntax_branch i a = syntax_branch i b" using same by (simp add: bound_branch_def)
    then show ?thesis by (rule injD[OF syntax_branch_injective])
  qed
qed

lemma bound_branch_overlap:
  assumes ij: "i \<noteq> j" and same: "bound_branch i a = bound_branch j b"
  shows "a = b \<and> a \<in> binder_addresses"
proof (cases "a \<in> binder_addresses")
  case True
  have "b \<in> binder_addresses"
    using True same bound_branch_boundary[of i a] bound_branch_boundary[of j b] by metis
  then show ?thesis using same True by (simp add: bound_branch_def)
next
  case False
  show ?thesis
  proof (cases "b \<in> binder_addresses")
    case True
    then have "syntax_branch i a = b" using same False by (simp add: bound_branch_def)
    then show ?thesis using True by (metis syntax_branch_not_binder)
  next
    case other: False
    then have "syntax_branch i a = syntax_branch j b" using same False by (simp add: bound_branch_def)
    then show ?thesis using ij by (simp add: syntax_branch_eq_iff)
  qed
qed

lemma bound_branch_image_outside:
  assumes "A \<inter> binder_addresses = {}"
  shows "bound_branch i ` A = syntax_branch i ` A"
proof (rule image_cong[OF refl])
  fix a assume "a \<in> A"
  then have "a \<notin> binder_addresses" using assms by blast
  then show "bound_branch i a = syntax_branch i a" by (rule bound_branch_other)
qed

lemma bound_branch_image_binders:
  assumes "A \<subseteq> binder_addresses"
  shows "bound_branch i ` A = A"
proof -
  have "bound_branch i ` A = id ` A"
  proof (rule image_cong[OF refl])
    fix a assume "a \<in> A"
    then show "bound_branch i a = id a" using assms by (auto simp: bound_branch_def)
  qed
  then show ?thesis by simp
qed

lemma bound_branch_addressing:
  assumes formed: "exact_formed R"
  shows "finite_addressing (rra_carrier (object_structure R)) (bound_branch i)"
proof -
  have branch: "finite_addressing (rra_carrier (object_structure R)) (syntax_branch i)"
    by (rule syntax_branch_addressing[OF formed])
  have addresses: "\<forall>a\<in>rra_carrier (object_structure R). octets_formed (bound_branch i a)"
    using branch formed by (auto simp: bound_branch_def finite_addressing_def exact_formed_def)
  have injective: "inj_on (bound_branch i) (rra_carrier (object_structure R))"
    by (rule inj_on_subset[OF bound_branch_injective subset_UNIV])
  show ?thesis using injective addresses by (simp add: finite_addressing_def)
qed

lemma renamed_pattern_bound_branch:
  assumes "binder_addressing (pattern_variables p) f"
  shows "rename_pattern (bound_branch i) (rename_pattern f p) = rename_pattern f p"
proof -
  have subset: "pattern_variables (rename_pattern f p) \<subseteq> binder_addresses"
    using assms by (simp add: binder_addressing_def rename_pattern_variables)
  show ?thesis by (rule rename_pattern_fixed) (use subset in \<open>auto simp: bound_branch_def\<close>)
qed

section \<open>The bound forest is its children placed at their branches\<close>

definition bound_forest :: "exact_artifact list \<Rightarrow> exact_artifact" where
  "bound_forest Rs =
    \<lparr>object_structure =
      \<lparr>rra_carrier = (\<Union>i<length Rs. bound_branch i ` rra_carrier (object_structure (Rs!i))),
       rra_incidence = (\<Union>i<length Rs. rra_incidence (push_structure (bound_branch i) (object_structure (Rs!i))))\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0),
       functional_bindings = (\<Union>i<length Rs. (\<lambda>(a,v). (bound_branch i a,v)) ` functional_bindings (object_data (Rs!i)))\<rparr>\<rparr>"

lemma bound_forest_Nil [simp]: "bound_forest [] = empty_artifact"
  by (simp add: bound_forest_def empty_artifact_def empty_basis_def)

lemma bound_forest_no_counts [simp]: "bag_count (object_data (bound_forest Rs)) = (\<lambda>_. 0)"
  by (simp add: bound_forest_def)

lemma bound_forest_carrier_member:
  "a \<in> rra_carrier (object_structure (bound_forest Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b\<in>rra_carrier (object_structure (Rs!i)). a = bound_branch i b)"
  by (auto simp: bound_forest_def)

lemma bound_forest_incidence_member:
  "(r,p,x) \<in> rra_incidence (object_structure (bound_forest Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = bound_branch i r' \<and> p = bound_branch i p' \<and> x = bound_branch i x')"
proof
  assume "(r,p,x) \<in> rra_incidence (object_structure (bound_forest Rs))"
  then show "\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = bound_branch i r' \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
    by (auto simp: bound_forest_def push_structure_def)
next
  assume "\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = bound_branch i r' \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
  then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
    and eqs: "r = bound_branch i r'" "p = bound_branch i p'" "x = bound_branch i x'" by blast
  have "(r,p,x) \<in> rra_incidence (push_structure (bound_branch i) (object_structure (Rs!i)))"
    unfolding push_structure_def eqs using edge by (auto intro: rev_image_eqI)
  then have "(r,p,x) \<in> (\<Union>i<length Rs. rra_incidence (push_structure (bound_branch i) (object_structure (Rs!i))))"
    using i by blast
  then show "(r,p,x) \<in> rra_incidence (object_structure (bound_forest Rs))" by (simp add: bound_forest_def)
qed

lemma bound_forest_binding_member:
  "(a,v) \<in> functional_bindings (object_data (bound_forest Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = bound_branch i b)"
proof
  assume "(a,v) \<in> functional_bindings (object_data (bound_forest Rs))"
  then show "\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = bound_branch i b"
    by (auto simp: bound_forest_def)
next
  assume "\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = bound_branch i b"
  then obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
    and ab: "a = bound_branch i b" by blast
  have "(a,v) \<in> (\<lambda>(a,v). (bound_branch i a,v)) ` functional_bindings (object_data (Rs!i))"
    unfolding ab using bv by (auto intro: rev_image_eqI)
  then have "(a,v) \<in> (\<Union>i<length Rs. (\<lambda>(a,v). (bound_branch i a,v)) ` functional_bindings (object_data (Rs!i)))"
    using i by blast
  then show "(a,v) \<in> functional_bindings (object_data (bound_forest Rs))" by (simp add: bound_forest_def)
qed

lemma bound_forest_silent:
  assumes silent: "\<forall>R\<in>set Rs. binder_silent R"
  shows "binder_silent (bound_forest Rs)"
proof -
  have child: "binder_silent (Rs!i)" if "i < length Rs" for i using silent nth_mem[OF that] by blast
  have heads: "\<forall>a\<in>binder_addresses. headed_incidence (object_structure (bound_forest Rs)) a = {}"
  proof (intro ballI equals0I)
    fix a y assume a: "a \<in> binder_addresses" and y: "y \<in> headed_incidence (object_structure (bound_forest Rs)) a"
    obtain p x where yp: "y = (p,x)" by (cases y)
    have "(a,p,x) \<in> rra_incidence (object_structure (bound_forest Rs))" using y by (simp add: yp headed_incidence_def)
    then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
      and at: "a = bound_branch i r'"
      unfolding bound_forest_incidence_member by blast
    have r: "r' \<in> binder_addresses" using a at bound_branch_boundary[of i r'] by metis
    have "(p',x') \<in> headed_incidence (object_structure (Rs!i)) r'" using edge by (simp add: headed_incidence_def)
    moreover have "headed_incidence (object_structure (Rs!i)) r' = {}"
      using child[OF i] r by (simp add: binder_silent_def)
    ultimately show False by simp
  qed
  have data: "restrict_basis binder_addresses (object_data (bound_forest Rs)) = empty_basis"
  proof (unfold empty_restriction_iff, intro ballI conjI allI)
    fix a v assume a: "a \<in> binder_addresses"
    show "bag_count (object_data (bound_forest Rs)) (a,v) = 0" by simp
    show "(a,v) \<notin> functional_bindings (object_data (bound_forest Rs))"
    proof
      assume "(a,v) \<in> functional_bindings (object_data (bound_forest Rs))"
      then obtain i b where i: "i < length Rs" and bind: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
        and at: "a = bound_branch i b"
        unfolding bound_forest_binding_member by blast
      have b: "b \<in> binder_addresses" using a at bound_branch_boundary[of i b] by metis
      have "restrict_basis binder_addresses (object_data (Rs!i)) = empty_basis"
        using child[OF i] by (simp add: binder_silent_def)
      then show False using b bind unfolding empty_restriction_iff by blast
    qed
  qed
  show ?thesis using heads data by (simp add: binder_silent_def)
qed

lemma bound_forest_formed:
  assumes formed: "\<forall>R\<in>set Rs. exact_formed R" and silent: "\<forall>R\<in>set Rs. binder_silent R"
  shows "exact_formed (bound_forest Rs)"
proof -
  let ?F = "bound_forest Rs"
  have child_formed: "exact_formed (Rs!i)" if "i < length Rs" for i using formed nth_mem[OF that] by blast
  have child_silent: "binder_silent (Rs!i)" if "i < length Rs" for i using silent nth_mem[OF that] by blast
  have child_object: "rra_formed (object_structure (Rs!i)) \<and>
      basis_formed (rra_carrier (object_structure (Rs!i))) (object_data (Rs!i))" if "i < length Rs" for i
    using child_formed[OF that] by (simp add: exact_formed_def object_formed_def)
  have cfin: "finite (rra_carrier (object_structure (Rs!i)))" if "i < length Rs" for i
    using child_object[OF that] by (simp add: rra_formed_def)
  have cinc: "finite (rra_incidence (object_structure (Rs!i)))" if "i < length Rs" for i
    using child_object[OF that] by (simp add: rra_formed_def)
  have cfun: "finite (functional_bindings (object_data (Rs!i)))" if "i < length Rs" for i
    using child_object[OF that] by (simp add: basis_formed_def)
  have csv: "single_valued (functional_bindings (object_data (Rs!i)))" if "i < length Rs" for i
    using child_object[OF that] by (simp add: basis_formed_def)
  have carrier: "finite (rra_carrier (object_structure ?F))"
    unfolding bound_forest_def by (auto simp: cfin intro!: finite_UN_I finite_imageI)
  have incidence: "finite (rra_incidence (object_structure ?F))"
    unfolding bound_forest_def by (auto simp: cinc push_structure_def intro!: finite_UN_I finite_imageI)
  have funsets: "finite (functional_bindings (object_data ?F))"
    unfolding bound_forest_def by (auto simp: cfun intro!: finite_UN_I finite_imageI)
  have ends: "\<forall>r p x. (r,p,x) \<in> rra_incidence (object_structure ?F) \<longrightarrow>
      r \<in> rra_carrier (object_structure ?F) \<and> p \<in> rra_carrier (object_structure ?F) \<and>
      x \<in> rra_carrier (object_structure ?F)"
  proof (intro allI impI)
    fix r p x assume "(r,p,x) \<in> rra_incidence (object_structure ?F)"
    then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
      and at: "r = bound_branch i r'" "p = bound_branch i p'" "x = bound_branch i x'"
      unfolding bound_forest_incidence_member by blast
    have inside: "r' \<in> rra_carrier (object_structure (Rs!i)) \<and> p' \<in> rra_carrier (object_structure (Rs!i)) \<and>
        x' \<in> rra_carrier (object_structure (Rs!i))"
      using child_object[OF i] edge by (auto simp: rra_formed_def)
    show "r \<in> rra_carrier (object_structure ?F) \<and> p \<in> rra_carrier (object_structure ?F) \<and>
        x \<in> rra_carrier (object_structure ?F)"
      unfolding bound_forest_carrier_member using i inside at by blast
  qed
  have sv: "single_valued (functional_bindings (object_data ?F))"
  proof (unfold single_valued_def, intro allI impI)
    fix a v w assume av: "(a,v) \<in> functional_bindings (object_data ?F)"
      and aw: "(a,w) \<in> functional_bindings (object_data ?F)"
    obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      and ab: "a = bound_branch i b"
      using av unfolding bound_forest_binding_member by blast
    obtain j c where j: "j < length Rs" and cw: "(c,w) \<in> functional_bindings (object_data (Rs!j))"
      and ac: "a = bound_branch j c"
      using aw unfolding bound_forest_binding_member by blast
    show "v = w"
    proof (cases "i = j")
      case True
      have "bound_branch i b = bound_branch i c" using ab ac True by simp
      then have "b = c" by (rule injD[OF bound_branch_injective])
      then show ?thesis using csv[OF i] bv cw True unfolding single_valued_def by blast
    next
      case False
      have "b = c \<and> b \<in> binder_addresses" using bound_branch_overlap[OF False, of b c] ab ac by metis
      then have "b \<in> binder_addresses" by (rule conjunct2)
      have "restrict_basis binder_addresses (object_data (Rs!i)) = empty_basis"
        using child_silent[OF i] by (simp add: binder_silent_def)
      then show ?thesis using \<open>b \<in> binder_addresses\<close> bv unfolding empty_restriction_iff by blast
    qed
  qed
  have within: "functional_bindings (object_data ?F) \<subseteq> rra_carrier (object_structure ?F) \<times> UNIV"
  proof
    fix y assume y: "y \<in> functional_bindings (object_data ?F)"
    obtain a v where yp: "y = (a,v)" by (cases y)
    obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      and ab: "a = bound_branch i b"
      using y unfolding yp bound_forest_binding_member by blast
    have "b \<in> rra_carrier (object_structure (Rs!i))" using child_object[OF i] bv by (auto simp: basis_formed_def)
    then show "y \<in> rra_carrier (object_structure ?F) \<times> UNIV"
      unfolding yp using i ab bound_forest_carrier_member by blast
  qed
  have addresses: "\<forall>a\<in>rra_carrier (object_structure ?F). octets_formed a"
  proof
    fix a assume "a \<in> rra_carrier (object_structure ?F)"
    then obtain i b where i: "i < length Rs" and b: "b \<in> rra_carrier (object_structure (Rs!i))"
      and ab: "a = bound_branch i b"
      unfolding bound_forest_carrier_member by blast
    show "octets_formed a" using bound_branch_addressing[OF child_formed[OF i], of i] b ab
      by (simp add: finite_addressing_def)
  qed
  have bags: "bag_support (object_data ?F) = {}" by (simp add: bag_support_def)
  have payloads: "\<forall>v\<in>basis_values (object_data ?F). octets_formed v"
  proof
    fix v assume "v \<in> basis_values (object_data ?F)"
    then obtain a where "(a,v) \<in> functional_bindings (object_data ?F)" by (auto simp: basis_values_def bags)
    then obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      unfolding bound_forest_binding_member by blast
    have "v \<in> basis_values (object_data (Rs!i))" using bv by (force simp: basis_values_def)
    then show "octets_formed v" using child_formed[OF i] by (simp add: exact_formed_def)
  qed
  show ?thesis unfolding exact_formed_def object_formed_def rra_formed_def basis_formed_def
    using carrier incidence funsets ends sv within addresses payloads by (simp add: bags)
qed

lemma bound_forest_reads:
  assumes i: "i < length Rs" and counts: "bag_count (object_data (Rs!i)) = (\<lambda>_. 0)"
    and inside: "A \<subseteq> rra_carrier (object_structure (Rs!i))" and outside: "A \<inter> binder_addresses = {}"
  shows "object_reads_agree (push_object (bound_branch i) (Rs!i)) (bound_forest Rs) (bound_branch i ` A)"
proof -
  let ?C = "Rs!i"
  let ?P = "push_object (bound_branch i) ?C"
  let ?F = "bound_forest Rs"
  have in_p: "bound_branch i ` A \<subseteq> rra_carrier (object_structure ?P)" using inside by (auto simp: push_object_def)
  have in_f: "bound_branch i ` A \<subseteq> rra_carrier (object_structure ?F)"
  proof
    fix y assume "y \<in> bound_branch i ` A"
    then obtain a where a: "a \<in> A" and y: "y = bound_branch i a" by blast
    show "y \<in> rra_carrier (object_structure ?F)"
      unfolding bound_forest_carrier_member using inside i a y by blast
  qed
  have other: "j = i \<and> r = a" if a: "a \<in> A" and same: "bound_branch i a = bound_branch j r" for a j r
  proof (cases "j = i")
    case True
    then have "bound_branch i a = bound_branch i r" using same by simp
    then have "a = r" by (rule injD[OF bound_branch_injective])
    then show ?thesis using True by simp
  next
    case False
    then have "a = r \<and> a \<in> binder_addresses" using bound_branch_overlap[of i j a r] same by metis
    then show ?thesis using a outside by blast
  qed
  have heads: "headed_incidence (object_structure ?P) (bound_branch i a) =
      headed_incidence (object_structure ?F) (bound_branch i a)" if a: "a \<in> A" for a
  proof (rule set_eqI)
    fix y :: "local_address \<times> local_address"
    obtain p x where yp: "y = (p,x)" by (cases y)
    have pushed: "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?P) \<longleftrightarrow>
        (\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x')"
    proof
      assume "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?P)"
      then obtain r' p' x' where edge: "(r',p',x') \<in> rra_incidence (object_structure ?C)"
        and eqs: "bound_branch i a = bound_branch i r'" "p = bound_branch i p'" "x = bound_branch i x'"
        by (auto simp: push_object_def push_structure_def)
      have "r' = a" using eqs(1) by (simp add: inj_eq[OF bound_branch_injective])
      then show "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
        using edge eqs by blast
    next
      assume "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
      then obtain p' x' where edge: "(a,p',x') \<in> rra_incidence (object_structure ?C)"
        and eqs: "p = bound_branch i p'" "x = bound_branch i x'" by blast
      show "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?P)"
        unfolding eqs using edge by (auto simp: push_object_def push_structure_def intro: rev_image_eqI)
    qed
    have forest: "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?F) \<longleftrightarrow>
        (\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x')"
    proof
      assume "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?F)"
      then obtain j r' p' x' where edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!j))"
        and s: "bound_branch i a = bound_branch j r'" and px: "p = bound_branch j p'" "x = bound_branch j x'"
        unfolding bound_forest_incidence_member by blast
      have ji: "j = i" "r' = a" using other[OF a s] by simp_all
      show "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
        using edge px ji by blast
    next
      assume "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = bound_branch i p' \<and> x = bound_branch i x'"
      then show "(bound_branch i a,p,x) \<in> rra_incidence (object_structure ?F)"
        unfolding bound_forest_incidence_member using i by blast
    qed
    show "y \<in> headed_incidence (object_structure ?P) (bound_branch i a) \<longleftrightarrow>
        y \<in> headed_incidence (object_structure ?F) (bound_branch i a)"
      using pushed forest by (simp add: yp headed_incidence_def)
  qed
  have bag: "bag_count (object_data ?P) = (\<lambda>_. 0)"
    by (rule ext) (simp add: push_object_def push_basis_def pushed_count_def counts split: prod.splits)
  have funsets: "{av \<in> functional_bindings (object_data ?P). fst av \<in> bound_branch i ` A} =
      {av \<in> functional_bindings (object_data ?F). fst av \<in> bound_branch i ` A}"
  proof (rule set_eqI, rule iffI)
    fix y assume y: "y \<in> {av \<in> functional_bindings (object_data ?P). fst av \<in> bound_branch i ` A}"
    obtain c v where yp: "y = (c,v)" by (cases y)
    obtain b where b: "(b,v) \<in> functional_bindings (object_data ?C)" and cb: "c = bound_branch i b"
      using y by (auto simp: yp push_object_def push_basis_def)
    show "y \<in> {av \<in> functional_bindings (object_data ?F). fst av \<in> bound_branch i ` A}"
      using y b cb i unfolding yp by (auto simp: bound_forest_binding_member)
  next
    fix y assume y: "y \<in> {av \<in> functional_bindings (object_data ?F). fst av \<in> bound_branch i ` A}"
    obtain c v where yp: "y = (c,v)" by (cases y)
    obtain a where a: "a \<in> A" and ca: "c = bound_branch i a" using y by (auto simp: yp)
    obtain j b where bv: "(b,v) \<in> functional_bindings (object_data (Rs!j))" and cb: "c = bound_branch j b"
      using y unfolding yp by (auto simp: bound_forest_binding_member)
    have s: "bound_branch i a = bound_branch j b" using ca cb by simp
    have ji: "j = i" "b = a" using other[OF a s] by simp_all
    show "y \<in> {av \<in> functional_bindings (object_data ?P). fst av \<in> bound_branch i ` A}"
      using bv ji ca a unfolding yp by (auto simp: push_object_def push_basis_def intro!: bexI[of _ "(a,v)"])
  qed
  have data: "restrict_basis (bound_branch i ` A) (object_data ?P) = restrict_basis (bound_branch i ` A) (object_data ?F)"
    by (simp add: restrict_basis_def bag funsets cong: if_cong)
  show ?thesis unfolding object_reads_agree_def using in_p in_f heads data by auto
qed

section \<open>Finite collections of bodies sharing one declared scope\<close>

definition pattern_forest_variables :: "'a term_pattern list \<Rightarrow> 'a set" where
  "pattern_forest_variables ps = (\<Union>p\<in>set ps. pattern_variables p)"

lemma pattern_forest_variables_simps [simp]:
  "pattern_forest_variables [] = {}"
  "pattern_forest_variables (p#ps) = pattern_variables p \<union> pattern_forest_variables ps"
  by (auto simp: pattern_forest_variables_def)

lemma pattern_forest_variables_finite [simp]: "finite (pattern_forest_variables ps)"
  by (simp add: pattern_forest_variables_def)

text \<open>
  The forest of the bodies' syntax places the i-th body at @{const bound_branch} i; its interior,
  its literal slots and its roots are the bodies' own, placed at the same branch.
\<close>

definition pattern_forest_syntax :: "('a \<Rightarrow> local_address) \<Rightarrow> 'a term_pattern list \<Rightarrow> exact_artifact" where
  "pattern_forest_syntax f ps = bound_forest (map (pattern_syntax f) ps)"

definition pattern_forest_interior :: "'a term_pattern list \<Rightarrow> local_address set" where
  "pattern_forest_interior ps = syntax_forest_positions (map pattern_syntax_interior ps)"

definition pattern_forest_bindings :: "'a term_pattern list \<Rightarrow> (local_address \<times> exact_artifact) set" where
  "pattern_forest_bindings ps =
    (\<Union>i<length ps. (\<lambda>(k,R). (syntax_branch i k,R)) ` pattern_literal_bindings (ps!i))"

definition pattern_forest_roots :: "'a list \<Rightarrow> local_address list" where
  "pattern_forest_roots ps = map (\<lambda>i. syntax_branch i []) [0..<length ps]"

lemma pattern_forest_Nil [simp]:
  "pattern_forest_syntax f [] = empty_artifact"
  "pattern_forest_interior [] = {}"
  "pattern_forest_bindings [] = {}"
  "pattern_forest_roots [] = []"
  by (simp_all add: pattern_forest_syntax_def pattern_forest_interior_def syntax_forest_positions_def
    pattern_forest_bindings_def pattern_forest_roots_def)

lemma pattern_forest_roots_map [simp]: "pattern_forest_roots (map f ps)=pattern_forest_roots ps"
  by (simp add: pattern_forest_roots_def)

lemma pattern_forest_roots_outside: "set (pattern_forest_roots ps)\<inter>binder_addresses={}"
  by (auto simp: pattern_forest_roots_def)

lemma pattern_forest_binding_member:
  "(a,R) \<in> pattern_forest_bindings ps \<longleftrightarrow>
    (\<exists>i<length ps. \<exists>k. (k,R) \<in> pattern_literal_bindings (ps!i) \<and> a = syntax_branch i k)"
proof
  assume "(a,R) \<in> pattern_forest_bindings ps"
  then show "\<exists>i<length ps. \<exists>k. (k,R) \<in> pattern_literal_bindings (ps!i) \<and> a = syntax_branch i k"
    by (auto simp: pattern_forest_bindings_def)
next
  assume "\<exists>i<length ps. \<exists>k. (k,R) \<in> pattern_literal_bindings (ps!i) \<and> a = syntax_branch i k"
  then obtain i k where i: "i < length ps" and kR: "(k,R) \<in> pattern_literal_bindings (ps!i)"
    and ak: "a = syntax_branch i k" by blast
  have "(a,R) \<in> (\<lambda>(k,R). (syntax_branch i k,R)) ` pattern_literal_bindings (ps!i)"
    unfolding ak using kR by (auto intro: rev_image_eqI)
  then show "(a,R) \<in> pattern_forest_bindings ps" unfolding pattern_forest_bindings_def using i by blast
qed

lemma pattern_forest_slots [simp]: "rel_dom (pattern_forest_bindings []) = {}"
  by (simp add: rel_dom_def)

lemma pattern_forest_slot_positions:
  "rel_dom (pattern_forest_bindings ps) =
    syntax_forest_positions (map (\<lambda>p. rel_dom (pattern_literal_bindings p)) ps)"
  unfolding syntax_forest_positions_def rel_dom_def
  by (auto simp: pattern_forest_binding_member)

lemma pattern_forest_heads:
  assumes "a \<in> pattern_forest_interior ps \<union> rel_dom (pattern_forest_bindings ps)"
  shows "\<exists>b. a = 2#b \<or> a = 3#b"
  using assms syntax_branch_top_prefix
  by (auto simp: pattern_forest_interior_def pattern_forest_slot_positions syntax_forest_position_member)

lemma pattern_forest_bindings_finite [simp]: "finite (pattern_forest_bindings ps)"
  unfolding pattern_forest_bindings_def
  by (auto simp: pattern_literal_bindings_finite intro!: finite_UN_I finite_imageI)

lemma pattern_forest_bindings_functional:
  "single_valued (pattern_forest_bindings ps)"
proof (unfold single_valued_def, intro allI impI)
  fix a R S assume aR: "(a,R) \<in> pattern_forest_bindings ps" and aS: "(a,S) \<in> pattern_forest_bindings ps"
  obtain i k where kR: "(k,R) \<in> pattern_literal_bindings (ps!i)" and ak: "a = syntax_branch i k"
    using aR unfolding pattern_forest_binding_member by blast
  obtain j l where lS: "(l,S) \<in> pattern_literal_bindings (ps!j)" and al: "a = syntax_branch j l"
    using aS unfolding pattern_forest_binding_member by blast
  have "i = j \<and> k = l" using ak al by (simp add: syntax_branch_eq_iff)
  then show "R = S"
    using pattern_literal_bindings_functional[of "ps!i"] kR lS unfolding single_valued_def by blast
qed

lemma pattern_forest_bindings_formed:
  assumes "\<forall>p\<in>set ps. pattern_formed p"
  shows "\<forall>k R. (k,R) \<in> pattern_forest_bindings ps \<longrightarrow> exact_formed R"
proof (intro allI impI)
  fix k R assume "(k,R) \<in> pattern_forest_bindings ps"
  then obtain i k' where i: "i < length ps" and kR: "(k',R) \<in> pattern_literal_bindings (ps!i)"
    unfolding pattern_forest_binding_member by blast
  have pf: "pattern_formed (ps!i)" using assms nth_mem[OF i] by blast
  show "exact_formed R" using pattern_literal_bindings_formed[OF pf] kR by blast
qed

lemma pattern_forest_interior_finite [simp]: "finite (pattern_forest_interior ps)"
  unfolding pattern_forest_interior_def syntax_forest_positions_def
  by (auto simp: pattern_syntax_interior_finite intro!: finite_UN_I finite_imageI)

lemma pattern_forest_interior_outside:
  "pattern_forest_interior ps \<inter> binder_addresses = {}"
  by (auto simp: pattern_forest_interior_def syntax_forest_position_member)

lemma pattern_forest_slots_outside:
  "rel_dom (pattern_forest_bindings ps) \<inter> binder_addresses = {}"
  by (auto simp: pattern_forest_slot_positions syntax_forest_position_member)

lemma pattern_forest_slot_boundary:
  "pattern_forest_interior ps \<inter> rel_dom (pattern_forest_bindings ps) = {}"
  unfolding pattern_forest_interior_def pattern_forest_slot_positions
  by (rule syntax_forest_positions_disjoint) (simp_all add: pattern_syntax_slot_boundary)

lemma pattern_forest_roots_inside:
  "set (pattern_forest_roots ps) \<subseteq> pattern_forest_interior ps"
proof
  fix a assume "a \<in> set (pattern_forest_roots ps)"
  then obtain i where i: "i < length ps" and a: "a = syntax_branch i []"
    by (auto simp: pattern_forest_roots_def)
  show "a \<in> pattern_forest_interior ps"
    unfolding pattern_forest_interior_def syntax_forest_position_member
    by (intro exI[of _ i] conjI bexI[of _ "[]"]) (use i a in simp_all)
qed

lemma pattern_forest_no_counts [simp]:
  "bag_count (object_data (pattern_forest_syntax f ps)) = (\<lambda>_. 0)"
  by (simp add: pattern_forest_syntax_def)

lemma pattern_forest_silent [simp]: "binder_silent (pattern_forest_syntax f ps)"
  unfolding pattern_forest_syntax_def by (rule bound_forest_silent) simp

lemma pattern_forest_formed:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "exact_formed (pattern_forest_syntax f ps)"
  unfolding pattern_forest_syntax_def
proof (rule bound_forest_formed)
  show "\<forall>R\<in>set (map (pattern_syntax f) ps). exact_formed R"
  proof
    fix R assume "R \<in> set (map (pattern_syntax f) ps)"
    then obtain p where p: "p \<in> set ps" and R: "R = pattern_syntax f p" by auto
    have paddr: "binder_addressing (pattern_variables p) f"
      by (rule binder_addressing_mono[OF addressing]) (use p in \<open>auto simp: pattern_forest_variables_def\<close>)
    have pf: "pattern_formed p" using formed p by blast
    show "exact_formed R" using pattern_syntax_formed[OF pf paddr] R by simp
  qed
  show "\<forall>R\<in>set (map (pattern_syntax f) ps). binder_silent R" by simp
qed

lemma pattern_forest_carrier:
  assumes addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "rra_carrier (object_structure (pattern_forest_syntax f ps)) =
    pattern_forest_interior ps \<union> rel_dom (pattern_forest_bindings ps) \<union> f ` pattern_forest_variables ps"
proof -
  have each: "bound_branch i ` rra_carrier (object_structure (pattern_syntax f (ps!i))) =
      syntax_branch i ` pattern_syntax_interior (ps!i) \<union>
      syntax_branch i ` rel_dom (pattern_literal_bindings (ps!i)) \<union> f ` pattern_variables (ps!i)"
    if i: "i < length ps" for i
  proof -
    have paddr: "binder_addressing (pattern_variables (ps!i)) f"
      by (rule binder_addressing_mono[OF addressing]) (use nth_mem[OF i] in \<open>auto simp: pattern_forest_variables_def\<close>)
    have pb: "f ` pattern_variables (ps!i) \<subseteq> binder_addresses" using paddr by (simp add: binder_addressing_def)
    show ?thesis
      by (simp only: pattern_syntax_carrier[OF paddr] image_Un
          bound_branch_image_outside[OF pattern_syntax_interior_outside]
          bound_branch_image_outside[OF pattern_literal_slots_outside]
          bound_branch_image_binders[OF pb])
  qed
  have vars0: "pattern_forest_variables ps = (\<Union>i<length ps. pattern_variables (ps!i))"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> pattern_forest_variables ps"
    then obtain p where p: "p \<in> set ps" and x: "x \<in> pattern_variables p" by (auto simp: pattern_forest_variables_def)
    then obtain i where i: "i < length ps" and pi: "ps!i = p" by (auto simp: in_set_conv_nth)
    show "x \<in> (\<Union>i<length ps. pattern_variables (ps!i))" using i pi x by blast
  next
    fix x assume "x \<in> (\<Union>i<length ps. pattern_variables (ps!i))"
    then obtain i where i: "i < length ps" and x: "x \<in> pattern_variables (ps!i)" by blast
    show "x \<in> pattern_forest_variables ps" using nth_mem[OF i] x by (auto simp: pattern_forest_variables_def)
  qed
  have vars: "f ` pattern_forest_variables ps = (\<Union>i<length ps. f ` pattern_variables (ps!i))"
    by (simp add: vars0 image_UN)
  have carrier: "rra_carrier (object_structure (pattern_forest_syntax f ps)) =
      (\<Union>i<length ps. bound_branch i ` rra_carrier (object_structure (pattern_syntax f (ps!i))))"
    by (simp add: pattern_forest_syntax_def bound_forest_def cong: SUP_cong_simp)
  show ?thesis
    by (simp add: carrier each vars pattern_forest_interior_def pattern_forest_slot_positions
        syntax_forest_positions_def UN_Un_distrib cong: SUP_cong_simp)
qed

definition pattern_forest_environment ::
  "('a \<Rightarrow> local_address) \<Rightarrow> 'a term_pattern list \<Rightarrow> local_address option artifact_environment" where
  "pattern_forest_environment f ps = literal_environment (pattern_forest_syntax f ps) (pattern_forest_bindings ps)"

lemma pattern_forest_environment_formed:
  assumes "\<forall>p\<in>set ps. pattern_formed p" "binder_addressing (pattern_forest_variables ps) f"
  shows "environment_formed (pattern_forest_environment f ps)"
  unfolding pattern_forest_environment_def
  by (rule literal_environment_formed[OF pattern_forest_formed[OF assms]
        pattern_forest_bindings_finite pattern_forest_bindings_functional
        pattern_forest_bindings_formed[OF assms(1)]])
     (auto simp: pattern_forest_carrier[OF assms(2)])

lemma pattern_forest_environment_source [simp]:
  "artifact_at (pattern_forest_environment f ps) None (pattern_forest_syntax f ps)"
  by (simp add: pattern_forest_environment_def)

lemma pattern_forest_environment_slots [simp]:
  "external_slot_values (pattern_forest_environment f ps) None k = {R. (k,R) \<in> pattern_forest_bindings ps}"
  by (simp add: pattern_forest_environment_def)

lemma pattern_forest_child_slots:
  assumes i: "i < length ps"
  shows "external_slot_values (pattern_forest_environment f ps) None (syntax_branch i k) =
      external_slot_values (pattern_environment f (ps!i)) None k"
proof -
  have "(syntax_branch i k,R) \<in> pattern_forest_bindings ps \<longleftrightarrow> (k,R) \<in> pattern_literal_bindings (ps!i)" for R
    unfolding pattern_forest_binding_member using i by (auto simp: syntax_branch_eq_iff)
  then show ?thesis by simp
qed

lemma pattern_forest_roots_prefix:
  "map (syntax_prefix n) (pattern_forest_roots ps) = map (Cons n) (pattern_forest_roots ps)"
proof (rule map_cong[OF refl])
  fix a assume member: "a \<in> set (pattern_forest_roots ps)"
  have outside: "a \<notin> binder_addresses"
    using pattern_forest_roots_outside[of ps] member by blast
  show "syntax_prefix n a = n#a" using outside by (simp add: syntax_prefix_def)
qed

lemma pattern_forest_renamed_prefix:
  assumes addressing: "binder_addressing (pattern_forest_variables ps) f"
  shows "map (rename_pattern (syntax_prefix n)) (map (rename_pattern f) ps) = map (rename_pattern f) ps"
proof -
  have each: "\<And>p. p \<in> set ps \<Longrightarrow>
    rename_pattern (syntax_prefix n) (rename_pattern f p) = rename_pattern f p"
  proof -
    fix p assume member: "p \<in> set ps"
    have paddr: "binder_addressing (pattern_variables p) f"
      by (rule binder_addressing_mono[OF addressing])
         (use member in \<open>auto simp: pattern_forest_variables_def\<close>)
    show "rename_pattern (syntax_prefix n) (rename_pattern f p) = rename_pattern f p"
      by (rule renamed_pattern_prefix[OF paddr])
  qed
  show ?thesis by (simp only: map_map) (rule map_cong[OF refl], use each in simp)
qed

theorem pattern_forest_recovers:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
    and scope: "f ` pattern_forest_variables ps \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
  shows "pattern_vector_at (pattern_forest_environment f ps) None V (pattern_forest_roots ps)
    (map (rename_pattern f) ps) (pattern_forest_interior ps) (rel_dom (pattern_forest_bindings ps))"
proof -
  let ?E = "pattern_forest_environment f ps"
  let ?R = "pattern_forest_syntax f ps"
  let ?I = "\<lambda>i. syntax_branch i ` pattern_syntax_interior (ps!i)"
  let ?K = "\<lambda>i. syntax_branch i ` rel_dom (pattern_literal_bindings (ps!i))"
  have ef: "environment_formed ?E" by (rule pattern_forest_environment_formed[OF formed addressing])
  have art: "artifact_at ?E None ?R" by simp
  have child_formed: "pattern_formed (ps!i)" if "i < length ps" for i using formed nth_mem[OF that] by blast
  have child_addr: "binder_addressing (pattern_variables (ps!i)) f" if "i < length ps" for i
    by (rule binder_addressing_mono[OF addressing]) (use nth_mem[OF that] in \<open>auto simp: pattern_forest_variables_def\<close>)
  have child_scope: "f ` pattern_variables (ps!i) \<subseteq> V" if "i < length ps" for i
    using scope nth_mem[OF that] by (auto simp: pattern_forest_variables_def)
  have child: "pattern_quoted_at ?E None V (syntax_branch i []) (rename_pattern f (ps!i)) (?I i) (?K i)"
    if i: "i < length ps" for i
  proof -
    let ?C = "pattern_syntax f (ps!i)"
    have cf: "exact_formed ?C" by (rule pattern_syntax_formed[OF child_formed[OF i] child_addr[OF i]])
    have source: "pattern_quoted_at (pattern_environment f (ps!i)) None V [] (rename_pattern f (ps!i))
      (pattern_syntax_interior (ps!i)) (rel_dom (pattern_literal_bindings (ps!i)))"
      by (rule pattern_syntax_recovers[OF child_formed[OF i] child_addr[OF i] child_scope[OF i] boundary])
    have inside: "pattern_syntax_interior (ps!i) \<subseteq> rra_carrier (object_structure ?C)"
      by (auto simp: pattern_syntax_carrier[OF child_addr[OF i]])
    have reads: "object_reads_agree (push_object (bound_branch i) ?C) ?R
      (bound_branch i ` pattern_syntax_interior (ps!i))"
      using bound_forest_reads[of i "map (pattern_syntax f) ps" "pattern_syntax_interior (ps!i)"]
        i inside pattern_syntax_interior_outside[of "ps!i"]
      by (simp add: pattern_forest_syntax_def pattern_syntax_no_counts)
    have slots: "\<forall>k\<in>rel_dom (pattern_literal_bindings (ps!i)).
      external_slot_values (pattern_environment f (ps!i)) None k = external_slot_values ?E None (bound_branch i k)"
    proof (intro ballI)
      fix k assume member: "k \<in> rel_dom (pattern_literal_bindings (ps!i))"
      have outside: "k \<notin> binder_addresses" using pattern_literal_slots_outside[of "ps!i"] member by blast
      show "external_slot_values (pattern_environment f (ps!i)) None k = external_slot_values ?E None (bound_branch i k)"
        using pattern_forest_child_slots[OF i, of f k] by (simp add: bound_branch_other[OF outside])
    qed
    have copied: "pattern_quoted_at ?E None (bound_branch i ` V) (bound_branch i [])
      (rename_pattern (bound_branch i) (rename_pattern f (ps!i)))
      (bound_branch i ` pattern_syntax_interior (ps!i)) (bound_branch i ` rel_dom (pattern_literal_bindings (ps!i)))"
      by (rule pattern_quotation_transport[OF source pattern_environment_source bound_branch_addressing[OF cf]
            reads slots bound_branch_injective ef art])
    show ?thesis
      using copied by (simp only: bound_branch_image_binders[OF boundary] bound_branch_root
        renamed_pattern_bound_branch[OF child_addr[OF i]]
        bound_branch_image_outside[OF pattern_syntax_interior_outside]
        bound_branch_image_outside[OF pattern_literal_slots_outside])
  qed
  have interior_slot: "a \<notin> rel_dom (pattern_literal_bindings p)" if "a \<in> pattern_syntax_interior p" for a p
    using pattern_syntax_slot_boundary[of p] that by blast
  have vector: "pattern_vector_at ?E None V (map (\<lambda>i. syntax_branch i []) js)
      (map (\<lambda>i. rename_pattern f (ps!i)) js) (\<Union>i\<in>set js. ?I i) (\<Union>i\<in>set js. ?K i)"
    if "set js \<subseteq> {..<length ps}" "distinct js" for js
    using that
  proof (induction js)
    case Nil
    show ?case using pattern_vector_at.empty[OF ef, of None V] by simp
  next
    case (Cons j js)
    have j: "j < length ps" and tail: "set js \<subseteq> {..<length ps}" and fresh: "j \<notin> set js"
      and dist: "distinct js" using Cons.prems by auto
    have separate: "?I j \<inter> (\<Union>i\<in>set js. ?I i) = {}" using fresh by (auto simp: syntax_branch_eq_iff)
    have apart: "(?I j \<union> (\<Union>i\<in>set js. ?I i)) \<inter> (?K j \<union> (\<Union>i\<in>set js. ?K i)) = {}"
      by (auto simp: syntax_branch_eq_iff interior_slot)
    show ?case using pattern_vector_at.cons[OF child[OF j] Cons.IH[OF tail dist] separate apart] by simp
  qed
  have all: "pattern_vector_at ?E None V (map (\<lambda>i. syntax_branch i []) [0..<length ps])
      (map (\<lambda>i. rename_pattern f (ps!i)) [0..<length ps])
      (\<Union>i\<in>set [0..<length ps]. ?I i) (\<Union>i\<in>set [0..<length ps]. ?K i)"
    by (rule vector) (simp_all add: atLeast0LessThan)
  have roots: "map (\<lambda>i. syntax_branch i []) [0..<length ps] = pattern_forest_roots ps"
    by (simp add: pattern_forest_roots_def)
  have patterns: "map (\<lambda>i. rename_pattern f (ps!i)) [0..<length ps] = map (rename_pattern f) ps"
    by (rule nth_equalityI) simp_all
  have interior: "(\<Union>i\<in>set [0..<length ps]. ?I i) = pattern_forest_interior ps"
    by (simp add: pattern_forest_interior_def syntax_forest_positions_def atLeast0LessThan cong: SUP_cong_simp)
  have slots: "(\<Union>i\<in>set [0..<length ps]. ?K i) = rel_dom (pattern_forest_bindings ps)"
    by (simp add: pattern_forest_slot_positions syntax_forest_positions_def atLeast0LessThan cong: SUP_cong_simp)
  show ?thesis using all by (simp only: roots patterns interior slots)
qed

text \<open>
  All bodies share exactly their declared binder occurrences. The construction
  contributes no intermediate pair headers: the i-th body stands at the i-th branch,
  as every child of a forest does, and its binders stay fixed. Every occurrence belongs
  to a recovered body, an external literal slot, or a referenced binder. It works
  for every finite list, including the empty list, with unchanged literal values.
\<close>

end
