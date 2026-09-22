theory RRA_Placed_Forests
  imports RRA_Syntax_Construction RRA_Finite_Artifacts
begin

section \<open>A forest over a family of placements\<close>

text \<open>
  A forest places each of its children at its own placement: the i-th child's carrier, incidence and
  functional bindings are pushed by @{text "g i"}, and the forest holds no counted data. Its positions
  and its reference table are placed by the same family. Nothing here reads a placement's equations:
  formation, reads and silence follow from each placement being an injective formed addressing of
  its child and from two placements meeting only at positions silent in both children.
\<close>

definition placed_positions :: "(nat \<Rightarrow> local_address \<Rightarrow> local_address) \<Rightarrow> local_address set list \<Rightarrow> local_address set" where
  "placed_positions g As = (\<Union>i<length As. g i ` (As!i))"

definition placed_forest :: "(nat \<Rightarrow> local_address \<Rightarrow> local_address) \<Rightarrow> exact_artifact list \<Rightarrow> exact_artifact" where
  "placed_forest g Rs =
    \<lparr>object_structure =
      \<lparr>rra_carrier = placed_positions g (map (\<lambda>R. rra_carrier (object_structure R)) Rs),
       rra_incidence = (\<Union>i<length Rs. rra_incidence (push_structure (g i) (object_structure (Rs!i))))\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0),
       functional_bindings = (\<Union>i<length Rs. (\<lambda>(a,v). (g i a,v)) ` functional_bindings (object_data (Rs!i)))\<rparr>\<rparr>"

definition placed_table :: "(nat \<Rightarrow> local_address \<Rightarrow> local_address) \<Rightarrow> (local_address \<times> 'a) set list \<Rightarrow> (local_address \<times> 'a) set" where
  "placed_table g Ms = (\<Union>i<length Ms. (\<lambda>(k,v). (g i k,v)) ` (Ms!i))"

lemma placed_positions_member:
  "a \<in> placed_positions g As \<longleftrightarrow> (\<exists>i<length As. \<exists>b\<in>As!i. a = g i b)"
  by (auto simp: placed_positions_def)

lemma placed_positions_Nil [simp]: "placed_positions g [] = {}"
  by (simp add: placed_positions_def)

lemma placed_table_member:
  "(a,v) \<in> placed_table g Ms \<longleftrightarrow> (\<exists>i<length Ms. \<exists>k. (k,v) \<in> Ms!i \<and> a = g i k)"
proof
  assume "(a,v) \<in> placed_table g Ms"
  then show "\<exists>i<length Ms. \<exists>k. (k,v) \<in> Ms!i \<and> a = g i k" by (auto simp: placed_table_def)
next
  assume "\<exists>i<length Ms. \<exists>k. (k,v) \<in> Ms!i \<and> a = g i k"
  then obtain i k where i: "i < length Ms" and kv: "(k,v) \<in> Ms!i" and ak: "a = g i k" by blast
  have "(a,v) \<in> (\<lambda>(k,v). (g i k,v)) ` (Ms!i)" unfolding ak using kv by (auto intro: rev_image_eqI)
  then show "(a,v) \<in> placed_table g Ms" unfolding placed_table_def using i by blast
qed

lemma placed_table_Nil [simp]: "placed_table g [] = {}"
  by (simp add: placed_table_def)

lemma placed_positions_child:
  assumes "i < length As" "b \<in> As!i"
  shows "g i b \<in> placed_positions g As"
  unfolding placed_positions_member using assms by blast

lemma placed_table_child:
  assumes "i < length Ms" "(k,v) \<in> Ms!i"
  shows "(g i k,v) \<in> placed_table g Ms"
  unfolding placed_table_member using assms by blast

lemma placed_positions_map_member:
  "a \<in> placed_positions g (map F xs) \<longleftrightarrow> (\<exists>i<length xs. \<exists>b\<in>F (xs!i). a = g i b)"
proof
  assume "a \<in> placed_positions g (map F xs)"
  then obtain i b where i: "i < length (map F xs)" and b: "b \<in> map F xs ! i" and ab: "a = g i b"
    unfolding placed_positions_member by blast
  have i': "i < length xs" using i by simp
  have b': "b \<in> F (xs!i)" using b i' by simp
  show "\<exists>i<length xs. \<exists>b\<in>F (xs!i). a = g i b" using i' b' ab by blast
next
  assume "\<exists>i<length xs. \<exists>b\<in>F (xs!i). a = g i b"
  then obtain i b where i': "i < length xs" and b': "b \<in> F (xs!i)" and ab: "a = g i b" by blast
  show "a \<in> placed_positions g (map F xs)" unfolding ab by (rule placed_positions_child) (use i' b' in simp_all)
qed

lemma placed_table_domain: "rel_dom (placed_table g Ms) = placed_positions g (map rel_dom Ms)"
proof (rule set_eqI, rule iffI)
  fix a assume "a \<in> rel_dom (placed_table g Ms)"
  then obtain v i k where i: "i < length Ms" and kv: "(k,v) \<in> Ms!i" and a: "a = g i k"
    unfolding rel_dom_def placed_table_member by blast
  have i': "i < length (map rel_dom Ms)" using i by simp
  have k: "k \<in> map rel_dom Ms ! i" using i kv by (auto simp: rel_dom_def)
  show "a \<in> placed_positions g (map rel_dom Ms)" unfolding a by (rule placed_positions_child[OF i' k])
next
  fix a assume "a \<in> placed_positions g (map rel_dom Ms)"
  then obtain i b where i: "i < length (map rel_dom Ms)" and b: "b \<in> map rel_dom Ms ! i" and a: "a = g i b"
    unfolding placed_positions_member by blast
  have i': "i < length Ms" using i by simp
  obtain v where bv: "(b,v) \<in> Ms!i" using b i' by (auto simp: rel_dom_def)
  have "(a,v) \<in> placed_table g Ms" unfolding a by (rule placed_table_child[OF i' bv])
  then show "a \<in> rel_dom (placed_table g Ms)" by (rule rel_domI)
qed

lemma placed_table_values:
  "map_relation_values h (placed_table g Ms) = placed_table g (map (map_relation_values h) Ms)"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> map_relation_values h (placed_table g Ms)"
  then obtain a v where x: "x = (a,h v)" and av: "(a,v) \<in> placed_table g Ms"
    by (auto simp: map_relation_values_def)
  obtain i k where i: "i < length Ms" and kv: "(k,v) \<in> Ms!i" and a: "a = g i k"
    using av unfolding placed_table_member by blast
  have i': "i < length (map (map_relation_values h) Ms)" using i by simp
  have kh: "(k,h v) \<in> map (map_relation_values h) Ms ! i" using i kv by auto
  show "x \<in> placed_table g (map (map_relation_values h) Ms)" unfolding x a by (rule placed_table_child[OF i' kh])
next
  fix x assume member: "x \<in> placed_table g (map (map_relation_values h) Ms)"
  obtain a w where x: "x = (a,w)" by (cases x)
  obtain i k where i: "i < length (map (map_relation_values h) Ms)"
    and kw: "(k,w) \<in> map (map_relation_values h) Ms ! i" and a: "a = g i k"
    using member unfolding x placed_table_member by blast
  have i': "i < length Ms" using i by simp
  obtain v where kv: "(k,v) \<in> Ms!i" and w: "w = h v" using kw i' by auto
  have "(a,v) \<in> placed_table g Ms" unfolding a by (rule placed_table_child[OF i' kv])
  then show "x \<in> map_relation_values h (placed_table g Ms)" unfolding x w by auto
qed

lemma placed_table_finite:
  assumes "\<And>i. i < length Ms \<Longrightarrow> finite (Ms!i)"
  shows "finite (placed_table g Ms)"
  unfolding placed_table_def using assms by (auto intro!: finite_UN_I finite_imageI)

lemma placed_forest_Nil [simp]: "placed_forest g [] = empty_artifact"
  by (simp add: placed_forest_def empty_artifact_def empty_basis_def)

lemma placed_forest_no_counts [simp]: "bag_count (object_data (placed_forest g Rs)) = (\<lambda>_. 0)"
  by (simp add: placed_forest_def)

lemma placed_forest_carrier_member:
  "a \<in> rra_carrier (object_structure (placed_forest g Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b\<in>rra_carrier (object_structure (Rs!i)). a = g i b)"
  by (auto simp: placed_forest_def placed_positions_def)

lemma placed_forest_incidence_member:
  "(r,p,x) \<in> rra_incidence (object_structure (placed_forest g Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = g i r' \<and> p = g i p' \<and> x = g i x')"
proof
  assume "(r,p,x) \<in> rra_incidence (object_structure (placed_forest g Rs))"
  then show "\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = g i r' \<and> p = g i p' \<and> x = g i x'"
    by (auto simp: placed_forest_def push_structure_def)
next
  assume "\<exists>i<length Rs. \<exists>r' p' x'. (r',p',x') \<in> rra_incidence (object_structure (Rs!i)) \<and>
      r = g i r' \<and> p = g i p' \<and> x = g i x'"
  then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
    and eqs: "r = g i r'" "p = g i p'" "x = g i x'" by blast
  have "(r,p,x) \<in> rra_incidence (push_structure (g i) (object_structure (Rs!i)))"
    unfolding eqs by (rule push_structure_incidence_member[OF edge])
  then have "(r,p,x) \<in> (\<Union>i<length Rs. rra_incidence (push_structure (g i) (object_structure (Rs!i))))"
    using i by blast
  then show "(r,p,x) \<in> rra_incidence (object_structure (placed_forest g Rs))" by (simp add: placed_forest_def)
qed

lemma placed_forest_binding_member:
  "(a,v) \<in> functional_bindings (object_data (placed_forest g Rs)) \<longleftrightarrow>
    (\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = g i b)"
proof
  assume "(a,v) \<in> functional_bindings (object_data (placed_forest g Rs))"
  then show "\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = g i b"
    by (auto simp: placed_forest_def)
next
  assume "\<exists>i<length Rs. \<exists>b. (b,v) \<in> functional_bindings (object_data (Rs!i)) \<and> a = g i b"
  then obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
    and ab: "a = g i b" by blast
  have "(a,v) \<in> (\<lambda>(a,v). (g i a,v)) ` functional_bindings (object_data (Rs!i))"
    unfolding ab using bv by (auto intro: rev_image_eqI)
  then have "(a,v) \<in> (\<Union>i<length Rs. (\<lambda>(a,v). (g i a,v)) ` functional_bindings (object_data (Rs!i)))"
    using i by blast
  then show "(a,v) \<in> functional_bindings (object_data (placed_forest g Rs))" by (simp add: placed_forest_def)
qed

section \<open>Silence at a position\<close>

text \<open>
  A position of an artifact is silent when no incidence is headed there and no data is attached there.
  Two placements may meet only at such positions.
\<close>

definition silent_at :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> bool" where
  "silent_at R a \<longleftrightarrow> headed_incidence (object_structure R) a = {} \<and> restrict_basis {a} (object_data R) = empty_basis"

lemma silent_at_iff:
  "silent_at R a \<longleftrightarrow> (\<forall>p x. (a,p,x) \<notin> rra_incidence (object_structure R)) \<and>
    (\<forall>v. bag_count (object_data R) (a,v) = 0) \<and> (\<forall>v. (a,v) \<notin> functional_bindings (object_data R))"
  by (auto simp: silent_at_def headed_incidence_def empty_restriction_iff)

lemma silent_on_iff:
  "(\<forall>a\<in>A. silent_at R a) \<longleftrightarrow>
    (\<forall>a\<in>A. headed_incidence (object_structure R) a = {}) \<and> restrict_basis A (object_data R) = empty_basis"
  by (auto simp: silent_at_def empty_restriction_iff)

theorem placed_forest_silent:
  assumes silent: "\<And>i a. i < length Rs \<Longrightarrow> g i a = c \<Longrightarrow> silent_at (Rs!i) a"
  shows "silent_at (placed_forest g Rs) c"
  unfolding silent_at_iff
proof (intro conjI allI)
  fix p x show "(c,p,x) \<notin> rra_incidence (object_structure (placed_forest g Rs))"
  proof
    assume "(c,p,x) \<in> rra_incidence (object_structure (placed_forest g Rs))"
    then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
      and at: "c = g i r'"
      unfolding placed_forest_incidence_member by blast
    show False using silent[OF i at[symmetric]] edge unfolding silent_at_iff by blast
  qed
next
  fix v show "bag_count (object_data (placed_forest g Rs)) (c,v) = 0" by simp
next
  fix v show "(c,v) \<notin> functional_bindings (object_data (placed_forest g Rs))"
  proof
    assume "(c,v) \<in> functional_bindings (object_data (placed_forest g Rs))"
    then obtain i b where i: "i < length Rs" and bind: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      and at: "c = g i b"
      unfolding placed_forest_binding_member by blast
    show False using silent[OF i at[symmetric]] bind unfolding silent_at_iff by blast
  qed
qed

text \<open>
  Where two objects are both silent, they read alike; a push by an injective placement is silent at
  the image of every position its object is silent at.
\<close>

lemma silent_reads_agree:
  assumes inside: "I \<subseteq> rra_carrier (object_structure R)" "I \<subseteq> rra_carrier (object_structure S)"
    and silent: "\<forall>a\<in>I. silent_at R a" "\<forall>a\<in>I. silent_at S a"
  shows "object_reads_agree R S I"
  using silent_on_iff[of I R] silent_on_iff[of I S] inside silent unfolding object_reads_agree_def by simp

lemma push_silent_at:
  assumes injective: "inj g" and counts: "bag_count (object_data R) = (\<lambda>_. 0)" and silent: "silent_at R a"
  shows "silent_at (push_object g R) (g a)"
  unfolding silent_at_iff
proof (intro conjI allI)
  fix p x show "(g a,p,x) \<notin> rra_incidence (object_structure (push_object g R))"
  proof
    assume "(g a,p,x) \<in> rra_incidence (object_structure (push_object g R))"
    then obtain r' p' x' where edge: "(r',p',x') \<in> rra_incidence (object_structure R)" and at: "g a = g r'"
      by (auto simp: push_object_def push_structure_def)
    have "r' = a" using at by (simp add: inj_eq[OF injective])
    then show False using edge silent unfolding silent_at_iff by blast
  qed
next
  fix v show "bag_count (object_data (push_object g R)) (g a,v) = 0"
    by (simp add: push_object_def push_basis_def pushed_count_def counts)
next
  fix v show "(g a,v) \<notin> functional_bindings (object_data (push_object g R))"
  proof
    assume "(g a,v) \<in> functional_bindings (object_data (push_object g R))"
    then obtain b where bv: "(b,v) \<in> functional_bindings (object_data R)" and at: "g a = g b"
      by (auto simp: push_object_def push_basis_def)
    have "b = a" using at by (simp add: inj_eq[OF injective])
    then show False using bv silent unfolding silent_at_iff by blast
  qed
qed

section \<open>Formation\<close>

theorem placed_forest_formed:
  assumes formed: "\<forall>R\<in>set Rs. exact_formed R"
    and addressing: "\<And>i. i < length Rs \<Longrightarrow> finite_addressing (rra_carrier (object_structure (Rs!i))) (g i)"
    and meeting: "\<And>i j a b. i < length Rs \<Longrightarrow> j < length Rs \<Longrightarrow> i \<noteq> j \<Longrightarrow>
      a \<in> rra_carrier (object_structure (Rs!i)) \<Longrightarrow> b \<in> rra_carrier (object_structure (Rs!j)) \<Longrightarrow>
      g i a = g j b \<Longrightarrow> silent_at (Rs!i) a \<and> silent_at (Rs!j) b"
  shows "exact_formed (placed_forest g Rs)"
proof -
  let ?F = "placed_forest g Rs"
  have child_formed: "exact_formed (Rs!i)" if "i < length Rs" for i using formed nth_mem[OF that] by blast
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
  have cin: "b \<in> rra_carrier (object_structure (Rs!i))"
    if "i < length Rs" "(b,v) \<in> functional_bindings (object_data (Rs!i))" for i b v
    using child_object[OF that(1)] that(2) by (auto simp: basis_formed_def)
  have carrier: "finite (rra_carrier (object_structure ?F))"
    unfolding placed_forest_def placed_positions_def by (auto simp: cfin intro!: finite_UN_I finite_imageI)
  have incidence: "finite (rra_incidence (object_structure ?F))"
    unfolding placed_forest_def by (auto simp: cinc push_structure_def intro!: finite_UN_I finite_imageI)
  have funsets: "finite (functional_bindings (object_data ?F))"
    unfolding placed_forest_def by (auto simp: cfun intro!: finite_UN_I finite_imageI)
  have ends: "\<forall>r p x. (r,p,x) \<in> rra_incidence (object_structure ?F) \<longrightarrow>
      r \<in> rra_carrier (object_structure ?F) \<and> p \<in> rra_carrier (object_structure ?F) \<and>
      x \<in> rra_carrier (object_structure ?F)"
  proof (intro allI impI)
    fix r p x assume "(r,p,x) \<in> rra_incidence (object_structure ?F)"
    then obtain i r' p' x' where i: "i < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!i))"
      and at: "r = g i r'" "p = g i p'" "x = g i x'"
      unfolding placed_forest_incidence_member by blast
    have inside: "r' \<in> rra_carrier (object_structure (Rs!i)) \<and> p' \<in> rra_carrier (object_structure (Rs!i)) \<and>
        x' \<in> rra_carrier (object_structure (Rs!i))"
      using child_object[OF i] edge by (auto simp: rra_formed_def)
    show "r \<in> rra_carrier (object_structure ?F) \<and> p \<in> rra_carrier (object_structure ?F) \<and>
        x \<in> rra_carrier (object_structure ?F)"
      unfolding placed_forest_carrier_member using i inside at by blast
  qed
  have sv: "single_valued (functional_bindings (object_data ?F))"
  proof (unfold single_valued_def, intro allI impI)
    fix a v w assume av: "(a,v) \<in> functional_bindings (object_data ?F)"
      and aw: "(a,w) \<in> functional_bindings (object_data ?F)"
    obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      and ab: "a = g i b"
      using av unfolding placed_forest_binding_member by blast
    obtain j c where j: "j < length Rs" and cw: "(c,w) \<in> functional_bindings (object_data (Rs!j))"
      and ac: "a = g j c"
      using aw unfolding placed_forest_binding_member by blast
    show "v = w"
    proof (cases "i = j")
      case True
      have "g i b = g i c" using ab ac True by simp
      then have "b = c"
        using addressing[OF i] cin[OF i bv] cin[OF j cw] True unfolding finite_addressing_def inj_on_def by blast
      then show ?thesis using csv[OF i] bv cw True unfolding single_valued_def by blast
    next
      case False
      have "silent_at (Rs!i) b" using meeting[OF i j False cin[OF i bv] cin[OF j cw]] ab ac by simp
      then show ?thesis using bv unfolding silent_at_iff by blast
    qed
  qed
  have within: "functional_bindings (object_data ?F) \<subseteq> rra_carrier (object_structure ?F) \<times> UNIV"
  proof
    fix y assume y: "y \<in> functional_bindings (object_data ?F)"
    obtain a v where yp: "y = (a,v)" by (cases y)
    obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      and ab: "a = g i b"
      using y unfolding yp placed_forest_binding_member by blast
    show "y \<in> rra_carrier (object_structure ?F) \<times> UNIV"
      unfolding yp using i ab cin[OF i bv] placed_forest_carrier_member by blast
  qed
  have addresses: "\<forall>a\<in>rra_carrier (object_structure ?F). octets_formed a"
  proof
    fix a assume "a \<in> rra_carrier (object_structure ?F)"
    then obtain i b where i: "i < length Rs" and b: "b \<in> rra_carrier (object_structure (Rs!i))"
      and ab: "a = g i b"
      unfolding placed_forest_carrier_member by blast
    show "octets_formed a" using addressing[OF i] b ab by (simp add: finite_addressing_def)
  qed
  have bags: "bag_support (object_data ?F) = {}" by (simp add: bag_support_def)
  have payloads: "\<forall>v\<in>basis_values (object_data ?F). octets_formed v"
  proof
    fix v assume "v \<in> basis_values (object_data ?F)"
    then obtain a where "(a,v) \<in> functional_bindings (object_data ?F)" by (auto simp: basis_values_def bags)
    then obtain i b where i: "i < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!i))"
      unfolding placed_forest_binding_member by blast
    have "v \<in> basis_values (object_data (Rs!i))" using bv by (force simp: basis_values_def)
    then show "octets_formed v" using child_formed[OF i] by (simp add: exact_formed_def)
  qed
  show ?thesis unfolding exact_formed_def object_formed_def rra_formed_def basis_formed_def
    using carrier incidence funsets ends sv within addresses payloads by (simp add: bags)
qed

section \<open>Reads of a child where no other placement meets it\<close>

theorem placed_forest_reads:
  assumes i: "i < length Rs" and injective: "inj (g i)" and counts: "bag_count (object_data (Rs!i)) = (\<lambda>_. 0)"
    and inside: "A \<subseteq> rra_carrier (object_structure (Rs!i))"
    and apart: "\<And>a j b. a \<in> A \<Longrightarrow> j < length Rs \<Longrightarrow> j \<noteq> i \<Longrightarrow> g i a \<noteq> g j b"
  shows "object_reads_agree (push_object (g i) (Rs!i)) (placed_forest g Rs) (g i ` A)"
proof -
  let ?C = "Rs!i"
  let ?P = "push_object (g i) ?C"
  let ?F = "placed_forest g Rs"
  have in_p: "g i ` A \<subseteq> rra_carrier (object_structure ?P)" using inside by (auto simp: push_object_def)
  have in_f: "g i ` A \<subseteq> rra_carrier (object_structure ?F)"
  proof
    fix y assume "y \<in> g i ` A"
    then obtain a where a: "a \<in> A" and y: "y = g i a" by blast
    show "y \<in> rra_carrier (object_structure ?F)"
      unfolding placed_forest_carrier_member using inside i a y by blast
  qed
  have other: "j = i \<and> r = a" if a: "a \<in> A" and j: "j < length Rs" and same: "g i a = g j r" for a j r
  proof (cases "j = i")
    case True
    then have "g i a = g i r" using same by simp
    then have "a = r" by (rule injD[OF injective])
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using apart[OF a j False] same by blast
  qed
  have heads: "headed_incidence (object_structure ?P) (g i a) =
      headed_incidence (object_structure ?F) (g i a)" if a: "a \<in> A" for a
  proof (rule set_eqI)
    fix y :: "local_address \<times> local_address"
    obtain p x where yp: "y = (p,x)" by (cases y)
    have pushed: "(g i a,p,x) \<in> rra_incidence (object_structure ?P) \<longleftrightarrow>
        (\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x')"
    proof
      assume "(g i a,p,x) \<in> rra_incidence (object_structure ?P)"
      then obtain r' p' x' where edge: "(r',p',x') \<in> rra_incidence (object_structure ?C)"
        and eqs: "g i a = g i r'" "p = g i p'" "x = g i x'"
        by (auto simp: push_object_def push_structure_def)
      have "r' = a" using eqs(1) by (simp add: inj_eq[OF injective])
      then show "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x'"
        using edge eqs by blast
    next
      assume "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x'"
      then obtain p' x' where edge: "(a,p',x') \<in> rra_incidence (object_structure ?C)"
        and eqs: "p = g i p'" "x = g i x'" by blast
      show "(g i a,p,x) \<in> rra_incidence (object_structure ?P)"
        unfolding eqs using edge by (auto simp: push_object_def push_structure_def intro: rev_image_eqI)
    qed
    have forest: "(g i a,p,x) \<in> rra_incidence (object_structure ?F) \<longleftrightarrow>
        (\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x')"
    proof
      assume "(g i a,p,x) \<in> rra_incidence (object_structure ?F)"
      then obtain j r' p' x' where j: "j < length Rs" and edge: "(r',p',x') \<in> rra_incidence (object_structure (Rs!j))"
        and s: "g i a = g j r'" and px: "p = g j p'" "x = g j x'"
        unfolding placed_forest_incidence_member by blast
      have ji: "j = i" "r' = a" using other[OF a j s] by simp_all
      show "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x'"
        using edge px ji by blast
    next
      assume "\<exists>p' x'. (a,p',x') \<in> rra_incidence (object_structure ?C) \<and> p = g i p' \<and> x = g i x'"
      then show "(g i a,p,x) \<in> rra_incidence (object_structure ?F)"
        unfolding placed_forest_incidence_member using i by blast
    qed
    show "y \<in> headed_incidence (object_structure ?P) (g i a) \<longleftrightarrow>
        y \<in> headed_incidence (object_structure ?F) (g i a)"
      using pushed forest by (simp add: yp headed_incidence_def)
  qed
  have bag: "bag_count (object_data ?P) = (\<lambda>_. 0)"
    by (rule ext) (simp add: push_object_def push_basis_def pushed_count_def counts split: prod.splits)
  have funsets: "{av \<in> functional_bindings (object_data ?P). fst av \<in> g i ` A} =
      {av \<in> functional_bindings (object_data ?F). fst av \<in> g i ` A}"
  proof (rule set_eqI, rule iffI)
    fix y assume y: "y \<in> {av \<in> functional_bindings (object_data ?P). fst av \<in> g i ` A}"
    obtain c v where yp: "y = (c,v)" by (cases y)
    obtain b where b: "(b,v) \<in> functional_bindings (object_data ?C)" and cb: "c = g i b"
      using y by (auto simp: yp push_object_def push_basis_def)
    show "y \<in> {av \<in> functional_bindings (object_data ?F). fst av \<in> g i ` A}"
      using y b cb i unfolding yp by (auto simp: placed_forest_binding_member)
  next
    fix y assume y: "y \<in> {av \<in> functional_bindings (object_data ?F). fst av \<in> g i ` A}"
    obtain c v where yp: "y = (c,v)" by (cases y)
    obtain a where a: "a \<in> A" and ca: "c = g i a" using y by (auto simp: yp)
    obtain j b where j: "j < length Rs" and bv: "(b,v) \<in> functional_bindings (object_data (Rs!j))" and cb: "c = g j b"
      using y unfolding yp by (auto simp: placed_forest_binding_member)
    have s: "g i a = g j b" using ca cb by simp
    have ji: "j = i" "b = a" using other[OF a j s] by simp_all
    show "y \<in> {av \<in> functional_bindings (object_data ?P). fst av \<in> g i ` A}"
      using bv ji ca a unfolding yp by (auto simp: push_object_def push_basis_def intro!: bexI[of _ "(a,v)"])
  qed
  have data: "restrict_basis (g i ` A) (object_data ?P) = restrict_basis (g i ` A) (object_data ?F)"
    by (simp add: restrict_basis_def bag funsets cong: if_cong)
  show ?thesis unfolding object_reads_agree_def using in_p in_f heads data by auto
qed

section \<open>The executable forest and table\<close>

text \<open>
  The executable forms place each child by the same family; their one code equation reads each child
  with its index through the list of indexed children, never by an index into the list.
\<close>

definition finite_placed_forest :: "(nat \<Rightarrow> local_address \<Rightarrow> local_address) \<Rightarrow> finite_exact_artifact list \<Rightarrow> finite_exact_artifact" where
  "finite_placed_forest g Rs=(let ns=[0..<length Rs] in \<lparr>finite_structure=\<lparr>
    finite_carrier=ffUnion (fset_of_list (map (\<lambda>i.
      fimage (g i) (finite_carrier (finite_structure (Rs!i)))) ns)),
    finite_incidence=ffUnion (fset_of_list (map (\<lambda>i.
      fimage (\<lambda>(a,p,x). (g i a,g i p,g i x))
        (finite_incidence (finite_structure (Rs!i)))) ns))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=ffUnion (fset_of_list (map (\<lambda>i.
      fimage (\<lambda>(a,v). (g i a,v)) (finite_bindings (finite_data (Rs!i)))) ns))\<rparr>\<rparr>)"

lemma decode_finite_placed_forest [simp]:
  "decode_finite_object (finite_placed_forest g Rs)=placed_forest g (map decode_finite_object Rs)"
  by (simp add: finite_placed_forest_def Let_def decode_finite_object_def decode_finite_structure_def
    decode_finite_basis_def placed_forest_def placed_positions_def push_structure_def
    fimage.rep_eq ffUnion.rep_eq fset_of_list.rep_eq image_image atLeast0LessThan fun_eq_iff
    cong: SUP_cong_simp)

definition finite_placed_table :: "(nat \<Rightarrow> local_address \<Rightarrow> local_address) \<Rightarrow> (local_address\<times>'a) fset list \<Rightarrow> (local_address\<times>'a) fset" where
  "finite_placed_table g Ms=ffUnion (fset_of_list
    (map (\<lambda>i. fimage (\<lambda>(k,v). (g i k,v)) (Ms!i)) [0..<length Ms]))"

lemma finite_placed_table_exact [simp]:
  "fset (finite_placed_table g Ms)=placed_table g (map fset Ms)"
  by (simp add: finite_placed_table_def placed_table_def ffUnion.rep_eq fset_of_list.rep_eq fimage.rep_eq
    image_image atLeast0LessThan cong: SUP_cong_simp)

lemma map_indexed_children: "map (\<lambda>(i,R). f i R) (zip [0..<length Rs] Rs) = map (\<lambda>i. f i (Rs!i)) [0..<length Rs]"
  by (rule nth_equalityI) simp_all

lemma finite_placed_forest_code [code]:
  "finite_placed_forest g Rs=(let rows=zip [0..<length Rs] Rs in \<lparr>finite_structure=\<lparr>
    finite_carrier=ffUnion (fset_of_list (map (\<lambda>(i,R).
      fimage (g i) (finite_carrier (finite_structure R))) rows)),
    finite_incidence=ffUnion (fset_of_list (map (\<lambda>(i,R).
      fimage (\<lambda>(a,p,x). (g i a,g i p,g i x)) (finite_incidence (finite_structure R))) rows))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=ffUnion (fset_of_list (map (\<lambda>(i,R).
      fimage (\<lambda>(a,v). (g i a,v)) (finite_bindings (finite_data R))) rows))\<rparr>\<rparr>)"
  by (simp only: finite_placed_forest_def map_indexed_children Let_def)

lemma finite_placed_table_code [code]:
  "finite_placed_table g Ms=ffUnion (fset_of_list
    (map (\<lambda>(i,M). fimage (\<lambda>(k,v). (g i k,v)) M) (zip [0..<length Ms] Ms)))"
  by (simp only: finite_placed_table_def map_indexed_children)

end
