theory Factor_Premise_Forests
  imports Factor_Premise_Construction
begin

section \<open>Mixed finite bodies retain their own roots and reference slots\<close>

definition template_list_variables :: "('a,'u) premise_template list \<Rightarrow> 'a set" where
  "template_list_variables ts = (\<Union>t\<in>set ts. template_variables t)"

lemma template_list_variables_simps [simp]:
  "template_list_variables [] = {}"
  "template_list_variables (t#ts) = template_variables t \<union> template_list_variables ts"
  by (auto simp: template_list_variables_def)

lemma template_list_addressing:
  assumes addressing: "binder_addressing (template_list_variables ts) f" and member: "t \<in> set ts"
  shows "binder_addressing (template_variables t) f"
  by (rule binder_addressing_mono[OF addressing]) (use member in \<open>auto simp: template_list_variables_def\<close>)

text \<open>
  The premise forest places its i-th premise through the forest's placement: the template's syntax at
  @{const bound_branch} i, its binders fixed, and its interior and its literal and callee slots at
  @{const syntax_branch} i, where the forest places them, since they avoid the binders.
\<close>

definition premise_forest_syntax :: "('a \<Rightarrow> local_address) \<Rightarrow> ('a,'u) premise_template list \<Rightarrow> exact_artifact" where
  "premise_forest_syntax f ts = bound_forest (map (template_syntax f) ts)"

definition premise_forest_interior :: "('a,'u) premise_template list \<Rightarrow> local_address set" where
  "premise_forest_interior ts = placed_positions syntax_branch (map template_interior ts)"

definition premise_forest_literals :: "('a,'u) premise_template list \<Rightarrow> (local_address \<times> exact_artifact) set" where
  "premise_forest_literals ts = placed_table syntax_branch (map template_literals ts)"

definition premise_forest_callees :: "('a,'u) premise_template list \<Rightarrow> (local_address \<times> 'u definition_site) set" where
  "premise_forest_callees ts = placed_table syntax_branch (map template_callees ts)"

lemma premise_forest_Nil [simp]:
  "premise_forest_syntax f [] = empty_artifact"
  "premise_forest_interior [] = {}"
  "premise_forest_literals [] = {}"
  "premise_forest_callees [] = {}"
  by (simp_all add: premise_forest_syntax_def premise_forest_interior_def premise_forest_literals_def
    premise_forest_callees_def)

lemma premise_forest_no_counts [simp]:
  "bag_count (object_data (premise_forest_syntax f ts)) = (\<lambda>_. 0)"
  by (simp add: premise_forest_syntax_def)

lemma premise_forest_silent [simp]: "binder_silent (premise_forest_syntax f ts)"
  unfolding premise_forest_syntax_def by (rule bound_forest_silent) (auto simp: template_syntax_properties)

lemma premise_forest_interior_outside:
  "premise_forest_interior ts \<inter> binder_addresses = {}"
  by (auto simp: premise_forest_interior_def placed_positions_member)

lemma premise_forest_reference_slots_outside:
  "(rel_dom (premise_forest_literals ts) \<union> rel_dom (premise_forest_callees ts)) \<inter> binder_addresses = {}"
  by (auto simp: premise_forest_literals_def premise_forest_callees_def placed_table_domain placed_positions_member)

lemma premise_forest_formed:
  assumes formed: "\<forall>t\<in>set ts. template_formed t"
    and addressing: "binder_addressing (template_list_variables ts) f"
  shows "exact_formed (premise_forest_syntax f ts)"
proof -
  have children: "\<forall>R\<in>set (map (template_syntax f) ts). exact_formed R"
  proof
    fix R assume "R \<in> set (map (template_syntax f) ts)"
    then obtain t where t: "t \<in> set ts" and R: "R = template_syntax f t" by auto
    show "exact_formed R" unfolding R
      by (rule template_syntax_formed[OF _ template_list_addressing[OF addressing t]]) (use formed t in blast)
  qed
  show ?thesis unfolding premise_forest_syntax_def
    by (rule bound_forest_formed[OF children]) (auto simp: template_syntax_properties)
qed

lemma premise_forest_carrier:
  assumes addressing: "binder_addressing (template_list_variables ts) f"
  shows "rra_carrier (object_structure (premise_forest_syntax f ts)) =
    premise_forest_interior ts \<union> rel_dom (premise_forest_literals ts) \<union>
      rel_dom (premise_forest_callees ts) \<union> f ` template_list_variables ts"
proof -
  have child: "rra_carrier (object_structure (template_syntax f (ts!i))) =
      template_interior (ts!i) \<union> rel_dom (template_literals (ts!i)) \<union> rel_dom (template_callees (ts!i)) \<union>
        f ` template_variables (ts!i)" if "i < length ts" for i
    by (rule template_syntax_carrier[OF template_list_addressing[OF addressing nth_mem[OF that]]])
  have branch: "bound_branch i b = syntax_branch i b"
    if "b \<in> template_interior t \<union> rel_dom (template_literals t) \<union> rel_dom (template_callees t)" for i b t
    using that template_interior_outside[of t] template_reference_slots_outside[of t] by (auto intro!: bound_branch_other)
  have fixed: "bound_branch i (f x) = f x" if "x \<in> template_list_variables ts" for i x
    using that addressing by (intro bound_branch_binder) (auto simp: binder_addressing_def)
  have placed: "a \<in> rra_carrier (object_structure (premise_forest_syntax f ts))"
    if i: "i < length ts" and b: "b \<in> rra_carrier (object_structure (template_syntax f (ts!i)))"
      and ab: "a = bound_branch i b" for a i b
  proof -
    have i': "i < length (map (template_syntax f) ts)" using i by simp
    have b': "b \<in> rra_carrier (object_structure (map (template_syntax f) ts ! i))" using i b by simp
    show ?thesis unfolding premise_forest_syntax_def bound_forest_carrier_member using i' b' ab by blast
  qed
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix a assume "a \<in> rra_carrier (object_structure (premise_forest_syntax f ts))"
    then obtain i b where i: "i < length ts" and b: "b \<in> rra_carrier (object_structure (template_syntax f (ts!i)))"
      and a: "a = bound_branch i b"
      by (auto simp: premise_forest_syntax_def bound_forest_carrier_member)
    have member: "ts!i \<in> set ts" by (rule nth_mem[OF i])
    show "a \<in> premise_forest_interior ts \<union> rel_dom (premise_forest_literals ts) \<union>
      rel_dom (premise_forest_callees ts) \<union> f ` template_list_variables ts"
    proof (cases "b \<in> f ` template_variables (ts!i)")
      case True
      then obtain x where x: "x \<in> template_variables (ts!i)" and bx: "b = f x" by blast
      have xl: "x \<in> template_list_variables ts" using x member by (auto simp: template_list_variables_def)
      show ?thesis using fixed[OF xl, of i] a bx xl by blast
    next
      case False
      then have inner: "b \<in> template_interior (ts!i) \<union> rel_dom (template_literals (ts!i)) \<union> rel_dom (template_callees (ts!i))"
        using b child[OF i] by blast
      have ab: "a = syntax_branch i b" using a branch[OF inner] by simp
      have "a \<in> premise_forest_interior ts \<union> rel_dom (premise_forest_literals ts) \<union> rel_dom (premise_forest_callees ts)"
        unfolding ab premise_forest_interior_def premise_forest_literals_def premise_forest_callees_def placed_table_domain
        using inner i placed_positions_child[of i "map template_interior ts" b syntax_branch]
          placed_positions_child[of i "map rel_dom (map template_literals ts)" b syntax_branch]
          placed_positions_child[of i "map rel_dom (map template_callees ts)" b syntax_branch]
        by auto
      then show ?thesis by blast
    qed
  next
    fix a assume a: "a \<in> premise_forest_interior ts \<union> rel_dom (premise_forest_literals ts) \<union>
      rel_dom (premise_forest_callees ts) \<union> f ` template_list_variables ts"
    show "a \<in> rra_carrier (object_structure (premise_forest_syntax f ts))"
    proof (cases "a \<in> f ` template_list_variables ts")
      case True
      then obtain x t where t: "t \<in> set ts" and x: "x \<in> template_variables t" and ax: "a = f x"
        by (auto simp: template_list_variables_def)
      obtain i where i: "i < length ts" and ti: "ts!i = t" using t by (auto simp: in_set_conv_nth)
      have xl: "x \<in> template_list_variables ts" using t x by (auto simp: template_list_variables_def)
      have b: "f x \<in> rra_carrier (object_structure (template_syntax f (ts!i)))" using child[OF i] x ti by simp
      show ?thesis by (rule placed[OF i b]) (simp add: ax fixed[OF xl])
    next
      case False
      have in3: "a \<in> premise_forest_interior ts \<union> rel_dom (premise_forest_literals ts) \<union> rel_dom (premise_forest_callees ts)"
        using a False by blast
      obtain i b where i: "i < length ts"
        and b: "b \<in> template_interior (ts!i) \<union> rel_dom (template_literals (ts!i)) \<union> rel_dom (template_callees (ts!i))"
        and ab: "a = syntax_branch i b"
        using in3[unfolded premise_forest_interior_def premise_forest_literals_def premise_forest_callees_def
          placed_table_domain map_map comp_def Un_iff placed_positions_map_member] by blast
      have inside: "b \<in> rra_carrier (object_structure (template_syntax f (ts!i)))" using child[OF i] b by blast
      show ?thesis by (rule placed[OF i inside]) (simp add: ab branch[OF b])
    qed
  qed
qed

lemma premise_forest_callee_origin:
  assumes member: "t \<in> set ts" and entry: "(k,d) \<in> template_callees t"
  shows "\<exists>j. (j,d) \<in> premise_forest_callees ts"
proof -
  obtain i where i: "i < length ts" and ti: "ts!i = t" using member by (auto simp: in_set_conv_nth)
  have "(syntax_branch i k,d) \<in> premise_forest_callees ts"
    unfolding premise_forest_callees_def
    using placed_table_child[of i "map template_callees ts" k d syntax_branch] i ti entry by simp
  then show ?thesis by blast
qed

lemma cloned_reference_site_outside:
  assumes ef: "environment_formed E" and fresh: "z \<notin> environment_uses E"
    and refs: "syntax_references (clone_source_environment E u R h z) z L C" and entry: "(k,d) \<in> C"
  shows "fst d \<noteq> z"
proof -
  have binding: "binds_slot (clone_source_environment E u R h z) z k (fst d)"
    using refs entry unfolding syntax_references_def by blast
  have old: "fst d \<in> environment_uses E" by (rule clone_source_targets_are_old[OF ef fresh binding])
  show ?thesis using old fresh by blast
qed

text \<open>
  A copy that fixes every binder leaves a template's projection as it is, when no callee of the
  template is the copy's fresh use.
\<close>

lemma template_projection_fixed:
  assumes addressing: "binder_addressing (template_variables t) f"
    and nonlocal: "\<forall>k d. (k,d) \<in> template_callees t \<longrightarrow> fst d \<noteq> z"
    and fixed: "\<And>a. a \<in> binder_addresses \<Longrightarrow> h a = a"
  shows "map_native_premise h (relocated_site z u h) (template_projection f t) = template_projection f t"
proof (cases t)
  case (Inl pair)
  obtain d p where shape: "pair=(d,p)" by (cases pair)
  have addr: "binder_addressing (pattern_variables p) f" using addressing Inl shape by simp
  have separate: "fst d \<noteq> z" using nonlocal Inl shape by simp
  have site: "relocated_site z u h d = d" using separate by (cases d) simp
  have vars: "pattern_variables (rename_pattern f p) \<subseteq> binder_addresses"
    using addr by (simp add: binder_addressing_def rename_pattern_variables)
  have same: "rename_pattern h (rename_pattern f p) = rename_pattern f p"
    by (rule rename_pattern_fixed) (use vars fixed in blast)
  show ?thesis by (simp add: Inl shape site same)
next
  case (Inr M)
  have vars: "material_variables (rename_material_pattern f M) \<subseteq> binder_addresses"
    using addressing Inr by (simp add: binder_addressing_def renamed_material_variables)
  have same: "rename_material_pattern h (rename_material_pattern f M) =
    rename_material_pattern id (rename_material_pattern f M)"
    by (rule rename_material_agreement) (use vars fixed in auto)
  show ?thesis using same by (simp add: Inr)
qed

lemma template_projection_prefix:
  assumes addressing: "binder_addressing (template_variables t) f"
    and nonlocal: "\<forall>k d. (k,d) \<in> template_callees t \<longrightarrow> fst d \<noteq> z"
  shows "map_native_premise (syntax_prefix n) (relocated_site z u (syntax_prefix n)) (template_projection f t) =
    template_projection f t"
  by (rule template_projection_fixed[OF addressing nonlocal]) (simp add: syntax_prefix_def)

theorem premise_forest_recovers:
  fixes E :: "local_address option artifact_environment"
  assumes formed: "\<forall>t\<in>set ts. template_formed t"
    and addressing: "binder_addressing (template_list_variables ts) f"
    and scope: "f ` template_list_variables ts \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
    and ef: "environment_formed E" and source: "artifact_at E u (premise_forest_syntax f ts)"
    and refs: "syntax_references E u (premise_forest_literals ts) (premise_forest_callees ts)"
  shows "\<forall>i<length ts. native_premise_at E u V (bound_branch i []) (template_projection f (ts!i))
    (bound_branch i ` template_interior (ts!i))
    (bound_branch i ` (rel_dom (template_literals (ts!i)) \<union> rel_dom (template_callees (ts!i))))"
proof (intro allI impI)
  fix i assume index: "i < length ts"
  let ?t = "ts!i"
  let ?R = "template_syntax f ?t"
  let ?z = "clone_source_use E u"
  let ?L = "clone_source_environment E u ?R (bound_branch i) ?z"
  have member: "?t \<in> set ts" by (rule nth_mem[OF index])
  have fresh: "?z \<notin> environment_uses E" by (rule clone_source_use_fresh[OF ef])
  have tformed: "template_formed ?t" using formed member by blast
  have taddr: "binder_addressing (template_variables ?t) f" by (rule template_list_addressing[OF addressing member])
  have tscope: "f ` template_variables ?t \<subseteq> V" using scope member by (auto simp: template_list_variables_def)
  have rf: "exact_formed ?R" by (rule template_syntax_formed[OF tformed taddr])
  have addr: "finite_addressing (rra_carrier (object_structure ?R)) (bound_branch i)"
    by (rule bound_branch_addressing[OF rf])
  have reads: "object_reads_agree (push_object (bound_branch i) ?R) (premise_forest_syntax f ts)
    (bound_branch i ` rra_carrier (object_structure ?R))"
    using bound_forest_reads_carrier[of i "map (template_syntax f) ts"] index
    by (simp add: premise_forest_syntax_def template_syntax_properties)
  have outside: "rel_dom (template_literals ?t) \<union> rel_dom (template_callees ?t) \<subseteq> - binder_addresses"
    using template_reference_slots_outside[of ?t] by blast
  have lits: "map_slot_keys (bound_branch i) (template_literals ?t) \<subseteq> premise_forest_literals ts"
  proof
    fix y assume "y \<in> map_slot_keys (bound_branch i) (template_literals ?t)"
    then obtain k v where kv: "(k,v) \<in> template_literals ?t" and y: "y = (bound_branch i k,v)"
      by (auto simp: map_slot_keys_def)
    have "k \<in> rel_dom (template_literals ?t)" using kv by (rule rel_domI)
    then have "k \<notin> binder_addresses" using outside by blast
    then have "y = (syntax_branch i k,v)" using y by (simp add: bound_branch_other)
    then show "y \<in> premise_forest_literals ts"
      unfolding premise_forest_literals_def
      using placed_table_child[of i "map template_literals ts" k v syntax_branch] index kv by simp
  qed
  have callees: "map_slot_keys (bound_branch i) (template_callees ?t) \<subseteq> premise_forest_callees ts"
  proof
    fix y assume "y \<in> map_slot_keys (bound_branch i) (template_callees ?t)"
    then obtain k d where kd: "(k,d) \<in> template_callees ?t" and y: "y = (bound_branch i k,d)"
      by (auto simp: map_slot_keys_def)
    have "k \<in> rel_dom (template_callees ?t)" using kd by (rule rel_domI)
    then have "k \<notin> binder_addresses" using outside by blast
    then have "y = (syntax_branch i k,d)" using y by (simp add: bound_branch_other)
    then show "y \<in> premise_forest_callees ts"
      unfolding premise_forest_callees_def
      using placed_table_child[of i "map template_callees ts" k d syntax_branch] index kd by simp
  qed
  have mapped_refs: "syntax_references E u (map_slot_keys (bound_branch i) (template_literals ?t))
    (map_slot_keys (bound_branch i) (template_callees ?t))"
    by (rule syntax_references_mono[OF refs lits callees])
  have bounds: "rel_dom (template_literals ?t) \<union> rel_dom (template_callees ?t) \<subseteq> rra_carrier (object_structure ?R)"
    by (auto simp: template_syntax_carrier[OF taddr])
  have clone_refs: "syntax_references ?L ?z (template_literals ?t) (template_callees ?t)"
    by (rule cloned_syntax_references[OF ef fresh bounds mapped_refs])
  have lef: "environment_formed ?L" by (rule clone_environment_formed[OF ef rf fresh])
  have lsrc: "artifact_at ?L ?z ?R" by (simp add: clone_artifact_iff)
  have original: "native_premise_at ?L ?z V [] (template_projection f ?t) (template_interior ?t)
    (rel_dom (template_literals ?t) \<union> rel_dom (template_callees ?t))"
    by (rule template_syntax_recovers[OF tformed taddr tscope boundary lef lsrc clone_refs])
  have copy: "native_syntax_copy ?L ?z ?R E u (premise_forest_syntax f ts) (bound_branch i)
    (relocated_site ?z u (bound_branch i))"
    by (rule clone_environment_is_native_copy[OF ef rf fresh source bound_branch_injective addr reads])
  have nonlocal: "\<forall>k d. (k,d) \<in> template_callees ?t \<longrightarrow> fst d \<noteq> ?z"
    by (intro allI impI) (rule cloned_reference_site_outside[OF ef fresh clone_refs]; assumption)
  have projection: "map_native_premise (bound_branch i) (relocated_site ?z u (bound_branch i))
    (template_projection f ?t) = template_projection f ?t"
    by (rule template_projection_fixed[OF taddr nonlocal bound_branch_binder])
  show "native_premise_at E u V (bound_branch i []) (template_projection f ?t)
    (bound_branch i ` template_interior ?t)
    (bound_branch i ` (rel_dom (template_literals ?t) \<union> rel_dom (template_callees ?t)))"
    using native_syntax_copy.copy_premise[OF copy original]
    by (simp only: bound_branch_image_binders[OF boundary] projection)
qed

text \<open>
  Every finite mixed list is placed as the forest places its children, without extra constructor
  headers. Each body retains its independently recovered premise, transported interior, and complete
  slot boundary. Literal values and callee uses are checked in the destination environment. All
  bodies use the same explicit binder scope, while distinct bodies retain their separate structural
  occurrence positions.
\<close>

end
