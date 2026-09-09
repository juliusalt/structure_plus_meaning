theory Factor_Adoption_Comparison
  imports Factor_Permission_Presentations Factor_Generation_Contracts Factor_Product_Contracts
begin

section \<open>The existing target and generation contracts supply all three fields\<close>

definition adoption_comparison_base :: "(nat,nat,nat,nat) schema_system" where
  "adoption_comparison_base=rooted_system generation_value_system {35,135,139,140}"

lemma adoption_comparison_base_formed [simp]: "schema_system_formed adoption_comparison_base"
  unfolding adoption_comparison_base_def by (rule rooted_system_formed[OF generation_value_system_formed])

lemma adoption_comparison_base_roots: "{35,135,139,140}\<subseteq>system_definitions adoption_comparison_base"
  unfolding adoption_comparison_base_def
  by (rule rooted_system_roots[OF generation_value_system_formed])
    (use generation_target_roots in auto)

lemma adoption_comparison_base_subdomain:
  "system_definitions adoption_comparison_base\<subseteq>system_definitions generation_value_system"
  unfolding adoption_comparison_base_def by (rule rooted_system_subdomain)

lemma adoption_comparison_base_least:
  assumes "{35,135,139,140}\<subseteq>U" "system_dependency_closed generation_value_system U"
  shows "system_definitions adoption_comparison_base\<subseteq>U"
  unfolding adoption_comparison_base_def
  by (rule rooted_system_least[OF generation_value_system_formed _ assms])
    (use generation_target_roots in auto)

lemma adoption_comparison_base_bound: "system_definitions adoption_comparison_base\<subseteq>{..146}"
proof -
  have lower: "system_definitions generation_target_system\<subseteq>{..146}"
    by (rule subset_trans[OF generation_target_subdomain]) auto
  have whole: "system_definitions generation_value_system\<subseteq>{..146}"
    by (simp only: generation_value_definitions) (use lower in \<open>auto dest: subsetD\<close>)
  show ?thesis by (rule subset_trans[OF adoption_comparison_base_subdomain whole])
qed

lemma adoption_comparison_base_call:
  "schema_call_formed adoption_comparison_base d t \<longleftrightarrow>
    d\<in>system_definitions adoption_comparison_base \<and> term_formed t"
  unfolding adoption_comparison_base_def
  by (rule rooted_system_variable_calls[OF generation_value_system_formed generation_value_call])

lemma adoption_comparison_base_meaning:
  assumes "d\<in>system_definitions adoption_comparison_base"
  shows "(d,t)\<in>positive_meaning adoption_comparison_base \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_value_system"
  using rooted_system_meaning_at[OF generation_value_system_formed
    assms[unfolded adoption_comparison_base_def], of t]
  by (simp only: adoption_comparison_base_def)

definition adoption_admission_schema :: "(nat,nat,nat) factor_schema" where
  "adoption_admission_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_z))
    {(0,35,data_x),(1,139,data_y),(2,35,data_z)}"

definition adoption_identity_schema :: "(nat,nat,nat) factor_schema" where
  "adoption_identity_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
      (Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))))
    {(0,135,Pattern_Pair data_x data_w),
     (1,140,Pattern_Pair data_y (Pattern_Variable 4)),
     (2,135,Pattern_Pair data_z (Pattern_Variable 5))}"

definition adoption_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "adoption_admission_system=add_view_definition adoption_comparison_base 269 data_x {(0,adoption_admission_schema)}"

interpretation adoption_admission_view: positive_view adoption_comparison_base 269 data_x "{(0,adoption_admission_schema)}"
  by (rule positive_view.intro)
    (use adoption_comparison_base_formed adoption_comparison_base_bound adoption_comparison_base_roots
      in \<open>auto simp: adoption_admission_schema_def schema_formed_def schema_dependencies_def
        single_valued_def rel_ran_def dest: subsetD\<close>)

lemma adoption_admission_system_formed [simp]: "schema_system_formed adoption_admission_system"
  using adoption_admission_view.formed by (simp only: adoption_admission_system_def)

lemma adoption_admission_definitions [simp]:
  "system_definitions adoption_admission_system=insert 269 (system_definitions adoption_comparison_base)"
  by (simp add: adoption_admission_system_def)

lemma adoption_admission_call:
  "schema_call_formed adoption_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions adoption_admission_system \<and> term_formed t"
  using added_variable_calls[OF adoption_comparison_base_formed adoption_admission_view.formed adoption_comparison_base_call]
  by (simp only: adoption_admission_system_def)

definition adoption_value_system :: "(nat,nat,nat,nat) schema_system" where
  "adoption_value_system=add_view_definition adoption_admission_system 270 data_x {(0,adoption_identity_schema)}"

interpretation adoption_identity_view: positive_view adoption_admission_system 270 data_x "{(0,adoption_identity_schema)}"
  by (rule positive_view.intro)
    (use adoption_admission_system_formed adoption_comparison_base_bound adoption_comparison_base_roots
      in \<open>auto simp: adoption_identity_schema_def schema_formed_def schema_dependencies_def
        single_valued_def rel_ran_def dest: subsetD\<close>)

lemma adoption_value_system_formed [simp]: "schema_system_formed adoption_value_system"
  using adoption_identity_view.formed by (simp only: adoption_value_system_def)

lemma adoption_value_definitions [simp]:
  "system_definitions adoption_value_system=insert 270 (insert 269 (system_definitions adoption_comparison_base))"
  by (simp add: adoption_value_system_def)

lemma adoption_value_call:
  "schema_call_formed adoption_value_system d t \<longleftrightarrow>
    d\<in>system_definitions adoption_value_system \<and> term_formed t"
  using added_variable_calls[OF adoption_admission_system_formed adoption_identity_view.formed adoption_admission_call]
  by (simp only: adoption_value_system_def)

lemma adoption_value_clause:
  "((269,c),S)\<in>system_clauses adoption_value_system \<longleftrightarrow> c=0 \<and> S=adoption_admission_schema"
  "((270,c),S)\<in>system_clauses adoption_value_system \<longleftrightarrow> c=0 \<and> S=adoption_identity_schema"
  using adoption_admission_view.no_old_clause adoption_identity_view.no_old_clause
  by (auto simp: adoption_value_system_def adoption_admission_system_def)

lemma adoption_value_old_meaning:
  assumes member: "d\<in>system_definitions adoption_comparison_base"
  shows "(d,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_value_system"
proof -
  have middle: "d\<in>system_definitions adoption_admission_system" using member by simp
  show ?thesis using adoption_identity_view.old_meaning[OF middle, of t]
    adoption_admission_view.old_meaning[OF member, of t] adoption_comparison_base_meaning[OF member, of t]
    by (simp only: adoption_value_system_def adoption_admission_system_def)
qed

lemma adoption_value_components:
  "(35,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow> (\<exists>a. target_value_presents a t)"
  "(139,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow> (\<exists>G. generation_value_presents G t)"
  "(135,Pair_Term p q)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    presented_relation target_value_presents target_value_presents (=) p q"
  "(140,Pair_Term p q)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    presented_relation generation_value_presents generation_value_presents (=) p q"
  using adoption_comparison_base_roots adoption_value_old_meaning[of 35 t]
    adoption_value_old_meaning[of 139 t] adoption_value_old_meaning[of 135 "Pair_Term p q"]
    adoption_value_old_meaning[of 140 "Pair_Term p q"]
  by (auto simp: generation_value_components generation_admission_exact
    target_identity_contract.exact generation_identity_contract.exact)

section \<open>Every complete valuation has the independently specified meaning\<close>

lemma adoption_admission_valuation:
  "(269,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
      (35,h 0)\<in>positive_meaning adoption_value_system \<and>
      (139,h 1)\<in>positive_meaning adoption_value_system \<and>
      (35,h 2)\<in>positive_meaning adoption_value_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: adoption_value_clause adoption_admission_schema_def schema_variables_def adoption_value_call)

lemma adoption_comparison_valuation:
  "(270,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2)))
        (Pair_Term (h 3) (Pair_Term (h 4) (h 5))) \<and>
      (135,Pair_Term (h 0) (h 3))\<in>positive_meaning adoption_value_system \<and>
      (140,Pair_Term (h 1) (h 4))\<in>positive_meaning adoption_value_system \<and>
      (135,Pair_Term (h 2) (h 5))\<in>positive_meaning adoption_value_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: adoption_value_clause adoption_identity_schema_def schema_variables_def adoption_value_call)

lemma adoption_admission_fields:
  "(269,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>a g p. t=Pair_Term a (Pair_Term g p) \<and>
      (35,a)\<in>positive_meaning adoption_value_system \<and>
      (139,g)\<in>positive_meaning adoption_value_system \<and>
      (35,p)\<in>positive_meaning adoption_value_system)"
proof
  assume "(269,t)\<in>positive_meaning adoption_value_system"
  then show "\<exists>a g p. t=Pair_Term a (Pair_Term g p) \<and>
      (35,a)\<in>positive_meaning adoption_value_system \<and>
      (139,g)\<in>positive_meaning adoption_value_system \<and>
      (35,p)\<in>positive_meaning adoption_value_system"
    by (simp only: adoption_admission_valuation) blast
next
  assume "\<exists>a g p. t=Pair_Term a (Pair_Term g p) \<and>
      (35,a)\<in>positive_meaning adoption_value_system \<and>
      (139,g)\<in>positive_meaning adoption_value_system \<and>
      (35,p)\<in>positive_meaning adoption_value_system"
  then obtain a g p where parts: "t=Pair_Term a (Pair_Term g p)"
    "(35,a)\<in>positive_meaning adoption_value_system"
    "(139,g)\<in>positive_meaning adoption_value_system"
    "(35,p)\<in>positive_meaning adoption_value_system" by blast
  have formed: "term_formed a" "term_formed g" "term_formed p"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by blast+
  show "(269,t)\<in>positive_meaning adoption_value_system"
    by (simp only: adoption_admission_valuation,
      rule exI[of _ "\<lambda>n::nat. if n=0 then a else if n=1 then g else p"])
      (use parts formed in auto)
qed

lemma adoption_comparison_fields:
  "(270,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>a g p b h q. t=Pair_Term (Pair_Term a (Pair_Term g p)) (Pair_Term b (Pair_Term h q)) \<and>
      (135,Pair_Term a b)\<in>positive_meaning adoption_value_system \<and>
      (140,Pair_Term g h)\<in>positive_meaning adoption_value_system \<and>
      (135,Pair_Term p q)\<in>positive_meaning adoption_value_system)"
proof
  assume "(270,t)\<in>positive_meaning adoption_value_system"
  then show "\<exists>a g p b h q. t=Pair_Term (Pair_Term a (Pair_Term g p)) (Pair_Term b (Pair_Term h q)) \<and>
      (135,Pair_Term a b)\<in>positive_meaning adoption_value_system \<and>
      (140,Pair_Term g h)\<in>positive_meaning adoption_value_system \<and>
      (135,Pair_Term p q)\<in>positive_meaning adoption_value_system"
    by (simp only: adoption_comparison_valuation) blast
next
  assume "\<exists>a g p b h q. t=Pair_Term (Pair_Term a (Pair_Term g p)) (Pair_Term b (Pair_Term h q)) \<and>
      (135,Pair_Term a b)\<in>positive_meaning adoption_value_system \<and>
      (140,Pair_Term g h)\<in>positive_meaning adoption_value_system \<and>
      (135,Pair_Term p q)\<in>positive_meaning adoption_value_system"
  then obtain a g p b h q where parts:
    "t=Pair_Term (Pair_Term a (Pair_Term g p)) (Pair_Term b (Pair_Term h q))"
    "(135,Pair_Term a b)\<in>positive_meaning adoption_value_system"
    "(140,Pair_Term g h)\<in>positive_meaning adoption_value_system"
    "(135,Pair_Term p q)\<in>positive_meaning adoption_value_system" by blast
  have formed: "term_formed a" "term_formed g" "term_formed p" "term_formed b" "term_formed h" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by auto
  show "(270,t)\<in>positive_meaning adoption_value_system"
    by (simp only: adoption_comparison_valuation,
      rule exI[of _ "\<lambda>n::nat. if n=0 then a else if n=1 then g else if n=2 then p
        else if n=3 then b else if n=4 then h else q"])
      (use parts formed in auto)
qed

theorem adoption_admission_exact:
  "(269,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>z. adoption_context_presents z t)"
  by (simp only: adoption_admission_fields adoption_value_components split_paired_Ex adoption_context_fields)
    (auto simp: adoption_value_presents_def)

theorem adoption_identity_at_pair:
  "(270,Pair_Term p q)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    presentation_transport adoption_context_presents adoption_context_presents p q"
proof -
  have product: "presented_relation adoption_context_presents adoption_context_presents (=) p q \<longleftrightarrow>
      (270,Pair_Term p q)\<in>positive_meaning adoption_value_system"
    by (simp only: factor_pair_identity_lifting)
      (auto simp: adoption_comparison_fields adoption_value_components)
  show ?thesis using product by (auto simp: presented_relation_def presentation_transport_def)
qed

theorem adoption_identity_exact:
  "(270,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> presentation_transport adoption_context_presents adoption_context_presents p q)"
proof
  assume positive: "(270,t)\<in>positive_meaning adoption_value_system"
  obtain p q where shape: "t=Pair_Term p q"
    using positive by (simp only: adoption_comparison_fields) blast
  show "\<exists>p q. t=Pair_Term p q \<and>
      presentation_transport adoption_context_presents adoption_context_presents p q"
    using positive adoption_identity_at_pair[of p q] by (auto simp only: shape)
next
  assume "\<exists>p q. t=Pair_Term p q \<and>
      presentation_transport adoption_context_presents adoption_context_presents p q"
  then show "(270,t)\<in>positive_meaning adoption_value_system"
    by (auto simp only: adoption_identity_at_pair)
qed

theorem adoption_native_presentation_class:
  "presentation_class adoption_context_presents adoption_context_formed
    (\<lambda>t. (269,t)\<in>positive_meaning adoption_value_system)"
  using adoption_context_presentation_class by (simp only: adoption_admission_exact)

interpretation adoption_identity_contract: presented_relation_contract
  adoption_context_presents adoption_context_formed "\<lambda>t. (269,t)\<in>positive_meaning adoption_value_system"
  adoption_context_presents adoption_context_formed "\<lambda>t. (269,t)\<in>positive_meaning adoption_value_system"
  "(=)" "\<lambda>p q. (270,Pair_Term p q)\<in>positive_meaning adoption_value_system"
  by (rule presented_relation_contract.intro[OF adoption_native_presentation_class
    adoption_native_presentation_class]; unfold_locales)
    (simp only: adoption_identity_at_pair; auto simp: presentation_transport_def presented_relation_def)

theorem adoption_comparison_on_values:
  assumes "adoption_value_presents A G purpose p" "adoption_value_presents B H other q"
  shows "(270,Pair_Term p q)\<in>positive_meaning adoption_value_system \<longleftrightarrow>
    A=B \<and> G=H \<and> purpose=other"
  using adoption_identity_contract.at[of "(A,G,purpose)" p "(B,H,other)" q] assms
  by (simp only: adoption_context_fields prod.inject)

abbreviation adoption_value_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "adoption_value_operation_result d t \<equiv>
    if d=269 then (\<exists>z. adoption_context_presents z t)
    else (\<exists>p q. t=Pair_Term p q \<and> presentation_transport adoption_context_presents adoption_context_presents p q)"

theorem adoption_value_operations_exact:
  "d\<in>{269,270} \<Longrightarrow>
    ((d,t)\<in>positive_meaning adoption_value_system \<longleftrightarrow> adoption_value_operation_result d t)"
  by (auto simp: adoption_admission_exact adoption_identity_exact)

theorem native_adoption_value_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {269::nat,270} \<and>
    (\<forall>d\<in>{269,270}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> adoption_value_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{269,270}\<subseteq>system_definitions adoption_value_system" by simp
  have calls: "schema_call_formed adoption_value_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{269,270}" for d t
    using selected that by (simp only: adoption_value_call) blast
  show ?thesis
    by (rule compiled_exact_operations[OF adoption_value_system_formed selected calls adoption_value_operations_exact])
qed

theorem native_adoption_value_reference:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu R k admit.
    closed_native_package_at C cu [] R \<and> native_package_environment C cu []=C \<and>
    k\<noteq>admit \<and> {k,admit}\<subseteq>system_definitions R \<and>
    (\<forall>d\<in>{k,admit}. \<forall>z. schema_call_formed R d z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (k,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport adoption_context_presents adoption_context_presents p q)) \<and>
    (\<forall>z. (admit,z)\<in>positive_meaning R \<longleftrightarrow> (\<exists>a. adoption_context_presents a z))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu R where compiled:
    "inj_on g (system_definitions adoption_value_system)"
    "closed_native_package_at C cu [] R" "native_package_environment C cu []=C"
    "system_alpha_variant (rename_system g adoption_value_system) R"
    "positive_meaning R=map_prod g id ` positive_meaning adoption_value_system"
    using program_compilation_total[OF adoption_value_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have roots: "270\<in>system_definitions adoption_value_system" "269\<in>system_definitions adoption_value_system"
    by simp_all
  have separate: "g 270\<noteq>g 269" using inj_onD[OF compiled(1) _ roots] by auto
  have members: "{g 270,g 269}\<subseteq>system_definitions R"
    using roots compiled(4) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have calls: "schema_call_formed R (g d) z \<longleftrightarrow> term_formed z"
    if "d\<in>{269,270}" for d z
  proof -
    have member: "d\<in>system_definitions adoption_value_system" using that by auto
    show ?thesis by (simp only: compiled_system_call_boundary[OF adoption_value_system_formed
      compiled(1,4) member] adoption_value_call; use member in simp)
  qed
  have comparison: "(g 270,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport adoption_context_presents adoption_context_presents p q)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) roots(1) compiled(5)] adoption_identity_exact adoption_admission_exact)
  have admit: "(g 269,z)\<in>positive_meaning R \<longleftrightarrow> (\<exists>a. adoption_context_presents a z)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) roots(2) compiled(5)] adoption_identity_exact adoption_admission_exact)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ R],
      rule exI[of _ "g 270"], rule exI[of _ "g 269"])
    (use compiled(2,3) separate members calls comparison admit in auto)
qed

text \<open>
  Admission and correspondence are two ordinary definitions with three
  identified premises each. Their base is the least complete-definition
  closure of the four actual target and generation callees. Comparison
  consumes the component identity contracts through generic product lifting;
  it does not inspect target enumerations or repeat generation recursion.

  All complete authority, core, and purpose presentations remain admitted.
  Equality of the three independent fields gives exactly full correspondence.
  A target's authority or purpose role comes from its position in this actual
  application. Generation admission and identity do not establish cause validity.

  One fixed native program supports both entries before all future formed
  operands, with its scope and every old artifact and binding retained.
  Permission, publication, currentness, and mathematical proof admission remain
  separate operations.
\<close>

end
