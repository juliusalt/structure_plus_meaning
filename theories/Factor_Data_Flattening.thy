theory Factor_Data_Flattening
  imports Factor_List_Folds Factor_Recursive_Groups
begin

section \<open>Concatenation specializes the right fold to append and an empty seed\<close>

definition data_flatten_schema :: "(nat,nat,nat) factor_schema" where
  "data_flatten_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,217,collection_join_pattern (Pattern_Payload []) data_x data_y)}"

definition data_flatten_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "data_flatten_clause_family d=(if d=217 then list_fold_clauses 46 217
    else if d=218 then {(0,data_flatten_schema)} else {})"

definition data_flatten_group_system :: "(nat,nat,nat,nat) schema_system" where
  "data_flatten_group_system=\<lparr>
    system_interfaces={(217,data_x),(218,data_x)},
    system_clauses={((d,c),S). d\<in>{217,218} \<and> (c,S)\<in>data_flatten_clause_family d}\<rparr>"

lemma data_flatten_group_definitions [simp]: "system_definitions data_flatten_group_system={217,218}"
  by (auto simp: data_flatten_group_system_def system_definitions_def rel_dom_def)

lemma data_flatten_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces data_flatten_group_system \<longleftrightarrow>
    d\<in>{217,218} \<and> p=data_x"
  by (auto simp: data_flatten_group_system_def)

lemma data_flatten_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses data_flatten_group_system \<longleftrightarrow>
    d\<in>{217,218} \<and> (c,S)\<in>data_flatten_clause_family d"
  by (simp add: data_flatten_group_system_def)

lemmas data_flatten_schema_defs = data_flatten_schema_def list_fold_clauses_def
  list_fold_nil_schema_def list_fold_step_schema_def

lemma data_flatten_group_formed_over: "schema_system_formed_over {46} data_flatten_group_system"
proof -
  have interfaces: "system_interfaces data_flatten_group_system={(217,data_x),(218,data_x)}"
    by (simp add: data_flatten_group_system_def)
  have clauses: "system_clauses data_flatten_group_system=
      {((217,0),list_fold_nil_schema),((217,1),list_fold_step_schema 46 217),((218,0),data_flatten_schema)}"
    by (auto simp: data_flatten_group_system_def data_flatten_clause_family_def list_fold_clauses_def)
  show ?thesis by (simp only: schema_system_formed_over_def interfaces clauses data_flatten_group_definitions)
    (auto simp: data_flatten_schema_defs schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)
qed

lemma data_flatten_external_dependencies: "system_external_dependencies data_flatten_group_system={46}"
proof -
  have bounded: "system_external_dependencies data_flatten_group_system\<subseteq>{46}"
    by (rule system_external_dependencies_boundary[OF data_flatten_group_formed_over])
  have clause: "((217,1),list_fold_step_schema 46 217)\<in>system_clauses data_flatten_group_system"
    by (simp add: data_flatten_clause_family_def list_fold_clauses_def)
  have dependency: "46\<in>schema_dependencies (list_fold_step_schema 46 217)"
    by (simp add: list_fold_step_schema_def schema_dependencies_def rel_ran_image)
  have reached: "46\<in>(\<Union>row\<in>system_clauses data_flatten_group_system. schema_dependencies (snd row))"
    by (rule UN_I[OF clause]) (use dependency in simp)
  show ?thesis using bounded reached
    by (auto simp: system_external_dependencies_clauses)
qed

definition data_flatten_base_system :: "(nat,nat,nat,nat) schema_system" where
  "data_flatten_base_system=rooted_system data_append_system
    (system_external_dependencies data_flatten_group_system)"

lemma data_flatten_base_formed [simp]: "schema_system_formed data_flatten_base_system"
  unfolding data_flatten_base_system_def by (rule rooted_system_formed[OF data_append_system_formed])

lemma data_flatten_base_subdomain:
  "system_definitions data_flatten_base_system\<subseteq>system_definitions data_append_system"
  unfolding data_flatten_base_system_def by (rule rooted_system_subdomain)

lemma data_flatten_base_roots: "{46}\<subseteq>system_definitions data_flatten_base_system"
  unfolding data_flatten_base_system_def data_flatten_external_dependencies
  by (rule rooted_system_roots[OF data_append_system_formed]) auto

lemma data_flatten_base_least:
  assumes "{46}\<subseteq>U" "system_dependency_closed data_append_system U"
  shows "system_definitions data_flatten_base_system\<subseteq>U"
  unfolding data_flatten_base_system_def data_flatten_external_dependencies
  by (rule rooted_system_least[OF data_append_system_formed _ assms]) auto

lemma data_flatten_base_call:
  "schema_call_formed data_flatten_base_system d t \<longleftrightarrow>
    d\<in>system_definitions data_flatten_base_system \<and> term_formed t"
proof -
  have roots: "system_external_dependencies data_flatten_group_system\<subseteq>system_definitions data_append_system"
    by (simp add: data_flatten_external_dependencies)
  have domain: "system_definitions data_flatten_base_system=
      system_definition_closure data_append_system (system_external_dependencies data_flatten_group_system)"
    unfolding data_flatten_base_system_def by (rule rooted_system_definitions[OF data_append_system_formed roots])
  have inside: "d\<in>system_definition_closure data_append_system (system_external_dependencies data_flatten_group_system)
      \<Longrightarrow> d\<in>system_definitions data_append_system"
    using data_flatten_base_subdomain by (simp only: domain; blast)
  show ?thesis
    by (simp only: data_flatten_base_system_def rooted_system_calls[OF data_append_system_formed]
      data_append_call domain[unfolded data_flatten_base_system_def]) (use inside in blast)
qed

interpretation data_flatten_group: positive_definition_group data_flatten_base_system data_flatten_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed data_flatten_base_system" by simp
  show "schema_system_formed_over (system_definitions data_flatten_base_system) data_flatten_group_system"
    by (rule schema_system_formed_over_mono[OF data_flatten_group_formed_over data_flatten_base_roots])
  show "system_definitions data_flatten_base_system\<inter>system_definitions data_flatten_group_system={}"
    using data_flatten_base_subdomain by auto
qed

definition data_flatten_system :: "(nat,nat,nat,nat) schema_system" where
  "data_flatten_system=system_union data_flatten_base_system data_flatten_group_system"

lemma data_flatten_system_formed [simp]: "schema_system_formed data_flatten_system"
  using data_flatten_group.formed by (simp only: data_flatten_system_def)

lemma data_flatten_definitions [simp]:
  "system_definitions data_flatten_system=system_definitions data_flatten_base_system\<union>{217,218}"
  by (simp add: data_flatten_system_def)

lemma data_flatten_call:
  "schema_call_formed data_flatten_system d t \<longleftrightarrow>
    d\<in>system_definitions data_flatten_system \<and> term_formed t"
  unfolding data_flatten_system_def
  by (rule data_flatten_group.variable_calls[OF data_flatten_base_call data_flatten_group_interfaces])

lemma data_flatten_clause:
  assumes "d\<in>{217,218}"
  shows "((d,c),S)\<in>system_clauses data_flatten_system \<longleftrightarrow> (c,S)\<in>data_flatten_clause_family d"
  using data_flatten_group.no_old_clause[of d c S] assms by (simp add: data_flatten_system_def)

lemma data_flatten_append_meaning:
  "(46,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
proof -
  have member: "46\<in>system_definitions data_flatten_base_system" using data_flatten_base_roots by blast
  have closure: "46\<in>system_definition_closure data_append_system (system_external_dependencies data_flatten_group_system)"
    using member by (auto simp: data_flatten_base_system_def rooted_system_def)
  show ?thesis using data_flatten_group.old_meaning[OF member, of t]
    rooted_system_meaning[OF data_append_system_formed,
      where roots="system_external_dependencies data_flatten_group_system" and d=46 and t=t] closure
    by (simp only: data_flatten_system_def data_flatten_base_system_def; blast)
qed

interpretation data_append_fold: list_fold_profile data_flatten_system 46 217
  by (unfold_locales)
    (auto simp: data_flatten_clause data_flatten_clause_family_def data_flatten_call)

theorem data_append_fold_exact:
  assumes "data_elements ys"
  shows "(217,collection_join_argument (data_list_term ys) p q)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
    (\<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and>
      p=data_list_term (map data_list_term xss) \<and> q=data_list_term (concat xss@ys))"
proof -
  have element: "(46,collection_join_argument p (data_list_term a) q)\<in>positive_meaning data_flatten_system
      \<longleftrightarrow> (\<exists>xs. data_elements xs \<and> p=data_list_term xs \<and> q=data_list_term (xs@a))"
    if "data_elements a" for a p q
    using that by (auto simp: data_flatten_append_meaning data_append_exact data_list_term_injective)
  have folded: "(217,collection_join_argument (data_list_term ys) p q)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
      (\<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and>
        p=data_list_term (map data_list_term xss) \<and> q=data_list_term (foldr (@) xss ys))"
    by (rule data_append_fold.encoded[where E=data_elements and D=data_elements and f="(@)"
        and h=data_list_term and g=data_list_term and z=ys])
      (use assms element in \<open>auto simp: data_list_term_formed\<close>)
  have append: "foldr (@) xss ys=concat xss@ys" for xss
    by (induction xss) auto
  show ?thesis by (simp only: folded append)
qed

lemma data_flatten_equation:
  "(218,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and>
      (217,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning data_flatten_system)"
proof -
  have valuation: "(218,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> t=Pair_Term (h 0) (h 1) \<and>
        (217,collection_join_argument (Payload_Term []) (h 0) (h 1))\<in>positive_meaning data_flatten_system)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: data_flatten_clause data_flatten_clause_family_def data_flatten_schema_def
        schema_variables_def data_flatten_call)
  have formed: "term_formed p \<and> term_formed q"
    if "(217,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning data_flatten_system" for p q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by auto
  show ?thesis
  proof
    assume "(218,t)\<in>positive_meaning data_flatten_system"
    then show "\<exists>p q. t=Pair_Term p q \<and>
        (217,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning data_flatten_system"
      by (simp only: valuation; blast)
  next
    assume "\<exists>p q. t=Pair_Term p q \<and>
      (217,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning data_flatten_system"
    then obtain p q where parts: "t=Pair_Term p q"
      "(217,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning data_flatten_system" by blast
    show "(218,t)\<in>positive_meaning data_flatten_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else q"])
        (use parts formed[OF parts(2)] in auto)
  qed
qed

theorem data_flatten_exact:
  "(218,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
    (\<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and>
      t=Pair_Term (data_list_term (map data_list_term xss)) (data_list_term (concat xss)))"
  using data_append_fold_exact[of "[]"] by (auto simp: data_flatten_equation)

corollary data_flatten_at_lists:
  "(218,Pair_Term (data_list_term (map data_list_term xss)) q)\<in>positive_meaning data_flatten_system
    \<longleftrightarrow> (\<forall>xs\<in>set xss. data_elements xs) \<and> q=data_list_term (concat xss)"
proof -
  have injective: "inj data_list_term" by (simp add: inj_def data_list_term_injective)
  show ?thesis by (auto simp: data_flatten_exact data_list_term_injective inj_map_eq_map[OF injective])
qed

text \<open>
  The two definitions contain three ordinary clauses. Their sole external
  callee is the existing exact append operation; its complete dependency
  closure supplies the least base. The group retains those actual definitions
  and their complete meanings. Concatenation is the append specialization of
  the general fold, so no separate native flattening induction is needed.

  Every inner list and the complete outer boundary is consumed. Empty inner
  lists and repeated elements are preserved according to ordinary concat.
  The elements are formed self-contained terms because append has that domain.
  The private fold's empty case still accepts any formed seed; the public
  concatenation fixes its seed to the empty data list.
\<close>

end
