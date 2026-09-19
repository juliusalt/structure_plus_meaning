theory Factor_Finite_Development_Questions
  imports Factor_Development_Criterion_Sources Finite_Binary_Values Native_Collection_Programs
begin

section \<open>A question's scope holds its candidates for any subject\<close>

text \<open>
  A native question has a subject, the problem its conditions judge, and a scope, the candidates it
  judges. The scope is presented by a native program that holds of a subject paired with each of its
  candidates, for every subject: one rule for each candidate, whose conclusion pairs any term its
  premise recognizes with the candidate. The premise is the universal recognizer the guard source
  already defines, so the scope states its candidates and nothing about the subject, and a question
  never restates its subject in its scope. Generation binds the subject through that premise and
  returns exactly the candidates.
\<close>

definition finite_scope_rule :: "finite_factor_term \<Rightarrow>
    (local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "finite_scope_rule y=finite_native_rule (Finite_Pattern_Pair (native_var 0) (finite_exact_term_pattern y))
    [([0],((None,[Suc 0]),native_var 0))]"

definition scope_rule :: "factor_term \<Rightarrow> local_address option native_schema" where
  "scope_rule y=\<lparr>schema_conclusion=Pattern_Pair (Pattern_Variable [0]) (exact_term_pattern y),
    schema_premises={([0],(None,[Suc 0]),Pattern_Variable [0])},schema_material_premises={}\<rparr>"

lemma finite_scope_rule_correct [simp]:
  "decode_finite_schema (finite_scope_rule y)=scope_rule (decode_finite_term y)"
  by (rule factor_schema.equality) (simp_all add: finite_scope_rule_def scope_rule_def map_relation_values_def)

lemma scope_rule_formed:
  assumes "term_formed y"
  shows "schema_formed (scope_rule y)"
  using assms by (auto simp: scope_rule_def schema_formed_def single_valued_def)

lemma scope_rule_dependencies [simp]: "schema_dependencies (scope_rule y)={(None,[Suc 0])}"
  by (auto simp: scope_rule_def schema_dependencies_def rel_ran_def)

lemma scope_rule_variables [simp]: "schema_variables (scope_rule y)={[0]}"
  by (auto simp: scope_rule_def schema_variables_def)

lemma scope_rule_instance:
  assumes formed: "term_formed y"
  shows "schema_rule_instance (scope_rule y) M t \<longleftrightarrow>
    (\<exists>x. term_formed x \<and> t=Pair_Term x y \<and> ((None,[Suc 0]),x)\<in>M)"
proof -
  have valuation: "schema_rule_instance (scope_rule y) M t \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables (scope_rule y). term_formed (f a)) \<and>
      t=evaluate_pattern f (schema_conclusion (scope_rule y)) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises (scope_rule y) \<longrightarrow> (d,evaluate_pattern f p)\<in>M))"
    by (rule ordinary_schema_rule_valuation[OF scope_rule_formed[OF formed]]) (simp add: scope_rule_def)
  show ?thesis
  proof
    assume "schema_rule_instance (scope_rule y) M t"
    then obtain f where variables: "\<forall>a\<in>schema_variables (scope_rule y). term_formed (f a)"
      and conclusion: "t=evaluate_pattern f (schema_conclusion (scope_rule y))"
      and supports: "\<forall>s d p. (s,d,p)\<in>schema_premises (scope_rule y) \<longrightarrow> (d,evaluate_pattern f p)\<in>M"
      by (auto simp only: valuation)
    have assignment: "term_formed (f [0])" using variables by (simp only: scope_rule_variables) simp
    have shape: "t=Pair_Term (f [0]) y" using conclusion by (simp add: scope_rule_def)
    have support: "((None,[Suc 0]),f [0])\<in>M" using supports by (simp add: scope_rule_def)
    show "\<exists>x. term_formed x \<and> t=Pair_Term x y \<and> ((None,[Suc 0]),x)\<in>M"
      using assignment shape support by blast
  next
    assume "\<exists>x. term_formed x \<and> t=Pair_Term x y \<and> ((None,[Suc 0]),x)\<in>M"
    then obtain x where xf: "term_formed x" and shape: "t=Pair_Term x y" and guard: "((None,[Suc 0]),x)\<in>M"
      by blast
    have witness: "(\<forall>a\<in>schema_variables (scope_rule y). term_formed ((\<lambda>_. x) a)) \<and>
        t=evaluate_pattern (\<lambda>_. x) (schema_conclusion (scope_rule y)) \<and>
        (\<forall>s d p. (s,d,p)\<in>schema_premises (scope_rule y) \<longrightarrow> (d,evaluate_pattern (\<lambda>_. x) p)\<in>M)"
    proof (intro conjI)
      show "\<forall>a\<in>schema_variables (scope_rule y). term_formed ((\<lambda>_. x) a)" using xf by simp
      show "t=evaluate_pattern (\<lambda>_. x) (schema_conclusion (scope_rule y))" using shape by (simp add: scope_rule_def)
      show "\<forall>s d p. (s,d,p)\<in>schema_premises (scope_rule y) \<longrightarrow> (d,evaluate_pattern (\<lambda>_. x) p)\<in>M"
        using guard by (simp add: scope_rule_def)
    qed
    show "schema_rule_instance (scope_rule y) M t"
      unfolding valuation by (rule exI[of _ "\<lambda>_. x"]) (rule witness)
  qed
qed

definition finite_scope_clauses :: "finite_factor_term list \<Rightarrow>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) fset" where
  "finite_scope_clauses ys=fset_of_list (map (\<lambda>i. ([i],finite_scope_rule (ys!i))) [0..<length ys])"

definition scope_clause_family :: "finite_factor_term list \<Rightarrow>
    (local_address\<times>local_address option native_schema) set" where
  "scope_clause_family ys=(\<lambda>i. ([i],scope_rule (decode_finite_term (ys!i)))) ` {0..<length ys}"

lemma finite_scope_clauses_correct:
  "map_relation_values decode_finite_schema (fset (finite_scope_clauses ys))=scope_clause_family ys"
  by (simp add: finite_scope_clauses_def scope_clause_family_def map_relation_values_def
    fset_of_list.rep_eq image_image split_def)

lemma scope_clause_view:
  assumes formed: "list_all finite_term_formed ys"
  shows "positive_view (decode_finite_system (finite_guard_source_program True)) (Some [],[])
    (Pattern_Variable []) (scope_clause_family ys)"
proof (rule positive_view.intro[OF native_package_system_formed[OF finite_guard_source_package]])
  show "(Some [],[])\<notin>system_definitions (decode_finite_system (finite_guard_source_program True))"
    by (simp add: finite_guard_source_program_definitions)
  show "pattern_formed (Pattern_Variable [])" by simp
  show "finite (scope_clause_family ys)" by (simp add: scope_clause_family_def)
  show "single_valued (scope_clause_family ys)"
    by (auto simp: scope_clause_family_def single_valued_def)
  show "\<forall>c S. (c,S)\<in>scope_clause_family ys \<longrightarrow> schema_formed S"
    using formed by (auto simp: scope_clause_family_def list_all_iff finite_term_formed_correct
      intro!: scope_rule_formed)
  show "\<forall>c S. (c,S)\<in>scope_clause_family ys \<longrightarrow>
      schema_dependencies S\<subseteq>system_definitions (decode_finite_system (finite_guard_source_program True))"
    by (auto simp: scope_clause_family_def finite_guard_source_program_definitions)
qed

lemma scope_clause_family_rule:
  assumes formed: "list_all finite_term_formed ys"
  shows "(\<exists>c S. (c,S)\<in>scope_clause_family ys \<and>
      schema_rule_instance S (positive_meaning (decode_finite_system (finite_guard_source_program True))) t)
    \<longleftrightarrow> (\<exists>x y. term_formed x \<and> t=Pair_Term x (decode_finite_term y) \<and> y\<in>set ys)"
proof
  assume "\<exists>c S. (c,S)\<in>scope_clause_family ys \<and>
    schema_rule_instance S (positive_meaning (decode_finite_system (finite_guard_source_program True))) t"
  then obtain i where bound: "i<length ys" and rule: "schema_rule_instance (scope_rule (decode_finite_term (ys!i)))
      (positive_meaning (decode_finite_system (finite_guard_source_program True))) t"
    by (auto simp: scope_clause_family_def)
  have yf: "term_formed (decode_finite_term (ys!i))"
    using formed bound by (auto simp: list_all_iff finite_term_formed_correct)
  obtain x where xf: "term_formed x" and shape: "t=Pair_Term x (decode_finite_term (ys!i))"
    using rule by (auto simp: scope_rule_instance[OF yf])
  have "ys!i\<in>set ys" using bound by (rule nth_mem)
  then show "\<exists>x y. term_formed x \<and> t=Pair_Term x (decode_finite_term y) \<and> y\<in>set ys"
    using xf shape by blast
next
  assume "\<exists>x y. term_formed x \<and> t=Pair_Term x (decode_finite_term y) \<and> y\<in>set ys"
  then obtain x y where xf: "term_formed x" and shape: "t=Pair_Term x (decode_finite_term y)"
    and member: "y\<in>set ys" by blast
  obtain i where bound: "i<length ys" and index: "y=ys!i"
    using member by (auto simp: in_set_conv_nth)
  have yf: "term_formed (decode_finite_term (ys!i))"
    using formed bound by (auto simp: list_all_iff finite_term_formed_correct)
  have clause: "([i],scope_rule (decode_finite_term (ys!i)))\<in>scope_clause_family ys"
    unfolding scope_clause_family_def by (rule imageI) (use bound in auto)
  have guard: "((None,[Suc 0]),x)\<in>positive_meaning (decode_finite_system (finite_guard_source_program True))"
    using xf by (simp add: finite_guard_source_meaning)
  have "schema_rule_instance (scope_rule (decode_finite_term (ys!i)))
      (positive_meaning (decode_finite_system (finite_guard_source_program True))) t"
    using xf shape index guard by (auto simp: scope_rule_instance[OF yf])
  then show "\<exists>c S. (c,S)\<in>scope_clause_family ys \<and>
      schema_rule_instance S (positive_meaning (decode_finite_system (finite_guard_source_program True))) t"
    using clause by blast
qed

definition finite_scope_program :: "finite_factor_term list \<Rightarrow> local_address option finite_native_system" where
  "finite_scope_program ys=finite_add_view_definition (finite_guard_source_program True)
    (Some [],[]) (Finite_Variable []) (finite_scope_clauses ys)"

lemma finite_scope_program_correct:
  "decode_finite_system (finite_scope_program ys)=
    add_view_definition (decode_finite_system (finite_guard_source_program True)) (Some [],[])
      (Pattern_Variable []) (scope_clause_family ys)"
  by (simp add: finite_scope_program_def finite_scope_clauses_correct)

lemma finite_scope_program_entry:
  "(Some [],[]) |\<in>| finite_system_definitions (finite_scope_program ys)"
  by (simp add: finite_scope_program_def finite_system_definitions_def finite_add_view_definition_def)

lemma finite_scope_program_meaning:
  assumes formed: "list_all finite_term_formed ys"
  shows "((Some [],[]),t)\<in>positive_meaning (decode_finite_system (finite_scope_program ys)) \<longleftrightarrow>
    (\<exists>x y. term_formed x \<and> t=Pair_Term x (decode_finite_term y) \<and> y\<in>set ys)"
proof -
  interpret scope: positive_view "decode_finite_system (finite_guard_source_program True)" "(Some [],[])"
    "Pattern_Variable []" "scope_clause_family ys" by (rule scope_clause_view[OF formed])
  have members: "\<forall>y\<in>set ys. term_formed (decode_finite_term y)"
    using formed by (auto simp: list_all_iff finite_term_formed_correct)
  show ?thesis
    using members by (simp only: finite_scope_program_correct scope.view_meaning scope_clause_family_rule[OF formed];
      auto)
qed

lemma finite_scope_program_context:
  assumes formed: "list_all finite_term_formed ys"
  shows "finite_source_extension_context (finite_guard_source True) None [0] (finite_scope_program ys)=
    Some (finite_guard_source_program True)"
proof -
  interpret scope: positive_view "decode_finite_system (finite_guard_source_program True)" "(Some [],[])"
    "Pattern_Variable []" "scope_clause_family ys" by (rule scope_clause_view[OF formed])
  show ?thesis using finite_guard_source_package[where b=True] scope.formed scope.old_agreement
    by (simp only: finite_source_extension_context_correct finite_scope_program_correct; blast)
qed

definition finite_development_source where
  "finite_development_source ys=(if list_all finite_term_formed ys then
    finite_install_source_entry (finite_guard_source True) None [0] (finite_scope_program ys) (Some [],[]) else None)"

theorem finite_development_source_total:
  "(\<exists>d F u. finite_development_source ys=Some (d,F,u)) \<longleftrightarrow> list_all finite_term_formed ys"
  using finite_install_source_entry_total[of "finite_guard_source True" None "[0]" "finite_scope_program ys" "(Some [],[])"]
    finite_scope_program_context[of ys]
  by (auto simp: finite_development_source_def finite_scope_program_entry split: if_splits)

theorem finite_development_source_meaning:
  assumes installed: "finite_development_source ys=Some (d,F,u)"
  obtains P where "native_package_at (decode_finite_environment F) u [] P"
    "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>x y. term_formed x \<and> t=Pair_Term x (decode_finite_term y) \<and> y\<in>set ys)"
proof -
  have formed: "list_all finite_term_formed ys" and result:
    "finite_install_source_entry (finite_guard_source True) None [0] (finite_scope_program ys) (Some [],[])=Some (d,F,u)"
    using installed by (auto simp: finite_development_source_def split: if_splits)
  obtain P where native: "native_package_at (decode_finite_environment F) u [] P" and exact:
    "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow>
      ((Some [],[]),t)\<in>positive_meaning (decode_finite_system (finite_scope_program ys))"
    using finite_install_source_entry_correct[OF result finite_scope_program_context[OF formed]] by blast
  show thesis by (rule that[OF native]) (use exact finite_scope_program_meaning[OF formed] in blast)
qed

section \<open>A question of a subject\<close>

text \<open>
  A question of a subject judges each candidate of its scope by its conditions, each a native program
  read at an entry, on the subject paired with the candidate. Every admitted candidate satisfies every
  condition on the subject; nothing about the subject is restated beside it.
\<close>

definition finite_subject_question :: "finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow>
    native_development_condition option list \<Rightarrow> native_development_question option" where
  "finite_subject_question x ys cs=(if ys=[] \<or> cs=[] \<or> \<not>list_all (\<lambda>C. C\<noteq>None) cs then None else
    case finite_development_source ys of None \<Rightarrow> None | Some (d,F,u) \<Rightarrow>
      Some \<lparr>development_source=F,development_source_use=u,development_source_root=[],
        development_generator_entry=d,development_problem=x,development_conditions=map the cs,
        development_scope_criticism=development_scope_condition True,development_selected_facets=[]\<rparr>)"

lemma finite_subject_question_fields:
  assumes "finite_subject_question x ys cs=Some Q"
  obtains d F u where "finite_development_source ys=Some (d,F,u)" "development_source Q=F"
    "development_source_use Q=u" "development_source_root Q=[]" "development_generator_entry Q=d"
    "development_problem Q=x" "development_conditions Q=map the cs" "list_all (\<lambda>C. C\<noteq>None) cs"
  using assms by (auto simp: finite_subject_question_def split: if_splits option.splits prod.splits)

theorem finite_subject_question_conditions:
  assumes constructed: "finite_subject_question x ys cs=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and selected: "y\<in>set accepted" and condition: "Some C\<in>set cs"
  shows "development_condition_holds C x y"
proof -
  have conditions: "development_conditions Q=map the cs" and problem: "development_problem Q=x"
    by (rule finite_subject_question_fields[OF constructed]; simp)+
  have member: "C\<in>set (development_conditions Q)"
    using condition by (simp only: conditions set_map) (metis image_eqI option.sel)
  show ?thesis using native_development_original_conditions[OF admitted selected member]
    by (simp only: problem)
qed

definition finite_development_rows where
  "finite_development_rows xs=map (Finite_Pair (Finite_Payload [])) xs"

definition finite_development_question where
  "finite_development_question xs facets=finite_subject_question (Finite_Payload []) xs
    (map (\<lambda>ys. finite_ground_condition (finite_development_rows ys)) facets)"

lemma finite_development_question_source:
  assumes "finite_development_question xs facets=Some Q"
  obtains d F u where "finite_development_source xs=Some (d,F,u)"
    "development_source Q=F" "development_source_use Q=u" "development_source_root Q=[]"
    "development_generator_entry Q=d" "development_problem Q=Finite_Payload []"
  by (rule finite_subject_question_fields[OF assms[unfolded finite_development_question_def]]) blast

lemma finite_development_original_criterion:
  assumes constructed: "finite_development_question xs facets=Some Q" and facet: "ys\<in>set facets"
  obtains C where "C\<in>set (development_conditions Q)" "development_problem Q=Finite_Payload []"
    "finite_ground_condition (finite_development_rows ys)=Some C"
proof -
  let ?cs="map (\<lambda>ys. finite_ground_condition (finite_development_rows ys)) facets"
  have complete: "list_all (\<lambda>C. C\<noteq>None) ?cs"
    and conditions: "development_conditions Q=map the ?cs"
    and problem: "development_problem Q=Finite_Payload []"
    by (rule finite_subject_question_fields[OF constructed[unfolded finite_development_question_def]]; simp)+
  have present: "finite_ground_condition (finite_development_rows ys)\<noteq>None"
    using complete facet by (auto simp: list_all_iff)
  obtain C where actual: "finite_ground_condition (finite_development_rows ys)=Some C"
    using present by auto
  have member: "Some C\<in>set ?cs" using facet by (metis imageI set_map actual)
  have "C\<in>set (development_conditions Q)"
    using imageI[OF member, of the] by (simp only: conditions set_map option.sel)
  then show thesis by (rule that[OF _ problem actual])
qed

theorem finite_development_original_conditions:
  assumes constructed: "finite_development_question xs facets=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted" and facet: "ys\<in>set facets"
  shows "x\<in>set ys"
proof -
  obtain C where member: "C\<in>set (development_conditions Q)" and problem: "development_problem Q=Finite_Payload []"
    and condition: "finite_ground_condition (finite_development_rows ys)=Some C"
    by (rule finite_development_original_criterion[OF constructed facet]) blast
  have holds: "development_condition_holds C (development_problem Q) x"
    by (rule native_development_original_conditions[OF admitted selected member])
  show ?thesis using holds
    by (simp only: problem finite_ground_condition_exact[OF condition])
      (auto simp: finite_development_rows_def)
qed

definition finite_development_generated where
  "finite_development_generated xs=(case finite_development_source xs of None \<Rightarrow> None
    | Some (d,F,u) \<Rightarrow> map_option (\<lambda>(P,D,A,rows). finite_generated_outputs d (Finite_Payload []) rows)
      (finite_native_generation F u [] (Finite_Payload [])))"

definition finite_development_scope_complete where
  "finite_development_scope_complete xs=(case finite_development_generated xs of None \<Rightarrow> False
    | Some actual \<Rightarrow> list_all (\<lambda>x. x\<in>set actual) xs)"

lemma finite_development_question_generated:
  assumes constructed: "finite_development_question xs facets=Some Q"
  shows "map_option (development_generated_values Q)
      (finite_native_generation (development_source Q) (development_source_use Q)
        (development_source_root Q) (development_problem Q))=finite_development_generated xs"
proof -
  obtain d F u where source: "finite_development_source xs=Some (d,F,u)"
    and fields: "development_source Q=F" "development_source_use Q=u" "development_source_root Q=[]"
      "development_generator_entry Q=d" "development_problem Q=Finite_Payload []"
    by (rule finite_development_question_source[OF constructed]) blast
  show ?thesis by (cases "finite_native_generation F u [] (Finite_Payload [])")
    (auto simp: fields finite_development_generated_def source development_generated_values_def
      split: prod.splits)
qed

theorem finite_development_complete_scope:
  assumes question: "finite_development_question xs facets=Some Q"
    and complete: "finite_development_scope_complete xs"
    and generation: "finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)=Some G"
  shows "set xs\<subseteq>set (development_generated_values Q G)"
proof -
  have actual: "finite_development_generated xs=Some (development_generated_values Q G)"
    using finite_development_question_generated[OF question] by (simp add: generation)
  show ?thesis using complete
    by (simp add: finite_development_scope_complete_def actual list_all_iff subset_iff)
qed

definition finite_development_index where
  "finite_development_index n=finite_binary_natural_value n"

lemma finite_development_index_decode [simp]:
  "decode_finite_term (finite_development_index n)=Payload_Term (map (\<lambda>b. if b then 1 else 0) (natural_binary_digits n))"
  by (simp add: finite_development_index_def finite_binary_natural_value_def finite_storage_path_value_def)

lemma finite_development_index_formed [simp]: "finite_term_formed (finite_development_index n)"
  by (simp add: finite_development_index_def)

lemma finite_development_index_eq [simp]:
  "finite_development_index m=finite_development_index n \<longleftrightarrow> m=n"
  by (simp add: finite_development_index_def inj_eq[OF finite_binary_natural_value_injective])

text \<open>
  A development question over the empty subject is a question of a subject: its scope states its
  candidates and each facet is the ground condition of a finite value family, reflected into ordinary
  native source clauses. Membership alone asserts no condition about another subject. Each caller must
  establish how every facet family was computed from its complete original subjects. The scope
  observation compares the actual native generation with every supplied candidate value; it is not a
  proposed coverage flag. A candidate's index is the binary presentation of its natural: one payload
  of its digits, without the byte bound of a single octet, whose size grows with the number of digits
  rather than with the index, so a question over n candidates has a source of O(n log n) addresses.
\<close>

end
