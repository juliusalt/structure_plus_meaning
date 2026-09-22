theory Development_Native_Decomposition
imports Development_Located_Rows Development_Decomposition_Soundness Factor_Finite_Payload_Literals
begin

section \<open>The decomposition schema is a native program over problem rows\<close>

text \<open>
  An application of the decomposition schema at a parent that has a locus is presented less its part
  child (the decomposition entry of task 66): the part child stands at the parent's own locus, so what
  the application adds is its intermediates, whose definition children it poses. The native schema
  therefore reads the material the application rests on and nothing it poses: the parent's row as the
  store holds it, a locus and a body, and the intermediates as a nonempty family of citations of the
  state's constants. Its argument is the development's store (@{const development_rows_term}), the
  parent's row and the intermediates; no state is an argument.

  What the program decides is exactly that: at a presented parent it holds exactly when the
  intermediates are nonempty (@{text native_decomposition_applies}). Whether the state poses the
  application's children is not decided here; it is a separate premise of the soundness instance
  (@{text native_decomposition_reduction}), until the state's rows are read natively (task 94).

  The program is the development's one row search (@{const development_row_definitions}) and the
  schema's entry at a site of its own, whose one rule concludes the parent's row over the store and the
  intermediates and premises the search at the parent's locus. Its only literal is the empty payload,
  in the shapes of the bits a locus is read by, so no kind, role, origin or authority is compared by an
  octet.
\<close>

abbreviation decomposition_applies :: "local_address option definition_site" where
  "decomposition_applies \<equiv> (Some [],[1])"

definition decomposition_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "decomposition_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
      (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 3))
        (Finite_Pattern_Pair (native_var 4) (native_var 5)))))
    [([0],(development_row_search,Finite_Pattern_Pair (native_var 3)
      (Finite_Pattern_Pair (native_var 2) (native_var 1))))]"

definition decomposition_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "decomposition_definitions=(decomposition_applies,[([0],decomposition_rule)])#development_row_definitions"

definition finite_native_decomposition :: "local_address option finite_native_system" where
  "finite_native_decomposition=finite_rule_program decomposition_definitions"

definition native_decomposition_system :: "local_address option native_system" where
  "native_decomposition_system=decode_finite_system finite_native_decomposition"

lemma finite_native_decomposition_formed: "finite_system_formed finite_native_decomposition"
  by code_simp

lemma native_decomposition_formed: "schema_system_formed native_decomposition_system"
  using finite_native_decomposition_formed
  by (simp only: native_decomposition_system_def finite_system_formed_correct)

interpretation decomposition_applies_family: native_rule_family native_decomposition_system decomposition_applies
    "[([0],decomposition_rule)]"
  unfolding native_decomposition_system_def finite_native_decomposition_def
  by (rule finite_rule_program_family[OF native_decomposition_formed[unfolded native_decomposition_system_def
    finite_native_decomposition_def]])
    (simp_all add: decomposition_definitions_def development_row_definitions_def decomposition_rule_def)

text \<open>
  The row search keeps its meaning in this program: the two programs hold the same definitions at the
  search's and the check's sites, and the entry is at a site of its own, so their shared definitions
  agree (@{thm positive_meaning_shared_definitions}) and no argument about the search is made again.
\<close>

lemma native_decomposition_search:
  "(development_row_search,t)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (development_row_search,t)\<in>positive_meaning development_rows_program"
proof -
  have defs: "system_definitions native_decomposition_system=
      {decomposition_applies,development_row_search,development_row_check}"
    by (simp add: native_decomposition_system_def finite_native_decomposition_def finite_rule_program_definitions
      decomposition_definitions_def development_row_definitions_def)
  have rows_defs: "system_definitions development_rows_program={development_row_search,development_row_check}"
    by (simp add: development_rows_program_def finite_development_rows_program_def finite_rule_program_definitions
      development_row_definitions_def)
  have shared: "system_definitions native_decomposition_system\<inter>system_definitions development_rows_program=
      {development_row_search,development_row_check}"
    using defs rows_defs by auto
  have agree: "systems_agree_on native_decomposition_system development_rows_program
      {development_row_search,development_row_check}"
    unfolding systems_agree_on_def native_decomposition_system_def finite_native_decomposition_def
      development_rows_program_def finite_development_rows_program_def
      finite_rule_program_interface finite_rule_program_clause
    by (simp add: decomposition_definitions_def development_row_definitions_def)
  show ?thesis
    by (rule positive_meaning_shared_definitions[OF native_decomposition_formed development_rows_program_formed])
      (use agree shared defs rows_defs in simp_all)
qed

section \<open>The program's only literal is the empty payload\<close>

text \<open>
  By the criterion of \<open>Factor_Positive_Parametricity\<close>, the payloads a program states are the octets
  it reads as structure. This program states the empty payload alone: it reads the bits of a locus by
  their shapes and compares every other octet, of a contract term, a name or a citation, only as a whole.
\<close>

lemma finite_native_decomposition_payloads: "finite_system_payloads finite_native_decomposition={|[]|}"
  by code_simp

theorem native_decomposition_payloads: "system_payloads native_decomposition_system={[]}"
  using finite_system_payloads_exact[of finite_native_decomposition]
  by (simp add: native_decomposition_system_def finite_native_decomposition_payloads)

section \<open>The subject: the parent's row, the store and the intermediates\<close>

definition development_parent_row :: "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> factor_term) \<Rightarrow>
    (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem \<Rightarrow> factor_term" where
  "development_parent_row key inert origin grant p=Pair_Term
    (path_term (development_located_at key Development_Problem_Role p))
    (development_problem_body inert (origin p) (grant p) (problem_contract p))"

definition development_decomposition_argument ::
    "factor_term \<Rightarrow> development_store_rows \<Rightarrow> factor_term \<Rightarrow> (nat \<Rightarrow> bool list) \<Rightarrow> nat list \<Rightarrow> factor_term" where
  "development_decomposition_argument x rows row key I=Pair_Term x (Pair_Term (development_rows_term rows)
    (Pair_Term row (development_row_family (map key I))))"

text \<open>
  The state an application is read in poses its children: every intermediate has a definition problem
  there and the parent's constant a problem of the parent's kind. The schema does not read this; it is
  the premise of the soundness instance below, read where the request is constructed.
\<close>

definition development_state_poses :: "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat list \<Rightarrow> bool" where
  "development_state_poses C p I \<longleftrightarrow> (\<forall>h\<in>set I. development_intermediate_problem C h\<noteq>None) \<and>
    (\<forall>c. c |\<in>| problem_subject p \<longrightarrow> development_part_problem C p c\<noteq>None)"

lemma development_row_family_nonempty: "development_row_family ls=Pair_Term a b \<Longrightarrow> ls\<noteq>[]"
  by (cases ls) (simp_all add: development_row_family_def)

section \<open>Every native application makes progress\<close>

text \<open>
  At a parent that has a locus the subject is one constant, so progress is a nonempty family of
  intermediates; the rule's pattern demands one. The degenerate application, whose only child is the
  parent, is no application of this program.
\<close>

theorem native_decomposition_progress:
  assumes holds: "(decomposition_applies,Pair_Term x (Pair_Term S (Pair_Term row (development_row_family ls))))
      \<in>positive_meaning native_decomposition_system"
  shows "ls\<noteq>[]"
proof -
  obtain c F f where rule: "(c,F)\<in>set [([0::nat],decomposition_rule)]"
    and conclusion: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term S (Pair_Term row (development_row_family ls)))"
    by (rule decomposition_applies_family.holds_cases[OF holds])
  from rule have "F=decomposition_rule" by simp
  with conclusion have "development_row_family ls=Pair_Term (f [4]) (f [5])"
    by (simp add: decomposition_rule_def)
  then show ?thesis by (rule development_row_family_nonempty)
qed

section \<open>The contract: at a presented parent the schema holds exactly of nonempty intermediates\<close>

context
  fixes key ekey inert origin grant supported scope decs ps rs iss rows
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
begin

theorem native_decomposition_applies:
  assumes p: "p\<in>set ps" and xf: "term_formed x"
  shows "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    I\<noteq>[]"
proof
  assume holds: "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I)\<in>positive_meaning native_decomposition_system"
  show "I\<noteq>[]"
    using native_decomposition_progress[OF holds[unfolded development_decomposition_argument_def]] by simp
next
  assume "I\<noteq>[]"
  then obtain h hs where I: "map key I=h#hs" by (cases I) auto
  define b where "b=development_problem_body inert (origin p) (grant p) (problem_contract p)"
  define l where "l=path_term (development_located_at key Development_Problem_Role p)"
  have lookup: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=Some b"
    unfolding b_def by (rule development_rows_problem[OF present p]) simp
  have found_rows: "(development_row_search,Pair_Term b (Pair_Term l (development_rows_term rows)))
      \<in>positive_meaning development_rows_program"
    unfolding l_def using development_row_lookup_at[OF development_rows_formed[OF present]] lookup by blast
  have found: "(development_row_search,Pair_Term b (Pair_Term l (development_rows_term rows)))
      \<in>positive_meaning native_decomposition_system"
    using found_rows native_decomposition_search by blast
  have formed: "term_formed (Pair_Term b (Pair_Term l (development_rows_term rows)))"
    using found by (rule positive_meaning_term_formed)
  define f where "f=(\<lambda>a::local_address. if a=[0] then x else if a=[1] then development_rows_term rows
    else if a=[2] then l else if a=[3] then b else if a=[4] then path_term h
    else data_list_term (map path_term hs))"
  have "(decomposition_applies,evaluate_pattern f (decode_finite_pattern
      (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 3))
          (Finite_Pattern_Pair (native_var 4) (native_var 5)))))))\<in>positive_meaning native_decomposition_system"
  proof (rule decomposition_applies_family.native_step[of "[0]"])
    show "([0],finite_native_rule (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 3))
          (Finite_Pattern_Pair (native_var 4) (native_var 5)))))
        [([0],(development_row_search,Finite_Pattern_Pair (native_var 3)
          (Finite_Pattern_Pair (native_var 2) (native_var 1))))])\<in>set [([0],decomposition_rule)]"
      by (simp add: decomposition_rule_def)
    have hs: "term_formed (data_list_term (map path_term hs))"
      using development_row_family_formed[of hs] by (simp add: development_row_family_def)
    show "\<forall>a\<in>pattern_variables (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 3))
          (Finite_Pattern_Pair (native_var 4) (native_var 5)))))) \<union>
      (\<Union>(s,d,q)\<in>set [([0::nat],(development_row_search,Finite_Pattern_Pair (native_var 3)
          (Finite_Pattern_Pair (native_var 2) (native_var 1))))]. pattern_variables (decode_finite_pattern q)).
        term_formed (f a)"
      using xf formed hs by (auto simp: f_def l_def)
    show "\<forall>(s,d,q)\<in>set [([0::nat],(development_row_search,Finite_Pattern_Pair (native_var 3)
          (Finite_Pattern_Pair (native_var 2) (native_var 1))))].
        (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning native_decomposition_system"
      using found by (simp add: f_def)
  qed
  then show "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I)\<in>positive_meaning native_decomposition_system"
    using I by (simp add: f_def development_decomposition_argument_def development_parent_row_def
      development_row_family_def b_def l_def)
qed

section \<open>The native soundness is task 60's, instantiated\<close>

text \<open>
  The state's posing of the children is this instance's own premise: with it every native application
  is an application of task 60's schema at the parent, and its reduction is task 60's theorem.
\<close>

theorem native_decomposition_reduction:
  assumes p: "p\<in>set ps" and xf: "term_formed x" and state: "development_state_poses C p I"
    and holds: "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I)\<in>positive_meaning native_decomposition_system"
  obtains H where "development_decomposition_application C p I H"
    "obligation_reduction {p} (development_problem_stated names C') (development_problem_stated names C')
      (\<lambda>_. fset H)"
proof -
  have "I\<noteq>[]" using holds native_decomposition_applies[OF p xf] by blast
  obtain c where c: "problem_subject p={|c|}" by (rule development_rows_problem[OF present p])
  have "\<exists>H. development_decomposition_application C p I H"
    by (rule development_decomposition_application_exists)
      (use c state in \<open>simp_all add: development_state_poses_def\<close>)
  then obtain H where "development_decomposition_application C p I H" by blast
  then show ?thesis using that development_decomposition_reduction by blast
qed

end

end
