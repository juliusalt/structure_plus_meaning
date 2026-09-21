theory Development_Located_Rows
imports Development_Rows
begin

section \<open>The value asked is the value found\<close>

text \<open>
  A search of a path store checks the value it finds in a context (@{locale native_store_search_program}).
  Asking which value a store holds at a locus is that search whose context is the value asked and whose
  check is equality: one rule, whose conclusion is a pair of one variable with itself and which has no
  premise. It compares the two values only for equality, through the variable that occurs twice, and
  reads nothing inside them.
\<close>

definition native_value_rule :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_value_rule=finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 0)) []"

declare native_value_rule_def [code_unfold]

locale native_value_program = native_rule_family P ch "[([0],native_value_rule)]"
  for P :: "'u native_system" and ch :: "'u definition_site"
begin

theorem exact: "(ch,Pair_Term x y)\<in>positive_meaning P \<longleftrightarrow> term_formed x \<and> x=y"
proof
  assume holds: "(ch,Pair_Term x y)\<in>positive_meaning P"
  have "x=y"
    by (rule holds_cases[OF holds]) (simp add: native_value_rule_def, metis)
  then show "term_formed x \<and> x=y" using holds_formed[OF holds] by simp
next
  assume given: "term_formed x \<and> x=y"
  then have xf: "term_formed x" and xy: "x=y" by blast+
  have "(ch,evaluate_pattern (\<lambda>_. x) (decode_finite_pattern
      (Finite_Pattern_Pair (native_var 0) (native_var 0))))\<in>positive_meaning P"
    by (rule native_step[where c="[0]" and p="Finite_Pattern_Pair (native_var 0) (native_var 0)" and ps="[]"])
      (use xf in \<open>simp_all add: native_value_rule_def\<close>)
  then show "(ch,Pair_Term x y)\<in>positive_meaning P" using xy by simp
qed

end

section \<open>The development's store and its one search\<close>

text \<open>
  The development's store is the path store of its rows (@{const development_rows_present}), and one
  search reads it: the search of the path store (@{locale native_store_search_program}) installed at its own site, whose check is
  the value rule above at a second site. A row stands at a locus and the locus alone selects it: the
  role and the kind are prefixes of the path the search descends, so no program selects a family,
  compares a kind or a role, or reads a name.

  A native call's argument is formed, so the store is presented with each value formed: a formed value
  is presented as itself, and the one shape a native program cannot hold is presented as the empty
  payload. Every body the presentation stores is formed, so for those the presentation is the value
  itself; whether every row's value is formed is a question about the presentation relation, and this
  theory asks it of no row but the one it reads.
\<close>

abbreviation development_row_search :: "local_address option definition_site" where
  "development_row_search \<equiv> (Some [],[1])"

abbreviation development_row_check :: "local_address option definition_site" where
  "development_row_check \<equiv> (Some [],[2])"

definition development_row_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "development_row_definitions=[(development_row_search,native_store_search_rules development_row_search development_row_check),
    (development_row_check,[([0],native_value_rule)])]"

definition finite_development_rows_program :: "local_address option finite_native_system" where
  "finite_development_rows_program=finite_rule_program development_row_definitions"

definition development_rows_program :: "local_address option native_system" where
  "development_rows_program=decode_finite_system finite_development_rows_program"

lemma finite_development_rows_program_formed: "finite_system_formed finite_development_rows_program"
  by code_simp

lemma development_rows_program_formed: "schema_system_formed development_rows_program"
  using finite_development_rows_program_formed
  by (simp only: development_rows_program_def finite_system_formed_correct)

lemma development_rows_family:
  assumes member: "(d,rs)\<in>set development_row_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family development_rows_program d rs"
proof (rule native_rule_family.intro)
  show "schema_system_formed development_rows_program" by (rule development_rows_program_formed)
  have distinct: "distinct (map fst development_row_definitions)" by (simp add: development_row_definitions_def)
  show "((d,c),S)\<in>system_clauses development_rows_program \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F)" for c S
  proof -
    have "((d,c),S)\<in>system_clauses development_rows_program \<longleftrightarrow>
        (\<exists>rs'. (d,rs')\<in>set development_row_definitions \<and> (\<exists>F. (c,F)\<in>set rs' \<and> S=decode_finite_schema F))"
      unfolding development_rows_program_def finite_development_rows_program_def by (rule finite_rule_program_clause)
    then show ?thesis using eq_key_imp_eq_value[OF distinct member] member by blast
  qed
  have site: "d\<in>fst ` set development_row_definitions" using member by (rule rev_image_eqI) simp
  show "schema_call_formed development_rows_program d t \<longleftrightarrow> term_formed t" for t
    unfolding development_rows_program_def finite_development_rows_program_def
    by (rule finite_rule_program_call[OF development_rows_program_formed[unfolded development_rows_program_def
      finite_development_rows_program_def] site])
  show "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}" by (rule plain)
qed

interpretation development_row_searches: native_store_search_program development_rows_program
    development_row_search development_row_check
  unfolding native_store_search_program_def by (rule development_rows_family)
    (simp_all add: development_row_definitions_def native_store_search_rules_def native_store_found_rule_def
      native_store_left_rule_def native_store_right_rule_def)

interpretation development_row_checks: native_value_program development_rows_program development_row_check
  unfolding native_value_program_def by (rule development_rows_family)
    (simp_all add: development_row_definitions_def native_value_rule_def)

definition development_row_value :: "factor_term \<Rightarrow> factor_term" where
  "development_row_value y=(if term_formed y then y else Payload_Term [])"

lemma development_row_value_formed: "term_formed (development_row_value y)"
  by (simp add: development_row_value_def octets_formed_def)

lemma development_row_value_at: "term_formed y \<Longrightarrow> development_row_value y=y"
  by (simp add: development_row_value_def)

definition development_rows_term :: "development_store_rows \<Rightarrow> factor_term" where
  "development_rows_term rows=store_term development_row_value (path_store rows)"

text \<open>
  On a single-valued store the search holds at a locus of exactly the value its row holds there: the
  search's own contract (@{thm development_row_searches.exact}) and the store's lookup
  (@{thm path_store_lookup}) compose, neither restated.
\<close>

theorem development_row_lookup_at:
  "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow>
    term_formed v \<and> (\<exists>w. store_lookup (path_store rows) l=Some w \<and> v=development_row_value w)"
proof -
  have "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow>
    term_formed v \<and> (\<exists>bs w. path_term l=path_term bs \<and> store_lookup (path_store rows) bs=Some w \<and>
      (development_row_check,Pair_Term v (development_row_value w))\<in>positive_meaning development_rows_program)"
    unfolding development_rows_term_def by (rule development_row_searches.exact) (rule development_row_value_formed)
  also have "\<dots> \<longleftrightarrow> term_formed v \<and> (\<exists>w. store_lookup (path_store rows) l=Some w \<and> v=development_row_value w)"
    by (simp only: path_term_injective development_row_checks.exact) blast
  finally show ?thesis .
qed

theorem development_row_at:
  assumes sv: "single_valued (set rows)"
  shows "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow>
    term_formed v \<and> (\<exists>w. (l,w)\<in>set rows \<and> v=development_row_value w)"
proof -
  have "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow>
    term_formed v \<and> (\<exists>bs w. path_term l=path_term bs \<and> store_lookup (path_store rows) bs=Some w \<and>
      (development_row_check,Pair_Term v (development_row_value w))\<in>positive_meaning development_rows_program)"
    unfolding development_rows_term_def by (rule development_row_searches.exact) (rule development_row_value_formed)
  also have "\<dots> \<longleftrightarrow> term_formed v \<and> (\<exists>w. (l,w)\<in>set rows \<and> v=development_row_value w)"
    by (simp only: path_term_injective path_store_lookup[OF sv] development_row_checks.exact) blast
  finally show ?thesis .
qed

section \<open>The request at a locus\<close>

lemma development_row_family_formed: "term_formed (development_row_family ls)"
  by (induct ls) (simp_all add: development_row_family_def octets_formed_def)

lemma development_request_body_formed: "term_formed (development_request_body S E)"
  by (simp add: development_request_body_def development_row_family_formed)

text \<open>
  The request of a problem is the value the store holds at the problem's locus under the request's role
  prefix: the search holds there of that request and of no other value. "The single request of that
  subject" is the lookup's functionality under single-valuedness, which is the locus's own "at most one":
  no name is looked up, no position of a name table is read and no list is filtered.
\<close>

theorem development_request_at:
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and r: "r\<in>set rs"
  shows "(development_row_search,Pair_Term v (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
      (development_rows_term rows)))\<in>positive_meaning development_rows_program \<longleftrightarrow>
    v=development_request_body (supported r) (scope r)"
proof -
  have look: "store_lookup (path_store rows) (development_located_at key Development_Request_Role (fst r))=
      Some (development_request_body (supported r) (scope r))"
    by (rule development_rows_request(5)[OF present r])
  have formed: "term_formed (development_request_body (supported r) (scope r))"
    by (rule development_request_body_formed)
  show ?thesis
    unfolding development_row_lookup_at look option.inject
    using formed development_row_value_at[OF formed] by auto
qed

text \<open>
  A problem and its request stand at one locus under two role prefixes: the request's locus is the
  request's role prefix followed by what follows the role in the problem's locus.
\<close>

corollary development_request_problem_locus:
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and p: "p\<in>set ps"
  shows "development_located_at key Development_Request_Role p=
    development_role_path Development_Request_Role @ drop 3 (development_located_at key Development_Problem_Role p)"
proof -
  obtain c where c: "problem_subject p={|c|}" by (rule development_rows_problem[OF present p])
  have "development_locus key Development_Request_Role (problem_contract p) c=
      take 3 (development_locus key Development_Request_Role (problem_contract p) c) @
      drop 3 (development_locus key Development_Request_Role (problem_contract p) c)"
    by (rule append_take_drop_id[symmetric])
  also have "\<dots>=development_role_path Development_Request_Role @
      drop 3 (development_locus key Development_Problem_Role (problem_contract p) c)"
    by (simp only: development_locus_parts(1)
      development_locus_shared_tail[of key Development_Request_Role "problem_contract p" c Development_Problem_Role])
  finally show ?thesis by (simp only: development_located_at_subject[OF c])
qed

end
