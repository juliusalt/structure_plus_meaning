theory Development_Located_Rows
imports Development_Rows Factor_Native_Equality Factor_System_Relocation
begin

section \<open>The development's store and its one search\<close>

text \<open>
  The development's store is the path store of its rows (@{const development_rows_present}), and one
  search reads it: the search of the path store (@{locale native_store_search_program}) installed at its
  own site, whose check is equality at a second site. Asking which value a store holds at a locus is that
  search whose context is the value asked: the check compares the two values only for equality and reads
  nothing inside them. A row stands at a locus and the locus alone selects it: the role and the kind are
  prefixes of the path the search descends, so no program selects a family, compares a kind or a role, or
  reads a name. The two sites are the program's own: native readiness holds its definitions at other
  sites, so the two programs can be joined in one system.

  The store presents each row's value as itself. Every row value is formed by the presentation relation
  (@{thm development_rows_formed}), which is a premise owned by whoever presents a state.
\<close>

definition native_value_rule :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_value_rule=finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 0)) []"

declare native_value_rule_def [code_unfold]

text \<open>
  The value rule's contract is stated once, here: a site whose family is the value rule holds of a pair exactly
  when its two components are one formed term. It is the family's law (@{locale native_rule_law}) at the one rule
  without premise; every site of the rule is an instance of this program.
\<close>

locale native_value_program = native_rule_family P d "[([0],native_value_rule)]"
  for P :: "'u native_system" and d :: "'u definition_site"
begin

sublocale law: native_rule_law P d "[([0],native_value_rule)]"
  by (rule native_rule_lawI[OF native_rule_family_axioms]) (auto simp: native_value_rule_def)

theorem exact: "(d,Pair_Term x y)\<in>positive_meaning P \<longleftrightarrow> term_formed x \<and> x=y"
proof
  assume "(d,Pair_Term x y)\<in>positive_meaning P"
  then obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set [([0]::local_address,
      native_value_rule::(local_address,local_address,'u definition_site) finite_factor_schema)]"
    and formed: "\<forall>a\<in>pattern_variables (decode_finite_pattern p). term_formed (f a)"
    and evaluated: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x y"
    unfolding law.exact by (elim exE conjE) (rule that; assumption)
  from rule have p: "p=Finite_Pattern_Pair (native_var 0) (native_var 0)"
    by (simp add: native_value_rule_def finite_native_rule_eq_iff)
  show "term_formed x \<and> x=y" using formed evaluated by (auto simp: p)
next
  assume formed: "term_formed x \<and> x=y"
  show "(d,Pair_Term x y)\<in>positive_meaning P"
    unfolding law.exact
    by (rule exI[of _ "[0]"], rule exI[of _ "Finite_Pattern_Pair (native_var 0) (native_var 0)"],
      rule exI[of _ "[]"], rule exI[of _ "\<lambda>_. x"]) (use formed in \<open>auto simp: native_value_rule_def\<close>)
qed

end

abbreviation development_row_search :: "local_address option definition_site" where
  "development_row_search \<equiv> (Some [],[8])"

abbreviation development_row_check :: "local_address option definition_site" where
  "development_row_check \<equiv> (Some [],[9])"

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
  unfolding development_rows_program_def finite_development_rows_program_def
  by (rule finite_rule_program_family[OF development_rows_program_formed[unfolded development_rows_program_def
    finite_development_rows_program_def] _ member plain]) (simp add: development_row_definitions_def)

interpretation development_row_searches: native_store_search_program development_rows_program
    development_row_search development_row_check
  unfolding native_store_search_program_def by (rule development_rows_family)
    (simp_all add: development_row_definitions_def native_store_search_rules_def native_store_found_rule_def
      native_store_left_rule_def native_store_right_rule_def)

section \<open>The check is the value rule's program\<close>

text \<open>
  The check's family is the value rule, so its meaning is the value rule's program's
  (@{locale native_value_program}): no argument about equality is made again here.
\<close>

interpretation development_row_checks: native_value_program development_rows_program development_row_check
  unfolding native_value_program_def by (rule development_rows_family)
    (simp_all add: development_row_definitions_def native_value_rule_def)

theorem development_row_check_exact:
  "(development_row_check,Pair_Term x y)\<in>positive_meaning development_rows_program \<longleftrightarrow> term_formed x \<and> x=y"
  by (rule development_row_checks.exact)

section \<open>The value asked is the value found\<close>

text \<open>
  A store presented by the identity holds formed values exactly where its rows do, which is all the
  search's contract asks of it (@{thm development_row_searches.exact_held}).
\<close>

definition development_rows_term :: "development_store_rows \<Rightarrow> factor_term" where
  "development_rows_term rows=store_term id (path_store rows)"

text \<open>
  On formed rows the search holds at a locus of exactly the value the store holds there: the search's
  own contract (@{thm development_row_searches.exact_held}) and the check's compose, neither restated. On a
  single-valued store that is the value its row holds (the path store's index,
  @{thm [source] path_store_carrier_index}).
\<close>

theorem development_row_lookup_at:
  assumes formed: "\<forall>(l,w)\<in>set rows. term_formed w"
  shows "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow> store_lookup (path_store rows) l=Some v"
proof -
  have stored: "term_formed (id w)" if "store_lookup (path_store rows) bs=Some w" for bs w
    using path_store_found[OF that] formed by (simp only: id_apply) blast
  have "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow>
    term_formed v \<and> (\<exists>bs w. path_term l=path_term bs \<and> store_lookup (path_store rows) bs=Some w \<and>
      (development_row_check,Pair_Term v (id w))\<in>positive_meaning development_rows_program)"
    unfolding development_rows_term_def by (rule development_row_searches.exact_held) (rule stored)
  also have "\<dots> \<longleftrightarrow> store_lookup (path_store rows) l=Some v"
  proof
    assume "term_formed v \<and> (\<exists>bs w. path_term l=path_term bs \<and> store_lookup (path_store rows) bs=Some w \<and>
      (development_row_check,Pair_Term v (id w))\<in>positive_meaning development_rows_program)"
    then obtain bs w where key: "path_term l=path_term bs" and found: "store_lookup (path_store rows) bs=Some w"
      and checked: "(development_row_check,Pair_Term v (id w))\<in>positive_meaning development_rows_program" by blast
    have "l=bs" using key by (simp only: path_term_injective)
    moreover have "v=id w" using checked by (simp only: development_row_check_exact)
    ultimately show "store_lookup (path_store rows) l=Some v" using found by simp
  next
    assume found: "store_lookup (path_store rows) l=Some v"
    have formed_v: "term_formed v" using stored[OF found] by (simp only: id_apply)
    then have "(development_row_check,Pair_Term v (id v))\<in>positive_meaning development_rows_program"
      by (simp add: development_row_check_exact)
    then show "term_formed v \<and> (\<exists>bs w. path_term l=path_term bs \<and> store_lookup (path_store rows) bs=Some w \<and>
      (development_row_check,Pair_Term v (id w))\<in>positive_meaning development_rows_program)"
      using found formed_v by blast
  qed
  finally show ?thesis .
qed

theorem development_row_at:
  assumes sv: "single_valued (set rows)" and formed: "\<forall>(l,w)\<in>set rows. term_formed w"
  shows "(development_row_search,Pair_Term v (Pair_Term (path_term l) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program \<longleftrightarrow> (l,v)\<in>set rows"
  by (simp only: development_row_lookup_at[OF formed]
    carrier_index.query_search[OF path_store_carrier_index sv UNIV_I, simplified id_apply])

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
  show ?thesis
    unfolding development_row_lookup_at[OF development_rows_formed[OF present]] look by auto
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
