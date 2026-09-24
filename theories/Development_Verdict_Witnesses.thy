theory Development_Verdict_Witnesses
  imports Development_Verdict_Mentions
begin

section \<open>The reasons a refusal carries\<close>

text \<open>
  Acceptance is positive and needs no absence: every field of it is an \<open>every\<close> or a \<open>some\<close> with
  membership decided by a search, and the fields of tasks 34, 36, 38 and 40 are built so. A refusal,
  though, must say which rows and which constants offend, and that is the other side: for each field
  whose acceptance reads "the list is empty", a relation that holds of exactly the members of that
  list. The two are dual positive programs; neither is defined as the other's negation, and no field
  is redefined through its witness. Each witness below states exactly its HOL list of
  \<^const>\<open>development_constant_verdict\<close>, and each consumes its field's contract rather than proving it
  again.

  The witnesses need what acceptance did not: absence, which \<open>Native_Path_Stores\<close> now supplies as the
  other half of its search (\<open>native_store_absent_program\<close>), positive, descending a path by its bits'
  shapes and comparing no keys. \<open>excess\<close> comes first, because \<^const>\<open>development_refinement_repair\<close>
  reads \<^const>\<open>development_verdict_excess\<close> to derive the request's extension and is the one consumer a
  witness has today. It is read over the subject index of task 138, as \<open>excess\<close> itself is: the fibre at
  the subject's key, and for each of its rows the mentions the support store does not hold. No witness
  reads a row that is not about the subject it is asked at.
\<close>

section \<open>A \<open>some\<close> reading of the rows about a key\<close>

text \<open>
  The index of a family by a key reading is read with an \<open>every\<close> checker where a field asks that every
  row about the key satisfy a reading (\<open>key_index_program\<close>, \<open>key_selection_program\<close>). A witness asks
  the opposite question of the same index: whether \<^emph>\<open>some\<close> row about the key offends. That is the index's
  reading (\<open>key_index_reading\<close>) at the other checker, the family's \<open>some\<close>-reading
  (\<open>family_some_reading\<close>), and the selection's call is the one call locale (\<open>subject_call_program\<close>)
  both selection readings extend. Nothing of the index or of the call is established again.
\<close>

lemma index_term_formed:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "term_formed (key_index_term rd ident A F)"
  unfolding key_index_term_def
  by (rule store_term_formed) (rule state_family_term_formed[OF identity])

locale key_index_some_program = search: native_store_search_program P kx ch +
    family: family_some_reading P ch r present ident reads
  for P :: "'u native_system" and kx ch r :: "'u definition_site" and present
    and ident :: "'i \<Rightarrow> factor_term" and reads +
  fixes rd :: "'i state_row \<Rightarrow> state_key list"
begin

sublocale reading: key_index_reading P kx ch present ident "\<lambda>c F. \<exists>z\<in>set F. reads c z" rd
  by unfold_locales (simp_all add: family.identity family.exact)

theorem exact:
  "(kx,Pair_Term (present c) (Pair_Term (path_term a) (key_index_term rd ident A F)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> a\<in>set A \<and> (\<exists>z\<in>set F. a\<in>set (rd (snd z)) \<and> reads c z)"
  by (simp add: reading.fibre_exact Bex_def key_fibre_member conj_assoc)

end

locale key_selection_some_program = index: key_index_some_program P kx ch r present ident reads rd +
    call: subject_call_program P g kx + some: native_some_program P s g
  for P :: "'u native_system" and s g kx ch r :: "'u definition_site" and present ident reads rd
begin

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (present c)) (key_indexes_term rd ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. a\<in>set (rd (snd z)) \<and> reads c z)"
proof -
  have formed: "\<And>F. term_formed (key_index_term rd ident A F)"
    by (rule index_term_formed) (rule index.family.identity)
  show ?thesis
    using some.exact[of "Pair_Term (path_term a) (present c)" "map (key_index_term rd ident A) Fs"]
    by (auto simp: key_indexes_term_def formed call.call_exact index.exact atom)
qed

end

section \<open>The witnesses' own program\<close>

text \<open>
  The sites are its own. Store absence, membership, a row's mentions, the \<open>some\<close>-readings of a family
  and of a selection, the subject index searched with the \<open>some\<close>-reading, and one rule per witness.
  The program compares no key with another and states no octet but the empty payload.
\<close>

abbreviation witness_absent :: "local_address option definition_site" where
  "witness_absent \<equiv> (Some [],[90])"

abbreviation witness_member :: "local_address option definition_site" where
  "witness_member \<equiv> (Some [],[91])"

abbreviation witness_row_mentions :: "local_address option definition_site" where
  "witness_row_mentions \<equiv> (Some [],[92])"

abbreviation witness_family_some :: "local_address option definition_site" where
  "witness_family_some \<equiv> (Some [],[93])"

abbreviation witness_selection_some :: "local_address option definition_site" where
  "witness_selection_some \<equiv> (Some [],[94])"

abbreviation witness_index_search :: "local_address option definition_site" where
  "witness_index_search \<equiv> (Some [],[95])"

abbreviation witness_index_call :: "local_address option definition_site" where
  "witness_index_call \<equiv> (Some [],[96])"

abbreviation witness_index_some :: "local_address option definition_site" where
  "witness_index_some \<equiv> (Some [],[97])"

abbreviation witness_excess :: "local_address option definition_site" where
  "witness_excess \<equiv> (Some [],[98])"

abbreviation witness_undeclared :: "local_address option definition_site" where
  "witness_undeclared \<equiv> (Some [],[99])"

abbreviation witness_malformed :: "local_address option definition_site" where
  "witness_malformed \<equiv> (Some [],[100])"

text \<open>
  A constant is excess when the support store holds it nowhere and some row about the subject mentions
  it. The two premises read the two parts the field reads, and nothing else.
\<close>

definition excess_witness_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "excess_witness_rule=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))
    [([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
       (Finite_Pattern_Pair (native_var 3) (native_var 1)))),
     ([1],(witness_index_some,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 3))
       (native_var 2)))]"

text \<open>
  A constant is undeclared when the declaration store holds it nowhere and some row, or some root,
  mentions it: two rules of one site, the disjunction positive.
\<close>

definition undeclared_witness_row_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "undeclared_witness_row_rule=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))
    [([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
       (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
     ([1],(witness_selection_some,Finite_Pattern_Pair (native_var 3) (native_var 1)))]"

definition undeclared_witness_root_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "undeclared_witness_root_rule=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))
    [([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
       (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
     ([1],(witness_family_some,Finite_Pattern_Pair (native_var 3) (native_var 2)))]"

text \<open>
  A row is malformed when it declares nothing and is a statement of nothing: two empty citation
  lists, a shape and no octet. Which families are visited says the rest, as the field's own reading
  does: the specification family is not among them.
\<close>

definition malformed_witness_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "malformed_witness_rule=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])
      (native_var 2) (native_var 3)) []"

definition verdict_witness_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "verdict_witness_definitions=[
    (witness_absent,native_store_absent_rules witness_absent),
    (witness_member,native_member_rules witness_member),
    (witness_row_mentions,[([0],row_mentions_rule witness_member)]),
    (witness_family_some,native_some_rules witness_family_some witness_row_mentions),
    (witness_selection_some,native_some_rules witness_selection_some witness_family_some),
    (witness_index_search,native_store_search_rules witness_index_search witness_family_some),
    (witness_index_call,[([0],subject_call_rule witness_index_search)]),
    (witness_index_some,native_some_rules witness_index_some witness_index_call),
    (witness_excess,[([0],excess_witness_rule)]),
    (witness_undeclared,[([0],undeclared_witness_row_rule),([1],undeclared_witness_root_rule)]),
    (witness_malformed,[([0],malformed_witness_rule)])]"

definition finite_verdict_witnesses :: "local_address option finite_native_system" where
  "finite_verdict_witnesses=finite_rule_program verdict_witness_definitions"

definition verdict_witness_system :: "local_address option native_system" where
  "verdict_witness_system=decode_finite_system finite_verdict_witnesses"

lemma finite_verdict_witnesses_formed: "finite_system_formed finite_verdict_witnesses"
  by code_simp

lemma verdict_witness_formed: "schema_system_formed verdict_witness_system"
  using finite_verdict_witnesses_formed
  by (simp only: verdict_witness_system_def finite_system_formed_correct)

lemma verdict_witness_family:
  assumes member: "(d,rs)\<in>set verdict_witness_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family verdict_witness_system d rs"
proof -
  have distinct: "distinct (map fst verdict_witness_definitions)"
    by (simp add: verdict_witness_definitions_def)
  show ?thesis
    using finite_rule_program_family[OF verdict_witness_formed[unfolded verdict_witness_system_def
      finite_verdict_witnesses_def] distinct member plain]
    by (simp add: verdict_witness_system_def finite_verdict_witnesses_def)
qed

lemmas verdict_witness_rule_defs = verdict_witness_definitions_def native_store_absent_rules_def
  native_absent_empty_rule_def native_absent_none_rule_def native_absent_left_leaf_rule_def
  native_absent_left_rule_def native_absent_right_leaf_rule_def native_absent_right_rule_def
  native_member_rules_def native_member_here_def native_member_later_def native_some_rules_def
  native_some_first_def native_some_rest_def native_store_search_rules_def native_store_found_rule_def
  native_store_left_rule_def native_store_right_rule_def row_mentions_rule_def subject_call_rule_def
  excess_witness_rule_def undeclared_witness_row_rule_def undeclared_witness_root_rule_def
  malformed_witness_rule_def

interpretation witness_absences: native_store_absent_program verdict_witness_system witness_absent
  unfolding native_store_absent_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

interpretation witness_members: native_member_program verdict_witness_system witness_member
  unfolding native_member_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

interpretation witness_family_somes: native_some_program verdict_witness_system witness_family_some
    witness_row_mentions
  unfolding native_some_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

interpretation witness_selection_somes: native_some_program verdict_witness_system
    witness_selection_some witness_family_some
  unfolding native_some_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

interpretation witness_index_searches: native_store_search_program verdict_witness_system
    witness_index_search witness_family_some
  unfolding native_store_search_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

text \<open>
  The row reading every witness uses: the key the call carries is among the keys the row mentions. It
  is \<open>row_mentions_rule\<close> with a membership callee, and that rule is one rearrangement of its
  conclusion's variables, so the existing rearranging program supplies its law.
\<close>

interpretation witness_mentions: native_rearranging_program verdict_witness_system witness_row_mentions
    "row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)"
    witness_member "Finite_Pattern_Pair (native_var 0) (native_var 4)"
proof (rule native_rearranging_program.intro)
  show "native_rule_family verdict_witness_system witness_row_mentions
      [([0],finite_native_rule (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3)
        (native_var 4) (native_var 5))
        [([0],(witness_member,Finite_Pattern_Pair (native_var 0) (native_var 4)))])]"
    by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)
next
  show "native_rearranging_program_axioms
      (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
      (Finite_Pattern_Pair (native_var 0) (native_var 4))"
    unfolding native_rearranging_program_axioms_def row_pattern_variables by simp
qed

interpretation witness_index_calls: subject_call_program verdict_witness_system witness_index_call
    witness_index_search
  unfolding subject_call_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

interpretation witness_index_somes: native_some_program verdict_witness_system witness_index_some
    witness_index_call
  unfolding native_some_program_def by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)

lemma witness_mentioned_rows:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(witness_row_mentions,Pair_Term (path_term d) (state_row_term ident z))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> d\<in>set (row_mentions (snd z))"
proof -
  let ?f="native_values [path_term d,path_term (fst z),keys_term (row_declared (snd z)),
    keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))]"
  have member: "(witness_member,Pair_Term (path_term d) (keys_term (row_mentions (snd z))))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> d\<in>set (row_mentions (snd z))"
    using witness_members.exact[of "path_term d" "map path_term (row_mentions (snd z))"]
    by (auto simp: keys_term_def path_term_injective)
  show ?thesis
    using witness_mentions.at[of ?f]
    by (auto simp: row_pattern_def state_row_term_def member identity)
qed

section \<open>The witness of \<open>excess\<close>\<close>

text \<open>
  The rule reads the subject's key, the support store and the indexes of the replaceable families, and
  holds of the key of a constant the support store does not hold that some row about the subject
  mentions.
\<close>

interpretation excess_witness_family: native_rule_law verdict_witness_system witness_excess
    "[([0],excess_witness_rule)]"
proof (rule native_rule_lawI)
  show "native_rule_family verdict_witness_system witness_excess [([0],excess_witness_rule)]"
    by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)
next
  fix c F assume "(c,F)\<in>set [([0]::local_address,excess_witness_rule)]"
  then show "\<exists>p ps. F=finite_native_rule p ps" by (auto simp: excess_witness_rule_def)
qed

lemma excess_witness_at:
  "(witness_excess,Pair_Term (Pair_Term K (Pair_Term SS IX)) D)\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (witness_absent,Pair_Term D (Pair_Term D SS))\<in>positive_meaning verdict_witness_system \<and>
    (witness_index_some,Pair_Term (Pair_Term K D) IX)\<in>positive_meaning verdict_witness_system"
proof
  assume holds: "(witness_excess,Pair_Term (Pair_Term K (Pair_Term SS IX)) D)\<in>positive_meaning verdict_witness_system"
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set [([0]::local_address,excess_witness_rule)]"
    and concl: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term (Pair_Term K (Pair_Term SS IX)) D"
    and prem: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning verdict_witness_system"
    by (rule excess_witness_family.holds_rule[OF holds]) blast
  have F: "finite_native_rule p ps=excess_witness_rule" using rule by simp
  then have p: "p=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3)"
    and ps: "set ps={([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
         (Finite_Pattern_Pair (native_var 3) (native_var 1)))),
       ([1],(witness_index_some,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 3))
         (native_var 2)))}"
    by (simp_all add: excess_witness_rule_def finite_native_rule_eq_iff)
  have vals: "f [0]=K" "f [Suc 0]=SS" "f [2]=IX" "f [3]=D" using concl by (simp_all add: p)
  show "(witness_absent,Pair_Term D (Pair_Term D SS))\<in>positive_meaning verdict_witness_system \<and>
      (witness_index_some,Pair_Term (Pair_Term K D) IX)\<in>positive_meaning verdict_witness_system"
    using prem by (simp add: ps vals)
next
  assume given: "(witness_absent,Pair_Term D (Pair_Term D SS))\<in>positive_meaning verdict_witness_system \<and>
    (witness_index_some,Pair_Term (Pair_Term K D) IX)\<in>positive_meaning verdict_witness_system"
  have "(witness_excess,evaluate_pattern (native_values [K,SS,IX,D]) (decode_finite_pattern
      (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))))\<in>positive_meaning verdict_witness_system"
    by (rule excess_witness_family.step_at[where c="[0]" and ps="[([0],(witness_absent,
        Finite_Pattern_Pair (native_var 3) (Finite_Pattern_Pair (native_var 3) (native_var 1)))),
      ([1],(witness_index_some,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 3))
        (native_var 2)))]"])
      (use given in \<open>simp_all add: excess_witness_rule_def\<close>)
  then show "(witness_excess,Pair_Term (Pair_Term K (Pair_Term SS IX)) D)\<in>positive_meaning verdict_witness_system"
    by simp
qed

text \<open>
  The rows contract: over the rows about the subject's key alone, and the support store read by
  absence. The premise \<open>k\<in>set A\<close> is the one the index reads, as the field's own rows contract has it.
\<close>

theorem native_excess_witness_rows:
  assumes identity: "\<And>y. term_formed (ident y)" and atom: "k\<in>set A"
  shows "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ss)
      (subject_indexes_term ident A Fs))) (path_term d))\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<notin>set ss \<and> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. k\<in>set (row_subjects (snd z)) \<and> d\<in>set (row_mentions (snd z)))"
proof -
  interpret indexes: key_selection_some_program verdict_witness_system witness_index_some
      witness_index_call witness_index_search witness_family_some witness_row_mentions
      path_term ident "\<lambda>d z. d\<in>set (row_mentions (snd z))" row_subjects
    by unfold_locales (simp_all add: identity witness_mentioned_rows[where ident=ident,OF identity])
  have absence: "(witness_absent,Pair_Term (path_term d) (Pair_Term (path_term d) (support_term ss)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> d\<notin>set ss"
    using witness_absences.exact_at_path[of path_term "path_term d" d "support_store ss"]
      support_store_lookup[of ss d] by (auto simp: support_term_def)
  show ?thesis
    by (simp only: excess_witness_at absence indexes.exact[OF atom])
      (simp add: identity)
qed

text \<open>
  The contract: exactly the constants of \<^const>\<open>development_answer_statements_excess\<close>, the field's own
  HOL list. The field's positive contract is untouched; this states the members of the list whose
  emptiness that contract states.
\<close>

lemma answer_statements_excess_member:
  "d\<in>set (development_answer_statements_excess kind C P S) \<longleftrightarrow> d |\<notin>| S \<and>
    (\<exists>e\<in>set (development_answer_statements kind C P). d\<in>set (entity_mentions e))"
proof -
  have "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)) \<longleftrightarrow>
      (\<exists>e\<in>set L. d\<in>set (entity_mentions e))" for L
  proof
    assume "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L))"
    then obtain l where listed: "l\<in>set (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)"
      and inside: "d\<in>set l" by auto
    obtain e where member: "e\<in>set L"
      and read: "(map_option isabelle_term_constants \<circ> isabelle_specified_proposition) e=Some l"
      using listed by (simp only: map_filter_member) blast
    obtain q where statement: "isabelle_specified_proposition e=Some q"
      and constants: "l=isabelle_term_constants q"
      using read by (auto simp: map_option_eq_Some)
    have "d\<in>set (entity_mentions e)"
      using inside constants statement by (simp add: entity_mentions_def)
    then show "\<exists>e\<in>set L. d\<in>set (entity_mentions e)" using member by blast
  next
    assume "\<exists>e\<in>set L. d\<in>set (entity_mentions e)"
    then obtain e where member: "e\<in>set L" and inside: "d\<in>set (entity_mentions e)" by blast
    obtain q where statement: "isabelle_specified_proposition e=Some q"
      and constants: "d\<in>set (isabelle_term_constants q)"
      using inside by (cases "isabelle_specified_proposition e") (simp_all add: entity_mentions_def)
    have "(map_option isabelle_term_constants \<circ> isabelle_specified_proposition) e=Some (isabelle_term_constants q)"
      by (simp add: statement)
    then have "isabelle_term_constants q\<in>set (List.map_filter
        (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)"
      using member by (simp only: map_filter_member) blast
    then show "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L))"
      using constants by auto
  qed
  then show ?thesis by (simp add: development_answer_statements_excess_def; blast)
qed


theorem native_excess_witness_exact:
  assumes present: "state_presents key S R" and kinds: "kinds_present replaceable ks"
    and selection: "set Fs=state_entities R ` ks" and bound: "c<length (fst (snd S))"
    and dbound: "d<length (fst (snd S))"
    and support: "\<And>e. e<length (fst (snd S)) \<Longrightarrow> key e\<in>set ss \<longleftrightarrow> e |\<in>| X"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(witness_excess,Pair_Term (Pair_Term (path_term (key c)) (Pair_Term (support_term ss)
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))) (path_term (key d)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<in>set (development_answer_statements_excess replaceable (snd S) {|c|} X)"
proof -
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have rows: "(\<exists>F\<in>set Fs. \<exists>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<and> key d\<in>set (row_mentions (snd z))) \<longleftrightarrow>
      (\<exists>e\<in>set (development_answer_statements replaceable (snd S) {|c|}). d\<in>set (entity_mentions e))"
  proof -
    have "(\<exists>F\<in>set Fs. \<exists>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<and> key d\<in>set (row_mentions (snd z))) \<longleftrightarrow>
        (\<exists>F\<in>set Fs. \<exists>z\<in>set (subject_fibre (key c) F). key d\<in>set (row_mentions (snd z)))"
      by (simp add: Bex_def subject_fibre_member conj_assoc)
    also have "\<dots> \<longleftrightarrow> (\<exists>p\<in>(\<Union>F\<in>set Fs. snd ` set (subject_fibre (key c) F)). key d\<in>set (row_mentions p))"
      by blast
    also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (development_answer_statements replaceable (snd S) {|c|}). d\<in>set (entity_mentions e))"
      unfolding subject_fibre_statements[OF present kinds selection bound]
      using entity_row_mention_key[OF present dbound answer_statements_entities] by auto
    finally show ?thesis .
  qed
  have absent: "key d\<notin>set ss \<longleftrightarrow> d |\<notin>| X" using support[OF dbound] by simp
  show ?thesis
    by (simp only: native_excess_witness_rows[where ident=ident,OF identity atom] rows absent
      answer_statements_excess_member)
qed

text \<open>
  The two contracts stand apart: the field's says the list is empty, the witness's says which constants
  are in it. Neither is the other's negation; the equivalence below is derived from the two HOL sides,
  once, and is not a definition of either.
\<close>

corollary native_excess_no_witness:
  assumes present: "state_presents key S R" and kinds: "kinds_present replaceable ks"
    and selection: "set Fs=state_entities R ` ks" and bound: "c<length (fst (snd S))"
    and support: "\<And>e. e<length (fst (snd S)) \<Longrightarrow> key e\<in>set ss \<longleftrightarrow> e |\<in>| X"
    and identity: "\<And>y. term_formed (ident y)"
    and inside: "\<And>d. d\<in>set (development_answer_statements_excess replaceable (snd S) {|c|} X) \<Longrightarrow>
      d<length (fst (snd S))"
  shows "development_answer_statements_excess replaceable (snd S) {|c|} X=[] \<longleftrightarrow>
    (\<forall>d<length (fst (snd S)). (witness_excess,Pair_Term (Pair_Term (path_term (key c))
      (Pair_Term (support_term ss) (subject_indexes_term ident (map fst (state_atoms R)) Fs)))
      (path_term (key d)))\<notin>positive_meaning verdict_witness_system)"
proof
  assume empty: "development_answer_statements_excess replaceable (snd S) {|c|} X=[]"
  show "\<forall>d<length (fst (snd S)). (witness_excess,Pair_Term (Pair_Term (path_term (key c))
      (Pair_Term (support_term ss) (subject_indexes_term ident (map fst (state_atoms R)) Fs)))
      (path_term (key d)))\<notin>positive_meaning verdict_witness_system"
    using native_excess_witness_exact[where ident=ident,OF present kinds selection bound _ support identity] empty by simp
next
  assume none: "\<forall>d<length (fst (snd S)). (witness_excess,Pair_Term (Pair_Term (path_term (key c))
      (Pair_Term (support_term ss) (subject_indexes_term ident (map fst (state_atoms R)) Fs)))
      (path_term (key d)))\<notin>positive_meaning verdict_witness_system"
  show "development_answer_statements_excess replaceable (snd S) {|c|} X=[]"
  proof (rule ccontr)
    assume "development_answer_statements_excess replaceable (snd S) {|c|} X\<noteq>[]"
    then obtain d where member: "d\<in>set (development_answer_statements_excess replaceable (snd S) {|c|} X)"
      by (cases "development_answer_statements_excess replaceable (snd S) {|c|} X") auto
    show False
      using none inside[OF member] member
        native_excess_witness_exact[where ident=ident,OF present kinds selection bound inside[OF member] support identity]
      by blast
  qed
qed

text \<open>
  What the repair reads. \<^const>\<open>development_refinement_repair\<close> takes \<^const>\<open>development_verdict_excess\<close>
  of the refinement verdict and extends the request state by the material the answer state holds about
  those constants. That field is the list this witness states the members of.
\<close>

lemma development_verdict_excess_field:
  "development_verdict_excess (development_constant_verdict replaceable demanded S (p,s,support,E) S')=
    development_answer_statements_excess replaceable (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject p))
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) support)"
  by (simp add: development_verdict_excess_def development_constant_verdict_def Let_def)

text \<open>
  The witness at the request's presentation, the analogue of @{thm [source] native_excess_answer}: the
  subject and the support carried to the answer state by the one discharge the field reads
  (@{thm [source] request_answer_subject}), the witness then states exactly the members of the verdict's
  own list at every key of the answer state. This is the lemma a native repair consumes.
\<close>

corollary native_excess_witness_answer:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and named: "(!) (fst (snd S)) ` fset (problem_subject (fst r))\<subseteq>set (fst (snd S'))"
    and kinds: "kinds_present replaceable kinds" and selection: "set Fs=state_entities R' ` kinds"
    and dbound: "d<length (fst (snd S'))" and identity: "\<And>y. term_formed (ident y)"
  shows "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident (map fst (state_atoms R')) Fs))) (path_term (key' d)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<in>set (development_verdict_excess (development_constant_verdict replaceable demanded S r S'))"
proof -
  obtain c where image: "fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject (fst r))={|c|}"
    and k: "k=key' c" and bound: "c<length (fst (snd S'))"
    and support: "\<And>q. q<length (fst (snd S')) \<Longrightarrow> key' q\<in>set ks \<longleftrightarrow>
      q |\<in>| fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (fst (snd (snd r)))"
    by (rule request_answer_subject[OF request present' shared named]) blast
  have field: "development_verdict_excess (development_constant_verdict replaceable demanded S r S')=
      development_answer_statements_excess replaceable (snd S') {|c|}
        (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (fst (snd (snd r))))"
    using development_verdict_excess_field[of replaceable demanded S "fst r" "fst (snd r)"
      "fst (snd (snd r))" "snd (snd (snd r))" S'] image by simp
  show ?thesis
    unfolding k field by (rule native_excess_witness_exact[OF present' kinds selection bound dbound support identity])
qed

section \<open>The witness of \<open>undeclared\<close>\<close>

interpretation undeclared_witness_family: native_rule_law verdict_witness_system witness_undeclared
    "[([0],undeclared_witness_row_rule),([1],undeclared_witness_root_rule)]"
proof (rule native_rule_lawI)
  show "native_rule_family verdict_witness_system witness_undeclared
      [([0],undeclared_witness_row_rule),([1],undeclared_witness_root_rule)]"
    by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)
next
  fix c F assume "(c,F)\<in>set [([0]::local_address,undeclared_witness_row_rule),([1],undeclared_witness_root_rule)]"
  then show "\<exists>p ps. F=finite_native_rule p ps"
    by (auto simp: undeclared_witness_row_rule_def undeclared_witness_root_rule_def)
qed

lemma undeclared_witness_at:
  assumes fs: "term_formed FS" and rs: "term_formed RS"
  shows "(witness_undeclared,Pair_Term (Pair_Term DS (Pair_Term FS RS)) D)\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (witness_absent,Pair_Term D (Pair_Term D DS))\<in>positive_meaning verdict_witness_system \<and>
    ((witness_selection_some,Pair_Term D FS)\<in>positive_meaning verdict_witness_system \<or>
     (witness_family_some,Pair_Term D RS)\<in>positive_meaning verdict_witness_system)"
proof
  assume holds: "(witness_undeclared,Pair_Term (Pair_Term DS (Pair_Term FS RS)) D)\<in>positive_meaning verdict_witness_system"
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set
      [([0]::local_address,undeclared_witness_row_rule),([1],undeclared_witness_root_rule)]"
    and concl: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term (Pair_Term DS (Pair_Term FS RS)) D"
    and prem: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning verdict_witness_system"
    by (rule undeclared_witness_family.holds_rule[OF holds]) blast
  have cases: "finite_native_rule p ps=undeclared_witness_row_rule \<or>
      finite_native_rule p ps=undeclared_witness_root_rule" using rule by auto
  then show "(witness_absent,Pair_Term D (Pair_Term D DS))\<in>positive_meaning verdict_witness_system \<and>
      ((witness_selection_some,Pair_Term D FS)\<in>positive_meaning verdict_witness_system \<or>
       (witness_family_some,Pair_Term D RS)\<in>positive_meaning verdict_witness_system)"
  proof (elim disjE)
    assume F: "finite_native_rule p ps=undeclared_witness_row_rule"
    then have p: "p=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3)"
      and ps: "set ps={([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
           (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
         ([1],(witness_selection_some,Finite_Pattern_Pair (native_var 3) (native_var 1)))}"
      by (simp_all add: undeclared_witness_row_rule_def finite_native_rule_eq_iff)
    have vals: "f [0]=DS" "f [Suc 0]=FS" "f [2]=RS" "f [3]=D" using concl by (simp_all add: p)
    show ?thesis using prem by (simp add: ps vals)
  next
    assume F: "finite_native_rule p ps=undeclared_witness_root_rule"
    then have p: "p=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3)"
      and ps: "set ps={([0],(witness_absent,Finite_Pattern_Pair (native_var 3)
           (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
         ([1],(witness_family_some,Finite_Pattern_Pair (native_var 3) (native_var 2)))}"
      by (simp_all add: undeclared_witness_root_rule_def finite_native_rule_eq_iff)
    have vals: "f [0]=DS" "f [Suc 0]=FS" "f [2]=RS" "f [3]=D" using concl by (simp_all add: p)
    show ?thesis using prem by (simp add: ps vals)
  qed
next
  assume given: "(witness_absent,Pair_Term D (Pair_Term D DS))\<in>positive_meaning verdict_witness_system \<and>
    ((witness_selection_some,Pair_Term D FS)\<in>positive_meaning verdict_witness_system \<or>
     (witness_family_some,Pair_Term D RS)\<in>positive_meaning verdict_witness_system)"
  show "(witness_undeclared,Pair_Term (Pair_Term DS (Pair_Term FS RS)) D)\<in>positive_meaning verdict_witness_system"
  proof (cases "(witness_selection_some,Pair_Term D FS)\<in>positive_meaning verdict_witness_system")
    case True
    have "(witness_undeclared,evaluate_pattern (native_values [DS,FS,RS,D]) (decode_finite_pattern
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))))\<in>positive_meaning verdict_witness_system"
      by (rule undeclared_witness_family.step_at[where c="[0]" and ps="[([0],(witness_absent,
          Finite_Pattern_Pair (native_var 3) (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
        ([1],(witness_selection_some,Finite_Pattern_Pair (native_var 3) (native_var 1)))]"])
        (use given True rs in \<open>auto simp: undeclared_witness_row_rule_def\<close>)
    then show ?thesis by simp
  next
    case False
    then have roots: "(witness_family_some,Pair_Term D RS)\<in>positive_meaning verdict_witness_system"
      using given by simp
    have "(witness_undeclared,evaluate_pattern (native_values [DS,FS,RS,D]) (decode_finite_pattern
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3))))\<in>positive_meaning verdict_witness_system"
      by (rule undeclared_witness_family.step_at[where c="[1]" and ps="[([0],(witness_absent,
          Finite_Pattern_Pair (native_var 3) (Finite_Pattern_Pair (native_var 3) (native_var 0)))),
        ([1],(witness_family_some,Finite_Pattern_Pair (native_var 3) (native_var 2)))]"])
        (use given roots fs in \<open>auto simp: undeclared_witness_root_rule_def\<close>)
    then show ?thesis by simp
  qed
qed

theorem native_undeclared_witness_rows:
  assumes identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
  shows "(witness_undeclared,Pair_Term (Pair_Term (declaration_term Fs)
      (Pair_Term (state_families_term ident Fs) (state_family_term identr Rs))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. d\<notin>set (row_declared (snd z))) \<and>
    ((\<exists>F\<in>set Fs. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))) \<or> (\<exists>z\<in>set Rs. d\<in>set (row_mentions (snd z))))"
proof -
  interpret families: selection_some_reading verdict_witness_system witness_selection_some
      witness_family_some witness_row_mentions path_term ident "\<lambda>d z. d\<in>set (row_mentions (snd z))"
    by unfold_locales (simp_all add: identity witness_mentioned_rows[where ident=ident,OF identity])
  interpret rootrows: family_some_reading verdict_witness_system witness_family_some
      witness_row_mentions path_term identr "\<lambda>d z. d\<in>set (row_mentions (snd z))"
    by unfold_locales (simp_all add: roots witness_mentioned_rows[where ident=identr,OF roots])
  have absence: "(witness_absent,Pair_Term (path_term d) (Pair_Term (path_term d) (declaration_term Fs)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> (\<forall>F\<in>set Fs. \<forall>z\<in>set F. d\<notin>set (row_declared (snd z)))"
  proof -
    have "(witness_absent,Pair_Term (path_term d) (Pair_Term (path_term d) (declaration_term Fs)))
        \<in>positive_meaning verdict_witness_system \<longleftrightarrow> store_lookup (declaration_store Fs) d=None"
      using witness_absences.exact_at_path[of path_term "path_term d" d "declaration_store Fs"]
      by (simp add: declaration_term_def)
    then show ?thesis using declaration_store_declared[of Fs d] by blast
  qed
  have fam: "\<And>F. term_formed (state_family_term ident F)" by (rule state_family_term_formed) (rule identity)
  have ffs: "term_formed (state_families_term ident Fs)"
    unfolding state_families_term_def by (induction Fs) (simp_all add: fam octets_formed_def)
  have frs: "term_formed (state_family_term identr Rs)" by (rule state_family_term_formed) (rule roots)
  show ?thesis
    by (simp only: undeclared_witness_at[OF ffs frs] absence families.exact rootrows.exact path_term_formed
      simp_thms)
qed

text \<open>
  The contract: exactly the constants of \<^const>\<open>isabelle_undeclared_constants\<close>, the assessment's own
  list, at a key of the state.
\<close>

theorem native_undeclared_witness_exact:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and bound: "d<length (fst (snd S))"
    and identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
  shows "(witness_undeclared,Pair_Term (Pair_Term (declaration_term Fs)
      (Pair_Term (state_families_term ident Fs) (state_family_term identr (state_roots R))))
      (path_term (key d)))\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<in>set (isabelle_undeclared_constants (fst S) (snd S))"
proof -
  have declared: "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. key d\<notin>set (row_declared (snd z))) \<longleftrightarrow>
      d\<notin>set (List.map_filter isabelle_declared_constant (snd (snd S)))"
  proof -
    have "(\<exists>F\<in>set Fs. \<exists>z\<in>set F. key d\<in>set (row_declared (snd z))) \<longleftrightarrow>
        (\<exists>e\<in>set (snd (snd S)). d\<in>set (entity_declared e))"
      by (rule trans[OF sym[OF declaration_store_declared[of Fs "key d"]]
        declaration_store_constant[OF present families bound]])
    then show ?thesis unfolding declared_constants_member by blast
  qed
  have mentioned: "((\<exists>F\<in>set Fs. \<exists>z\<in>set F. key d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set (state_roots R). key d\<in>set (row_mentions (snd z)))) \<longleftrightarrow>
    d\<in>set (isabelle_mentioned_constants (fst S) (snd S))"
  proof -
    have "((\<exists>F\<in>set Fs. \<exists>z\<in>set F. key d\<in>set (row_mentions (snd z))) \<or>
        (\<exists>z\<in>set (state_roots R). key d\<in>set (row_mentions (snd z)))) \<longleftrightarrow>
      key d\<in>key ` set (isabelle_mentioned_constants (fst S) (snd S))"
      unfolding presented_row_mentions[OF present families, symmetric] by blast
    then show ?thesis
      using state_presents_key_member[OF present bound presented_mentioned_inside[OF present]] by simp
  qed

  show ?thesis
    by (simp only: native_undeclared_witness_rows[where ident=ident and identr=identr,OF identity roots] declared mentioned
      isabelle_undeclared_constants_exact) blast
qed

section \<open>The witness of \<open>malformed\<close>\<close>

interpretation malformed_witness_family: native_rule_law verdict_witness_system witness_malformed
    "[([0],malformed_witness_rule)]"
proof (rule native_rule_lawI)
  show "native_rule_family verdict_witness_system witness_malformed [([0],malformed_witness_rule)]"
    by (rule verdict_witness_family) (simp_all add: verdict_witness_rule_defs)
next
  fix c F assume "(c,F)\<in>set [([0]::local_address,malformed_witness_rule)]"
  then show "\<exists>p ps. F=finite_native_rule p ps" by (auto simp: malformed_witness_rule_def)
qed

interpretation malformed_witness_conjunction: native_conjunction_program verdict_witness_system witness_malformed
    "row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])
      (native_var 2) (native_var 3)" "[]"
  unfolding native_conjunction_program_def native_conjunction_program_axioms_def
  using malformed_witness_family.native_rule_family_axioms[unfolded malformed_witness_rule_def] by simp

theorem native_malformed_witness_row:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    term_formed x \<and> row_declared (snd z)=[] \<and> row_subjects (snd z)=[]"
proof
  assume holds: "(witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
  let ?p="row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])
      (native_var 2) (native_var 3)"
  obtain f where formed: "\<forall>a\<in>pattern_variables (decode_finite_pattern ?p). term_formed (f a)"
    and concl: "evaluate_pattern f (decode_finite_pattern ?p)=Pair_Term x (state_row_term ident z)"
    using holds[unfolded malformed_witness_conjunction.exact] by blast
  have vals: "f [0]=x" "keys_term (row_declared (snd z))=Payload_Term []"
      "keys_term (row_subjects (snd z))=Payload_Term []"
    using concl by (simp_all add: row_pattern_def state_row_term_def eq_commute[of "Payload_Term []"])
  have "term_formed x" using formed vals by (simp add: row_pattern_def)
  then show "term_formed x \<and> row_declared (snd z)=[] \<and> row_subjects (snd z)=[]"
    using vals by (cases "row_declared (snd z)"; cases "row_subjects (snd z)") (simp_all add: keys_term_def)
next
  assume empty: "term_formed x \<and> row_declared (snd z)=[] \<and> row_subjects (snd z)=[]"
  have "(witness_malformed,evaluate_pattern (native_values [x,path_term (fst z),
      keys_term (row_mentions (snd z)),ident (row_identity (snd z))]) (decode_finite_pattern
      (row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])
        (native_var 2) (native_var 3))))\<in>positive_meaning verdict_witness_system"
    by (rule malformed_witness_conjunction.at[THEN iffD2])
      (use empty identity in \<open>auto simp: row_pattern_def\<close>)
  then show "(witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
    using empty by (simp add: row_pattern_def state_row_term_def keys_term_def)
qed

text \<open>
  The contract: exactly the entities of \<^const>\<open>isabelle_malformed_entities\<close>, read at the rows of the
  families the field's own reading visits, the specification family not among them.
\<close>

theorem native_malformed_witness_exact:
  assumes identity: "\<And>y. term_formed (ident y)" and xf: "term_formed x"
    and member: "e\<in>set (snd C)" and kind: "entity_kind_of e\<noteq>Specification_Kind"
  shows "(witness_malformed,Pair_Term x (state_row_term ident (a,entity_row key C e)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> e\<in>set (isabelle_malformed_entities C)"
  using native_malformed_witness_row[where ident=ident,OF identity, of x "(a,entity_row key C e)"] xf member kind
    entity_row_formed[of e key C] isabelle_malformed_entities_member[of e C]
  by (auto simp: entity_declared_def
    entity_subjects_outside_specifications[of e "fst C" "isabelle_development_constants (snd C)" "[]"]
    split: option.splits)

end
