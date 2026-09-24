theory Development_Native_Verdict
imports Development_Verdict_Difference Development_Verdict_Unreached Development_Native_Decomposition
  Development_Refinement_Verification Development_Definition_Verification
begin

section \<open>The verdict of a kind is one native definition over two states' rows\<close>

text \<open>
  The fields of the verdict were built each with its own program and its own contract: \<open>statements\<close> and
  \<open>malformed\<close> (\<open>Development_Verdict_Statements\<close>), \<open>excess\<close> and \<open>undeclared\<close> (\<open>Development_Verdict_Mentions\<close>),
  \<open>unreached\<close> (\<open>Development_Verdict_Unreached\<close>), the permitted removed and added rows and \<open>roots\<close>
  (\<open>Development_Verdict_Difference\<close>). Here they become one judgment. The verdict's program is the join of the
  field programs, each definition at its own site, and one rule of its own at its entry: eight premises, one per
  field, each passed only the part of the argument it reads. The argument is the tuple of those parts; the kind
  arguments of the verdict are the selections of families the parts are built from, so the refinement and the
  definition verdicts are this one definition at their selections. Acceptance is positive: every premise is an
  \<open>every\<close> or a \<open>some\<close>, and no premise reads an absence.
\<close>

subsection \<open>The entry rule\<close>

text \<open>
  The entry's argument is the tuple of the parts (@{const term_tuple}, with its pattern
  @{const finite_pattern_tuple}, of theory \<open>Native_Collection_Programs\<close>).
\<close>

abbreviation verdict_entry :: "local_address option definition_site" where
  "verdict_entry \<equiv> (Some [],[80])"

definition verdict_entry_conclusion :: "local_address finite_term_pattern" where
  "verdict_entry_conclusion=finite_pattern_tuple (map native_var [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16])"

definition verdict_entry_premises ::
    "(local_address\<times>(local_address option definition_site\<times>local_address finite_term_pattern)) list" where
  "verdict_entry_premises=[
    ([0],(verdict_statements,Finite_Pattern_Pair (native_var 0) (native_var 1))),
    ([1],(verdict_excess,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 2)) (native_var 3))),
    ([2],(verdict_formed,Finite_Pattern_Pair (native_var 0) (native_var 4))),
    ([3],(verdict_undeclared,Finite_Pattern_Pair (native_var 5) (Finite_Pattern_Pair (native_var 6) (native_var 7)))),
    ([4],(verdict_unreached,Finite_Pattern_Pair (native_var 8) (native_var 6))),
    ([5],(verdict_removed,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 9) (native_var 0))
      (Finite_Pattern_Pair (native_var 10) (native_var 11)))),
    ([6],(verdict_added,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 12) (native_var 0))
      (Finite_Pattern_Pair (native_var 13) (native_var 14)))),
    ([7],(verdict_roots,Finite_Pattern_Pair (native_var 15) (native_var 16)))]"

definition verdict_entry_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "verdict_entry_rule=finite_native_rule verdict_entry_conclusion verdict_entry_premises"

subsection \<open>The program: the field programs joined, and the entry\<close>

text \<open>
  The first four definitions of the difference program (the member, the any-checker, the store search and the
  found search) are those of the rows and mentions programs at the same sites, so they are held once.
\<close>

definition native_verdict_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "native_verdict_definitions=verdict_rows_definitions@verdict_mentions_definitions@verdict_unreached_definitions@
    drop 4 verdict_difference_definitions@[(verdict_entry,[([0],verdict_entry_rule)])]"

definition finite_native_verdict :: "local_address option finite_native_system" where
  "finite_native_verdict=finite_rule_program native_verdict_definitions"

definition native_verdict_system :: "local_address option native_system" where
  "native_verdict_system=decode_finite_system finite_native_verdict"

lemma finite_native_verdict_formed: "finite_system_formed finite_native_verdict"
  by code_simp

lemma native_verdict_formed: "schema_system_formed native_verdict_system"
  using finite_native_verdict_formed
  by (simp only: native_verdict_system_def finite_system_formed_correct)

lemma native_verdict_distinct: "distinct (map fst native_verdict_definitions)"
  by code_simp

lemma native_verdict_family:
  assumes member: "(d,rs)\<in>set native_verdict_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family native_verdict_system d rs"
  unfolding native_verdict_system_def finite_native_verdict_def
  by (rule finite_rule_program_family[OF native_verdict_formed[unfolded native_verdict_system_def
    finite_native_verdict_def] native_verdict_distinct member plain])

interpretation verdict_entry_family: native_rule_law native_verdict_system verdict_entry "[([0],verdict_entry_rule)]"
  by (rule native_rule_lawI, rule native_verdict_family)
    (auto simp: native_verdict_definitions_def verdict_entry_rule_def)

subsection \<open>The fields keep their meanings in the verdict's program\<close>

text \<open>The join law of rule programs (@{thm finite_rule_program_join}), consumed once per field program.\<close>

lemma native_verdict_whole:
  "set verdict_rows_definitions\<subseteq>set native_verdict_definitions"
  "set verdict_mentions_definitions\<subseteq>set native_verdict_definitions"
  "set verdict_unreached_definitions\<subseteq>set native_verdict_definitions"
  "set verdict_difference_definitions\<subseteq>set native_verdict_definitions"
proof -
  show "set verdict_rows_definitions\<subseteq>set native_verdict_definitions"
    "set verdict_mentions_definitions\<subseteq>set native_verdict_definitions"
    "set verdict_unreached_definitions\<subseteq>set native_verdict_definitions"
    by (auto simp: native_verdict_definitions_def)
  have split: "set verdict_difference_definitions=
      set (take 4 verdict_difference_definitions)\<union>set (drop 4 verdict_difference_definitions)"
    by (metis append_take_drop_id set_append)
  have "set (take 4 verdict_difference_definitions)\<subseteq>set verdict_rows_definitions\<union>set verdict_mentions_definitions"
    by (simp add: verdict_difference_definitions_def verdict_rows_definitions_def verdict_mentions_definitions_def)
  then show "set verdict_difference_definitions\<subseteq>set native_verdict_definitions"
    unfolding split by (auto simp: native_verdict_definitions_def)
qed

lemma native_verdict_shares:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and whole: "set ds\<subseteq>set native_verdict_definitions"
    and site: "d\<in>fst ` set ds"
  shows "(d,t)\<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning (decode_finite_system (finite_rule_program ds))"
proof -
  have whole_formed: "schema_system_formed (decode_finite_system (finite_rule_program native_verdict_definitions))"
    using native_verdict_formed by (simp add: native_verdict_system_def finite_native_verdict_def)
  show ?thesis unfolding native_verdict_system_def finite_native_verdict_def
    by (rule finite_rule_program_join[OF whole_formed native_verdict_distinct formed whole site])
qed

lemma native_verdict_rows_field:
  assumes site: "d\<in>fst ` set verdict_rows_definitions"
  shows "(d,t)\<in>positive_meaning native_verdict_system \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_rows_system"
  unfolding verdict_rows_system_def finite_verdict_rows_def
  by (rule native_verdict_shares)
    (use verdict_rows_formed site native_verdict_whole(1) in \<open>simp_all add: verdict_rows_system_def
      finite_verdict_rows_def\<close>)

lemma native_verdict_mentions_field:
  assumes site: "d\<in>fst ` set verdict_mentions_definitions"
  shows "(d,t)\<in>positive_meaning native_verdict_system \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_mentions_system"
  unfolding verdict_mentions_system_def finite_verdict_mentions_def
  by (rule native_verdict_shares)
    (use verdict_mentions_formed site native_verdict_whole(2) in \<open>simp_all add: verdict_mentions_system_def
      finite_verdict_mentions_def\<close>)

lemma native_verdict_unreached_field:
  assumes site: "d\<in>fst ` set verdict_unreached_definitions"
  shows "(d,t)\<in>positive_meaning native_verdict_system \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_unreached_system"
  unfolding verdict_unreached_system_def finite_verdict_unreached_def
  by (rule native_verdict_shares)
    (use verdict_unreached_formed site native_verdict_whole(3) in \<open>simp_all add: verdict_unreached_system_def
      finite_verdict_unreached_def\<close>)

lemma native_verdict_difference_field:
  assumes site: "d\<in>fst ` set verdict_difference_definitions"
  shows "(d,t)\<in>positive_meaning native_verdict_system \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_difference_system"
  unfolding verdict_difference_system_def finite_verdict_difference_def
  by (rule native_verdict_shares)
    (use verdict_difference_formed site native_verdict_whole(4) in \<open>simp_all add: verdict_difference_system_def
      finite_verdict_difference_def\<close>)

subsection \<open>The entry holds exactly when its eight fields do\<close>

theorem native_verdict_entry:
  "(verdict_entry,term_tuple [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16])
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_statements,Pair_Term a0 a1)\<in>positive_meaning native_verdict_system \<and>
    (verdict_excess,Pair_Term (Pair_Term a0 a2) a3)\<in>positive_meaning native_verdict_system \<and>
    (verdict_formed,Pair_Term a0 a4)\<in>positive_meaning native_verdict_system \<and>
    (verdict_undeclared,Pair_Term a5 (Pair_Term a6 a7))\<in>positive_meaning native_verdict_system \<and>
    (verdict_unreached,Pair_Term a8 a6)\<in>positive_meaning native_verdict_system \<and>
    (verdict_removed,Pair_Term (Pair_Term a9 a0) (Pair_Term a10 a11))\<in>positive_meaning native_verdict_system \<and>
    (verdict_added,Pair_Term (Pair_Term a12 a0) (Pair_Term a13 a14))\<in>positive_meaning native_verdict_system \<and>
    (verdict_roots,Pair_Term a15 a16)\<in>positive_meaning native_verdict_system"
  (is "?entry \<longleftrightarrow> ?fields")
proof
  assume holds: ?entry
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set [([0::nat],verdict_entry_rule)]"
    and eval: "evaluate_pattern f (decode_finite_pattern p)=
      term_tuple [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16]"
    and support: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning native_verdict_system"
    by (rule verdict_entry_family.holds_rule[OF holds]) blast
  have "finite_native_rule p ps=verdict_entry_rule" using rule by simp
  then have p: "p=verdict_entry_conclusion" and ps: "set ps=set verdict_entry_premises"
    unfolding verdict_entry_rule_def by (simp_all add: finite_native_rule_eq_iff)
  have vals: "f [0]=a0 \<and> f [1]=a1 \<and> f [2]=a2 \<and> f [3]=a3 \<and> f [4]=a4 \<and> f [5]=a5 \<and> f [6]=a6 \<and> f [7]=a7 \<and>
      f [8]=a8 \<and> f [9]=a9 \<and> f [10]=a10 \<and> f [11]=a11 \<and> f [12]=a12 \<and> f [13]=a13 \<and> f [14]=a14 \<and>
      f [15]=a15 \<and> f [16]=a16"
    using eval by (simp add: p verdict_entry_conclusion_def evaluate_pattern_tuple)
  show ?fields using support by (simp add: ps verdict_entry_premises_def vals vals[simplified One_nat_def])
next
  assume fields: ?fields
  let ?f="native_values [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16]"
  have rule: "([0],finite_native_rule verdict_entry_conclusion verdict_entry_premises)\<in>set [([0],verdict_entry_rule)]"
    by (simp add: verdict_entry_rule_def)
  have "(verdict_entry,evaluate_pattern ?f (decode_finite_pattern verdict_entry_conclusion))
      \<in>positive_meaning native_verdict_system"
    by (rule verdict_entry_family.step_at[OF rule])
      (use fields in \<open>simp_all add: verdict_entry_conclusion_def verdict_entry_premises_def\<close>)
  then show ?entry by (simp add: verdict_entry_conclusion_def evaluate_pattern_tuple)
qed

subsection \<open>The argument: each field passed only the part it reads\<close>

text \<open>
  The kinds outside a selection, listed in the order the kinds are: the families a field reads beside the
  selected ones (the other families of the permitted-row fields, and every family but the specifications for
  \<open>malformed\<close>).
\<close>

definition kinds_outside :: "entity_kind list \<Rightarrow> entity_kind list" where
  "kinds_outside ks=filter (\<lambda>j. j\<notin>set ks) entity_kinds"

lemma kinds_outside_set [simp]: "set (kinds_outside ks)=- set ks"
  by (auto simp: kinds_outside_def)

text \<open>
  The verdict's argument over a request state presented by \<open>R\<close>, an answer state presented by \<open>R'\<close>, the
  subject's key \<open>k\<close>, the support's keys \<open>ks\<close>, and the selections \<open>kr\<close> (what an answer may replace) and \<open>kd\<close> (what
  it must state). Every part is computed from the presented rows; nothing is supplied beside them.
\<close>

definition native_verdict_argument ::
    "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> ((String.literal list\<times>isabelle_term) \<Rightarrow> factor_term) \<Rightarrow>
      state_rows \<Rightarrow> state_rows \<Rightarrow> state_key \<Rightarrow> state_key list \<Rightarrow> entity_kind list \<Rightarrow> entity_kind list \<Rightarrow>
      factor_term" where
  "native_verdict_argument ident identr R R' k ks kr kd=term_tuple [path_term k,
    state_families_term ident (map (state_entities R') kd),
    support_term ks,
    subject_indexes_term ident (map fst (state_atoms R')) (map (state_entities R') kr),
    state_families_term ident (map (state_entities R') (kinds_outside [Specification_Kind])),
    declaration_term (state_all_families R'),
    state_families_term ident (state_all_families R'),
    state_family_term identr (state_roots R'),
    reach_table_term (state_reach_table (state_atoms R') (state_roots R') (state_all_families R')),
    family_row_term ident (state_all_families R'),
    state_families_term ident (map (state_entities R) kr),
    state_families_term ident (map (state_entities R) (kinds_outside kr)),
    family_row_term ident (state_all_families R),
    state_families_term ident (map (state_entities R') kr),
    state_families_term ident (map (state_entities R') (kinds_outside kr)),
    keys_term (map fst (state_roots R)),
    keys_term (map fst (state_roots R'))]"

subsection \<open>The HOL verdict's acceptance, field by field\<close>

lemma fset_of_list_empty_iff: "fset_of_list xs={||} \<longleftrightarrow> xs=[]"
  by (cases xs) simp_all

text \<open>
  Of the verdict's fields, two are conditions the presentation carries: the unknown positions are vacuous and
  the names of both states are distinct (@{thm [source] state_presents_unknown_positions},
  @{thm [source] state_presents_distinct_names}). Acceptance is then the conjunction of the eight computed fields.
\<close>

lemma development_verdict_accepted_fields:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
  defines "f\<equiv>isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  shows "development_verdict_accepted (development_constant_verdict replaceable demanded S r S') \<longleftrightarrow>
    filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S) (problem_subject (fst r)) e \<and>
      isabelle_declared_constant e=None) (isabelle_state_removed (snd S) (snd S'))=[] \<and>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') (fimage f (problem_subject (fst r))) g)
      (isabelle_state_added (snd S) (snd S'))=[] \<and>
    development_answer_statements demanded (snd S') (fimage f (problem_subject (fst r)))\<noteq>[] \<and>
    development_answer_statements_excess replaceable (snd S') (fimage f (problem_subject (fst r)))
      (fimage f (fst (snd (snd r))))=[] \<and>
    isabelle_malformed_entities (snd S')=[] \<and>
    isabelle_undeclared_constants (fst S') (snd S')=[] \<and>
    isabelle_unreached_entities (fst S') (snd S')=[] \<and>
    map (isabelle_term_rename f) (fst S)=fst S'"
proof -
  obtain p s sup E where r: "r=(p,s,sup,E)" by (cases r)
  have unknown: "isabelle_unknown_positions (snd S')=[]" by (rule state_presents_unknown_positions[OF present'])
  have distinct: "distinct (fst (snd S))" "distinct (fst (snd S'))"
    by (rule state_presents_distinct_names[OF present], rule state_presents_distinct_names[OF present'])
  show ?thesis
    using unknown distinct
    by (simp add: r f_def development_verdict_accepted_def development_constant_verdict_def Let_def
      isabelle_assessment_closed_def isabelle_context_assessment_def fset_of_list_empty_iff conj_ac)
qed

subsection \<open>The contract\<close>

theorem native_verdict_exact:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and replaceable: "kinds_present replaceable (set kr)" and demanded: "kinds_present demanded (set kd)"
    and identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
  shows "(verdict_entry,native_verdict_argument ident identr R R' k ks kr kd)\<in>positive_meaning native_verdict_system \<longleftrightarrow>
    development_verdict_accepted (development_constant_verdict replaceable demanded S r S')"
proof -
  have present: "state_presents key S R" using request by (simp add: request_presents_def)
  obtain c where subject: "problem_subject (fst r)={|c|}" and kc: "k=key c" and bound: "c<length (fst (snd S))"
    and "(k,fst (snd S)!c)\<in>set (state_atoms R)" and "set ks=key ` fset (fst (snd (snd r)))"
    and "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF request])
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  note hol=development_verdict_accepted_fields[OF present present', of replaceable demanded r]

  have sel_d: "set (map (state_entities R') kd)=state_entities R' ` set kd" by simp
  have sel_r: "set (map (state_entities R') kr)=state_entities R' ` set kr" by simp
  have sel_o: "set (map (state_entities R') (kinds_outside kr))=state_entities R' ` (- set kr)" by simp
  have sel_rr: "set (map (state_entities R) kr)=state_entities R ` set kr" by simp
  have sel_ro: "set (map (state_entities R) (kinds_outside kr))=state_entities R ` (- set kr)" by simp
  have sel_s: "set (map (state_entities R') (kinds_outside [Specification_Kind]))=
      state_entities R' ` (- {Specification_Kind})" by simp
  have fam: "set (state_all_families R')=range (state_entities R')" by (rule state_all_families_range)
  have sites: "verdict_statements\<in>fst ` set verdict_rows_definitions"
    "verdict_formed\<in>fst ` set verdict_rows_definitions"
    "verdict_excess\<in>fst ` set verdict_mentions_definitions"
    "verdict_undeclared\<in>fst ` set verdict_mentions_definitions"
    "verdict_unreached\<in>fst ` set verdict_unreached_definitions"
    "verdict_removed\<in>fst ` set verdict_difference_definitions"
    "verdict_added\<in>fst ` set verdict_difference_definitions"
    "verdict_roots\<in>fst ` set verdict_difference_definitions"
    by (simp_all add: verdict_rows_definitions_def verdict_mentions_definitions_def
      verdict_unreached_definitions_def verdict_difference_definitions_def)
  have formed_field: "(verdict_formed,Pair_Term (path_term k)
      (state_families_term ident (map (state_entities R') (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow> isabelle_malformed_entities (snd S')=[]"
    using native_verdict_rows_field[OF sites(2)]
      native_formed_exact_specifications[OF present' sel_s identity path_term_formed] by simp
  have undeclared_field: "(verdict_undeclared,Pair_Term (declaration_term (state_all_families R'))
      (Pair_Term (state_families_term ident (state_all_families R')) (state_family_term identr (state_roots R'))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow> isabelle_undeclared_constants (fst S') (snd S')=[]"
    using native_verdict_mentions_field[OF sites(4)]
      native_undeclared_exact[OF present' fam identity roots_identity] by simp
  have unreached_field: "(verdict_unreached,Pair_Term
      (reach_table_term (state_reach_table (state_atoms R') (state_roots R') (state_all_families R')))
      (state_families_term ident (state_all_families R')))\<in>positive_meaning native_verdict_system \<longleftrightarrow>
      isabelle_unreached_entities (fst S') (snd S')=[]"
    using native_verdict_unreached_field[OF sites(5)] native_unreached_exact[OF present' fam identity] by simp
  have removed_field: "(verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families R'))
      (path_term k)) (Pair_Term (state_families_term ident (map (state_entities R) kr))
        (state_families_term ident (map (state_entities R) (kinds_outside kr)))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
      filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S) (problem_subject (fst r)) e \<and>
        isabelle_declared_constant e=None) (isabelle_state_removed (snd S) (snd S'))=[]"
    using native_verdict_difference_field[OF sites(6)]
      native_removed_request[OF request present' shared replaceable sel_rr sel_ro identity] by simp
  have roots_field: "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R'))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow> map (isabelle_term_rename ?f) (fst S)=fst S'"
    using native_verdict_difference_field[OF sites(8)] native_roots_exact[OF present present' shared] by simp
  show ?thesis
  proof (cases "(!) (fst (snd S)) ` fset (problem_subject (fst r))\<subseteq>set (fst (snd S'))")
    case True
    note named=True
    have statements_field: "(verdict_statements,Pair_Term (path_term k)
        (state_families_term ident (map (state_entities R') kd)))\<in>positive_meaning native_verdict_system \<longleftrightarrow>
        development_answer_statements demanded (snd S') (fimage ?f (problem_subject (fst r)))\<noteq>[]"
      using native_verdict_rows_field[OF sites(1)]
        native_statements_answer[OF request present' shared named demanded sel_d identity] by simp
    have excess_field: "(verdict_excess,Pair_Term (Pair_Term (path_term k) (support_term ks))
        (subject_indexes_term ident (map fst (state_atoms R')) (map (state_entities R') kr)))
        \<in>positive_meaning native_verdict_system \<longleftrightarrow>
        development_answer_statements_excess replaceable (snd S') (fimage ?f (problem_subject (fst r)))
          (fimage ?f (fst (snd (snd r))))=[]"
      using native_verdict_mentions_field[OF sites(3)]
        native_excess_answer[OF request present' shared named replaceable sel_r identity] by simp
    have added_field: "(verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R))
        (path_term k)) (Pair_Term (state_families_term ident (map (state_entities R') kr))
          (state_families_term ident (map (state_entities R') (kinds_outside kr)))))
        \<in>positive_meaning native_verdict_system \<longleftrightarrow>
        filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') (fimage ?f (problem_subject (fst r))) g)
          (isabelle_state_added (snd S) (snd S'))=[]"
      using native_verdict_difference_field[OF sites(7)]
        native_added_request[OF request present' shared named replaceable sel_r sel_o identity] by simp
    show ?thesis
      unfolding native_verdict_argument_def native_verdict_entry hol statements_field excess_field formed_field undeclared_field unreached_field
        removed_field added_field roots_field
      by blast
  next
    case False
    have native_false: "\<not>(verdict_statements,Pair_Term (path_term k)
        (state_families_term ident (map (state_entities R') kd)))\<in>positive_meaning native_verdict_system"
    proof
      assume "(verdict_statements,Pair_Term (path_term k)
          (state_families_term ident (map (state_entities R') kd)))\<in>positive_meaning native_verdict_system"
      then have "(verdict_statements,Pair_Term (path_term k)
          (state_families_term ident (map (state_entities R') kd)))\<in>positive_meaning verdict_rows_system"
        using native_verdict_rows_field[OF sites(1)] by simp
      then obtain F z where F: "F\<in>set (map (state_entities R') kd)" and z: "z\<in>set F"
          and kz: "k\<in>set (row_subjects (snd z))"
        using verdict_statement_selections.exact[where ident=ident, OF identity] by blast
      obtain j where zj: "z\<in>set (state_entities R' j)" using F z by auto
      have "set (row_declared (snd z))\<union>set (row_subjects (snd z))\<union>set (row_mentions (snd z))
          \<subseteq>fst ` set (state_atoms R')"
        using state_presents_cited_atoms[OF present', of "fst z" "snd z" j] zj by simp
      then have "k\<in>fst ` set (state_atoms R')" using kz by blast
      moreover have "set (state_atoms R')=(\<lambda>i. (key' i,fst (snd S')!i)) ` {..<length (fst (snd S'))}"
        using state_presents_atoms[OF present'] by (simp add: atoms_present_def)
      ultimately obtain i where i: "i<length (fst (snd S'))" and ki: "k=key' i" by auto
      have "fst (snd S)!c=fst (snd S')!i"
        using keys_shared_atom[OF present present' shared bound i] kc ki by simp
      then have "fst (snd S)!c\<in>set (fst (snd S'))" using i by simp
      then show False using False subject by simp
    qed
    have hol_false: "\<not>development_verdict_accepted (development_constant_verdict replaceable demanded S r S')"
    proof
      assume "development_verdict_accepted (development_constant_verdict replaceable demanded S r S')"
      then have "development_answer_statements demanded (snd S') (fimage ?f (problem_subject (fst r)))\<noteq>[]"
        using hol by blast
      then obtain e where e: "e\<in>set (snd (snd S'))"
          and about: "development_answer_statement demanded (snd S') {|?f c|} e"
        using subject by (auto simp: development_answer_statements_def filter_empty_conv)
      have "?f c\<in>set (isabelle_entity_subjects (fst (snd S')) (isabelle_development_constants (snd (snd S'))) e)"
        using about by (auto simp: development_answer_statement_def list_ex_iff)
      then have "?f c\<in>set (isabelle_entity_positions e)" using isabelle_entity_subjects_positions by blast
      then have inside: "?f c<length (fst (snd S'))" using state_presents_entity_inside[OF present' e] by blast
      have "fst (snd S)!c\<notin>set (fst (snd S'))" using False subject by simp
      then have "?f c=length (fst (snd S'))+c"
        by (intro isabelle_state_embedding_unshared) (use bound in \<open>simp add: isabelle_name_at_def\<close>)
      then show False using inside by simp
    qed
    show ?thesis using native_false hol_false unfolding native_verdict_argument_def native_verdict_entry by blast
  qed
qed

subsection \<open>The report's removed and added lists are the edit's own\<close>

text \<open>
  Acceptance reads no reduction of an edit. The report's first two fields, the removed and the added entities,
  are the answer's own two families of rows exactly when the edit is reduced, which is the answer reader's
  condition (@{const edit_reduced}), consumed here through @{thm [source] edit_reduced_lists}.
\<close>

corollary native_verdict_edit:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'" and edit: "edit_reduced R R' D A"
  shows "set (fst (development_constant_verdict replaceable demanded S r S'))=
      {e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}"
    and "set (fst (snd (development_constant_verdict replaceable demanded S r S')))=
      {g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}"
proof -
  obtain p s sup E where r: "r=(p,s,sup,E)" by (cases r)
  show "set (fst (development_constant_verdict replaceable demanded S r S'))=
      {e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}"
    using edit_reduced_lists(1)[OF present present' shared edit]
    by (simp add: r development_constant_verdict_def Let_def)
  show "set (fst (snd (development_constant_verdict replaceable demanded S r S')))=
      {g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}"
    using edit_reduced_lists(2)[OF present present' shared edit]
    by (simp add: r development_constant_verdict_def Let_def)
qed

section \<open>The refinement and the definition verdicts are the one definition at their selections\<close>

lemma refinement_kinds: "kinds_present (development_demanded isabelle_code_equation_proposition) (set [Equation_Kind])"
  by (simp add: kinds_present_def code_equation_kind)

lemma definition_replaceable_kinds:
  "kinds_present development_definition_replaceable (set [Definition_Kind,Equation_Kind])"
  by (auto simp: kinds_present_def development_definition_replaceable_def code_equation_kind definition_kind)

theorem native_refinement_verdict_exact:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
  shows "(verdict_entry,native_verdict_argument ident identr R R' k ks [Equation_Kind] [Equation_Kind])
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    development_verdict_accepted (development_refinement_verdict S r S')"
  unfolding development_refinement_verdict_def
  by (rule native_verdict_exact[OF request present' shared refinement_kinds refinement_kinds identity roots_identity])

theorem native_definition_verdict_exact:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
  shows "(verdict_entry,native_verdict_argument ident identr R R' k ks [Definition_Kind,Equation_Kind] [Definition_Kind])
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    development_verdict_accepted (development_definition_verdict S r S')"
  unfolding development_definition_verdict_def
  by (rule native_verdict_exact[OF request present' shared definition_replaceable_kinds definition_families_present
    identity roots_identity])

section \<open>The verdict's program reads no octet as structure\<close>

text \<open>
  By the criterion of \<open>Factor_Positive_Parametricity\<close>, the payloads a program states are the octets it reads as
  structure. The verdict's program, with every field's clauses it composes, states the empty payload alone.
\<close>

lemma finite_native_verdict_payloads: "finite_system_payloads finite_native_verdict={|[]|}"
  by code_simp

theorem native_verdict_payloads: "system_payloads native_verdict_system={[]}"
  using finite_system_payloads_exact[of finite_native_verdict]
  by (simp add: native_verdict_system_def finite_native_verdict_payloads)

end
