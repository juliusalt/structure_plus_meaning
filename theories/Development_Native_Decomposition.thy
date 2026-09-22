theory Development_Native_Decomposition
imports Development_Located_Rows Development_Verdict_Mentions Development_Decomposition_Soundness
  Factor_Finite_Payload_Literals
begin

section \<open>The decomposition schema is a native program over problem rows and the state's rows\<close>

text \<open>
  An application of the decomposition schema at a parent that has a locus is presented less its part
  child (the decomposition entry of task 66): the part child stands at the parent's own locus, so what
  the application adds is its intermediates, whose definition children it poses. The native schema
  reads the material the application rests on: the parent's row as the development's store holds it,
  the intermediates as a nonempty family of citations of the state's constants, and the state's own rows
  that state what the children are about and declare their constants. Those are the Definition family of
  \<open>Development_State_Rows\<close>, for the intermediates' definition children, the families of the
  parent's kind, for its part child, each presented as a selection of families
  (@{const state_families_term}), and the declaration store of all the state's families
  (@{const declaration_term}).

  Every citation is read by the traversals of tasks 34 and 36, consumed and not restated: some row of the
  selection has the cited key among its subjects (@{text verdict_statement_selections}), and the
  declaration store holds a row at the cited key (@{const verdict_key_found}). The intermediates are read
  by two premises over their whole family (@{locale native_every_program}): the statement reading through
  a transposition of its call, the declaration reading directly. The part child is read by two premises
  at the key of the parent's constant, read from the parent's locus, whose last part is that key. No
  absence is read: acceptance is positive.
\<close>

abbreviation decomposition_applies :: "local_address option definition_site" where
  "decomposition_applies \<equiv> (Some [],[1])"
abbreviation decomposition_every :: "local_address option definition_site" where
  "decomposition_every \<equiv> (Some [],[2])"
abbreviation decomposition_defined :: "local_address option definition_site" where
  "decomposition_defined \<equiv> (Some [],[3])"
abbreviation decomposition_declared :: "local_address option definition_site" where
  "decomposition_declared \<equiv> (Some [],[4])"

text \<open>
  A locus is a role prefix of three bits, a kind prefix of three bits and the key of its constant, so the
  pattern of a locus names its six bits and binds the key as the rest.
\<close>

definition decomposition_locus_pattern :: "local_address finite_term_pattern" where
  "decomposition_locus_pattern=Finite_Pattern_Pair (native_var 8) (Finite_Pattern_Pair (native_var 9)
    (Finite_Pattern_Pair (native_var 10) (Finite_Pattern_Pair (native_var 11)
      (Finite_Pattern_Pair (native_var 12) (Finite_Pattern_Pair (native_var 13) (native_var 14))))))"

definition decomposition_conclusion :: "local_address finite_term_pattern" where
  "decomposition_conclusion=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
      (Finite_Pattern_Pair (Finite_Pattern_Pair decomposition_locus_pattern (native_var 3))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 4) (native_var 5))
          (Finite_Pattern_Pair (native_var 6) (Finite_Pattern_Pair (native_var 7) (native_var 15))))))"

definition decomposition_premises :: "(local_address\<times>(local_address option definition_site\<times>
    local_address finite_term_pattern)) list" where
  "decomposition_premises=[([0],(development_row_search,Finite_Pattern_Pair (native_var 3)
      (Finite_Pattern_Pair decomposition_locus_pattern (native_var 1)))),
    ([1],(decomposition_every,Finite_Pattern_Pair (native_var 6)
      (Finite_Pattern_Pair (native_var 4) (native_var 5)))),
    ([2],(verdict_statements,Finite_Pattern_Pair (native_var 14) (native_var 7))),
    ([3],(decomposition_declared,Finite_Pattern_Pair (native_var 15)
      (Finite_Pattern_Pair (native_var 4) (native_var 5)))),
    ([4],(verdict_key_found,Finite_Pattern_Pair (native_var 15) (native_var 14)))]"

definition decomposition_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "decomposition_rule=finite_native_rule decomposition_conclusion decomposition_premises"


definition decomposition_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "decomposition_definitions=(decomposition_applies,[([0],decomposition_rule)])#
    (decomposition_every,native_every_rules decomposition_every decomposition_defined)#
    (decomposition_defined,[([0],native_swap_rule verdict_statements)])#
    (decomposition_declared,native_every_rules decomposition_declared verdict_key_found)#
    development_row_definitions@verdict_rows_definitions@verdict_mentions_definitions"

definition finite_native_decomposition :: "local_address option finite_native_system" where
  "finite_native_decomposition=finite_rule_program decomposition_definitions"

definition native_decomposition_system :: "local_address option native_system" where
  "native_decomposition_system=decode_finite_system finite_native_decomposition"

lemma finite_native_decomposition_formed: "finite_system_formed finite_native_decomposition"
  by code_simp

lemma native_decomposition_formed: "schema_system_formed native_decomposition_system"
  using finite_native_decomposition_formed
  by (simp only: native_decomposition_system_def finite_system_formed_correct)

lemma native_decomposition_family:
  assumes member: "(d,rs)\<in>set decomposition_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family native_decomposition_system d rs"
  unfolding native_decomposition_system_def finite_native_decomposition_def
  by (rule finite_rule_program_family[OF native_decomposition_formed[unfolded native_decomposition_system_def
    finite_native_decomposition_def] _ member plain])
    (simp add: decomposition_definitions_def development_row_definitions_def verdict_rows_definitions_def
      verdict_mentions_definitions_def)

interpretation decomposition_applies_family: native_rule_family native_decomposition_system decomposition_applies
    "[([0],decomposition_rule)]"
  by (rule native_decomposition_family) (simp_all add: decomposition_definitions_def decomposition_rule_def)

interpretation decomposition_defined_swap: native_swap_program native_decomposition_system decomposition_defined
    verdict_statements
  unfolding native_swap_program_def
  by (rule native_decomposition_family)
    (simp_all add: decomposition_definitions_def native_swap_rule_def)

interpretation decomposition_everys: native_every_program native_decomposition_system decomposition_every
    decomposition_defined
  unfolding native_every_program_def
  by (rule native_decomposition_family)
    (simp_all add: decomposition_definitions_def native_every_rules_def native_every_nil_def native_every_step_def)

interpretation decomposition_declareds: native_every_program native_decomposition_system decomposition_declared
    verdict_key_found
  unfolding native_every_program_def
  by (rule native_decomposition_family)
    (simp_all add: decomposition_definitions_def native_every_rules_def native_every_nil_def native_every_step_def)

section \<open>The search and the traversals keep their meanings in this program\<close>

text \<open>
  The program holds the row search's and the traversals' definitions as their own programs hold them, at
  sites of their own, so their shared definitions agree (@{thm positive_meaning_shared_definitions}) and no
  argument about the search or the traversals is made again: each is an instance of the join law of rule
  programs (@{thm finite_rule_program_join}).
\<close>

lemma native_decomposition_definitions:
  "system_definitions native_decomposition_system=
    {decomposition_applies,decomposition_every,decomposition_defined,decomposition_declared}\<union>
    fst ` set development_row_definitions \<union> fst ` set verdict_rows_definitions \<union>
    fst ` set verdict_mentions_definitions"
  by (simp add: native_decomposition_system_def finite_native_decomposition_def finite_rule_program_definitions
    decomposition_definitions_def image_Un Un_assoc)


lemma native_decomposition_shares:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and distinct: "distinct (map fst ds)" and whole: "set ds\<subseteq>set decomposition_definitions"
    and site: "d\<in>fst ` set ds"
  shows "(d,t)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning (decode_finite_system (finite_rule_program ds))"
proof -
  have outer: "distinct (map fst decomposition_definitions)" by code_simp
  have whole_formed: "schema_system_formed (decode_finite_system (finite_rule_program decomposition_definitions))"
    using native_decomposition_formed by (simp add: native_decomposition_system_def finite_native_decomposition_def)
  show ?thesis unfolding native_decomposition_system_def finite_native_decomposition_def
    by (rule finite_rule_program_join[OF whole_formed outer formed whole site])
qed

lemma native_decomposition_search:
  "(development_row_search,t)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (development_row_search,t)\<in>positive_meaning development_rows_program"
  unfolding development_rows_program_def finite_development_rows_program_def
  by (rule native_decomposition_shares)
    (use development_rows_program_formed in \<open>simp_all add: development_rows_program_def
      finite_development_rows_program_def decomposition_definitions_def development_row_definitions_def\<close>)

lemma native_decomposition_statements:
  "(verdict_statements,t)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (verdict_statements,t)\<in>positive_meaning verdict_rows_system"
  unfolding verdict_rows_system_def finite_verdict_rows_def
  by (rule native_decomposition_shares)
    (use verdict_rows_formed in \<open>simp_all add: verdict_rows_system_def finite_verdict_rows_def
      decomposition_definitions_def verdict_rows_definitions_def\<close>)

lemma native_decomposition_found:
  "(verdict_key_found,t)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (verdict_key_found,t)\<in>positive_meaning verdict_mentions_system"
  unfolding verdict_mentions_system_def finite_verdict_mentions_def
  by (rule native_decomposition_shares)
    (use verdict_mentions_formed in \<open>simp_all add: verdict_mentions_system_def finite_verdict_mentions_def
      decomposition_definitions_def verdict_mentions_definitions_def\<close>)

text \<open>
  The transposition passes an element of the intermediates, called beside its context, to the traversal,
  which is called with the key first.
\<close>

lemma native_decomposition_defined:
  "(decomposition_defined,Pair_Term a b)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    (verdict_statements,Pair_Term b a)\<in>positive_meaning native_decomposition_system"
  by (rule decomposition_defined_swap.exact)

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

section \<open>The subject: the parent's row, the store, the intermediates and the state's families\<close>

definition development_parent_row :: "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> factor_term) \<Rightarrow>
    (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem \<Rightarrow> factor_term" where
  "development_parent_row key inert origin grant p=Pair_Term
    (path_term (development_located_at key Development_Problem_Role p))
    (development_problem_body inert (origin p) (grant p) (problem_contract p))"

definition development_decomposition_families ::
    "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> state_rows \<Rightarrow> entity_kind list \<Rightarrow> factor_term" where
  "development_decomposition_families ident R ks=state_families_term ident (map (state_entities R) ks)"

definition development_decomposition_argument :: "factor_term \<Rightarrow> development_store_rows \<Rightarrow> factor_term \<Rightarrow>
    (nat \<Rightarrow> bool list) \<Rightarrow> nat list \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "development_decomposition_argument x rows row key I D P Q=Pair_Term x (Pair_Term (development_rows_term rows)
    (Pair_Term row (Pair_Term (development_row_family (map key I)) (Pair_Term D (Pair_Term P Q)))))"

text \<open>
  The families of a contract's kind are the families whose rows are the statements its reading demands:
  the code equations of a refinement, the kernel definitions of a definition, and no family for a kind
  whose reading demands nothing.
\<close>

fun development_contract_families :: "development_contract \<Rightarrow> entity_kind list" where
  "development_contract_families (Development_Refinement t)=[Equation_Kind]"
| "development_contract_families (Development_Definition t)=[Definition_Kind]"
| "development_contract_families (Development_Proof t)=[]"
| "development_contract_families (Development_Presentation t)=[]"
| "development_contract_families (Development_Amendment t)=[]"

lemma code_equation_kind:
  "development_demanded isabelle_code_equation_proposition e \<longleftrightarrow> entity_kind_of e=Equation_Kind"
  by (cases e) (simp_all add: development_demanded_def)

lemma definition_kind:
  "development_demanded isabelle_definition_proposition e \<longleftrightarrow> entity_kind_of e=Definition_Kind"
  by (cases e) (simp_all add: development_demanded_def)

lemma nothing_demanded: "development_demanded (\<lambda>_. None) e \<longleftrightarrow> False"
  by (simp add: development_demanded_def)

lemma development_contract_families_present:
  "kinds_present (development_demanded (development_contract_reading k)) (set (development_contract_families k))"
  unfolding kinds_present_def
  by (cases k) (simp_all only: development_contract_reading.simps development_contract_families.simps
    code_equation_kind definition_kind nothing_demanded list.set empty_iff insert_iff simp_thms)

lemma definition_families_present:
  "kinds_present (development_demanded isabelle_definition_proposition) (set [Definition_Kind])"
  unfolding kinds_present_def by (simp add: definition_kind)

lemma development_row_family_nonempty: "development_row_family ls=Pair_Term a b \<Longrightarrow> ls\<noteq>[]"
  by (cases ls) (simp_all add: development_row_family_def)

lemma development_locus_term:
  "path_term (development_locus key r k c)=Pair_Term (bit_term (development_role_path r!0))
    (Pair_Term (bit_term (development_role_path r!1)) (Pair_Term (bit_term (development_role_path r!2))
      (Pair_Term (bit_term (development_kind_path k!0)) (Pair_Term (bit_term (development_kind_path k!1))
        (Pair_Term (bit_term (development_kind_path k!2)) (path_term (key c)))))))"
  by (cases r; cases k) (simp_all add: development_locus_def)

section \<open>A cited constant is found by the traversal exactly when the state states it\<close>

lemma answer_statements_stated:
  "development_answer_statements (development_demanded reading) C {|c|}\<noteq>[] \<longleftrightarrow>
    development_statements reading C c\<noteq>[]"
proof -
  have left: "development_answer_statements (development_demanded reading) C {|c|}\<noteq>[] \<longleftrightarrow>
      (\<exists>e\<in>set (snd C). reading e\<noteq>None \<and>
        c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))"
    by (auto simp: development_answer_statements_def development_answer_statement_def development_demanded_def
      filter_empty_conv list_ex_iff)
  have nonempty: "xs\<noteq>[] \<longleftrightarrow> (\<exists>q. q\<in>set xs)" for xs :: "isabelle_term list"
    by (cases xs) auto
  have right: "development_statements reading C c\<noteq>[] \<longleftrightarrow>
      (\<exists>e\<in>set (snd C). reading e\<noteq>None \<and>
        c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))"
    unfolding nonempty development_statements_exact by (auto simp: development_constant_scope_def)
  show ?thesis using left right by simp
qed

theorem native_decomposition_stated:
  assumes present: "state_presents key S R" and kinds: "kinds_present (development_demanded reading) (set ks)"
    and bound: "c<length (fst (snd S))" and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_statements,Pair_Term (path_term (key c)) (development_decomposition_families ident R ks))
      \<in>positive_meaning native_decomposition_system \<longleftrightarrow> development_statements reading (snd S) c\<noteq>[]"
proof -
  have selection: "set (map (state_entities R) ks)=state_entities R ` set ks" by simp
  show ?thesis
    unfolding native_decomposition_statements development_decomposition_families_def
      native_statements_exact[OF present kinds bound selection identity]
    by (rule answer_statements_stated)
qed

theorem native_decomposition_declared:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and bound: "c<length (fst (snd S))"
  shows "(verdict_key_found,Pair_Term (declaration_term Fs) (path_term (key c)))
      \<in>positive_meaning native_decomposition_system \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). c\<in>set (entity_declared e))"
  unfolding native_decomposition_found by (rule native_declared_exact[OF present families bound])

section \<open>A stated and declared constant is a stated contract\<close>

text \<open>
  The traversals find a statement and a declaration; task 60's application needs the constant as the
  state declares it, which is one declaration. The declaration store's single-valuedness, the condition
  task 36 names and the exporter owns (@{const declarations_single_valued}), makes the declaration one:
  two declaring rows would be held at one key, and two rows of one key are one entity.
\<close>

lemma development_stated_native:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and single: "declarations_single_valued Fs"
  shows "development_stated_constant reading (snd S) h\<noteq>None \<longleftrightarrow>
    development_statements reading (snd S) h\<noteq>[] \<and> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
proof
  assume "development_stated_constant reading (snd S) h\<noteq>None"
  then obtain t where "set (development_constant_declarations (snd S) h)={t}"
    and stated: "development_statements reading (snd S) h\<noteq>[]"
    using development_stated_constant_exact by blast
  then have "t\<in>set (development_constant_declarations (snd S) h)" by simp
  then obtain e where "e\<in>set (snd (snd S))" "isabelle_declared_constant e=Some h"
    unfolding development_constant_declarations_member by blast
  then show "development_statements reading (snd S) h\<noteq>[] \<and> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
    using stated by (auto simp: entity_declared_def) (metis)
next
  assume "development_statements reading (snd S) h\<noteq>[] \<and> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
  then have stated: "development_statements reading (snd S) h\<noteq>[]"
    and "\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e)" by blast+
  then obtain e0 where e0: "e0\<in>set (snd (snd S))" "h\<in>set (entity_declared e0)" by blast
  have d0: "isabelle_declared_constant e0=Some h"
    using e0(2) by (simp add: entity_declared_def split: option.splits)
  obtain t where t: "isabelle_declaration_term e0=Some t" using d0 by (cases e0) auto
  have distinct: "distinct (fst (snd S))" by (rule state_presents_distinct_names[OF present])
  have fam: "state_entities R k\<in>set Fs" for k using families by simp
  have inside: "\<forall>i\<in>set (isabelle_entity_positions g). i<length (fst (snd S))" if "g\<in>set (snd (snd S))" for g
    using state_presents_inside[OF present] that by (force simp: state_positions_def)
  have corr: "isabelle_table_correspondence id (fst (snd S)) (fst (snd S))"
    by (simp add: isabelle_table_correspondence_def)
  have same: "e=e0" if e: "e\<in>set (snd (snd S))" "isabelle_declared_constant e=Some h" for e
  proof -
    obtain a where a: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
      by (rule state_presents_row[OF present e(1)])
    obtain a0 where a0: "(a0,entity_row key (snd S) e0)\<in>set (state_entities R (entity_kind_of e0))"
      by (rule state_presents_row[OF present e0(1)])
    have kd: "key h\<in>set (row_declared (entity_row key (snd S) e))"
      using e(2) by (simp add: entity_declared_def)
    have kd0: "key h\<in>set (row_declared (entity_row key (snd S) e0))"
      using d0 by (simp add: entity_declared_def)
    have rows: "(key h,a)\<in>set (declaration_rows Fs)" "(key h,a0)\<in>set (declaration_rows Fs)"
      unfolding declaration_rows_member
      using fam[of "entity_kind_of e"] a kd fam[of "entity_kind_of e0"] a0 kd0 by blast+
    have "a=a0" using single rows unfolding declarations_single_valued_def single_valued_def by blast
    then have "row_identity (entity_row key (snd S) e)=row_identity (entity_row key (snd S) e0)"
      using keyed_agreeD[OF state_presents_row_keys[OF present] presented_rows_member[OF a]
        presented_rows_member[OF a0]] by blast
    then have identical: "isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S)) [e0]"
      by (simp only: entity_row_fields)
    have moved: "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S))) e=e0"
      by (rule iffD1[OF isabelle_local_entities_compared[OF distinct inside[OF e(1)] inside[OF e0(1)]] identical])
    have "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S))) e=isabelle_entity_rename id e"
    proof (rule isabelle_entity_rename_cong)
      fix i assume "i\<in>set (isabelle_entity_positions e)"
      then have "i<length (fst (snd S))" using inside[OF e(1)] by blast
      then show "isabelle_state_embedding (fst (snd S)) (fst (snd S)) i=id i"
        by (rule isabelle_state_embedding_agrees[OF distinct corr])
    qed
    then show "e=e0" using moved by (simp add: isabelle_entity_rename_id)
  qed
  have "set (development_constant_declarations (snd S) h)={t}"
  proof (rule set_eqI)
    fix u
    show "u\<in>set (development_constant_declarations (snd S) h) \<longleftrightarrow> u\<in>{t}"
    proof
      assume "u\<in>set (development_constant_declarations (snd S) h)"
      then obtain e where "e\<in>set (snd (snd S))" "isabelle_declared_constant e=Some h"
        "isabelle_declaration_term e=Some u"
        unfolding development_constant_declarations_member by blast
      then show "u\<in>{t}" using same t by simp
    next
      assume "u\<in>{t}"
      then show "u\<in>set (development_constant_declarations (snd S) h)"
        unfolding development_constant_declarations_member using e0(1) d0 t by blast
    qed
  qed
  then show "development_stated_constant reading (snd S) h\<noteq>None"
    using stated development_stated_constant_exact by blast
qed

section \<open>The application exists exactly when its children are stated\<close>

lemma list_all2_some_defined: "list_all2 (\<lambda>x y. f x=Some y) xs ys \<Longrightarrow> \<forall>x\<in>set xs. f x\<noteq>None"
  by (induction rule: list_all2_induct) simp_all

lemma development_application_stated:
  "(\<exists>H. development_decomposition_application C p I H) \<longleftrightarrow> problem_subject p\<noteq>{||} \<and>
    (\<forall>h\<in>set I. development_stated_constant isabelle_definition_proposition C h\<noteq>None) \<and>
    (\<forall>c. c |\<in>| problem_subject p \<longrightarrow>
      development_stated_constant (development_contract_reading (problem_contract p)) C c\<noteq>None)"
proof -
  have inter: "development_intermediate_problem C h\<noteq>None \<longleftrightarrow>
      development_stated_constant isabelle_definition_proposition C h\<noteq>None" for h
    by (simp add: development_intermediate_problem_def development_constant_problem_def
      development_constant_contract_def)
  have part: "development_part_problem C p c\<noteq>None \<longleftrightarrow>
      development_stated_constant (development_contract_reading (problem_contract p)) C c\<noteq>None" for c
    by (simp add: development_part_problem_def development_constant_problem_def development_constant_contract_def)
  show ?thesis
  proof
    assume "\<exists>H. development_decomposition_application C p I H"
    then obtain ds rs where subject: "problem_subject p\<noteq>{||}"
      and defs: "list_all2 (\<lambda>h q. development_intermediate_problem C h=Some q) I ds"
      and parts: "list_all2 (\<lambda>c q. development_part_problem C p c=Some q) (sorted_list_of_fset (problem_subject p)) rs"
      unfolding development_decomposition_application_def by blast
    show "problem_subject p\<noteq>{||} \<and>
      (\<forall>h\<in>set I. development_stated_constant isabelle_definition_proposition C h\<noteq>None) \<and>
      (\<forall>c. c |\<in>| problem_subject p \<longrightarrow>
        development_stated_constant (development_contract_reading (problem_contract p)) C c\<noteq>None)"
      using subject list_all2_some_defined[OF defs] list_all2_some_defined[OF parts] inter part by simp
  next
    assume "problem_subject p\<noteq>{||} \<and>
      (\<forall>h\<in>set I. development_stated_constant isabelle_definition_proposition C h\<noteq>None) \<and>
      (\<forall>c. c |\<in>| problem_subject p \<longrightarrow>
        development_stated_constant (development_contract_reading (problem_contract p)) C c\<noteq>None)"
    then show "\<exists>H. development_decomposition_application C p I H"
      using development_decomposition_application_exists inter part by simp
  qed
qed

section \<open>Every native application makes progress\<close>

text \<open>
  At a parent that has a locus the subject is one constant, so progress is a nonempty family of
  intermediates; the rule's pattern demands one. The degenerate application, whose only child is the
  parent, is no application of this program.
\<close>

theorem native_decomposition_progress:
  assumes holds: "(decomposition_applies,Pair_Term x (Pair_Term S (Pair_Term row
      (Pair_Term (development_row_family ls) Q))))\<in>positive_meaning native_decomposition_system"
  shows "ls\<noteq>[]"
proof -
  obtain c F f where rule: "(c,F)\<in>set [([0::nat],decomposition_rule)]"
    and conclusion: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term S (Pair_Term row (Pair_Term (development_row_family ls) Q)))"
    by (rule decomposition_applies_family.holds_cases[OF holds])
  from rule have "F=decomposition_rule" by simp
  with conclusion have "development_row_family ls=Pair_Term (f [4]) (f [5])"
    by (simp add: decomposition_rule_def decomposition_conclusion_def)
  then show ?thesis by (rule development_row_family_nonempty)
qed

section \<open>What the program reads at a presented parent\<close>

context
  fixes key ekey inert origin grant supported scope decs ps rs iss rows
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
begin

text \<open>
  At a presented parent the row search always finds the parent's row, so the program holds exactly when
  the intermediates are nonempty, each is found among the first selection's statements and in the
  declaration store, and so is the parent's constant among the second selection's statements.
\<close>

theorem native_decomposition_reads:
  assumes p: "p\<in>set ps" and c: "problem_subject p={|c|}" and xf: "term_formed x"
  shows "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I D P Q)\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    I\<noteq>[] \<and> (\<forall>h\<in>set I. (verdict_statements,Pair_Term (path_term (key h)) D)
        \<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key h)))\<in>positive_meaning native_decomposition_system) \<and>
      (verdict_statements,Pair_Term (path_term (key c)) P)\<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key c)))\<in>positive_meaning native_decomposition_system"
proof -
  define rp where "rp=development_role_path Development_Problem_Role"
  define kp where "kp=development_kind_path (problem_contract p)"
  have locus: "path_term (development_located_at key Development_Problem_Role p)=Pair_Term (bit_term (rp!0))
      (Pair_Term (bit_term (rp!1)) (Pair_Term (bit_term (rp!2)) (Pair_Term (bit_term (kp!0))
        (Pair_Term (bit_term (kp!1)) (Pair_Term (bit_term (kp!2)) (path_term (key c)))))))"
    unfolding rp_def kp_def development_located_at_subject[OF c] by (rule development_locus_term)
  define b where "b=development_problem_body inert (origin p) (grant p) (problem_contract p)"
  have lookup: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=Some b"
    unfolding b_def by (rule development_rows_problem[OF present p]) simp
  have found_rows: "(development_row_search,Pair_Term b (Pair_Term
      (path_term (development_located_at key Development_Problem_Role p)) (development_rows_term rows)))
      \<in>positive_meaning development_rows_program"
    using development_row_lookup_at[OF development_rows_formed[OF present]] lookup by blast
  have found: "(development_row_search,Pair_Term b (Pair_Term
      (path_term (development_located_at key Development_Problem_Role p)) (development_rows_term rows)))
      \<in>positive_meaning native_decomposition_system"
    using found_rows native_decomposition_search by blast
  show ?thesis
  proof
    assume holds: "(decomposition_applies,development_decomposition_argument x rows
        (development_parent_row key inert origin grant p) key I D P Q)\<in>positive_meaning native_decomposition_system"
    obtain c' F f where rule: "(c',F)\<in>set [([0::nat],decomposition_rule)]"
      and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
        development_decomposition_argument x rows (development_parent_row key inert origin grant p) key I D P Q"
      and support: "\<forall>s e q. (s,e,q)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
        (e,evaluate_pattern f q)\<in>positive_meaning native_decomposition_system"
      by (rule decomposition_applies_family.holds_cases[OF holds]) blast
    have F: "F=decomposition_rule" using rule by simp
    have supports: "(decomposition_every,Pair_Term (f [6]) (Pair_Term (f [4]) (f [5])))
        \<in>positive_meaning native_decomposition_system"
      "(verdict_statements,Pair_Term (f [14]) (f [7]))\<in>positive_meaning native_decomposition_system"
      "(decomposition_declared,Pair_Term (f [15]) (Pair_Term (f [4]) (f [5])))
        \<in>positive_meaning native_decomposition_system"
      "(verdict_key_found,Pair_Term (f [15]) (f [14]))\<in>positive_meaning native_decomposition_system"
      using native_rule_support[OF support[unfolded F decomposition_rule_def]]
      by (simp_all add: decomposition_premises_def)
    have fields: "f [14]=path_term (key c)" "Pair_Term (f [4]) (f [5])=development_row_family (map key I)"
      "f [6]=D" "f [7]=P" "f [15]=Q"
      using shape by (simp_all add: F decomposition_rule_def decomposition_conclusion_def
        decomposition_locus_pattern_def development_decomposition_argument_def development_parent_row_def locus)
    have nonempty: "I\<noteq>[]" using development_row_family_nonempty[OF fields(2)[symmetric]] by simp
    have every: "(decomposition_every,Pair_Term D (data_list_term (map path_term (map key I))))
        \<in>positive_meaning native_decomposition_system"
      using supports(1) fields(2,3) by (simp add: development_row_family_def)
    have declared: "(decomposition_declared,Pair_Term Q (data_list_term (map path_term (map key I))))
        \<in>positive_meaning native_decomposition_system"
      using supports(3) fields(2,5) by (simp add: development_row_family_def)
    have "\<forall>h\<in>set I. (verdict_statements,Pair_Term (path_term (key h)) D)\<in>positive_meaning native_decomposition_system"
      using every by (simp add: decomposition_everys.exact native_decomposition_defined)
    moreover have "\<forall>h\<in>set I. (verdict_key_found,Pair_Term Q (path_term (key h)))
        \<in>positive_meaning native_decomposition_system"
      using declared by (simp add: decomposition_declareds.exact)
    ultimately show "I\<noteq>[] \<and> (\<forall>h\<in>set I. (verdict_statements,Pair_Term (path_term (key h)) D)
        \<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key h)))\<in>positive_meaning native_decomposition_system) \<and>
      (verdict_statements,Pair_Term (path_term (key c)) P)\<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key c)))\<in>positive_meaning native_decomposition_system"
      using nonempty supports(2,4) fields(1,4,5) by simp
  next
    assume reads: "I\<noteq>[] \<and> (\<forall>h\<in>set I. (verdict_statements,Pair_Term (path_term (key h)) D)
        \<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key h)))\<in>positive_meaning native_decomposition_system) \<and>
      (verdict_statements,Pair_Term (path_term (key c)) P)\<in>positive_meaning native_decomposition_system \<and>
      (verdict_key_found,Pair_Term Q (path_term (key c)))\<in>positive_meaning native_decomposition_system"
    then obtain h0 hs0 where I: "I=h0#hs0" by (cases I) auto
    have first: "(verdict_statements,Pair_Term (path_term (key h0)) D)\<in>positive_meaning native_decomposition_system"
      using reads I by simp
    have Df: "term_formed D" using positive_meaning_term_formed[OF first] by simp
    have part: "(verdict_statements,Pair_Term (path_term (key c)) P)\<in>positive_meaning native_decomposition_system"
      using reads by blast
    have Pf: "term_formed P" using positive_meaning_term_formed[OF part] by simp
    have part_found: "(verdict_key_found,Pair_Term Q (path_term (key c)))\<in>positive_meaning native_decomposition_system"
      using reads by blast
    have Qf: "term_formed Q" using positive_meaning_term_formed[OF part_found] by simp
    have every: "(decomposition_every,Pair_Term D (Pair_Term (path_term (key h0))
        (data_list_term (map path_term (map key hs0)))))\<in>positive_meaning native_decomposition_system"
      using decomposition_everys.exact[of D "map path_term (map key I)"] Df reads I
      by (simp add: native_decomposition_defined)
    have declared: "(decomposition_declared,Pair_Term Q (Pair_Term (path_term (key h0))
        (data_list_term (map path_term (map key hs0)))))\<in>positive_meaning native_decomposition_system"
      using decomposition_declareds.exact[of Q "map path_term (map key I)"] Qf reads I by simp
    have bf: "term_formed b" using positive_meaning_term_formed[OF found] by simp
    have sf: "term_formed (development_rows_term rows)" using positive_meaning_term_formed[OF found] by simp
    define f where "f=native_values [x,development_rows_term rows,Payload_Term [],b,path_term (key h0),
      data_list_term (map path_term (map key hs0)),D,P,bit_term (rp!0),bit_term (rp!1),bit_term (rp!2),
      bit_term (kp!0),bit_term (kp!1),bit_term (kp!2),path_term (key c),Q]"
    have "(decomposition_applies,evaluate_pattern f (decode_finite_pattern decomposition_conclusion))
        \<in>positive_meaning native_decomposition_system"
    proof (rule decomposition_applies_family.native_step[where c="[0]" and ps=decomposition_premises])
      show "([0],finite_native_rule decomposition_conclusion decomposition_premises)\<in>set [([0],decomposition_rule)]"
        by (simp add: decomposition_rule_def)
      have hs: "term_formed (data_list_term (map path_term (map key hs0)))"
        using development_row_family_formed[of "map key hs0"] by (simp add: development_row_family_def)
      show "\<forall>a\<in>pattern_variables (decode_finite_pattern decomposition_conclusion) \<union>
          (\<Union>(s,d,q)\<in>set decomposition_premises. pattern_variables (decode_finite_pattern q)). term_formed (f a)"
        using xf bf sf hs Df Pf Qf
        by (simp add: f_def decomposition_conclusion_def decomposition_premises_def decomposition_locus_pattern_def)
      show "\<forall>(s,d,q)\<in>set decomposition_premises.
          (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning native_decomposition_system"
        using found every declared part part_found locus
        by (simp add: f_def decomposition_premises_def decomposition_locus_pattern_def)
    qed
    then show "(decomposition_applies,development_decomposition_argument x rows
        (development_parent_row key inert origin grant p) key I D P Q)\<in>positive_meaning native_decomposition_system"
      using I locus by (simp add: f_def decomposition_conclusion_def decomposition_locus_pattern_def
        development_decomposition_argument_def development_parent_row_def development_row_family_def b_def)
  qed
qed

section \<open>The contract: the native applications are task 60's applications\<close>

text \<open>
  At a presented parent, in a state presented by @{const state_presents} with the key the development's
  rows use, whose families the argument carries and whose declaration store is single-valued, the program
  holds exactly when the intermediates are nonempty and task 60's application exists at the parent: the
  equality task 66's entry fixes. No premise states that the state poses the children.
\<close>

theorem native_decomposition_applies:
  assumes p: "p\<in>set ps" and xf: "term_formed x" and state: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)"
    and families: "set Fs=range (state_entities R)" and single: "declarations_single_valued Fs"
    and intermediates: "set I\<subseteq>{..<length (fst (snd S))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
  shows "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I
      (development_decomposition_families ident R [Definition_Kind])
      (development_decomposition_families ident R (development_contract_families (problem_contract p)))
      (declaration_term Fs))\<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    I\<noteq>[] \<and> (\<exists>H. development_decomposition_application (snd S) p I H)"
proof -
  obtain c where c: "problem_subject p={|c|}" by (rule development_rows_problem[OF present p])
  have cb: "c<length (fst (snd S))" using subject c by simp
  have each: "(verdict_statements,Pair_Term (path_term (key h))
      (development_decomposition_families ident R [Definition_Kind]))\<in>positive_meaning native_decomposition_system
      \<longleftrightarrow> development_statements isabelle_definition_proposition (snd S) h\<noteq>[]" if "h\<in>set I" for h
    using native_decomposition_stated[OF state definition_families_present _ identity] intermediates that by auto
  have each_declared: "(verdict_key_found,Pair_Term (declaration_term Fs) (path_term (key h)))
      \<in>positive_meaning native_decomposition_system \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
    if "h\<in>set I" for h
    using native_decomposition_declared[OF state families] intermediates that by auto
  have part: "(verdict_statements,Pair_Term (path_term (key c))
      (development_decomposition_families ident R (development_contract_families (problem_contract p))))
      \<in>positive_meaning native_decomposition_system \<longleftrightarrow>
    development_statements (development_contract_reading (problem_contract p)) (snd S) c\<noteq>[]"
    by (rule native_decomposition_stated[OF state development_contract_families_present cb identity])
  have part_declared: "(verdict_key_found,Pair_Term (declaration_term Fs) (path_term (key c)))
      \<in>positive_meaning native_decomposition_system \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). c\<in>set (entity_declared e))"
    by (rule native_decomposition_declared[OF state families cb])
  have stated: "development_stated_constant r (snd S) d\<noteq>None \<longleftrightarrow>
      development_statements r (snd S) d\<noteq>[] \<and> (\<exists>e\<in>set (snd (snd S)). d\<in>set (entity_declared e))" for r d
    by (rule development_stated_native[OF state families single])
  show ?thesis
    unfolding native_decomposition_reads[OF p c xf] development_application_stated
    using each each_declared part part_declared stated c by auto
qed

section \<open>The native soundness is task 60's, instantiated\<close>

text \<open>
  Every native application is an application of task 60's schema at the parent, by the contract above, and
  its reduction is task 60's theorem.
\<close>

theorem native_decomposition_reduction:
  assumes p: "p\<in>set ps" and xf: "term_formed x" and state: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)"
    and families: "set Fs=range (state_entities R)" and single: "declarations_single_valued Fs"
    and intermediates: "set I\<subseteq>{..<length (fst (snd S))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
    and holds: "(decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I
      (development_decomposition_families ident R [Definition_Kind])
      (development_decomposition_families ident R (development_contract_families (problem_contract p)))
      (declaration_term Fs))\<in>positive_meaning native_decomposition_system"
  obtains H where "development_decomposition_application (snd S) p I H"
    "obligation_reduction {p} (development_problem_stated names C') (development_problem_stated names C')
      (\<lambda>_. fset H)"
proof -
  have "I\<noteq>[] \<and> (\<exists>H. development_decomposition_application (snd S) p I H)"
    using holds native_decomposition_applies[where ident=ident, OF p xf state identity families single
      intermediates subject] by blast
  then obtain H where "development_decomposition_application (snd S) p I H" by blast
  then show ?thesis using that development_decomposition_reduction by blast
qed

end

end
