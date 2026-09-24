theory Development_Verdict_Statements
imports Development_Request_Keys Native_Collection_Programs
begin

section \<open>The rows of a presented state as native terms\<close>

text \<open>
  A field of the verdict reads a state's families of rows. A key is a path, a list of keys the data list
  of their paths, and a row the pair of its key and its fields: the keys it declares, the keys it is a
  statement of, the keys it mentions, and its identity, carried inert by whatever presents it. A family
  is the data list of its rows and a selection of families the data list of the families. A kind is the
  family holding a row: no row term carries its kind, and a selection of kinds is the list of families
  passed, never a datum a program compares.
\<close>

definition state_row_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> state_key\<times>'i state_row \<Rightarrow> factor_term" where
  "state_row_term ident z=Pair_Term (path_term (fst z)) (Pair_Term (keys_term (row_declared (snd z)))
    (Pair_Term (keys_term (row_subjects (snd z))) (Pair_Term (keys_term (row_mentions (snd z)))
      (ident (row_identity (snd z))))))"

definition state_family_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> 'i state_family \<Rightarrow> factor_term" where
  "state_family_term ident F=data_list_term (map (state_row_term ident) F)"

definition state_families_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "state_families_term ident Fs=data_list_term (map (state_family_term ident) Fs)"

lemma path_term_image_member [simp]: "path_term k\<in>path_term ` A \<longleftrightarrow> k\<in>A"
  by (auto simp: path_term_injective)

lemma state_row_term_formed:
  assumes "\<And>y. term_formed (ident y)"
  shows "term_formed (state_row_term ident z)"
  using assms by (simp add: state_row_term_def)

lemma state_family_term_formed:
  assumes "\<And>y. term_formed (ident y)"
  shows "term_formed (state_family_term ident F)"
  by (simp add: state_family_term_def data_list_term_formed state_row_term_formed[OF assms])

text \<open>
  Every program of a row reads it through one pattern: the context the call carries, then the row's key,
  its three citation lists and its identity. A rule of a field fills the positions it reads and leaves the
  identity a variable, so no rule states a datum of a statement.
\<close>

definition row_pattern ::
    "local_address finite_term_pattern \<Rightarrow> local_address finite_term_pattern \<Rightarrow> local_address finite_term_pattern \<Rightarrow>
      local_address finite_term_pattern \<Rightarrow> local_address finite_term_pattern \<Rightarrow> local_address finite_term_pattern \<Rightarrow>
      local_address finite_term_pattern" where
  "row_pattern x a d s m i=Finite_Pattern_Pair x (Finite_Pattern_Pair a (Finite_Pattern_Pair d
    (Finite_Pattern_Pair s (Finite_Pattern_Pair m i))))"

text \<open>The row pattern at six variables binds exactly those six: every rule of a row reads its premises' variables here.\<close>

lemma row_pattern_variables:
  "pattern_variables (decode_finite_pattern (row_pattern (native_var 0) (native_var 1) (native_var 2)
    (native_var 3) (native_var 4) (native_var 5)))={[0],[1],[2],[3],[4],[5]}"
  by (auto simp: row_pattern_def)

text \<open>
  The row pattern at six variables is read at the valuation of a context and a row: its evaluation is the
  pair of the context and the row's term, and every field is formed when the identity is. A rule of a row
  whose single premise reads the context and some fields is a rearranging rule
  (@{locale native_rearranging_program}), and its site holds of a context and a row exactly when the callee
  holds of the premise evaluated there: the obligation of the pattern, stated once for every such rule.
\<close>

definition row_valuation :: "factor_term \<Rightarrow> ('i \<Rightarrow> factor_term) \<Rightarrow> state_key\<times>'i state_row \<Rightarrow>
    local_address \<Rightarrow> factor_term" where
  "row_valuation x ident z=native_values [x,path_term (fst z),keys_term (row_declared (snd z)),
    keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))]"

context native_rearranging_program
begin

lemma row_at:
  assumes row: "p=row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)"
    and read: "[0]\<in>pattern_variables (decode_finite_pattern q)" and identity: "\<And>y. term_formed (ident y)"
  shows "(s,Pair_Term x (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    (r,evaluate_pattern (row_valuation x ident z) (decode_finite_pattern q))\<in>positive_meaning P"
proof -
  have evaluated: "evaluate_pattern (row_valuation x ident z) (decode_finite_pattern p)=Pair_Term x (state_row_term ident z)"
    by (simp add: row row_pattern_def row_valuation_def state_row_term_def)
  have rest: "\<forall>a\<in>pattern_variables (decode_finite_pattern p)-pattern_variables (decode_finite_pattern q).
      term_formed (row_valuation x ident z a)"
    using read identity by (auto simp: row row_pattern_def row_valuation_def)
  show ?thesis using at[of "row_valuation x ident z", unfolded evaluated] rest by blast
qed

end

section \<open>A family and a selection of families read by any row reading\<close>

text \<open>
  Every field of the verdict reads a family of rows, and a selection of families, through one traversal:
  a program at a row site reads a row in a context, and \<open>every\<close> or \<open>some\<close> row of a family, and of every
  or some family of a selection, is read by it. The traversal is one notion, generic over the row reading:
  the context is presented by any \<open>present\<close>, the row reading is any relation \<open>reads\<close> the row site holds
  exactly of, and the traversal's contract is stated once here. A row reading of subjects, of formation,
  of mentions found in a store, and the guarded reading of the rows about a key are its instances.
\<close>

locale family_every_reading = every: native_every_program P v r
  for P :: "'u native_system" and v r :: "'u definition_site" +
  fixes present :: "'c \<Rightarrow> factor_term" and ident :: "'i \<Rightarrow> factor_term"
    and reads :: "'c \<Rightarrow> state_key\<times>'i state_row \<Rightarrow> bool"
  assumes identity: "\<And>y. term_formed (ident y)"
    and row: "\<And>c z. (r,Pair_Term (present c) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> reads c z"
begin

theorem exact:
  "(v,Pair_Term (present c) (state_family_term ident F))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<forall>z\<in>set F. reads c z)"
  by (simp add: state_family_term_def every.exact row)

end

locale family_some_reading = some: native_some_program P f r
  for P :: "'u native_system" and f r :: "'u definition_site" +
  fixes present :: "'c \<Rightarrow> factor_term" and ident :: "'i \<Rightarrow> factor_term"
    and reads :: "'c \<Rightarrow> state_key\<times>'i state_row \<Rightarrow> bool"
  assumes identity: "\<And>y. term_formed (ident y)"
    and row: "\<And>c z. (r,Pair_Term (present c) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> reads c z"
begin

theorem exact:
  "(f,Pair_Term (present c) (state_family_term ident F))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<exists>z\<in>set F. reads c z)"
  by (simp add: state_family_term_def some.exact row state_row_term_formed[OF identity])

end

locale selection_every_reading = families: family_every_reading P v r present ident reads +
    every: native_every_program P u v
  for P :: "'u native_system" and u v r :: "'u definition_site" and present ident reads
begin

theorem exact:
  "(u,Pair_Term (present c) (state_families_term ident Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<forall>F\<in>set Fs. \<forall>z\<in>set F. reads c z)"
  by (auto simp: state_families_term_def every.exact families.exact)

end

locale selection_some_reading = families: family_some_reading P f r present ident reads +
    some: native_some_program P s f
  for P :: "'u native_system" and s f r :: "'u definition_site" and present ident reads
begin

theorem exact:
  "(s,Pair_Term (present c) (state_families_term ident Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. reads c z)"
  by (auto simp: state_families_term_def some.exact families.exact state_family_term_formed[OF families.identity])

end

section \<open>A row, and some row of a family, has a key among its subjects\<close>

text \<open>
  The traversal every field of the verdict that looks for a statement of a constant reads: a row has the
  key among the keys it is a statement of, and some row of a family has. It is stated over any family and
  any key, once, and a selection of families is one more \<open>some\<close> over it: the demanded families of the
  verdict, and any family a decomposition reads, instantiate it at their own sites.
\<close>

definition row_subject_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_subject_rule m=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 3)))]"

definition row_subject_rules :: "'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "row_subject_rules m=[([0],row_subject_rule m)]"

locale row_subject_program = native_rule_family P r "row_subject_rules m" + members: native_member_program P m
  for P :: "'u native_system" and r m :: "'u definition_site"
begin

sublocale rearranged: native_rearranging_program P r
    "row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)" m
    "Finite_Pattern_Pair (native_var 0) (native_var 3)"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def row_pattern_variables
  using native_rule_family_axioms[unfolded row_subject_rules_def row_subject_rule_def] by simp

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (path_term k) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> k\<in>set (row_subjects (snd z))"
  by (simp add: rearranged.row_at[OF refl _ identity] row_valuation_def keys_term_def members.exact)

end

locale family_subject_program = rows: row_subject_program P r m + some: native_some_program P f r
  for P :: "'u native_system" and f r m :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(f,Pair_Term (path_term k) (state_family_term ident F))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>z\<in>set F. k\<in>set (row_subjects (snd z)))"
proof -
  interpret reading: family_some_reading P f r path_term ident "\<lambda>k z. k\<in>set (row_subjects (snd z))"
    by unfold_locales (simp_all add: identity rows.exact[OF identity])
  show ?thesis by (simp add: reading.exact)
qed

end

locale selection_subject_program = families: family_subject_program P f r m + some: native_some_program P s f
  for P :: "'u native_system" and s f r m :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(s,Pair_Term (path_term k) (state_families_term ident Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>F\<in>set Fs. \<exists>z\<in>set F. k\<in>set (row_subjects (snd z)))"
proof -
  interpret reading: selection_some_reading P s f r path_term ident "\<lambda>k z. k\<in>set (row_subjects (snd z))"
    by unfold_locales (simp_all add: identity families.rows.exact[OF identity])
  show ?thesis by (simp add: reading.exact)
qed

end

section \<open>A row, every row of a family, declares a constant or states one\<close>

text \<open>
  A row is formed when it declares a constant or is a statement of one: two rules, one reading a nonempty
  declared list and one a nonempty subject list. Neither reads an absence; the specification family, whose
  rows are formed whatever they cite, is a family the selection does not pass.
\<close>

definition row_declares_rule :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_declares_rule=finite_native_rule (row_pattern (native_var 0) (native_var 1)
    (Finite_Pattern_Pair (native_var 2) (native_var 3)) (native_var 4) (native_var 5) (native_var 6)) []"

definition row_states_rule :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_states_rule=finite_native_rule (row_pattern (native_var 0) (native_var 1) (native_var 2)
    (Finite_Pattern_Pair (native_var 3) (native_var 4)) (native_var 5) (native_var 6)) []"

declare row_declares_rule_def [code_unfold] row_states_rule_def [code_unfold]

definition row_formed_rules ::
    "(local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "row_formed_rules=[([0],row_declares_rule),([1],row_states_rule)]"

declare row_formed_rules_def [code_unfold]

definition row_formed_listing :: "(local_address\<times>local_address finite_term_pattern\<times>
    (local_address\<times>('u definition_site\<times>local_address finite_term_pattern)) list) list" where
  "row_formed_listing=
    [([0],row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Pair (native_var 2) (native_var 3)) (native_var 4)
      (native_var 5) (native_var 6),[]),
     ([1],row_pattern (native_var 0) (native_var 1) (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4))
      (native_var 5) (native_var 6),[])]"

lemma row_formed_rules_listing: "row_formed_rules=native_rule_listing row_formed_listing"
  by (simp add: row_formed_rules_def row_formed_listing_def native_rule_listing_def row_declares_rule_def
    row_states_rule_def)

locale row_formed_program = native_rule_family P w row_formed_rules
  for P :: "'u native_system" and w :: "'u definition_site"
begin

sublocale triples: native_listed_law P w row_formed_listing
  unfolding native_listed_law_def row_formed_rules_listing[symmetric] by (rule native_rule_family_axioms)

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(w,Pair_Term x (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
proof
  assume holds: "(w,Pair_Term x (state_row_term ident z))\<in>positive_meaning P"
  have xf: "term_formed x" using holds_formed[OF holds] by simp
  obtain c p ps f where rule: "(c,p,ps)\<in>set (row_formed_listing::(local_address\<times>local_address finite_term_pattern\<times>
      (local_address\<times>('u definition_site\<times>local_address finite_term_pattern)) list) list)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (state_row_term ident z)"
    by (rule triples.holds_triple[OF holds]) (rule that; assumption)
  then have "row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    by (auto simp: row_formed_listing_def row_pattern_def state_row_term_def)
  then show "term_formed x \<and> (row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])" using xf by blast
next
  assume "term_formed x \<and> (row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
  then have xf: "term_formed x" and cited: "row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]" by blast+
  show "(w,Pair_Term x (state_row_term ident z))\<in>positive_meaning P"
  proof (cases "row_declared (snd z)")
    case (Cons d ds)
    have "(w,evaluate_pattern (native_values [x,path_term (fst z),path_term d,keys_term ds,
        keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))])
        (decode_finite_pattern (row_pattern (native_var 0) (native_var 1)
          (Finite_Pattern_Pair (native_var 2) (native_var 3)) (native_var 4) (native_var 5) (native_var 6))))
        \<in>positive_meaning P"
      by (rule triples.step_triple[where c="[0]" and ps="[]"])
        (use xf identity in \<open>simp_all add: row_formed_listing_def row_pattern_def\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def Cons keys_term_Cons)
  next
    case Nil
    then obtain d ds where subjects: "row_subjects (snd z)=d#ds" using cited by (cases "row_subjects (snd z)") auto
    have "(w,evaluate_pattern (native_values [x,path_term (fst z),keys_term (row_declared (snd z)),path_term d,
        keys_term ds,keys_term (row_mentions (snd z)),ident (row_identity (snd z))])
        (decode_finite_pattern (row_pattern (native_var 0) (native_var 1) (native_var 2)
          (Finite_Pattern_Pair (native_var 3) (native_var 4)) (native_var 5) (native_var 6))))
        \<in>positive_meaning P"
      by (rule triples.step_triple[where c="[1]" and ps="[]"])
        (use xf identity in \<open>simp_all add: row_formed_listing_def row_pattern_def\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def subjects keys_term_Cons)
  qed
qed

end

locale family_formed_program = rows: row_formed_program P w + every: native_every_program P v w
  for P :: "'u native_system" and v w :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(v,Pair_Term x (state_family_term ident F))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
proof -
  interpret reading: family_every_reading P v w "\<lambda>x. x" ident
      "\<lambda>x z. term_formed x \<and> (row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
    by unfold_locales (simp_all add: identity rows.exact[OF identity])
  show ?thesis using reading.exact[of x F] by auto
qed

end

locale selection_formed_program = families: family_formed_program P v w + every: native_every_program P u v
  for P :: "'u native_system" and u v w :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(u,Pair_Term x (state_families_term ident Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<forall>F\<in>set Fs. \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
proof -
  interpret reading: selection_every_reading P u v w "\<lambda>x. x" ident
      "\<lambda>x z. term_formed x \<and> (row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
    by unfold_locales (simp_all add: identity families.rows.exact[OF identity])
  show ?thesis using reading.exact[of x Fs] by auto
qed

end

section \<open>The program of the two fields\<close>

abbreviation verdict_row_member :: "local_address option definition_site" where
  "verdict_row_member \<equiv> (Some [],[11])"
abbreviation verdict_row_subject :: "local_address option definition_site" where
  "verdict_row_subject \<equiv> (Some [],[12])"
abbreviation verdict_family_subject :: "local_address option definition_site" where
  "verdict_family_subject \<equiv> (Some [],[13])"
abbreviation verdict_statements :: "local_address option definition_site" where
  "verdict_statements \<equiv> (Some [],[14])"
abbreviation verdict_row_formed :: "local_address option definition_site" where
  "verdict_row_formed \<equiv> (Some [],[15])"
abbreviation verdict_family_formed :: "local_address option definition_site" where
  "verdict_family_formed \<equiv> (Some [],[16])"
abbreviation verdict_formed :: "local_address option definition_site" where
  "verdict_formed \<equiv> (Some [],[17])"

definition verdict_rows_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "verdict_rows_definitions=[(verdict_row_member,native_member_rules verdict_row_member),
    (verdict_row_subject,row_subject_rules verdict_row_member),
    (verdict_family_subject,native_some_rules verdict_family_subject verdict_row_subject),
    (verdict_statements,native_some_rules verdict_statements verdict_family_subject),
    (verdict_row_formed,row_formed_rules),
    (verdict_family_formed,native_every_rules verdict_family_formed verdict_row_formed),
    (verdict_formed,native_every_rules verdict_formed verdict_family_formed)]"

definition finite_verdict_rows :: "local_address option finite_native_system" where
  "finite_verdict_rows=finite_rule_program verdict_rows_definitions"

definition verdict_rows_system :: "local_address option native_system" where
  "verdict_rows_system=decode_finite_system finite_verdict_rows"

lemma finite_verdict_rows_formed: "finite_system_formed finite_verdict_rows"
  by code_simp

lemma verdict_rows_formed: "schema_system_formed verdict_rows_system"
  using finite_verdict_rows_formed by (simp only: verdict_rows_system_def finite_system_formed_correct)

lemma verdict_rows_family:
  assumes member: "(d,rs)\<in>set verdict_rows_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family verdict_rows_system d rs"
proof (rule native_rule_family.intro)
  show "schema_system_formed verdict_rows_system" by (rule verdict_rows_formed)
  have distinct: "distinct (map fst verdict_rows_definitions)" by (simp add: verdict_rows_definitions_def)
  show "((d,c),S)\<in>system_clauses verdict_rows_system \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F)" for c S
  proof -
    have "((d,c),S)\<in>system_clauses verdict_rows_system \<longleftrightarrow>
        (\<exists>rs'. (d,rs')\<in>set verdict_rows_definitions \<and> (\<exists>F. (c,F)\<in>set rs' \<and> S=decode_finite_schema F))"
      unfolding verdict_rows_system_def finite_verdict_rows_def by (rule finite_rule_program_clause)
    then show ?thesis using eq_key_imp_eq_value[OF distinct member] member by blast
  qed
  have site: "d\<in>fst ` set verdict_rows_definitions" using member by (rule rev_image_eqI) simp
  show "schema_call_formed verdict_rows_system d t \<longleftrightarrow> term_formed t" for t
    unfolding verdict_rows_system_def finite_verdict_rows_def
    by (rule finite_rule_program_call[OF verdict_rows_formed[unfolded verdict_rows_system_def
      finite_verdict_rows_def] site])
  show "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}" by (rule plain)
qed

interpretation verdict_statement_selections:
    selection_subject_program verdict_rows_system verdict_statements verdict_family_subject
      verdict_row_subject verdict_row_member
  unfolding selection_subject_program_def family_subject_program_def row_subject_program_def
    native_some_program_def native_member_program_def
  by (intro conjI; rule verdict_rows_family)
    (simp_all add: verdict_rows_definitions_def native_some_rules_def native_some_first_def
      native_member_rules_def native_member_here_def native_member_later_def row_subject_rules_def
      row_subject_rule_def)

interpretation verdict_formed_selections:
    selection_formed_program verdict_rows_system verdict_formed verdict_family_formed verdict_row_formed
  unfolding selection_formed_program_def family_formed_program_def row_formed_program_def
    native_every_program_def
  by (intro conjI; rule verdict_rows_family)
    (simp_all add: verdict_rows_definitions_def native_every_rules_def native_every_nil_def
      native_every_step_def row_formed_rules_def row_declares_rule_def row_states_rule_def)

section \<open>The field \<open>statements\<close>\<close>

text \<open>
  A presented row of the state has the subject's key among its subjects exactly when its entity is a
  statement of the subject: keys are injective on the state's atoms, and every subject of an entity is one
  of them. The rows of the demanded families that have the key are therefore the rows of
  @{const development_answer_statements}, and the field's acceptance reading, that the answer states one of
  the demanded kind, is that some such row exists: a \<open>some\<close>, not an absence.
\<close>

lemma entity_row_subject_key:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and member: "e\<in>set (snd (snd S))"
  shows "key c\<in>set (row_subjects (entity_row key (snd S) e)) \<longleftrightarrow>
    c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
proof -
  have "set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)\<subseteq>
      {..<length (fst (snd S))}"
    using state_presents_subject_inside[OF present member] by blast
  then show ?thesis by (simp add: state_presents_key_member[OF present bound])
qed

text \<open>
  Every entity of a presented state has its row at some key; the entity-key condition names one key
  assignment that keys every entity's row as the presentation does. It is a condition of a presentation,
  stated once here and consumed by name.
\<close>

lemma entity_row_presented:
  assumes present: "state_presents key S R" and member: "e\<in>set (snd (snd S))"
  shows "\<exists>a. (a,entity_row key (snd S) e)\<in>presented_rows R"
proof -
  obtain a where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
    by (rule state_presents_row[OF present member])
  then show ?thesis by (blast intro: presented_rows_member)
qed

text \<open>
  The keyed rows of a \<open>kinds_present\<close> selection having the key of \<open>c\<close> among their subjects are the
  presented rows of the entities the selection's predicate holds of that have \<open>c\<close> among theirs. Every use
  that reads the rows about a constant, over whatever selection, is a corollary of this one lemma.
\<close>

lemma selection_rows_about:
  assumes present: "state_presents key S R" and kinds: "kinds_present demanded ks"
    and bound: "c<length (fst (snd S))"
  shows "(\<exists>k\<in>ks. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p) \<longleftrightarrow>
    (a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set (snd (snd S)). demanded e \<and>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<and>
      p=entity_row key (snd S) e)"
proof
  assume "(\<exists>k\<in>ks. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p)"
  then obtain k where k: "k\<in>ks" and row: "(a,p)\<in>set (state_entities R k)"
    and about: "key c\<in>set (row_subjects p)" by blast
  obtain e where e: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
    by (rule state_presents_row_origin[OF present row])
  have "demanded e" using kinds_presentD[OF kinds, of e] e(2) k by simp
  moreover have "c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
    using entity_row_subject_key[OF present bound e(1)] about e(3) by simp
  ultimately show "(a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set (snd (snd S)). demanded e \<and>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<and>
      p=entity_row key (snd S) e)"
    using presented_rows_member[OF row] e(1) e(3) by blast
next
  assume "(a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set (snd (snd S)). demanded e \<and>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<and>
      p=entity_row key (snd S) e)"
  then obtain e where row: "(a,p)\<in>presented_rows R" and e: "e\<in>set (snd (snd S))" "demanded e"
    "c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
    "p=entity_row key (snd S) e" by blast
  obtain k where family: "(a,p)\<in>set (state_entities R k)" by (rule presented_rows_family[OF row])
  have "k=entity_kind_of e"
  proof (rule ccontr)
    assume "k\<noteq>entity_kind_of e"
    then have "entity_row key (snd S) e\<notin>set (map snd (state_entities R k))"
      by (rule state_presents_kind_only[OF present e(1)])
    then show False using family e(4) by force
  qed
  then have "k\<in>ks" using kinds_presentD[OF kinds, of e] e(2) by simp
  moreover have "key c\<in>set (row_subjects p)" using entity_row_subject_key[OF present bound e(1)] e(3) e(4) by simp
  ultimately show "(\<exists>k\<in>ks. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p)"
    using family by blast
qed

text \<open>A property of every row of a selection of families is one of every keyed row of the selected kinds.\<close>

lemma selection_rows_all:
  assumes selection: "set Fs=G ` ks"
  shows "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. P z \<longrightarrow> Q z) \<longleftrightarrow>
    (\<forall>a p. (\<exists>k\<in>ks. (a,p)\<in>set (G k)) \<and> P (a,p) \<longrightarrow> Q (a,p))"
proof
  assume rows: "\<forall>F\<in>set Fs. \<forall>z\<in>set F. P z \<longrightarrow> Q z"
  show "\<forall>a p. (\<exists>k\<in>ks. (a,p)\<in>set (G k)) \<and> P (a,p) \<longrightarrow> Q (a,p)"
  proof (intro allI impI)
    fix a p assume "(\<exists>k\<in>ks. (a,p)\<in>set (G k)) \<and> P (a,p)"
    then obtain k where k: "k\<in>ks" and row: "(a,p)\<in>set (G k)" and about: "P (a,p)" by blast
    have "G k\<in>set Fs" using selection k by simp
    then show "Q (a,p)" using rows row about by blast
  qed
next
  assume rows: "\<forall>a p. (\<exists>k\<in>ks. (a,p)\<in>set (G k)) \<and> P (a,p) \<longrightarrow> Q (a,p)"
  show "\<forall>F\<in>set Fs. \<forall>z\<in>set F. P z \<longrightarrow> Q z"
  proof (intro ballI impI)
    fix F z assume F: "F\<in>set Fs" and z: "z\<in>set F" and about: "P z"
    obtain k where k: "k\<in>ks" and Fk: "F=G k" using F selection by auto
    obtain a p where zp: "z=(a,p)" by (cases z)
    show "Q z" using rows k z Fk about zp by blast
  qed
qed

theorem statement_rows_exact:
  assumes present: "state_presents key S R" and kinds: "kinds_present demanded ks"
    and bound: "c<length (fst (snd S))"
  shows "{p. p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k))) \<and> key c\<in>set (row_subjects p)}=
    entity_row key (snd S) ` set (development_answer_statements demanded (snd S) {|c|})"
proof -
  let ?A="{p. p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k))) \<and> key c\<in>set (row_subjects p)}"
  let ?B="entity_row key (snd S) ` set (development_answer_statements demanded (snd S) {|c|})"
  have statements: "e\<in>set (development_answer_statements demanded (snd S) {|c|}) \<longleftrightarrow> e\<in>set (snd (snd S)) \<and>
      demanded e \<and> c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)" for e
    by (auto simp: development_answer_statements_def development_answer_statement_def list_ex_iff)
  have "p\<in>?A \<longleftrightarrow> p\<in>?B" for p
  proof -
    have "p\<in>?A \<longleftrightarrow> (\<exists>a. (\<exists>k\<in>ks. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p))" by force
    also have "\<dots> \<longleftrightarrow> (\<exists>a. (a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set (snd (snd S)). demanded e \<and>
        c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<and>
        p=entity_row key (snd S) e))"
      by (intro ex_cong1 selection_rows_about[OF present kinds bound])
    also have "\<dots> \<longleftrightarrow> p\<in>?B" using entity_row_presented[OF present] statements by blast
    finally show ?thesis .
  qed
  then show ?thesis by (rule set_eqI)
qed

theorem native_statements_exact:
  assumes present: "state_presents key S R" and kinds: "kinds_present demanded ks"
    and bound: "c<length (fst (snd S))" and selection: "set Fs=state_entities R ` ks"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident Fs))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    development_answer_statements demanded (snd S) {|c|}\<noteq>[]"
proof -
  have "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident Fs))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    (\<exists>p. p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k))) \<and> key c\<in>set (row_subjects p))"
    by (auto simp: verdict_statement_selections.exact[OF identity] selection)
  also have "\<dots> \<longleftrightarrow> {p. p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k))) \<and> key c\<in>set (row_subjects p)}\<noteq>{}"
    by blast
  also have "\<dots> \<longleftrightarrow> entity_row key (snd S) ` set (development_answer_statements demanded (snd S) {|c|})\<noteq>{}"
    by (simp only: statement_rows_exact[OF present kinds bound])
  also have "\<dots> \<longleftrightarrow> development_answer_statements demanded (snd S) {|c|}\<noteq>[]" by simp
  finally show ?thesis .
qed

text \<open>
  The verdict reads the field in the answer state, with the request's subject carried there by the
  correspondence of the two tables. The subject's key is the request's: @{const request_presents} gives
  it as the key of the problem's one subject constant, and the shared key assignment keys the carried
  constant with the same key, so the field consumes the request's key unchanged. An answer that drops the
  subject's name is outside this lemma, and left to the verdict's entry.
\<close>

corollary native_statements_answer:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and named: "(!) (fst (snd S)) ` fset (problem_subject (fst r))\<subseteq>set (fst (snd S'))"
    and kinds: "kinds_present demanded kinds" and selection: "set Fs=state_entities R' ` kinds"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_statements,Pair_Term (path_term k) (state_families_term ident Fs))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    development_answer_statements demanded (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject (fst r)))\<noteq>[]"
proof -
  have present: "state_presents key S R" using request by (simp add: request_presents_def)
  obtain c where subject: "problem_subject (fst r)={|c|}" and k: "k=key c" and bound: "c<length (fst (snd S))"
    and "(k,fst (snd S)!c)\<in>set (state_atoms R)" and "set ks=key ` fset (fst (snd (snd r)))"
    and "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF request])
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have name: "fst (snd S)!c\<in>set (fst (snd S'))" using named subject by simp
  have carried: "key' (?f c)=key c" by (rule keys_shared_embedding[OF present present' shared bound name])
  have "isabelle_name_at (fst (snd S')) (?f c)=Some (fst (snd S)!c)"
    by (rule isabelle_state_embedding_shared) (simp_all add: isabelle_name_at_def bound name)
  then have bound': "?f c<length (fst (snd S'))" by (simp add: isabelle_name_at_def split: if_splits)
  have image: "fimage ?f (problem_subject (fst r))={|?f c|}" using subject by simp
  show ?thesis
    unfolding k carried[symmetric] image by (rule native_statements_exact[OF present' kinds bound' selection identity])
qed

section \<open>The field \<open>malformed\<close>\<close>

text \<open>
  An entity is malformed when it declares nothing, is a statement of nothing, and is not a specification.
  Outside the specifications the subjects of an entity do not depend on the development constants it is
  read against, so the subjects its row carries are the ones @{const isabelle_malformed_entities} reads.
\<close>

lemma entity_subjects_outside_specifications:
  "entity_kind_of e\<noteq>Specification_Kind \<Longrightarrow> isabelle_entity_subjects names D e=isabelle_entity_subjects names D' e"
  by (cases e) simp_all

lemma isabelle_malformed_entities_member:
  "e\<in>set (isabelle_malformed_entities C) \<longleftrightarrow> e\<in>set (snd C) \<and> entity_kind_of e\<noteq>Specification_Kind \<and>
    isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst C) [] e=[]"
  by (cases e) (auto simp: isabelle_malformed_entities_def)

lemma entity_row_formed:
  assumes kind: "entity_kind_of e\<noteq>Specification_Kind"
  shows "(row_declared (entity_row key C e)\<noteq>[] \<or> row_subjects (entity_row key C e)\<noteq>[]) \<longleftrightarrow>
    \<not>(isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst C) [] e=[])"
  using entity_subjects_outside_specifications[OF kind, of "fst C" "isabelle_development_constants (snd C)" "[]"]
  by (simp add: entity_declared_def split: option.splits)

theorem malformed_row_exact:
  assumes member: "e\<in>set (snd C)" and kind: "entity_kind_of e\<noteq>Specification_Kind"
    and identity: "\<And>y. term_formed (ident y)" and xf: "term_formed x"
  shows "(verdict_row_formed,Pair_Term x (state_row_term ident (a,entity_row key C e)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> e\<notin>set (isabelle_malformed_entities C)"
  using member kind xf entity_row_formed[OF kind, of key C]
  by (simp add: verdict_formed_selections.families.rows.exact[OF identity] isabelle_malformed_entities_member)

theorem native_formed_exact:
  assumes present: "state_presents key S R"
    and kinds: "kinds_present (\<lambda>e. entity_kind_of e\<noteq>Specification_Kind) ks"
    and selection: "set Fs=state_entities R ` ks"
    and identity: "\<And>y. term_formed (ident y)" and xf: "term_formed x"
  shows "(verdict_formed,Pair_Term x (state_families_term ident Fs))\<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    isabelle_malformed_entities (snd S)=[]"
proof -
  have "(verdict_formed,Pair_Term x (state_families_term ident Fs))\<in>positive_meaning verdict_rows_system \<longleftrightarrow>
      (\<forall>p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k))). row_declared p\<noteq>[] \<or> row_subjects p\<noteq>[])"
    using xf by (auto simp: verdict_formed_selections.exact[OF identity] selection)
  also have "\<dots> \<longleftrightarrow> (\<forall>p\<in>entity_row key (snd S) ` {e\<in>set (snd (snd S)). entity_kind_of e\<noteq>Specification_Kind}.
      row_declared p\<noteq>[] \<or> row_subjects p\<noteq>[])"
    by (simp only: kinds_present_rows[OF present kinds])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<noteq>Specification_Kind \<longrightarrow>
      \<not>(isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst (snd S)) [] e=[]))"
    unfolding Ball_def image_iff mem_Collect_eq
    using entity_row_formed[where key=key and C="snd S"] by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>e. e\<notin>set (isabelle_malformed_entities (snd S)))"
    by (auto simp: isabelle_malformed_entities_member)
  also have "\<dots> \<longleftrightarrow> isabelle_malformed_entities (snd S)=[]" by simp
  finally show ?thesis .
qed

corollary native_formed_exact_specifications:
  assumes present: "state_presents key S R" and selection: "set Fs=state_entities R ` (- {Specification_Kind})"
    and identity: "\<And>y. term_formed (ident y)" and xf: "term_formed x"
  shows "(verdict_formed,Pair_Term x (state_families_term ident Fs))\<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    isabelle_malformed_entities (snd S)=[]"
  by (rule native_formed_exact[OF present _ selection identity xf]) (simp add: kinds_present_def)

end
