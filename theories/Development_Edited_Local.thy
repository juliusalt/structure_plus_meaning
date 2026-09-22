theory Development_Edited_Local
  imports Development_State_Edit
begin

section \<open>The local fields of an answer state, read from its request state and the edit\<close>

text \<open>
  An answer state is its request state updated by the edit (@{const edited_state}). Six fields of the answer
  state read only what the edit changes, the subject's own rows or the roots, so each is read at arguments the
  size of the edit: the field's own program at another argument, with no program of its own and no second
  verdict. Each lemma below states that the field's call at its incremental part holds exactly when its call at
  its whole part on the answer state holds, and composes that with the field's whole-state contract. Both
  contracts are consumed by name; nothing of a field is proved again.

  \<^item> \<open>statements\<close> and \<open>excess\<close> read the subject's fibres: the fibre at the subject's key of the request state's
    subject index without the removed rows, followed by the added rows about the key
    (@{text edited_fibres}); \<open>excess\<close> reads them through the subject index restricted to the subject's key.
  \<^item> \<open>formed\<close> reads the added families, the specification family exempt, on a request state that is formed.
  \<^item> \<open>removed\<close> and \<open>added\<close> read the removed and the added families at the empty row store.
  \<^item> \<open>roots\<close> reads the request state's root family twice: the edit keeps the roots.

  The premises are the constructor's contract (@{thm state_edit_contract}), gathered in the locale
  @{text edited_local} and discharged for the constructor once (@{text edited_local_constructed}). Only
  \<open>formed\<close> reads the premise that the request state is closed, as its own field's call on the request state.
  Every incremental part holds the edit's families, the fibres the request state's index finds at one key, or
  the roots: never a whole index or a whole family of the answer state. The families are read once each, by
  the list of kinds the call passes.
\<close>

lemma edited_state_entities:
  "state_entities (edited_state R e) j=filter (\<lambda>z. z\<notin>set (edit_removed e j)) (state_entities R j) @ edit_added e j"
  by (simp add: edited_state_def)

lemma edited_state_roots [simp]: "state_roots (edited_state R e)=state_roots R"
  by (simp add: edited_state_def)

lemma edited_state_member:
  "z\<in>set (state_entities (edited_state R e) j) \<longleftrightarrow>
    (z\<in>set (state_entities R j) \<and> z\<notin>set (edit_removed e j)) \<or> z\<in>set (edit_added e j)"
  by (auto simp: edited_state_entities)

text \<open>A removed row of the constructor's edit is a row of its own kind's family in the request state.\<close>

lemma state_edit_of_removed_within:
  assumes presented: "state_presenter S=Some R" and edit: "state_edit_of S ns removed added=Some e"
  shows "set (edit_removed e j)\<subseteq>set (state_entities R j)"
proof -
  have R: "R=state_rows_of S" using presented by (simp add: state_presenter_def split: if_splits)
  show ?thesis using edit by (auto simp: R state_rows_of_def state_edit_of_def Let_def split: if_splits)
qed

section \<open>The subject's fibres after the edit\<close>

definition edited_fibres :: "state_rows \<Rightarrow> state_edit \<Rightarrow> state_key \<Rightarrow> entity_kind list \<Rightarrow>
    isabelle_context state_family list" where
  "edited_fibres R e k ks=map (\<lambda>j. filter (\<lambda>z. z\<notin>set (edit_removed e j)) (subject_fibre k (state_entities R j)) @
    subject_fibre k (edit_added e j)) ks"

text \<open>
  The fibre of the request state is what its subject index finds at the key (@{thm subject_index_lookup}), and
  the edited fibre is the answer state's own fibre (@{thm key_fibre_edited}).
\<close>

lemma edited_fibres_found:
  "k\<in>set A \<Longrightarrow> store_lookup (subject_index A (state_entities R j)) k=Some (subject_fibre k (state_entities R j))"
  by (simp add: subject_index_lookup)

lemma edited_fibres_whole:
  "edited_fibres R e k ks=map (\<lambda>j. subject_fibre k (state_entities (edited_state R e) j)) ks"
  by (simp add: edited_fibres_def edited_state_entities key_fibre_edited)

lemma fibres_some:
  "(\<exists>F\<in>set (map (\<lambda>j. subject_fibre k (G j)) ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z))) \<longleftrightarrow>
    (\<exists>F\<in>set (map G ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z)))"
proof
  assume "\<exists>F\<in>set (map (\<lambda>j. subject_fibre k (G j)) ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z))"
  then obtain j z where j: "j\<in>set ks" and z: "z\<in>set (subject_fibre k (G j))" by auto
  show "\<exists>F\<in>set (map G ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z))"
  proof (rule bexI[of _ "G j"])
    show "\<exists>z\<in>set (G j). k\<in>set (row_subjects (snd z))" using z by (auto simp: key_fibre_member)
    show "G j\<in>set (map G ks)" using j by simp
  qed
next
  assume "\<exists>F\<in>set (map G ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z))"
  then obtain j z where j: "j\<in>set ks" and z: "z\<in>set (G j)" and k: "k\<in>set (row_subjects (snd z))" by auto
  show "\<exists>F\<in>set (map (\<lambda>j. subject_fibre k (G j)) ks). \<exists>z\<in>set F. k\<in>set (row_subjects (snd z))"
  proof (rule bexI[of _ "subject_fibre k (G j)"])
    have "z\<in>set (subject_fibre k (G j))" using z k by (simp add: key_fibre_member)
    then show "\<exists>z\<in>set (subject_fibre k (G j)). k\<in>set (row_subjects (snd z))" using k by blast
    show "subject_fibre k (G j)\<in>set (map (\<lambda>j. subject_fibre k (G j)) ks)" using j by simp
  qed
qed

lemma fibres_every:
  "(\<forall>F\<in>set (map (\<lambda>j. subject_fibre k (G j)) ks). \<forall>z\<in>set F. k\<in>set (row_subjects (snd z)) \<longrightarrow> Q z) \<longleftrightarrow>
    (\<forall>F\<in>set (map G ks). \<forall>z\<in>set F. k\<in>set (row_subjects (snd z)) \<longrightarrow> Q z)"
  by (auto simp: key_fibre_member)

text \<open>The empty row store, at the type of a row store.\<close>

abbreviation empty_row_store :: "(state_key\<times>isabelle_context state_row) binary_path_store" where
  "empty_row_store \<equiv> Empty_Store"

section \<open>The premises: the constructor's contract\<close>

locale edited_local =
  fixes key :: "nat \<Rightarrow> state_key" and S :: isabelle_rooted_context and R :: state_rows and e :: state_edit
    and S' :: isabelle_rooted_context and ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes request: "state_presents key S R"
    and answer: "state_presents key S' (edited_state R e)"
    and shared: "keys_shared R (edited_state R e)"
    and retired: "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and fresh: "\<And>b q. (b,q)\<in>edit_rows (edit_added e) \<Longrightarrow> b\<notin>fst ` presented_rows R"
    and removed_within: "\<And>j. set (edit_removed e j)\<subseteq>set (state_entities R j)"
    and identity: "\<And>y. term_formed (ident y)"

theorem edited_local_constructed:
  assumes presented: "state_presenter S=Some R"
    and answer: "state_presentable (edit_applied S ns removed added)"
    and edit: "state_edit_of S ns removed added=Some e" and identity: "\<And>y. term_formed (ident y)"
  shows "edited_local state_constant_key S R e (edit_applied S ns removed added) ident"
proof (rule edited_local.intro)
  note contract=state_edit_contract[OF presented answer edit]
  show "state_presents state_constant_key S R" by (rule state_presenter_presents[OF presented])
  show "state_presents state_constant_key (edit_applied S ns removed added) (edited_state R e)" by (rule contract(1))
  show "keys_shared R (edited_state R e)" by (rule contract(2))
  show "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)" by (rule contract(8))
  show "\<And>b q. (b,q)\<in>edit_rows (edit_added e) \<Longrightarrow> b\<notin>fst ` presented_rows R" by (rule contract(9))
  show "\<And>j. set (edit_removed e j)\<subseteq>set (state_entities R j)"
    by (rule state_edit_of_removed_within[OF presented edit])
  show "\<And>y. term_formed (ident y)" by (rule identity)
qed

context edited_local
begin

section \<open>The field \<open>statements\<close>\<close>

theorem edited_statements:
  assumes kinds: "kinds_present demanded (set ks)" and bound: "c<length (fst (snd S'))"
  shows "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (edited_fibres R e (key c) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    (verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_rows_system"
  and "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (edited_fibres R e (key c) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> development_answer_statements demanded (snd S') {|c|}\<noteq>[]"
proof -
  show whole: "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (edited_fibres R e (key c) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    (verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_rows_system"
    by (simp only: verdict_statement_selections.exact[OF identity] edited_fibres_whole fibres_some)
  have selection: "set (map (state_entities (edited_state R e)) ks)=state_entities (edited_state R e) ` set ks" by simp
  show "(verdict_statements,Pair_Term (path_term (key c)) (state_families_term ident (edited_fibres R e (key c) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> development_answer_statements demanded (snd S') {|c|}\<noteq>[]"
    by (simp only: whole native_statements_exact[OF answer kinds bound selection identity])
qed

section \<open>The field \<open>excess\<close>\<close>

theorem edited_excess:
  assumes kinds: "kinds_present replaceable (set ks)" and bound: "c<length (fst (snd S'))"
    and support: "\<And>d. d<length (fst (snd S')) \<Longrightarrow> key d\<in>set ss \<longleftrightarrow> d |\<in>| P"
  shows "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident [key c] (edited_fibres R e (key c) ks)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident (map fst (state_atoms (edited_state R e))) (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_mentions_system"
  and "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident [key c] (edited_fibres R e (key c) ks)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    development_answer_statements_excess replaceable (snd S') {|c|} P=[]"
proof -
  have atom: "key c\<in>set (map fst (state_atoms (edited_state R e)))"
    using atoms_present_atom[OF state_presents_atoms[OF answer] bound] by force
  have own: "key c\<in>set [key c]" by simp
  show whole: "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident [key c] (edited_fibres R e (key c) ks)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident (map fst (state_atoms (edited_state R e))) (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_mentions_system"
    by (simp only: native_excess_rows[OF identity own] native_excess_rows[OF identity atom]
      edited_fibres_whole fibres_every)
  have selection: "set (map (state_entities (edited_state R e)) ks)=state_entities (edited_state R e) ` set ks" by simp
  show "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ss))
      (subject_indexes_term ident [key c] (edited_fibres R e (key c) ks)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    development_answer_statements_excess replaceable (snd S') {|c|} P=[]"
    by (simp only: whole native_excess_exact[OF answer kinds selection bound support identity])
qed

section \<open>The field \<open>formed\<close>\<close>

theorem edited_formed:
  assumes kinds: "set ks=- {Specification_Kind}" and xf: "term_formed x"
    and closed: "(verdict_formed,Pair_Term x (state_families_term ident (map (state_entities R) ks)))
      \<in>positive_meaning verdict_rows_system"
  shows "(verdict_formed,Pair_Term x (state_families_term ident (map (edit_added e) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    (verdict_formed,Pair_Term x (state_families_term ident (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_rows_system"
  and "(verdict_formed,Pair_Term x (state_families_term ident (map (edit_added e) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> isabelle_malformed_entities (snd S')=[]"
proof -
  have kept: "\<forall>F\<in>set (map (state_entities R) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    using closed unfolding verdict_formed_selections.exact[OF identity] by (rule conjunct2)
  have mid: "(\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]) \<longleftrightarrow>
    (\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[])"
  proof
    assume added: "\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    show "\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    proof (intro ballI)
      fix F z assume F: "F\<in>set (map (state_entities (edited_state R e)) ks)" and z: "z\<in>set F"
      then obtain j where j: "j\<in>set ks" "F=state_entities (edited_state R e) j" by auto
      have "(z\<in>set (state_entities R j) \<and> z\<notin>set (edit_removed e j)) \<or> z\<in>set (edit_added e j)"
        using z j(2) by (simp add: edited_state_member)
      moreover have "state_entities R j\<in>set (map (state_entities R) ks)" "edit_added e j\<in>set (map (edit_added e) ks)"
        using j(1) by simp_all
      ultimately show "row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]" using kept added by blast
    qed
  next
    assume answer_rows: "\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F.
      row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    show "\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]"
    proof (intro ballI)
      fix F z assume F: "F\<in>set (map (edit_added e) ks)" and z: "z\<in>set F"
      then obtain j where j: "j\<in>set ks" "F=edit_added e j" by auto
      have "z\<in>set (state_entities (edited_state R e) j)" using z j(2) by (simp add: edited_state_member)
      moreover have "state_entities (edited_state R e) j\<in>set (map (state_entities (edited_state R e)) ks)"
        using j(1) by simp
      ultimately show "row_declared (snd z)\<noteq>[] \<or> row_subjects (snd z)\<noteq>[]" using answer_rows by blast
    qed
  qed
  show whole: "(verdict_formed,Pair_Term x (state_families_term ident (map (edit_added e) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow>
    (verdict_formed,Pair_Term x (state_families_term ident (map (state_entities (edited_state R e)) ks)))
      \<in>positive_meaning verdict_rows_system"
    by (simp only: verdict_formed_selections.exact[OF identity] mid)
  have selection: "set (map (state_entities (edited_state R e)) ks)=state_entities (edited_state R e) ` (- {Specification_Kind})"
    by (simp add: kinds)
  show "(verdict_formed,Pair_Term x (state_families_term ident (map (edit_added e) ks)))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> isabelle_malformed_entities (snd S')=[]"
    by (simp only: whole native_formed_exact_specifications[OF answer selection identity xf])
qed

section \<open>The fields \<open>removed\<close> and \<open>added\<close>\<close>

text \<open>
  A row of the request state is found in the answer state's row store exactly when the edit does not remove it,
  and a row of the answer state is found in the request state's exactly when the edit does not add it: a kept
  row is a row of both, a removed row's key is retired and an added row's key is fresh. So each whole traversal
  reads, row by row, what its traversal of the edit's rows reads at the empty store.
\<close>

lemma answer_rows_member:
  assumes "z\<in>set (state_entities (edited_state R e) j)"
  shows "z\<in>presented_rows (edited_state R e)"
  using assms by (auto simp: presented_rows_def)

lemma removed_found:
  assumes z: "z\<in>set (state_entities R j)"
  shows "store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<longleftrightarrow>
    z\<notin>set (edit_removed e j)"
proof -
  have "store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<longleftrightarrow>
      (\<exists>p. (fst z,p)\<in>presented_rows (edited_state R e))"
    by (simp only: family_row_store_found state_all_families_found)
  also have "\<dots> \<longleftrightarrow> z\<notin>set (edit_removed e j)"
  proof
    assume "\<exists>p. (fst z,p)\<in>presented_rows (edited_state R e)"
    then obtain p where p: "(fst z,p)\<in>presented_rows (edited_state R e)" by blast
    show "z\<notin>set (edit_removed e j)"
    proof
      assume "z\<in>set (edit_removed e j)"
      then have "(fst z,snd z)\<in>edit_rows (edit_removed e)" by (auto simp: edit_rows_def)
      then have out: "fst z\<notin>fst ` presented_rows (edited_state R e)" by (rule retired)
      have "fst z\<in>fst ` presented_rows (edited_state R e)" by (rule image_eqI[rotated, OF p]) simp
      with out show False by blast
    qed
  next
    assume "z\<notin>set (edit_removed e j)"
    then have "z\<in>set (state_entities (edited_state R e) j)" using z by (simp add: edited_state_member)
    then have "(fst z,snd z)\<in>presented_rows (edited_state R e)" by (simp add: answer_rows_member)
    then show "\<exists>p. (fst z,p)\<in>presented_rows (edited_state R e)" by blast
  qed
  finally show ?thesis .
qed

lemma added_found:
  assumes z: "z\<in>set (state_entities (edited_state R e) j)"
  shows "store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<longleftrightarrow> z\<notin>set (edit_added e j)"
proof -
  have "store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<longleftrightarrow> (\<exists>p. (fst z,p)\<in>presented_rows R)"
    by (simp only: family_row_store_found state_all_families_found)
  also have "\<dots> \<longleftrightarrow> z\<notin>set (edit_added e j)"
  proof
    assume "\<exists>p. (fst z,p)\<in>presented_rows R"
    then obtain p where p: "(fst z,p)\<in>presented_rows R" by blast
    show "z\<notin>set (edit_added e j)"
    proof
      assume "z\<in>set (edit_added e j)"
      then have "(fst z,snd z)\<in>edit_rows (edit_added e)" by (auto simp: edit_rows_def)
      then have out: "fst z\<notin>fst ` presented_rows R" by (rule fresh)
      have "fst z\<in>fst ` presented_rows R" by (rule image_eqI[rotated, OF p]) simp
      with out show False by blast
    qed
  next
    assume "z\<notin>set (edit_added e j)"
    then have "z\<in>set (state_entities R j)" using z by (simp add: edited_state_member)
    then have "(fst z,snd z)\<in>presented_rows R" by (auto simp: presented_rows_def)
    then show "\<exists>p. (fst z,p)\<in>presented_rows R" by blast
  qed
  finally show ?thesis .
qed

lemma removed_selections:
  "(\<forall>F\<in>set (map (state_entities R) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<or> C z) \<longleftrightarrow>
    (\<forall>F\<in>set (map (edit_removed e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z)"
proof
  assume whole: "\<forall>F\<in>set (map (state_entities R) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<or> C z"
  show "\<forall>F\<in>set (map (edit_removed e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z"
  proof (intro ballI)
    fix F z assume F: "F\<in>set (map (edit_removed e) ks)" and z: "z\<in>set F"
    then obtain j where j: "j\<in>set ks" "F=edit_removed e j" by auto
    have zD: "z\<in>set (edit_removed e j)" using z j(2) by simp
    have zR: "z\<in>set (state_entities R j)" using removed_within[of j] zD by blast
    have "state_entities R j\<in>set (map (state_entities R) ks)" using j(1) by simp
    then have "store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<or> C z"
      using whole zR by blast
    then show "store_lookup empty_row_store (fst z)\<noteq>None \<or> C z" using removed_found[OF zR] zD by simp
  qed
next
  assume edit: "\<forall>F\<in>set (map (edit_removed e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z"
  show "\<forall>F\<in>set (map (state_entities R) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<or> C z"
  proof (intro ballI)
    fix F z assume F: "F\<in>set (map (state_entities R) ks)" and z: "z\<in>set F"
    then obtain j where j: "j\<in>set ks" "F=state_entities R j" by auto
    have zR: "z\<in>set (state_entities R j)" using z j(2) by simp
    show "store_lookup (family_row_store (state_all_families (edited_state R e))) (fst z)\<noteq>None \<or> C z"
    proof (cases "z\<in>set (edit_removed e j)")
      case True
      have "edit_removed e j\<in>set (map (edit_removed e) ks)" using j(1) by simp
      then have "store_lookup empty_row_store (fst z)\<noteq>None \<or> C z" using edit True by blast
      then show ?thesis by simp
    next
      case False
      then show ?thesis using removed_found[OF zR] by simp
    qed
  qed
qed

lemma added_selections:
  "(\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<or> C z) \<longleftrightarrow>
    (\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z)"
proof
  assume whole: "\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<or> C z"
  show "\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z"
  proof (intro ballI)
    fix F z assume F: "F\<in>set (map (edit_added e) ks)" and z: "z\<in>set F"
    then obtain j where j: "j\<in>set ks" "F=edit_added e j" by auto
    have zA: "z\<in>set (edit_added e j)" using z j(2) by simp
    have zR: "z\<in>set (state_entities (edited_state R e) j)" using zA by (simp add: edited_state_member)
    have "state_entities (edited_state R e) j\<in>set (map (state_entities (edited_state R e)) ks)" using j(1) by simp
    then have "store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<or> C z"
      using whole zR by blast
    then show "store_lookup empty_row_store (fst z)\<noteq>None \<or> C z" using added_found[OF zR] zA by simp
  qed
next
  assume edit: "\<forall>F\<in>set (map (edit_added e) ks). \<forall>z\<in>set F. store_lookup empty_row_store (fst z)\<noteq>None \<or> C z"
  show "\<forall>F\<in>set (map (state_entities (edited_state R e)) ks). \<forall>z\<in>set F.
      store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<or> C z"
  proof (intro ballI)
    fix F z assume F: "F\<in>set (map (state_entities (edited_state R e)) ks)" and z: "z\<in>set F"
    then obtain j where j: "j\<in>set ks" "F=state_entities (edited_state R e) j" by auto
    have zR: "z\<in>set (state_entities (edited_state R e) j)" using z j(2) by simp
    show "store_lookup (family_row_store (state_all_families R)) (fst z)\<noteq>None \<or> C z"
    proof (cases "z\<in>set (edit_added e j)")
      case True
      have "edit_added e j\<in>set (map (edit_added e) ks)" using j(1) by simp
      then have "store_lookup empty_row_store (fst z)\<noteq>None \<or> C z" using edit True by blast
      then show ?thesis by simp
    next
      case False
      then show ?thesis using added_found[OF zR] by simp
    qed
  qed
qed

lemma state_row_values: "\<And>y. term_formed (state_row_term ident y)"
  by (rule state_row_term_formed[OF identity])

lemmas removed_replaceable_rows = removed_replaceable.exact[OF state_row_values identity]
lemmas removed_other_rows = removed_other.exact[OF state_row_values identity]
lemmas added_replaceable_rows = added_replaceable.exact[OF state_row_values identity]
lemmas added_other_rows = added_other.exact[OF state_row_values identity]

theorem edited_removed:
  assumes kinds: "kinds_present replaceable (set kr)" and other: "set ko=- set kr"
    and bound: "c<length (fst (snd S))"
  shows "(verdict_removed,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_removed e) kr)) (state_families_term ident (map (edit_removed e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families (edited_state R e))) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (state_entities R) kr)) (state_families_term ident (map (state_entities R) ko))))
      \<in>positive_meaning verdict_difference_system"
  and "(verdict_removed,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_removed e) kr)) (state_families_term ident (map (edit_removed e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S) {|c|} g \<and> isabelle_declared_constant g=None)
      (isabelle_state_removed (snd S) (snd S'))=[]"
proof -
  show whole: "(verdict_removed,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_removed e) kr)) (state_families_term ident (map (edit_removed e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families (edited_state R e))) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (state_entities R) kr)) (state_families_term ident (map (state_entities R) ko))))
      \<in>positive_meaning verdict_difference_system"
    by (simp only: removed_entry.exact removed_replaceable_rows removed_other_rows family_row_term_def removed_selections)
  have families: "set (map (state_entities R) kr)=state_entities R ` set kr"
    "set (map (state_entities R) ko)=state_entities R ` (- set kr)" by (simp_all add: other)
  show "(verdict_removed,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_removed e) kr)) (state_families_term ident (map (edit_removed e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S) {|c|} g \<and> isabelle_declared_constant g=None)
      (isabelle_state_removed (snd S) (snd S'))=[]"
    by (simp only: whole native_removed_exact[OF request answer shared kinds bound families identity])
qed

theorem edited_added:
  assumes kinds: "kinds_present replaceable (set kr)" and other: "set ko=- set kr"
    and bound: "c<length (fst (snd S'))"
  shows "(verdict_added,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_added e) kr)) (state_families_term ident (map (edit_added e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (state_entities (edited_state R e)) kr))
        (state_families_term ident (map (state_entities (edited_state R e)) ko))))
      \<in>positive_meaning verdict_difference_system"
  and "(verdict_added,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_added e) kr)) (state_families_term ident (map (edit_added e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') {|c|} g) (isabelle_state_added (snd S) (snd S'))=[]"
proof -
  show whole: "(verdict_added,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_added e) kr)) (state_families_term ident (map (edit_added e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (state_entities (edited_state R e)) kr))
        (state_families_term ident (map (state_entities (edited_state R e)) ko))))
      \<in>positive_meaning verdict_difference_system"
    by (simp only: added_entry.exact added_replaceable_rows added_other_rows family_row_term_def added_selections)
  have families: "set (map (state_entities (edited_state R e)) kr)=state_entities (edited_state R e) ` set kr"
    "set (map (state_entities (edited_state R e)) ko)=state_entities (edited_state R e) ` (- set kr)"
    by (simp_all add: other)
  show "(verdict_added,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term (key c)))
      (Pair_Term (state_families_term ident (map (edit_added e) kr)) (state_families_term ident (map (edit_added e) ko))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') {|c|} g) (isabelle_state_added (snd S) (snd S'))=[]"
    by (simp only: whole native_added_exact[OF request answer shared kinds bound families identity])
qed

section \<open>The field \<open>roots\<close>\<close>

text \<open>
  The edit keeps the roots, so the field's call on the answer state reads the request state's root family
  twice, and it holds: the roots agree, which is the premise that the roots agree, derived.
\<close>

theorem edited_roots:
  shows "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots (edited_state R e)))))
      \<in>positive_meaning verdict_difference_system"
  and "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
  and "map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
proof -
  show whole: "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots (edited_state R e)))))
      \<in>positive_meaning verdict_difference_system"
    by (simp only: edited_state_roots)
  show exact: "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
    by (simp only: whole native_roots_exact[OF request answer shared])
  have "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning verdict_difference_system"
    by (simp add: roots_entry.exact)
  then show "map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
    using exact by blast
qed

end

end
