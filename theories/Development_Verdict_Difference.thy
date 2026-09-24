theory Development_Verdict_Difference
imports Development_Verdict_Mentions
begin

section \<open>The search of a presented state's rows by row key\<close>

text \<open>
  A row of a presented state is found by its key. The rows of any selection of families are held in one
  path store at their keys, each row with its key as the value there, and the store is searched with the
  store's own search: this is stated once, for any presented state and any selection of families, and every
  reading of a state's rows by row key consumes it — the difference of two states below, and request
  construction when it searches the request state's rows.
\<close>

definition family_row_store :: "'i state_family list \<Rightarrow> (state_key\<times>'i state_row) binary_path_store" where
  "family_row_store Fs=path_store (map (\<lambda>z. (fst z,z)) (concat Fs))"

definition family_row_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "family_row_term ident Fs=store_term (state_row_term ident) (family_row_store Fs)"

lemma family_row_term_formed:
  assumes "\<And>y. term_formed (ident y)"
  shows "term_formed (family_row_term ident Fs)"
  unfolding family_row_term_def by (rule store_term_formed) (rule state_row_term_formed[OF assms])

theorem family_row_store_found:
  "store_lookup (family_row_store Fs) a\<noteq>None \<longleftrightarrow> (\<exists>F\<in>set Fs. \<exists>p. (a,p)\<in>set F)"
proof -
  have "store_lookup (family_row_store Fs) a\<noteq>None \<longleftrightarrow> a\<in>fst ` set (concat Fs)"
    by (simp only: family_row_store_def path_store_present) (simp add: image_image)
  also have "\<dots> \<longleftrightarrow> (\<exists>F\<in>set Fs. \<exists>p. (a,p)\<in>set F)" by force
  finally show ?thesis .
qed

theorem family_row_store_lookup:
  assumes sv: "single_valued (\<Union>F\<in>set Fs. set F)"
  shows "store_lookup (family_row_store Fs) a=Some z \<longleftrightarrow> fst z=a \<and> (\<exists>F\<in>set Fs. z\<in>set F)"
proof -
  have "single_valued (set (map (\<lambda>z. (fst z,z)) (concat Fs)))"
    unfolding single_valued_def
  proof (intro allI impI)
    fix x y w
    assume y: "(x,y)\<in>set (map (\<lambda>z. (fst z,z)) (concat Fs))" and w: "(x,w)\<in>set (map (\<lambda>z. (fst z,z)) (concat Fs))"
    have ym: "(x,snd y)\<in>(\<Union>F\<in>set Fs. set F)" and yx: "x=fst y" using y by force+
    have wm: "(x,snd w)\<in>(\<Union>F\<in>set Fs. set F)" and wx: "x=fst w" using w by force+
    have "snd y=snd w" by (rule single_valued_outputs[OF sv ym wm])
    then show "y=w" using yx wx by (simp add: prod_eq_iff)
  qed
  then have "store_lookup (family_row_store Fs) a=Some z \<longleftrightarrow> (a,z)\<in>set (map (\<lambda>z. (fst z,z)) (concat Fs))"
    unfolding family_row_store_def by (rule path_store_lookup)
  also have "\<dots> \<longleftrightarrow> fst z=a \<and> (\<exists>F\<in>set Fs. z\<in>set F)" by auto
  finally show ?thesis .
qed

subsection \<open>A presented state's rows are single-valued at their keys\<close>

lemma state_presents_entity_inside:
  assumes present: "state_presents key S R" and member: "e\<in>set (snd (snd S))"
  shows "\<forall>i\<in>set (isabelle_entity_positions e). i<length (fst (snd S))"
  using state_presents_inside[OF present] member by (force simp: state_positions_def)

lemma state_presents_root_inside:
  assumes present: "state_presents key S R" and member: "t\<in>set (fst S)"
  shows "\<forall>i\<in>set (isabelle_term_positions t). i<length (fst (snd S))"
  using state_presents_inside[OF present] member by (force simp: state_positions_def)

lemma isabelle_entity_rename_embedding_self:
  assumes distinct: "distinct names" and inside: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
  shows "isabelle_entity_rename (isabelle_state_embedding names names) e=e"
proof -
  have corr: "isabelle_table_correspondence id names names" by (simp add: isabelle_table_correspondence_def)
  have "isabelle_entity_rename (isabelle_state_embedding names names) e=isabelle_entity_rename id e"
    by (rule isabelle_entity_rename_cong) (use inside isabelle_state_embedding_agrees[OF distinct corr] in simp)
  then show ?thesis by (simp add: isabelle_entity_rename_id)
qed

theorem state_presents_rows_single_valued:
  assumes present: "state_presents key S R"
  shows "single_valued (presented_rows R)"
  unfolding single_valued_def
proof (intro allI impI)
  fix a p q assume p: "(a,p)\<in>presented_rows R" and q: "(a,q)\<in>presented_rows R"
  obtain k where pk: "(a,p)\<in>set (state_entities R k)" by (rule presented_rows_family[OF p])
  obtain l where ql: "(a,q)\<in>set (state_entities R l)" by (rule presented_rows_family[OF q])
  obtain e where e: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
    by (rule state_presents_row_origin[OF present pk])
  obtain g where g: "g\<in>set (snd (snd S))" "entity_kind_of g=l" "q=entity_row key (snd S) g"
    by (rule state_presents_row_origin[OF present ql])
  have dist: "distinct (fst (snd S))" by (rule state_presents_distinct_names[OF present])
  have ie: "\<forall>i\<in>set (isabelle_entity_positions e). i<length (fst (snd S))"
    by (rule state_presents_entity_inside[OF present e(1)])
  have ig: "\<forall>i\<in>set (isabelle_entity_positions g). i<length (fst (snd S))"
    by (rule state_presents_entity_inside[OF present g(1)])
  have "row_identity p=row_identity q" using keyed_agreeD[OF state_presents_row_keys[OF present] p q] by simp
  then have "isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S)) [g]"
    using e(3) g(3) by simp
  then have "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S))) e=g"
    by (simp only: isabelle_local_entities_compared[OF dist ie ig])
  then have "e=g" by (simp only: isabelle_entity_rename_embedding_self[OF dist ie])
  then show "p=q" using e(3) g(3) by simp
qed

theorem state_row_search:
  assumes present: "state_presents key S R"
  shows "store_lookup (family_row_store (state_all_families R)) a=Some z \<longleftrightarrow> fst z=a \<and> z\<in>presented_rows R"
proof -
  have sv: "single_valued (\<Union>F\<in>set (state_all_families R). set F)"
    unfolding state_all_families_rows by (rule state_presents_rows_single_valued[OF present])
  show ?thesis unfolding family_row_store_lookup[OF sv] state_all_families_rows[symmetric] by simp
qed

section \<open>Two presentations sharing keys, and their difference\<close>

text \<open>
  Two presented states under @{const keys_shared} use one key assignment. Then the correspondence of the two
  name tables is identity on the atoms both hold: a row of the request state and a row of the answer state
  have the same key exactly when @{const isabelle_state_embedding} carries the one's entity to the other's.
  The comparison of local presentations across two tables is consumed from
  @{thm isabelle_local_entities_compared}; nothing of it is derived again.

  The difference of the two presentations is therefore a difference of families: a row of the one state is
  found among the other's by its key exactly when its entity persists, as @{const isabelle_state_removed} and
  @{const isabelle_state_added} read it. This is a consequence of task 46's premises, not the reduction of an
  edit, which is stated after it over the answer's edit.
\<close>

theorem shared_keys_correspondence:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and e: "e\<in>set (snd (snd S))" and row: "(a,entity_row key (snd S) e)\<in>presented_rows R"
    and g: "g\<in>set (snd (snd S'))" and row': "(b,entity_row key' (snd S') g)\<in>presented_rows R'"
  shows "a=b \<longleftrightarrow> isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) e=g"
proof -
  have "a=b \<longleftrightarrow> row_identity (entity_row key (snd S) e)=row_identity (entity_row key' (snd S') g)"
    by (rule keys_shared_row[OF shared row row'])
  also have "\<dots> \<longleftrightarrow> isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S')) [g]"
    by simp
  also have "\<dots> \<longleftrightarrow> isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) e=g"
    by (rule isabelle_local_entities_compared[OF state_presents_distinct_names[OF present']
      state_presents_entity_inside[OF present e] state_presents_entity_inside[OF present' g]])
  finally show ?thesis .
qed

theorem state_difference_removed:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and e: "e\<in>set (snd (snd S))" and row: "(a,entity_row key (snd S) e)\<in>presented_rows R"
  shows "store_lookup (family_row_store (state_all_families R')) a\<noteq>None \<longleftrightarrow>
    e\<notin>set (isabelle_state_removed (snd S) (snd S'))"
proof -
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have "store_lookup (family_row_store (state_all_families R')) a\<noteq>None \<longleftrightarrow> (\<exists>q. (a,q)\<in>presented_rows R')"
    by (simp only: family_row_store_found state_all_families_found)
  also have "\<dots> \<longleftrightarrow> (\<exists>g\<in>set (snd (snd S')). isabelle_entity_rename ?f e=g)"
  proof
    assume "\<exists>q. (a,q)\<in>presented_rows R'"
    then obtain q where q: "(a,q)\<in>presented_rows R'" by blast
    obtain k where qk: "(a,q)\<in>set (state_entities R' k)" by (rule presented_rows_family[OF q])
    obtain g where g: "g\<in>set (snd (snd S'))" "entity_kind_of g=k" "q=entity_row key' (snd S') g"
      by (rule state_presents_row_origin[OF present' qk])
    have "a=a \<longleftrightarrow> isabelle_entity_rename ?f e=g"
      by (rule shared_keys_correspondence[OF present present' shared e row g(1)]) (use q g in simp)
    then show "\<exists>g\<in>set (snd (snd S')). isabelle_entity_rename ?f e=g" using g(1) by blast
  next
    assume "\<exists>g\<in>set (snd (snd S')). isabelle_entity_rename ?f e=g"
    then obtain g where g: "g\<in>set (snd (snd S'))" "isabelle_entity_rename ?f e=g" by blast
    obtain b where b: "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))"
      by (rule state_presents_row[OF present' g(1)])
    have "a=b"
      using shared_keys_correspondence[OF present present' shared e row g(1) presented_rows_member[OF b]] g(2) by simp
    then show "\<exists>q. (a,q)\<in>presented_rows R'" using presented_rows_member[OF b] by blast
  qed
  also have "\<dots> \<longleftrightarrow> e\<notin>set (isabelle_state_removed (snd S) (snd S'))"
    using e by (auto simp: isabelle_state_removed_exact)
  finally show ?thesis .
qed

theorem state_difference_added:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and g: "g\<in>set (snd (snd S'))" and row': "(b,entity_row key' (snd S') g)\<in>presented_rows R'"
  shows "store_lookup (family_row_store (state_all_families R)) b\<noteq>None \<longleftrightarrow>
    g\<notin>set (isabelle_state_added (snd S) (snd S'))"
proof -
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have "store_lookup (family_row_store (state_all_families R)) b\<noteq>None \<longleftrightarrow> (\<exists>p. (b,p)\<in>presented_rows R)"
    by (simp only: family_row_store_found state_all_families_found)
  also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). isabelle_entity_rename ?f e=g)"
  proof
    assume "\<exists>p. (b,p)\<in>presented_rows R"
    then obtain p where p: "(b,p)\<in>presented_rows R" by blast
    obtain k where pk: "(b,p)\<in>set (state_entities R k)" by (rule presented_rows_family[OF p])
    obtain e where e: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
      by (rule state_presents_row_origin[OF present pk])
    have "b=b \<longleftrightarrow> isabelle_entity_rename ?f e=g"
      by (rule shared_keys_correspondence[OF present present' shared e(1) _ g row']) (use p e in simp)
    then show "\<exists>e\<in>set (snd (snd S)). isabelle_entity_rename ?f e=g" using e(1) by blast
  next
    assume "\<exists>e\<in>set (snd (snd S)). isabelle_entity_rename ?f e=g"
    then obtain e where e: "e\<in>set (snd (snd S))" "isabelle_entity_rename ?f e=g" by blast
    obtain a where a: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
      by (rule state_presents_row[OF present e(1)])
    have "a=b"
      using shared_keys_correspondence[OF present present' shared e(1) presented_rows_member[OF a] g row'] e(2) by simp
    then show "\<exists>p. (b,p)\<in>presented_rows R" using presented_rows_member[OF a] by blast
  qed
  also have "\<dots> \<longleftrightarrow> g\<notin>set (isabelle_state_added (snd S) (snd S'))"
    using g by (auto simp: isabelle_state_added_exact)
  finally show ?thesis .
qed

section \<open>The reduction of an edit\<close>

text \<open>
  An answer's edit is read as two families of rows over the request state's atoms: the rows @{text D} it
  removes, rows of the request state, and the rows @{text A} it adds, rows of the answer state. The edit is
  reduced when every row of @{text D} is a row of the request state and no row of @{text A} has the key of a
  row of the request state, and it is applied when the answer state's rows are the request state's without
  @{text D} together with @{text A}. That condition is @{text edit_reduced}; its owner is the answer reader,
  which establishes it for the edit it reads, and it is decided over the edit's two families against the rows.
  Under it the report's removed and added lists are the answer's own two families
  (@{text edit_reduced_lists}), which the verdict's entry consumes rather than assumes.
\<close>

definition edit_reduced :: "state_rows \<Rightarrow> state_rows \<Rightarrow> (state_key\<times>isabelle_context state_row) set \<Rightarrow>
    (state_key\<times>isabelle_context state_row) set \<Rightarrow> bool" where
  "edit_reduced R R' D A \<longleftrightarrow> D\<subseteq>presented_rows R \<and>
    (\<forall>b q. (b,q)\<in>A \<longrightarrow> b\<notin>fst ` presented_rows R) \<and>
    presented_rows R'=(presented_rows R-D)\<union>A"

theorem edit_reduced_lists:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'" and edit: "edit_reduced R R' D A"
  shows "{e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}=set (isabelle_state_removed (snd S) (snd S'))"
    and "{g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}=set (isabelle_state_added (snd S) (snd S'))"
proof -
  have Dsub: "D\<subseteq>presented_rows R" and Afresh: "\<forall>b q. (b,q)\<in>A \<longrightarrow> b\<notin>fst ` presented_rows R"
    and applied: "presented_rows R'=(presented_rows R-D)\<union>A" using edit by (simp_all add: edit_reduced_def)
  have removed_row: "e\<in>set (isabelle_state_removed (snd S) (snd S')) \<longleftrightarrow> (a,entity_row key (snd S) e)\<in>D"
    if e: "e\<in>set (snd (snd S))" and row: "(a,entity_row key (snd S) e)\<in>presented_rows R" for a e
  proof -
    have found: "store_lookup (family_row_store (state_all_families R')) a\<noteq>None \<longleftrightarrow> (\<exists>p. (a,p)\<in>presented_rows R')"
      by (simp only: family_row_store_found state_all_families_found)
    have "e\<notin>set (isabelle_state_removed (snd S) (snd S')) \<longleftrightarrow> (\<exists>p. (a,p)\<in>presented_rows R')"
      using found state_difference_removed[OF present present' shared e row] by blast
    also have "\<dots> \<longleftrightarrow> (a,entity_row key (snd S) e)\<notin>D"
    proof
      assume "\<exists>p. (a,p)\<in>presented_rows R'"
      then obtain p where p: "(a,p)\<in>presented_rows R'" by blast
      have "a\<in>fst ` presented_rows R" using row by force
      then have notA: "(a,p)\<notin>A" using Afresh by blast
      have pR: "(a,p)\<in>presented_rows R" and pD: "(a,p)\<notin>D" using p applied notA by auto
      have "p=entity_row key (snd S) e"
        by (rule single_valued_outputs[OF state_presents_rows_single_valued[OF present] pR row])
      then show "(a,entity_row key (snd S) e)\<notin>D" using pD by simp
    next
      assume "(a,entity_row key (snd S) e)\<notin>D"
      then show "\<exists>p. (a,p)\<in>presented_rows R'" using row applied by blast
    qed
    finally show ?thesis by blast
  qed
  have added_row: "g\<in>set (isabelle_state_added (snd S) (snd S')) \<longleftrightarrow> (b,entity_row key' (snd S') g)\<in>A"
    if g: "g\<in>set (snd (snd S'))" and row': "(b,entity_row key' (snd S') g)\<in>presented_rows R'" for b g
  proof -
    have found: "store_lookup (family_row_store (state_all_families R)) b\<noteq>None \<longleftrightarrow> (\<exists>p. (b,p)\<in>presented_rows R)"
      by (simp only: family_row_store_found state_all_families_found)
    have "g\<notin>set (isabelle_state_added (snd S) (snd S')) \<longleftrightarrow> (\<exists>p. (b,p)\<in>presented_rows R)"
      using found state_difference_added[OF present present' shared g row'] by blast
    also have "\<dots> \<longleftrightarrow> (b,entity_row key' (snd S') g)\<notin>A"
    proof
      assume "\<exists>p. (b,p)\<in>presented_rows R"
      then have "b\<in>fst ` presented_rows R" by force
      then show "(b,entity_row key' (snd S') g)\<notin>A" using Afresh by blast
    next
      assume "(b,entity_row key' (snd S') g)\<notin>A"
      then have "(b,entity_row key' (snd S') g)\<in>presented_rows R" using row' applied by blast
      then show "\<exists>p. (b,p)\<in>presented_rows R" by blast
    qed
    finally show ?thesis by blast
  qed
  show "{e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}=set (isabelle_state_removed (snd S) (snd S'))"
  proof (intro set_eqI iffI)
    fix e assume "e\<in>{e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}"
    then obtain a where e: "e\<in>set (snd (snd S))" and d: "(a,entity_row key (snd S) e)\<in>D" by blast
    have row: "(a,entity_row key (snd S) e)\<in>presented_rows R" using d Dsub by blast
    show "e\<in>set (isabelle_state_removed (snd S) (snd S'))" using removed_row[OF e row] d by blast
  next
    fix e assume r: "e\<in>set (isabelle_state_removed (snd S) (snd S'))"
    have e: "e\<in>set (snd (snd S))" using r by (simp add: isabelle_state_removed_exact)
    obtain a where a: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
      by (rule state_presents_row[OF present e])
    have "(a,entity_row key (snd S) e)\<in>D" using removed_row[OF e presented_rows_member[OF a]] r by blast
    then show "e\<in>{e\<in>set (snd (snd S)). \<exists>a. (a,entity_row key (snd S) e)\<in>D}" using e by blast
  qed
  show "{g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}=set (isabelle_state_added (snd S) (snd S'))"
  proof (intro set_eqI iffI)
    fix g assume "g\<in>{g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}"
    then obtain b where g: "g\<in>set (snd (snd S'))" and d: "(b,entity_row key' (snd S') g)\<in>A" by blast
    have row': "(b,entity_row key' (snd S') g)\<in>presented_rows R'" using d applied by blast
    show "g\<in>set (isabelle_state_added (snd S) (snd S'))" using added_row[OF g row'] d by blast
  next
    fix g assume r: "g\<in>set (isabelle_state_added (snd S) (snd S'))"
    have g: "g\<in>set (snd (snd S'))" using r by (simp add: isabelle_state_added_exact)
    obtain b where b: "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))"
      by (rule state_presents_row[OF present' g])
    have "(b,entity_row key' (snd S') g)\<in>A" using added_row[OF g presented_rows_member[OF b]] r by blast
    then show "g\<in>{g\<in>set (snd (snd S')). \<exists>b. (b,entity_row key' (snd S') g)\<in>A}" using g by blast
  qed
qed

subsection \<open>Every row of a selection, read entity by entity\<close>

text \<open>
  A reading of every row of a selection of families is a reading of every entity of their kinds, once each
  row's reading is given as a reading of its entity: every entity has its row, and every row its entity.
\<close>

lemma presented_rows_every:
  assumes present: "state_presents key S R" and families: "set Fs=state_entities R ` K"
    and meaning: "\<And>a e. e\<in>set (snd (snd S)) \<Longrightarrow>
      (a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e)) \<Longrightarrow>
      Q (a,entity_row key (snd S) e) \<longleftrightarrow> Q' e"
  shows "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. Q z) \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>K \<longrightarrow> Q' e)"
proof
  assume rows: "\<forall>F\<in>set Fs. \<forall>z\<in>set F. Q z"
  show "\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>K \<longrightarrow> Q' e"
  proof (intro ballI impI)
    fix e assume e: "e\<in>set (snd (snd S))" and k: "entity_kind_of e\<in>K"
    obtain a where a: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
      by (rule state_presents_row[OF present e])
    have "state_entities R (entity_kind_of e)\<in>set Fs" unfolding families by (rule imageI) (rule k)
    then have "Q (a,entity_row key (snd S) e)" using rows a by blast
    then show "Q' e" using meaning[OF e a] by simp
  qed
next
  assume entities: "\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>K \<longrightarrow> Q' e"
  show "\<forall>F\<in>set Fs. \<forall>z\<in>set F. Q z"
  proof (intro ballI)
    fix F z assume F: "F\<in>set Fs" and z: "z\<in>set F"
    obtain k where k: "k\<in>K" "F=state_entities R k" using F families by auto
    obtain a p where zp: "z=(a,p)" by (cases z)
    have row: "(a,p)\<in>set (state_entities R k)" using z zp k by simp
    obtain e where e: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
      by (rule state_presents_row_origin[OF present row])
    have a: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))" using row e by simp
    have m: "Q (a,entity_row key (snd S) e) \<longleftrightarrow> Q' e" by (rule meaning[OF e(1) a])
    show "Q z" using m entities e k zp by auto
  qed
qed

section \<open>A row is permitted: found in the other state, or a replaceable statement, or a declaration\<close>

text \<open>
  The permitted side is the positive one. A row of one state is read in a context holding the other state's
  row store and the subject's key: it is permitted when its key is found in that store, and, where the
  selection allows it, when the subject's key is among its subjects, or when it declares a constant. The
  kind is the family holding the row, so whether a row may be a replaceable statement is decided by which
  selection of families is traversed with the subject case, never by a datum of the row. Each case is one
  rule, so the three readings are one rule family, instantiated by two flags at four sites. The offending
  rows, the witnesses of @{const development_constant_verdict}'s \<open>unpermitted_removed\<close> and
  \<open>unpermitted_added\<close>, need store absence and are not built here; neither side is the other's negation.
\<close>

definition permitted_found_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "permitted_found_rule m=finite_native_rule
    (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3) (native_var 4)
      (native_var 5) (native_var 6))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition permitted_subject_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "permitted_subject_rule mm=finite_native_rule
    (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3) (native_var 4)
      (native_var 5) (native_var 6))
    [([0],(mm,Finite_Pattern_Pair (native_var 1) (native_var 4)))]"

definition permitted_row_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "permitted_row_rules m mm subject declares=[([0],permitted_found_rule m)] @
    (if subject then [([1],permitted_subject_rule mm)] else []) @
    (if declares then [([2],row_declares_rule)] else [])"

locale permitted_row_program = native_rule_family P r "permitted_row_rules m mm subject declares" +
    found: store_found_program P m k ch + members: native_member_program P mm
  for P :: "'u native_system" and r m mm k ch :: "'u definition_site" and subject declares :: bool
begin

sublocale law: native_rule_law P r "permitted_row_rules m mm subject declares"
  by (rule native_rule_lawI[OF native_rule_family_axioms])
    (auto simp: permitted_row_rules_def permitted_found_rule_def permitted_subject_rule_def row_declares_rule_def
      split: if_splits)

theorem exact:
  assumes valued: "\<And>y. term_formed (val y)" and identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (Pair_Term (store_term val T) (path_term q)) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    store_lookup T (fst z)\<noteq>None \<or> (subject \<and> q\<in>set (row_subjects (snd z))) \<or> (declares \<and> row_declared (snd z)\<noteq>[])"
proof
  assume "(r,Pair_Term (Pair_Term (store_term val T) (path_term q)) (state_row_term ident z))\<in>positive_meaning P"
  then obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (permitted_row_rules m mm subject declares)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=
      Pair_Term (Pair_Term (store_term val T) (path_term q)) (state_row_term ident z)"
    and support: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    unfolding law.exact by (elim exE conjE) (rule that; assumption)
  from rule consider (hit) "finite_native_rule p ps=permitted_found_rule m"
      | (subj) "subject" "finite_native_rule p ps=permitted_subject_rule mm"
      | (decl) "declares" "finite_native_rule p ps=row_declares_rule"
    by (auto simp: permitted_row_rules_def split: if_splits)
  then show "store_lookup T (fst z)\<noteq>None \<or> (subject \<and> q\<in>set (row_subjects (snd z))) \<or>
      (declares \<and> row_declared (snd z)\<noteq>[])"
  proof cases
    case hit
    then have p: "p=row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3)
        (native_var 4) (native_var 5) (native_var 6)"
      and ps: "set ps={([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))}"
      by (simp_all add: permitted_found_rule_def finite_native_rule_eq_iff)
    have call: "(m,Pair_Term (f [0]) (f [2]))\<in>positive_meaning P" using support ps by auto
    have fields: "f [0]=store_term val T" "f [2]=path_term (fst z)"
      using shape by (simp_all add: p row_pattern_def state_row_term_def)
    show ?thesis using call by (simp add: fields found.exact[OF valued])
  next
    case subj
    then have p: "p=row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3)
        (native_var 4) (native_var 5) (native_var 6)"
      and ps: "set ps={([0],(mm,Finite_Pattern_Pair (native_var 1) (native_var 4)))}"
      by (simp_all add: permitted_subject_rule_def finite_native_rule_eq_iff)
    have call: "(mm,Pair_Term (f [1]) (f [4]))\<in>positive_meaning P" using support ps by auto
    have fields: "f [1]=path_term q" "f [4]=keys_term (row_subjects (snd z))"
      using shape by (simp_all add: p row_pattern_def state_row_term_def)
    show ?thesis using call subj(1) fields by (simp add: keys_term_def members.exact)
  next
    case decl
    then have p: "p=row_pattern (native_var 0) (native_var 1) (Finite_Pattern_Pair (native_var 2) (native_var 3))
        (native_var 4) (native_var 5) (native_var 6)"
      by (simp_all add: row_declares_rule_def finite_native_rule_eq_iff)
    have "row_declared (snd z)\<noteq>[]"
      using shape by (auto simp: p row_pattern_def state_row_term_def)
    then show ?thesis using decl(1) by simp
  qed
next
  have sf: "term_formed (store_term val T)" by (rule store_term_formed[OF valued])
  assume "store_lookup T (fst z)\<noteq>None \<or> (subject \<and> q\<in>set (row_subjects (snd z))) \<or>
      (declares \<and> row_declared (snd z)\<noteq>[])"
  then consider (hit) "store_lookup T (fst z)\<noteq>None" | (subj) "subject" "q\<in>set (row_subjects (snd z))"
      | (decl) "declares" "row_declared (snd z)\<noteq>[]" by blast
  then show "(r,Pair_Term (Pair_Term (store_term val T) (path_term q)) (state_row_term ident z))\<in>positive_meaning P"
  proof cases
    case hit
    have "(r,evaluate_pattern (native_values [store_term val T,path_term q,path_term (fst z),
        keys_term (row_declared (snd z)),keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),
        ident (row_identity (snd z))])
      (decode_finite_pattern (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)
        (native_var 3) (native_var 4) (native_var 5) (native_var 6))))\<in>positive_meaning P"
      by (rule law.step_at[where c="[0]" and ps="[([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
        (use hit sf identity in \<open>simp_all add: permitted_row_rules_def permitted_found_rule_def row_pattern_def
          found.exact[OF valued] insert_Diff_if data_list_term_formed\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def)
  next
    case subj
    have "(r,evaluate_pattern (native_values [store_term val T,path_term q,path_term (fst z),
        keys_term (row_declared (snd z)),keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),
        ident (row_identity (snd z))])
      (decode_finite_pattern (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)
        (native_var 3) (native_var 4) (native_var 5) (native_var 6))))\<in>positive_meaning P"
      by (rule law.step_at[where c="[1]" and ps="[([0],(mm,Finite_Pattern_Pair (native_var 1) (native_var 4)))]"])
        (use subj sf identity in \<open>simp_all add: permitted_row_rules_def permitted_subject_rule_def row_pattern_def
          keys_term_def members.exact data_list_term_formed insert_Diff_if\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def)
  next
    case decl
    obtain d ds where ds: "row_declared (snd z)=d#ds" using decl(2) by (cases "row_declared (snd z)") simp_all
    have "(r,evaluate_pattern (native_values [Pair_Term (store_term val T) (path_term q),path_term (fst z),
        path_term d,keys_term ds,keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),
        ident (row_identity (snd z))])
      (decode_finite_pattern (row_pattern (native_var 0) (native_var 1)
        (Finite_Pattern_Pair (native_var 2) (native_var 3)) (native_var 4) (native_var 5) (native_var 6))))
      \<in>positive_meaning P"
      by (rule law.step_at[where c="[2]" and ps="[]"])
        (use decl sf identity in \<open>simp_all add: permitted_row_rules_def row_declares_rule_def row_pattern_def
          insert_Diff_if data_list_term_formed\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def ds keys_term_Cons)
  qed
qed

end

locale permitted_selection_program = rows: permitted_row_program P r m mm k ch subject declares +
    families: native_every_program P v r + every: native_every_program P u v
  for P :: "'u native_system" and u v r m mm k ch :: "'u definition_site" and subject declares :: bool
begin

theorem exact:
  assumes valued: "\<And>y. term_formed (val y)" and identity: "\<And>y. term_formed (ident y)"
  shows "(u,Pair_Term (Pair_Term (store_term val T) (path_term q)) (state_families_term ident Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. store_lookup T (fst z)\<noteq>None \<or> (subject \<and> q\<in>set (row_subjects (snd z))) \<or>
      (declares \<and> row_declared (snd z)\<noteq>[]))"
proof -
  interpret reading: selection_every_reading P u v r "\<lambda>c. Pair_Term (store_term val (fst c)) (path_term (snd c))" ident
      "\<lambda>c z. store_lookup (fst c) (fst z)\<noteq>None \<or> (subject \<and> snd c\<in>set (row_subjects (snd z))) \<or>
        (declares \<and> row_declared (snd z)\<noteq>[])"
    by unfold_locales (simp_all add: identity rows.exact[OF valued identity])
  show ?thesis using reading.exact[of "(T,q)" Fs] by (simp add: store_term_formed[OF valued])
qed

end

section \<open>Two calls on one context, and the equality of two terms\<close>

text \<open>
  A field reading two selections calls both on one context: the rule @{const undeclared_rule}, whose program
  @{locale conjoined_calls_program} states its contract once in \<open>Development_Verdict_Mentions\<close>. The roots
  field compares two lists of keys by a variable occurring twice, the rule @{const native_value_rule}, whose
  program is @{locale native_value_program}. The sites below are instances of the two programs.
\<close>


section \<open>The program of the three fields\<close>

text \<open>
  The member program and the found program are the existing definitions at their existing sites
  (@{text Development_Verdict_Statements}, @{text Development_Verdict_Mentions}), so the programs agree on
  them where they are joined. The new sites are \<open>(Some [],[60..74])\<close>.
\<close>

abbreviation verdict_removed_replaceable_row :: "local_address option definition_site" where
  "verdict_removed_replaceable_row \<equiv> (Some [],[60])"
abbreviation verdict_removed_other_row :: "local_address option definition_site" where
  "verdict_removed_other_row \<equiv> (Some [],[61])"
abbreviation verdict_added_replaceable_row :: "local_address option definition_site" where
  "verdict_added_replaceable_row \<equiv> (Some [],[62])"
abbreviation verdict_added_other_row :: "local_address option definition_site" where
  "verdict_added_other_row \<equiv> (Some [],[63])"
abbreviation verdict_removed_replaceable_family :: "local_address option definition_site" where
  "verdict_removed_replaceable_family \<equiv> (Some [],[64])"
abbreviation verdict_removed_replaceable_selection :: "local_address option definition_site" where
  "verdict_removed_replaceable_selection \<equiv> (Some [],[65])"
abbreviation verdict_removed_other_family :: "local_address option definition_site" where
  "verdict_removed_other_family \<equiv> (Some [],[66])"
abbreviation verdict_removed_other_selection :: "local_address option definition_site" where
  "verdict_removed_other_selection \<equiv> (Some [],[67])"
abbreviation verdict_added_replaceable_family :: "local_address option definition_site" where
  "verdict_added_replaceable_family \<equiv> (Some [],[68])"
abbreviation verdict_added_replaceable_selection :: "local_address option definition_site" where
  "verdict_added_replaceable_selection \<equiv> (Some [],[69])"
abbreviation verdict_added_other_family :: "local_address option definition_site" where
  "verdict_added_other_family \<equiv> (Some [],[70])"
abbreviation verdict_added_other_selection :: "local_address option definition_site" where
  "verdict_added_other_selection \<equiv> (Some [],[71])"
abbreviation verdict_removed :: "local_address option definition_site" where
  "verdict_removed \<equiv> (Some [],[72])"
abbreviation verdict_added :: "local_address option definition_site" where
  "verdict_added \<equiv> (Some [],[73])"
abbreviation verdict_roots :: "local_address option definition_site" where
  "verdict_roots \<equiv> (Some [],[74])"

definition verdict_difference_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "verdict_difference_definitions=[(verdict_row_member,native_member_rules verdict_row_member),
    (verdict_found_any,[([0],native_any_rule)]),
    (verdict_found_search,native_store_search_rules verdict_found_search verdict_found_any),
    (verdict_key_found,[([0],store_found_rule verdict_found_search)]),
    (verdict_removed_replaceable_row,permitted_row_rules verdict_key_found verdict_row_member True True),
    (verdict_removed_other_row,permitted_row_rules verdict_key_found verdict_row_member False True),
    (verdict_added_replaceable_row,permitted_row_rules verdict_key_found verdict_row_member True False),
    (verdict_added_other_row,permitted_row_rules verdict_key_found verdict_row_member False False),
    (verdict_removed_replaceable_family,native_every_rules verdict_removed_replaceable_family verdict_removed_replaceable_row),
    (verdict_removed_replaceable_selection,native_every_rules verdict_removed_replaceable_selection verdict_removed_replaceable_family),
    (verdict_removed_other_family,native_every_rules verdict_removed_other_family verdict_removed_other_row),
    (verdict_removed_other_selection,native_every_rules verdict_removed_other_selection verdict_removed_other_family),
    (verdict_added_replaceable_family,native_every_rules verdict_added_replaceable_family verdict_added_replaceable_row),
    (verdict_added_replaceable_selection,native_every_rules verdict_added_replaceable_selection verdict_added_replaceable_family),
    (verdict_added_other_family,native_every_rules verdict_added_other_family verdict_added_other_row),
    (verdict_added_other_selection,native_every_rules verdict_added_other_selection verdict_added_other_family),
    (verdict_removed,[([0],undeclared_rule verdict_removed_replaceable_selection verdict_removed_other_selection)]),
    (verdict_added,[([0],undeclared_rule verdict_added_replaceable_selection verdict_added_other_selection)]),
    (verdict_roots,[([0],native_value_rule)])]"

definition finite_verdict_difference :: "local_address option finite_native_system" where
  "finite_verdict_difference=finite_rule_program verdict_difference_definitions"

definition verdict_difference_system :: "local_address option native_system" where
  "verdict_difference_system=decode_finite_system finite_verdict_difference"

lemma finite_verdict_difference_formed: "finite_system_formed finite_verdict_difference"
  by code_simp

lemma verdict_difference_formed: "schema_system_formed verdict_difference_system"
  using finite_verdict_difference_formed
  by (simp only: verdict_difference_system_def finite_system_formed_correct)

lemma verdict_difference_family:
  assumes member: "(d,rs)\<in>set verdict_difference_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family verdict_difference_system d rs"
  unfolding verdict_difference_system_def finite_verdict_difference_def
  by (rule finite_rule_program_family[OF verdict_difference_formed[unfolded verdict_difference_system_def
      finite_verdict_difference_def] _ member plain]) (simp add: verdict_difference_definitions_def)

lemmas verdict_difference_rule_defs = verdict_difference_definitions_def native_every_rules_def
  native_every_nil_def native_every_step_def native_store_search_rules_def native_store_found_rule_def
  native_store_left_rule_def native_store_right_rule_def native_any_rule_def store_found_rule_def
  native_context_call_rule_def
  native_member_rules_def native_member_here_def native_member_later_def permitted_row_rules_def
  permitted_found_rule_def permitted_subject_rule_def row_declares_rule_def undeclared_rule_def
  native_value_rule_def

interpretation removed_replaceable: permitted_selection_program verdict_difference_system
    verdict_removed_replaceable_selection verdict_removed_replaceable_family verdict_removed_replaceable_row
    verdict_key_found verdict_row_member verdict_found_search verdict_found_any True True
  unfolding permitted_selection_program_def permitted_row_program_def store_found_program_def
    native_store_search_program_def native_every_program_def native_member_program_def
  by (intro conjI; rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation removed_other: permitted_selection_program verdict_difference_system
    verdict_removed_other_selection verdict_removed_other_family verdict_removed_other_row
    verdict_key_found verdict_row_member verdict_found_search verdict_found_any False True
  unfolding permitted_selection_program_def permitted_row_program_def store_found_program_def
    native_store_search_program_def native_every_program_def native_member_program_def
  by (intro conjI; rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation added_replaceable: permitted_selection_program verdict_difference_system
    verdict_added_replaceable_selection verdict_added_replaceable_family verdict_added_replaceable_row
    verdict_key_found verdict_row_member verdict_found_search verdict_found_any True False
  unfolding permitted_selection_program_def permitted_row_program_def store_found_program_def
    native_store_search_program_def native_every_program_def native_member_program_def
  by (intro conjI; rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation added_other: permitted_selection_program verdict_difference_system
    verdict_added_other_selection verdict_added_other_family verdict_added_other_row
    verdict_key_found verdict_row_member verdict_found_search verdict_found_any False False
  unfolding permitted_selection_program_def permitted_row_program_def store_found_program_def
    native_store_search_program_def native_every_program_def native_member_program_def
  by (intro conjI; rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation removed_entry: conjoined_calls_program verdict_difference_system verdict_removed
    verdict_removed_replaceable_selection verdict_removed_other_selection
  unfolding conjoined_calls_program_def
  by (rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation added_entry: conjoined_calls_program verdict_difference_system verdict_added
    verdict_added_replaceable_selection verdict_added_other_selection
  unfolding conjoined_calls_program_def
  by (rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

interpretation roots_entry: native_value_program verdict_difference_system verdict_roots
  unfolding native_value_program_def
  by (rule verdict_difference_family) (simp_all add: verdict_difference_rule_defs)

text \<open>
  The search of a presented state's rows by row key, natively: the found program at the state's row store
  holds exactly at the keys of the state's rows.
\<close>

theorem native_row_found:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_key_found,Pair_Term (family_row_term ident (state_all_families R)) (path_term a))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow> (\<exists>p. (a,p)\<in>presented_rows R)"
  unfolding family_row_term_def
  by (simp only: removed_replaceable.rows.found.exact[OF state_row_term_formed[OF identity]] family_row_store_found
    state_all_families_found)

section \<open>The permitted removed rows\<close>

text \<open>
  Every row of the request state is permitted: its key is found in the answer state's row store, or it is a
  row of a replaceable family with the subject among its subjects, or it declares a constant. This is the
  acceptance reading of @{const development_constant_verdict}'s \<open>unpermitted_removed\<close> field, which keeps a
  removed entity that is neither a replaceable statement of the subject nor a declaration; whether a removed
  declaration is still mentioned is the closure assessment's, not this field's.
\<close>

theorem native_removed_exact:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'" and kinds: "kinds_present replaceable kinds"
    and bound: "c<length (fst (snd S))"
    and replaceable_families: "set Fs=state_entities R ` kinds" and other_families: "set Gs=state_entities R ` (-kinds)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families R')) (path_term (key c)))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S) {|c|} e \<and> isabelle_declared_constant e=None)
      (isabelle_state_removed (snd S) (snd S'))=[]"
proof -
  let ?T="family_row_store (state_all_families R')"
  let ?removed="set (isabelle_state_removed (snd S) (snd S'))"
  have valued: "\<And>z. term_formed (state_row_term ident z)" by (rule state_row_term_formed[OF identity])
  have found: "store_lookup ?T a\<noteq>None \<longleftrightarrow> e\<notin>?removed"
    if "e\<in>set (snd (snd S))" "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))" for a e
    by (rule state_difference_removed[OF present present' shared that(1) presented_rows_member[OF that(2)]])
  have subject: "key c\<in>set (row_subjects (entity_row key (snd S) e)) \<longleftrightarrow>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
    if "e\<in>set (snd (snd S))" for e
    by (rule entity_row_subject_key[OF present bound that])
  have declares: "row_declared (entity_row key (snd S) e)\<noteq>[] \<longleftrightarrow> isabelle_declared_constant e\<noteq>None" for e
    by (simp add: entity_declared_def split: option.split)
  have replaceable_rows: "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> key c\<in>set (row_subjects (snd z)) \<or>
        row_declared (snd z)\<noteq>[]) \<longleftrightarrow>
      (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>kinds \<longrightarrow> e\<notin>?removed \<or>
        c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<or>
        isabelle_declared_constant e\<noteq>None)"
    by (rule presented_rows_every[OF present replaceable_families])
      (simp only: prod.sel found subject declares not_not)
  have other_rows: "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> row_declared (snd z)\<noteq>[]) \<longleftrightarrow>
      (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>-kinds \<longrightarrow> e\<notin>?removed \<or> isabelle_declared_constant e\<noteq>None)"
    by (rule presented_rows_every[OF present other_families]) (simp only: prod.sel found declares not_not)
  have sub: "?removed\<subseteq>set (snd (snd S))" by (auto simp: isabelle_state_removed_exact)
  have "(verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families R')) (path_term (key c)))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> key c\<in>set (row_subjects (snd z)) \<or>
        row_declared (snd z)\<noteq>[]) \<and>
    (\<forall>F\<in>set Gs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> row_declared (snd z)\<noteq>[])"
    by (simp only: family_row_term_def removed_entry.exact removed_replaceable.exact[OF valued identity]
      removed_other.exact[OF valued identity] simp_thms)
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>kinds \<longrightarrow> e\<notin>?removed \<or>
        c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<or>
        isabelle_declared_constant e\<noteq>None) \<and>
      (\<forall>e\<in>set (snd (snd S)). entity_kind_of e\<in>-kinds \<longrightarrow> e\<notin>?removed \<or> isabelle_declared_constant e\<noteq>None)"
    by (simp only: replaceable_rows other_rows)
  also have "\<dots> \<longleftrightarrow> filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S) {|c|} e \<and>
      isabelle_declared_constant e=None) (isabelle_state_removed (snd S) (snd S'))=[]"
    using sub by (auto simp: filter_empty_conv development_answer_statement_def list_ex_iff kinds_presentD[OF kinds])
  finally show ?thesis .
qed

section \<open>The permitted added rows\<close>

text \<open>
  Every row of the answer state is permitted: its key is found in the request state's row store, or it is a
  row of a replaceable family with the subject among its subjects. This is the acceptance reading of the
  \<open>unpermitted_added\<close> field.
\<close>

theorem native_added_exact:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'" and kinds: "kinds_present replaceable kinds"
    and bound': "c'<length (fst (snd S'))"
    and replaceable_families: "set Fs=state_entities R' ` kinds" and other_families: "set Gs=state_entities R' ` (-kinds)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term (key' c')))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') {|c'|} g) (isabelle_state_added (snd S) (snd S'))=[]"
proof -
  let ?T="family_row_store (state_all_families R)"
  let ?added="set (isabelle_state_added (snd S) (snd S'))"
  have valued: "\<And>z. term_formed (state_row_term ident z)" by (rule state_row_term_formed[OF identity])
  have found: "store_lookup ?T b\<noteq>None \<longleftrightarrow> g\<notin>?added"
    if "g\<in>set (snd (snd S'))" "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))" for b g
    by (rule state_difference_added[OF present present' shared that(1) presented_rows_member[OF that(2)]])
  have subject: "key' c'\<in>set (row_subjects (entity_row key' (snd S') g)) \<longleftrightarrow>
      c'\<in>set (isabelle_entity_subjects (fst (snd S')) (isabelle_development_constants (snd (snd S'))) g)"
    if "g\<in>set (snd (snd S'))" for g
    by (rule entity_row_subject_key[OF present' bound' that])
  have replaceable_rows: "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> key' c'\<in>set (row_subjects (snd z))) \<longleftrightarrow>
      (\<forall>g\<in>set (snd (snd S')). entity_kind_of g\<in>kinds \<longrightarrow> g\<notin>?added \<or>
        c'\<in>set (isabelle_entity_subjects (fst (snd S')) (isabelle_development_constants (snd (snd S'))) g))"
    by (rule presented_rows_every[OF present' replaceable_families]) (simp only: prod.sel found subject not_not)
  have other_rows: "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None) \<longleftrightarrow>
      (\<forall>g\<in>set (snd (snd S')). entity_kind_of g\<in>-kinds \<longrightarrow> g\<notin>?added)"
    by (rule presented_rows_every[OF present' other_families]) (simp only: prod.sel found not_not)
  have sub: "?added\<subseteq>set (snd (snd S'))" by (auto simp: isabelle_state_added_exact)
  have "(verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term (key' c')))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None \<or> key' c'\<in>set (row_subjects (snd z))) \<and>
    (\<forall>F\<in>set Gs. \<forall>z\<in>set F. store_lookup ?T (fst z)\<noteq>None)"
    by (simp only: family_row_term_def added_entry.exact added_replaceable.exact[OF valued identity]
      added_other.exact[OF valued identity] simp_thms)
  also have "\<dots> \<longleftrightarrow> (\<forall>g\<in>set (snd (snd S')). entity_kind_of g\<in>kinds \<longrightarrow> g\<notin>?added \<or>
        c'\<in>set (isabelle_entity_subjects (fst (snd S')) (isabelle_development_constants (snd (snd S'))) g)) \<and>
      (\<forall>g\<in>set (snd (snd S')). entity_kind_of g\<in>-kinds \<longrightarrow> g\<notin>?added)"
    by (simp only: replaceable_rows other_rows)
  also have "\<dots> \<longleftrightarrow> filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S') {|c'|} g)
      (isabelle_state_added (snd S) (snd S'))=[]"
    using sub by (auto simp: filter_empty_conv development_answer_statement_def list_ex_iff kinds_presentD[OF kinds])
  finally show ?thesis .
qed

section \<open>The two fields at the request's subject\<close>

text \<open>
  At a presented request the subject is the problem's one subject constant and its key the request's key;
  in the answer state the subject is carried by the correspondence and keyed with the same key by the
  shared key assignment. These state exactly the verdict's \<open>unpermitted_removed\<close> and \<open>unpermitted_added\<close>
  fields, with the problem's subject as @{const development_constant_verdict} takes it.
\<close>

corollary native_removed_request:
  assumes request: "request_presents key S R rows r k support" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'" and kinds: "kinds_present replaceable kinds"
    and replaceable_families: "set Fs=state_entities R ` kinds" and other_families: "set Gs=state_entities R ` (-kinds)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families R')) (path_term k))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S) (problem_subject (fst r)) e \<and>
      isabelle_declared_constant e=None) (isabelle_state_removed (snd S) (snd S'))=[]"
proof -
  have present: "state_presents key S R" using request by (simp add: request_presents_def)
  obtain c where subject: "problem_subject (fst r)={|c|}" and k: "k=key c" and bound: "c<length (fst (snd S))"
    and "(k,fst (snd S)!c)\<in>set (state_atoms R)" and "set support=key ` fset (fst (snd (snd r)))"
    and "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF request])
  show ?thesis unfolding subject k
    by (rule native_removed_exact[OF present present' shared kinds bound replaceable_families other_families identity])
qed

corollary native_added_request:
  assumes request: "request_presents key S R rows r k support" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and named: "(!) (fst (snd S)) ` fset (problem_subject (fst r))\<subseteq>set (fst (snd S'))"
    and kinds: "kinds_present replaceable kinds"
    and replaceable_families: "set Fs=state_entities R' ` kinds" and other_families: "set Gs=state_entities R' ` (-kinds)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term k))
      (Pair_Term (state_families_term ident Fs) (state_families_term ident Gs)))\<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    filter (\<lambda>g. \<not>development_answer_statement replaceable (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject (fst r))) g)
      (isabelle_state_added (snd S) (snd S'))=[]"
proof -
  have present: "state_presents key S R" using request by (simp add: request_presents_def)
  obtain c where subject: "problem_subject (fst r)={|c|}" and k: "k=key c" and bound: "c<length (fst (snd S))"
    and "(k,fst (snd S)!c)\<in>set (state_atoms R)" and "set support=key ` fset (fst (snd (snd r)))"
    and "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF request])
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have name: "fst (snd S)!c\<in>set (fst (snd S'))" using named subject by simp
  have carried: "key' (?f c)=key c" by (rule keys_shared_embedding[OF present present' shared bound name])
  have "isabelle_name_at (fst (snd S')) (?f c)=Some (fst (snd S)!c)"
    by (rule isabelle_state_embedding_shared) (simp_all add: isabelle_name_at_def bound name)
  then have bound': "?f c<length (fst (snd S'))" by (simp add: isabelle_name_at_def split: if_splits)
  have image: "fimage ?f (problem_subject (fst r))={|?f c|}" using subject by simp
  show ?thesis unfolding k carried[symmetric] image
    by (rule native_added_exact[OF present present' shared kinds bound' replaceable_families other_families identity])
qed

section \<open>The field \<open>roots\<close>\<close>

text \<open>
  The two root families agree pairwise on their keys. The roots stay a family with distinct keys; their order
  is the one @{const roots_present} carries (@{thm state_presents_root_family}), owned by the exporter that
  defines a state's roots, and it is the only condition the HOL conjunct's comparison of lists needs: no
  further condition is carried. Under the shared key assignment two root keys at one position are equal
  exactly when the correspondence carries the one root to the other, which is
  @{thm isabelle_local_root_compared} at each position.
\<close>

lemma keys_term_eq_iff: "keys_term ks=keys_term ks' \<longleftrightarrow> ks=ks'"
proof (induction ks arbitrary: ks')
  case Nil
  show ?case by (cases ks') (simp_all add: keys_term_def)
next
  case (Cons k ks)
  show ?case by (cases ks') (simp_all add: keys_term_def path_term_injective Cons.IH[unfolded keys_term_def])
qed

theorem root_keys_exact:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
  shows "map fst (state_roots R)=map fst (state_roots R') \<longleftrightarrow>
    map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
proof -
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have sizes: "length (state_roots R)=length (fst S)" "length (state_roots R')=length (fst S')"
    by (rule state_presents_root_length[OF present], rule state_presents_root_length[OF present'])
  have pointwise: "fst (state_roots R!i)=fst (state_roots R'!i) \<longleftrightarrow> isabelle_term_rename ?f (fst S!i)=fst S'!i"
    if i: "i<length (fst S)" and i': "i<length (fst S')" for i
  proof -
    have m: "(fst (state_roots R!i),snd (state_roots R!i))\<in>set (state_roots R)" using i sizes by simp
    have m': "(fst (state_roots R'!i),snd (state_roots R'!i))\<in>set (state_roots R')" using i' sizes by simp
    have "fst (state_roots R!i)=fst (state_roots R'!i) \<longleftrightarrow>
        row_identity (snd (state_roots R!i))=row_identity (snd (state_roots R'!i))"
      by (rule keyed_agreeD[OF keys_shared_roots[OF shared] m m'])
    also have "\<dots> \<longleftrightarrow> isabelle_local_root (fst (snd S)) (fst S!i)=isabelle_local_root (fst (snd S')) (fst S'!i)"
      by (simp add: state_presents_root_row[OF present i] state_presents_root_row[OF present' i'])
    also have "\<dots> \<longleftrightarrow> isabelle_term_rename ?f (fst S!i)=fst S'!i"
      by (rule isabelle_local_root_compared[OF state_presents_distinct_names[OF present']
        state_presents_root_inside[OF present nth_mem[OF i]] state_presents_root_inside[OF present' nth_mem[OF i']]])
    finally show ?thesis .
  qed
  show ?thesis
  proof
    assume keys: "map fst (state_roots R)=map fst (state_roots R')"
    then have len: "length (fst S)=length (fst S')" using sizes by (metis length_map)
    show "map (isabelle_term_rename ?f) (fst S)=fst S'"
    proof (rule nth_equalityI)
      show "length (map (isabelle_term_rename ?f) (fst S))=length (fst S')" using len by simp
      fix i assume "i<length (map (isabelle_term_rename ?f) (fst S))"
      then have i: "i<length (fst S)" by simp
      have "map fst (state_roots R)!i=map fst (state_roots R')!i" using keys by simp
      then have "fst (state_roots R!i)=fst (state_roots R'!i)" using i len sizes by simp
      then show "map (isabelle_term_rename ?f) (fst S)!i=fst S'!i" using pointwise[of i] i len by simp
    qed
  next
    assume roots: "map (isabelle_term_rename ?f) (fst S)=fst S'"
    then have len: "length (fst S)=length (fst S')" by (metis length_map)
    show "map fst (state_roots R)=map fst (state_roots R')"
    proof (rule nth_equalityI)
      show "length (map fst (state_roots R))=length (map fst (state_roots R'))" using sizes len by simp
      fix i assume "i<length (map fst (state_roots R))"
      then have i: "i<length (fst S)" using sizes by simp
      have "map (isabelle_term_rename ?f) (fst S)!i=fst S'!i" using roots by simp
      then have "isabelle_term_rename ?f (fst S!i)=fst S'!i" using i by simp
      then show "map fst (state_roots R)!i=map fst (state_roots R')!i" using pointwise[of i] i len sizes by simp
    qed
  qed
qed

theorem native_roots_exact:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
  shows "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R'))))
      \<in>positive_meaning verdict_difference_system \<longleftrightarrow>
    map (isabelle_term_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S')))) (fst S)=fst S'"
  by (simp only: roots_entry.exact keys_term_formed keys_term_eq_iff root_keys_exact[OF present present' shared]
    simp_thms)

end
