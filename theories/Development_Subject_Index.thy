theory Development_Subject_Index
imports Development_Verdict_Statements Native_Path_Store_Indexes Binary_Store_Indexes
begin

section \<open>The rows of a family at a key, read through the index of a key reading\<close>

text \<open>
  A native definition that reads the rows of a family at a key reads them through the \<^emph>\<open>index of the family
  by a key reading\<close>, an instance of the index notion at the path store's carrier, and not through a
  complement. A key reading \<open>rd\<close> gives the keys a row is about: its subjects (\<^const>\<open>row_subjects\<close>) for the
  subject index, the keys it mentions (\<^const>\<open>row_mentions\<close>) for the mention index. For a family \<open>F\<close> and the
  state's atom keys \<open>A\<close>, the \<^emph>\<open>fibre\<close> of \<open>F\<close> at \<open>a\<close> is the family's rows having \<open>a\<close> among the keys the
  reading gives, in the family's order, each identity inert; the index is the path store of the rows
  \<open>(a, fibre of F at a)\<close> for \<open>a\<close> in \<open>A\<close>. It holds every atom of the state: at an atom no row has, the fibre
  is found and empty; at a key that is no atom of the state, nothing is found. No key is compared with
  another and no absence is read.

  The index is computed from the presented atoms and family where the call's argument is built; it is
  neither a field of \<^typ>\<open>state_rows\<close> nor a condition \<^const>\<open>state_presents\<close> carries, and it adds no kind.
  The notion is stated once, over the reading; the subject index and the mention index are its two
  instances, and every fact of each is the notion's at its reading.
\<close>

definition key_fibre :: "('i state_row \<Rightarrow> state_key list) \<Rightarrow> state_key \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family" where
  "key_fibre rd a F=filter (\<lambda>z. a\<in>set (rd (snd z))) F"

definition key_rows ::
    "('i state_row \<Rightarrow> state_key list) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> (state_key\<times>'i state_family) list" where
  "key_rows rd A F=map (\<lambda>a. (a,key_fibre rd a F)) A"

definition key_index ::
    "('i state_row \<Rightarrow> state_key list) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family binary_path_store" where
  "key_index rd A F=path_store (key_rows rd A F)"

definition key_index_term :: "('i state_row \<Rightarrow> state_key list) \<Rightarrow> ('i \<Rightarrow> factor_term) \<Rightarrow>
    state_key list \<Rightarrow> 'i state_family \<Rightarrow> factor_term" where
  "key_index_term rd ident A F=store_term (state_family_term ident) (key_index rd A F)"

definition key_indexes_term :: "('i state_row \<Rightarrow> state_key list) \<Rightarrow> ('i \<Rightarrow> factor_term) \<Rightarrow>
    state_key list \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "key_indexes_term rd ident A Fs=data_list_term (map (key_index_term rd ident A) Fs)"

section \<open>The index is an instance of the index notion\<close>

text \<open>
  The index's rows are single-valued whatever \<open>A\<close> is, since the value at a key is a function of the key; the
  distinctness of the atom keys is not needed. The obligations of the notion, for the key: (1) the key is
  the path itself (\<open>inj id\<close>, the carrier's own); (2) the lookup at \<open>a\<close> is the fibre exactly when \<open>a\<in>set A\<close>
  (@{text key_index_lookup}, the carrier's member equation through
  @{thm [source] path_store_carrier_index}); (3) the one operation its uses need, the filter lemma
  @{text key_fibre_member}; (4) the index of an edited family is the old index updated at the keys the
  edit's rows have (@{text key_index_edit}, below).
\<close>

lemma key_rows_single_valued: "single_valued (set (key_rows rd A F))"
  by (auto simp: single_valued_def key_rows_def)

lemma key_index_carrier_index:
  "carrier_index (\<lambda>AF a w. a\<in>set (fst AF) \<and> w=key_fibre rd a (snd AF)) (\<lambda>_. True) UNIV id
    (\<lambda>AF. key_index rd (fst AF) (snd AF)) (\<lambda>T bs w. store_lookup T bs=Some w)"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by (rule inj_on_id)
next
  fix AF k w
  have "store_lookup (path_store (key_rows rd (fst AF) (snd AF))) k=Some w \<longleftrightarrow>
      (\<exists>q\<in>UNIV. id q=k \<and> (q,w)\<in>set (key_rows rd (fst AF) (snd AF)))"
    by (rule carrier_index.represents[OF Native_Path_Store_Indexes.path_store_carrier_index key_rows_single_valued])
  then show "store_lookup (key_index rd (fst AF) (snd AF)) k=Some w \<longleftrightarrow>
      (\<exists>q\<in>UNIV. id q=k \<and> q\<in>set (fst AF) \<and> w=key_fibre rd q (snd AF))"
    by (auto simp: key_index_def key_rows_def)
qed

lemma key_index_lookup: "store_lookup (key_index rd A F) a=Some w \<longleftrightarrow> a\<in>set A \<and> w=key_fibre rd a F"
  using carrier_index.query_search[OF key_index_carrier_index, where c="(A,F)" and q=a and v=w] by simp

lemma key_fibre_member: "z\<in>set (key_fibre rd a F) \<longleftrightarrow> z\<in>set F \<and> a\<in>set (rd (snd z))"
  by (simp add: key_fibre_def)

text \<open>
  An atom no row has finds an empty fibre, a found and empty result; a key outside the state finds
  nothing, a failed one. The two are kept apart positively, by the index holding every atom.
\<close>

lemma key_index_empty:
  assumes atom: "a\<in>set A" and none: "\<forall>z\<in>set F. a\<notin>set (rd (snd z))"
  shows "store_lookup (key_index rd A F) a=Some []"
proof -
  have "key_fibre rd a F=[]" using none by (simp add: key_fibre_def filter_empty_conv)
  then show ?thesis using atom by (simp add: key_index_lookup)
qed

lemma key_index_outside:
  assumes outside: "a\<notin>set A"
  shows "store_lookup (key_index rd A F) a=None"
  using outside key_index_lookup[of rd A F a] by (cases "store_lookup (key_index rd A F) a") auto

section \<open>An edited family's index is the old index updated at the edit's keys\<close>

text \<open>
  The notion's fourth obligation. A family edited by removed rows \<open>D\<close> and added rows \<open>Ad\<close> is the family
  without \<open>D\<close>'s rows followed by \<open>Ad\<close>'s. Its fibre at every key is the old fibre without \<open>D\<close>'s rows followed
  by \<open>Ad\<close>'s rows at the key (@{text key_fibre_edited}); at a key no row of \<open>D\<close> or \<open>Ad\<close> has, it is the old
  fibre. So its index is the old index updated, through @{text path_store_updates}, at the atom keys the
  rows of \<open>D\<close> and \<open>Ad\<close> have, and nowhere else (@{text key_index_edit}, @{text key_index_edited}). The law
  is stated over any families and row lists; how an edit presents its rows is not read here.
\<close>

lemma key_fibre_edited:
  "key_fibre rd a (filter (\<lambda>z. z\<notin>set D) F @ Ad)=filter (\<lambda>z. z\<notin>set D) (key_fibre rd a F) @ key_fibre rd a Ad"
  by (induction F) (auto simp: key_fibre_def)

definition key_edit_keys ::
    "('i state_row \<Rightarrow> state_key list) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family \<Rightarrow> state_key list" where
  "key_edit_keys rd A D Ad=filter (\<lambda>a. a\<in>set A) (concat (map (\<lambda>z. rd (snd z)) (D @ Ad)))"

definition key_edit_update ::
    "('i state_row \<Rightarrow> state_key list) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family \<Rightarrow>
      'i state_family binary_path_store \<Rightarrow> 'i state_family binary_path_store" where
  "key_edit_update rd A D Ad F T=fold (\<lambda>a T. store_update T a
      (Some (filter (\<lambda>z. z\<notin>set D) (key_fibre rd a F) @ key_fibre rd a Ad))) (key_edit_keys rd A D Ad) T"

lemma key_fibre_untouched:
  assumes untouched: "a\<notin>set (concat (map (\<lambda>z. rd (snd z)) (D @ Ad)))"
  shows "filter (\<lambda>z. z\<notin>set D) (key_fibre rd a F) @ key_fibre rd a Ad=key_fibre rd a F"
proof -
  have D: "\<forall>z\<in>set D. a\<notin>set (rd (snd z))" and Ad: "\<forall>z\<in>set Ad. a\<notin>set (rd (snd z))" using untouched by auto
  have "key_fibre rd a Ad=[]" using Ad by (simp add: key_fibre_def filter_empty_conv)
  moreover have "filter (\<lambda>z. z\<notin>set D) (key_fibre rd a F)=key_fibre rd a F"
    using D by (auto simp: key_fibre_def filter_filter intro!: filter_cong)
  ultimately show ?thesis by simp
qed

theorem key_index_edit:
  "store_lookup (key_index rd A (filter (\<lambda>z. z\<notin>set D) F @ Ad)) k=Some w \<longleftrightarrow>
    store_lookup (key_edit_update rd A D Ad F (key_index rd A F)) k=Some w"
proof (cases "k\<in>set (key_edit_keys rd A D Ad)")
  case True
  moreover have "k\<in>set A" using True by (auto simp: key_edit_keys_def)
  ultimately show ?thesis
    by (simp add: key_edit_update_def key_index_lookup path_store_updates_fold key_fibre_edited)
next
  case False
  show ?thesis
  proof (cases "k\<in>set A")
    assume atom: "k\<in>set A"
    then have "k\<notin>set (concat (map (\<lambda>z. rd (snd z)) (D @ Ad)))" using False by (simp add: key_edit_keys_def)
    then have "filter (\<lambda>z. z\<notin>set D) (key_fibre rd k F) @ key_fibre rd k Ad=key_fibre rd k F"
      by (rule key_fibre_untouched)
    then have "key_fibre rd k (filter (\<lambda>z. z\<notin>set D) F @ Ad)=key_fibre rd k F"
      by (simp only: key_fibre_edited)
    then show ?thesis using False atom by (simp add: key_edit_update_def key_index_lookup path_store_updates_fold)
  next
    assume "k\<notin>set A"
    with False show ?thesis by (simp add: key_edit_update_def key_index_lookup path_store_updates_fold)
  qed
qed

corollary key_index_edited:
  "key_index rd A (filter (\<lambda>z. z\<notin>set D) F @ Ad)=key_edit_update rd A D Ad F (key_index rd A F)"
proof (rule store_canonical_lookup_eq)
  show "store_canonical (key_index rd A (filter (\<lambda>z. z\<notin>set D) F @ Ad))"
    by (simp add: key_index_def path_store_canonical)
  show "store_canonical (key_edit_update rd A D Ad F (key_index rd A F))"
    by (simp add: key_edit_update_def key_index_def path_store_canonical store_updates_canonical)
  fix q
  show "store_lookup (key_index rd A (filter (\<lambda>z. z\<notin>set D) F @ Ad)) q=
      store_lookup (key_edit_update rd A D Ad F (key_index rd A F)) q"
    by (rule lookup_eq_by_some) (rule key_index_edit)
qed

section \<open>The index restricted to the keys a call reaches\<close>

text \<open>
  A call carries only the part of the index its reading can reach: the index at the atom keys of a set
  \<open>S\<close> is the path store of the index's rows at those keys, which has the whole index's lookup at every kept
  key (@{thm [source] path_store_restrict}, of any listing).
\<close>

lemma key_rows_restrict: "filter (\<lambda>r. fst r\<in>S) (key_rows rd A F)=key_rows rd (filter (\<lambda>a. a\<in>S) A) F"
  by (induction A) (simp_all add: key_rows_def)

corollary key_index_restrict:
  assumes kept: "a\<in>S"
  shows "store_lookup (key_index rd (filter (\<lambda>b. b\<in>S) A) F) a=store_lookup (key_index rd A F) a"
  using path_store_restrict[OF kept, of "key_rows rd A F"]
  by (simp add: key_index_def key_rows_restrict)

section \<open>The native reading of the index\<close>

text \<open>
  The index's native part is the path store's search whose checker is the family's every-reading, generic
  over the row reading and the key reading: the search holds at the reading's context, the path of a key
  and the index exactly when the key is an atom and every row of the family at the key satisfies the row
  reading. It reads the fibre alone: no row that the key reading does not give the key is visited.
\<close>

locale key_index_program = search: native_store_search_program P k v +
    family: family_every_reading P v r present ident reads
  for P :: "'u native_system" and k v r :: "'u definition_site" and present
    and ident :: "'i \<Rightarrow> factor_term" and reads +
  fixes rd :: "'i state_row \<Rightarrow> state_key list"
begin

corollary native_index:
  "native_carrier_index (\<lambda>rows q w. (q,w)\<in>set rows) (\<lambda>rows. single_valued (set rows)) UNIV id path_store
    (\<lambda>T bs w. store_lookup T bs=Some w) (\<lambda>x t j. (k,Pair_Term x (Pair_Term t j))\<in>positive_meaning P)
    term_formed path_term (store_term (state_family_term ident))
    (\<lambda>x w. (v,Pair_Term x (state_family_term ident w))\<in>positive_meaning P)"
  by (rule search.index) (rule state_family_term_formed[OF family.identity])

theorem exact:
  "(k,Pair_Term (present c) (Pair_Term (path_term a) (key_index_term rd ident A F)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (rd (snd z)) \<longrightarrow> reads c z)"
proof -
  have "(k,Pair_Term (present c) (Pair_Term (path_term a) (store_term (state_family_term ident) (key_index rd A F))))
      \<in>positive_meaning P \<longleftrightarrow> term_formed (present c) \<and> (\<exists>bs w. path_term a=path_term bs \<and>
        store_lookup (key_index rd A F) bs=Some w \<and> (v,Pair_Term (present c) (state_family_term ident w))\<in>positive_meaning P)"
    by (rule search.exact) (rule state_family_term_formed[OF family.identity])
  also have "\<dots> \<longleftrightarrow> term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (rd (snd z)) \<longrightarrow> reads c z)"
    by (auto simp: path_term_injective key_index_lookup family.exact key_fibre_member)
  finally show ?thesis by (simp only: key_index_term_def)
qed

end

section \<open>The selection reading: every row of a selection at a key satisfies a row reading\<close>

text \<open>
  A selection is the \<open>every\<close> of the index search over the list of its families' indexes, with the key and the
  reading's context as the context: one rule rearranges the call. Stated once, over any selection, any
  row reading and any key reading; its contract holds at every atom key of the state.
\<close>

definition subject_call_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "subject_call_rule k=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))
    [([0],(k,Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Pair (native_var 0) (native_var 2))))]"

locale key_selection_program = index: key_index_program P k v r present ident reads rd +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r :: "'u definition_site" and present ident reads rd
begin

text \<open>The call is an instance of the rearranging rule; it proves only its patterns' obligations.\<close>

sublocale rearranged: native_rearranging_program P g
  "Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)" k
  "Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Pair (native_var 0) (native_var 2))"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def
  using call.native_rule_family_axioms[unfolded subject_call_rule_def] by auto

lemma call_exact:
  "(g,Pair_Term (Pair_Term x y) w)\<in>positive_meaning P \<longleftrightarrow> (k,Pair_Term y (Pair_Term x w))\<in>positive_meaning P"
  using rearranged.at[of "native_values [x,y,w]"] by (simp add: insert_commute)

theorem family_exact:
  "(g,Pair_Term (Pair_Term (path_term a) (present c)) (key_index_term rd ident A F))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (rd (snd z)) \<longrightarrow> reads c z)"
  by (simp only: call_exact index.exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (present c)) (key_indexes_term rd ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (rd (snd z)) \<longrightarrow> reads c z)"
  by (auto simp: key_indexes_term_def every.exact family_exact atom)

end

section \<open>The subject index: the reading of a row's subjects\<close>

text \<open>
  The rows about a subject are the fibre of the key reading \<^const>\<open>row_subjects\<close>. Every name of the
  subject index is the notion's at that reading; its facts are the notion's, instantiated.
\<close>

abbreviation subject_fibre :: "state_key \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family" where
  "subject_fibre \<equiv> key_fibre row_subjects"

abbreviation subject_rows :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> (state_key\<times>'i state_family) list" where
  "subject_rows \<equiv> key_rows row_subjects"

abbreviation subject_index :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family binary_path_store" where
  "subject_index \<equiv> key_index row_subjects"

abbreviation subject_index_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> factor_term" where
  "subject_index_term \<equiv> key_index_term row_subjects"

abbreviation subject_indexes_term ::
    "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "subject_indexes_term \<equiv> key_indexes_term row_subjects"

lemmas subject_rows_single_valued = key_rows_single_valued[where rd=row_subjects]
lemmas subject_index_carrier_index = key_index_carrier_index[where rd=row_subjects]

interpretation subject_indexes: carrier_index "\<lambda>AF a w. a\<in>set (fst AF) \<and> w=subject_fibre a (snd AF)"
    "\<lambda>_. True" UNIV id "\<lambda>AF. subject_index (fst AF) (snd AF)" "\<lambda>T bs w. store_lookup T bs=Some w"
  by (rule subject_index_carrier_index)

lemmas subject_index_lookup = key_index_lookup[where rd=row_subjects]
lemmas subject_fibre_member = key_fibre_member[where rd=row_subjects]
lemmas subject_index_empty = key_index_empty[where rd=row_subjects]
lemmas subject_index_outside = key_index_outside[where rd=row_subjects]

locale subject_index_program = key_index_program P k v r present ident reads row_subjects
  for P :: "'u native_system" and k v r :: "'u definition_site" and present ident reads

locale subject_selection_program = key_selection_program P s g k v r present ident reads row_subjects
  for P :: "'u native_system" and s g k v r :: "'u definition_site" and present ident reads

section \<open>The mention index: the reading of the keys a row mentions\<close>

text \<open>
  The rows mentioning a key are the fibre of the key reading \<^const>\<open>row_mentions\<close>: the second instance
  of the notion, which the field \<open>undeclared\<close> and the reach table's predecessors read.
\<close>

abbreviation mention_fibre :: "state_key \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family" where
  "mention_fibre \<equiv> key_fibre row_mentions"

abbreviation mention_rows :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> (state_key\<times>'i state_family) list" where
  "mention_rows \<equiv> key_rows row_mentions"

abbreviation mention_index :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family binary_path_store" where
  "mention_index \<equiv> key_index row_mentions"

abbreviation mention_index_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> factor_term" where
  "mention_index_term \<equiv> key_index_term row_mentions"

abbreviation mention_indexes_term ::
    "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "mention_indexes_term \<equiv> key_indexes_term row_mentions"

lemmas mention_rows_single_valued = key_rows_single_valued[where rd=row_mentions]
lemmas mention_index_carrier_index = key_index_carrier_index[where rd=row_mentions]

interpretation mention_indexes: carrier_index "\<lambda>AF a w. a\<in>set (fst AF) \<and> w=mention_fibre a (snd AF)"
    "\<lambda>_. True" UNIV id "\<lambda>AF. mention_index (fst AF) (snd AF)" "\<lambda>T bs w. store_lookup T bs=Some w"
  by (rule mention_index_carrier_index)

lemmas mention_index_lookup = key_index_lookup[where rd=row_mentions]
lemmas mention_fibre_member = key_fibre_member[where rd=row_mentions]
lemmas mention_index_empty = key_index_empty[where rd=row_mentions]
lemmas mention_index_outside = key_index_outside[where rd=row_mentions]

locale mention_index_program = key_index_program P k v r present ident reads row_mentions
  for P :: "'u native_system" and k v r :: "'u definition_site" and present ident reads

locale mention_selection_program = key_selection_program P s g k v r present ident reads row_mentions
  for P :: "'u native_system" and s g k v r :: "'u definition_site" and present ident reads

end
