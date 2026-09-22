theory Development_Subject_Index
imports Development_Verdict_Statements Native_Path_Store_Indexes
begin

section \<open>The rows about a subject, read through a subject index\<close>

text \<open>
  A native definition that reads the rows about a subject reads them through the \<^emph>\<open>subject index\<close> of each
  family, an instance of the index notion at the path store's carrier, and not through a complement of
  "about". For a family \<open>F\<close> and the state's atom keys \<open>A\<close>, the \<^emph>\<open>fibre\<close> of \<open>F\<close> at \<open>a\<close> is the family's rows
  having \<open>a\<close> among their subjects, in the family's order, each identity inert; the index is the path store of
  the rows \<open>(a, fibre of F at a)\<close> for \<open>a\<close> in \<open>A\<close>. It holds every atom of the state: at an atom no row is about,
  the fibre is found and empty; at a key that is no atom of the state, nothing is found. No key is compared
  with another and no absence is read.

  The index is computed from the presented atoms and family where the call's argument is built; it is
  neither a field of \<^typ>\<open>state_rows\<close> nor a condition \<^const>\<open>state_presents\<close> carries, and it adds no kind.
\<close>

definition subject_fibre :: "state_key \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family" where
  "subject_fibre a F=filter (\<lambda>z. a\<in>set (row_subjects (snd z))) F"

definition subject_rows :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> (state_key\<times>'i state_family) list" where
  "subject_rows A F=map (\<lambda>a. (a,subject_fibre a F)) A"

definition subject_index :: "state_key list \<Rightarrow> 'i state_family \<Rightarrow> 'i state_family binary_path_store" where
  "subject_index A F=path_store (subject_rows A F)"

definition subject_index_term :: "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family \<Rightarrow> factor_term" where
  "subject_index_term ident A F=store_term (state_family_term ident) (subject_index A F)"

definition subject_indexes_term ::
    "('i \<Rightarrow> factor_term) \<Rightarrow> state_key list \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "subject_indexes_term ident A Fs=data_list_term (map (subject_index_term ident A) Fs)"

section \<open>The index is an instance of the index notion\<close>

text \<open>
  The index's rows are single-valued whatever \<open>A\<close> is, since the value at a key is a function of the key; the
  distinctness of the atom keys is not needed. The four obligations of the notion, for the key: (1) the key
  is the path itself (\<open>inj id\<close>, the carrier's own); (2) the lookup at \<open>a\<close> is the fibre exactly when
  \<open>a\<in>set A\<close> (@{text subject_index_lookup}, the carrier's member equation through
  @{thm [source] path_store_carrier_index}); (3) the one operation its uses need, the filter lemma
  @{text subject_fibre_member}; (4) none, since the index is built once per presented state and never
  updated.
\<close>

lemma subject_rows_single_valued: "single_valued (set (subject_rows A F))"
  by (auto simp: single_valued_def subject_rows_def)

lemma subject_index_carrier_index:
  "carrier_index (\<lambda>AF a w. a\<in>set (fst AF) \<and> w=subject_fibre a (snd AF)) (\<lambda>_. True) UNIV id
    (\<lambda>AF. subject_index (fst AF) (snd AF)) (\<lambda>T bs w. store_lookup T bs=Some w)"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by (rule inj_on_id)
next
  fix AF :: "state_key list\<times>'i state_family" and k w
  have "store_lookup (path_store (subject_rows (fst AF) (snd AF))) k=Some w \<longleftrightarrow>
      (\<exists>q\<in>UNIV. id q=k \<and> (q,w)\<in>set (subject_rows (fst AF) (snd AF)))"
    by (rule carrier_index.represents[OF path_store_carrier_index subject_rows_single_valued])
  then show "store_lookup (subject_index (fst AF) (snd AF)) k=Some w \<longleftrightarrow>
      (\<exists>q\<in>UNIV. id q=k \<and> q\<in>set (fst AF) \<and> w=subject_fibre q (snd AF))"
    by (auto simp: subject_index_def subject_rows_def)
qed

interpretation subject_indexes: carrier_index "\<lambda>AF a w. a\<in>set (fst AF) \<and> w=subject_fibre a (snd AF)"
    "\<lambda>_. True" UNIV id "\<lambda>AF. subject_index (fst AF) (snd AF)" "\<lambda>T bs w. store_lookup T bs=Some w"
  by (rule subject_index_carrier_index)

lemma subject_index_lookup: "store_lookup (subject_index A F) a=Some w \<longleftrightarrow> a\<in>set A \<and> w=subject_fibre a F"
  using subject_indexes.query_search[where c="(A,F)" and q=a and v=w] by simp

lemma subject_fibre_member: "z\<in>set (subject_fibre a F) \<longleftrightarrow> z\<in>set F \<and> a\<in>set (row_subjects (snd z))"
  by (simp add: subject_fibre_def)

text \<open>
  An atom no row is about finds an empty fibre, a found and empty result; a key outside the state finds
  nothing, a failed one. The two are kept apart positively, by the index holding every atom.
\<close>

lemma subject_index_empty:
  assumes atom: "a\<in>set A" and none: "\<forall>z\<in>set F. a\<notin>set (row_subjects (snd z))"
  shows "store_lookup (subject_index A F) a=Some []"
proof -
  have "subject_fibre a F=[]" using none by (simp add: subject_fibre_def filter_empty_conv)
  then show ?thesis using atom by (simp add: subject_index_lookup)
qed

lemma subject_index_outside:
  assumes outside: "a\<notin>set A"
  shows "store_lookup (subject_index A F) a=None"
  using outside subject_index_lookup[of A F a] by (cases "store_lookup (subject_index A F) a") auto

section \<open>The native reading of the index\<close>

text \<open>
  The index's native part is the path store's search whose checker is the family's every-reading, generic
  over the row reading: the search holds at the reading's context, the path of a key and the index exactly
  when the key is an atom and every row of the family about it satisfies the reading. It reads the fibre
  alone: no row that is not about the key is visited.
\<close>

locale subject_index_program = search: native_store_search_program P k v +
    family: family_every_reading P v r present ident reads
  for P :: "'u native_system" and k v r :: "'u definition_site" and present ident reads
begin

corollary native_index:
  "native_carrier_index (\<lambda>rows q w. (q,w)\<in>set rows) (\<lambda>rows. single_valued (set rows)) UNIV id path_store
    (\<lambda>T bs w. store_lookup T bs=Some w) (\<lambda>x t j. (k,Pair_Term x (Pair_Term t j))\<in>positive_meaning P)
    term_formed path_term (store_term (state_family_term ident))
    (\<lambda>x w. (v,Pair_Term x (state_family_term ident w))\<in>positive_meaning P)"
  by (rule search.index) (rule state_family_term_formed[OF family.identity])

theorem exact:
  "(k,Pair_Term (present c) (Pair_Term (path_term a) (subject_index_term ident A F)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> reads c z)"
proof -
  have "(k,Pair_Term (present c) (Pair_Term (path_term a) (store_term (state_family_term ident) (subject_index A F))))
      \<in>positive_meaning P \<longleftrightarrow> term_formed (present c) \<and> (\<exists>bs w. path_term a=path_term bs \<and>
        store_lookup (subject_index A F) bs=Some w \<and> (v,Pair_Term (present c) (state_family_term ident w))\<in>positive_meaning P)"
    by (rule search.exact) (rule state_family_term_formed[OF family.identity])
  also have "\<dots> \<longleftrightarrow> term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> reads c z)"
    by (auto simp: path_term_injective subject_index_lookup family.exact subject_fibre_member)
  finally show ?thesis by (simp only: subject_index_term_def)
qed

end

section \<open>The selection reading: every row of a selection about a key satisfies a row reading\<close>

text \<open>
  A selection is the \<open>every\<close> of the index search over the list of its families' indexes, with the key and the
  reading's context as the context: one rule rearranges the call. Stated once, over any selection and any
  row reading; its contract holds at every atom key of the state.
\<close>

definition subject_call_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "subject_call_rule k=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))
    [([0],(k,Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Pair (native_var 0) (native_var 2))))]"

locale subject_selection_program = index: subject_index_program P k v r present ident reads +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r :: "'u definition_site" and present ident reads
begin

lemma call_exact:
  "(g,Pair_Term (Pair_Term x y) w)\<in>positive_meaning P \<longleftrightarrow> (k,Pair_Term y (Pair_Term x w))\<in>positive_meaning P"
proof
  assume holds: "(g,Pair_Term (Pair_Term x y) w)\<in>positive_meaning P"
  obtain c F f where rule: "(c,F)\<in>set [([0]::local_address,subject_call_rule k)]"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=Pair_Term (Pair_Term x y) w"
    and support: "\<forall>s e q. (s,e,q)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (e,evaluate_pattern f q)\<in>positive_meaning P"
    by (rule call.holds_cases[OF holds]) blast
  have F: "F=subject_call_rule k" using rule by simp
  have fields: "f [0]=x" "f [Suc 0]=y" "f [2]=w" using shape by (simp_all add: F subject_call_rule_def)
  show "(k,Pair_Term y (Pair_Term x w))\<in>positive_meaning P"
    using native_rule_support[OF support[unfolded F subject_call_rule_def]] by (simp add: fields)
next
  assume held: "(k,Pair_Term y (Pair_Term x w))\<in>positive_meaning P"
  have formed: "term_formed x" "term_formed y" "term_formed w"
    using positive_meaning_term_formed[OF held] by simp_all
  have "(g,evaluate_pattern (native_values [x,y,w]) (decode_finite_pattern
      (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))))
      \<in>positive_meaning P"
    by (rule call.native_step[where c="[0]" and
        ps="[([0],(k,Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Pair (native_var 0) (native_var 2))))]"])
      (use held formed in \<open>simp_all add: subject_call_rule_def\<close>)
  then show "(g,Pair_Term (Pair_Term x y) w)\<in>positive_meaning P" by simp
qed

theorem family_exact:
  "(g,Pair_Term (Pair_Term (path_term a) (present c)) (subject_index_term ident A F))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> a\<in>set A \<and> (\<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> reads c z)"
  by (simp only: call_exact index.exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (present c)) (subject_indexes_term ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed (present c) \<and> (\<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> reads c z)"
  by (auto simp: subject_indexes_term_def every.exact family_exact atom)

end

end
