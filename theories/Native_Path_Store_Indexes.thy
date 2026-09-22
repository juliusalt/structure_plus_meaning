theory Native_Path_Store_Indexes
  imports Carrier_Indexes Native_Path_Stores
begin

section \<open>A path store is the native carrier of an index\<close>

text \<open>
  The native carrier of the index notion is the path store. Its host part: the carrier is a list of rows
  over paths, formed where the rows are single-valued, the key is the path itself, the index the path
  store of the rows and the search the lookup of a path; the member equation is @{text path_store_lookup}.
  Its native part is the search program of @{text native_store_search_program}: the site holds at a
  context, a key term and a presented store, keys are presented by @{text path_term} and stores by
  @{text store_term}, and the checker is the program's own at the found value. The contract is the
  program's @{text exact}, stated for every store and every key term, and it needs its values formed;
  its one-directional form, @{text sound}, needs nothing and gives the notion's
  @{text index_search_sound} for every presentation of the values.

  Both are stated in the context of @{text native_store_search_program}, as @{text index} and
  @{text index_sound}, and not as a sublocale: the instance of @{text index} is conditional on the values'
  formation, which is not a parameter of the program.
\<close>

lemma path_store_carrier_index:
  "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>rows. single_valued (set rows)) UNIV id path_store
    (\<lambda>T bs v. store_lookup T bs=Some v)"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by (rule inj_on_id)
next
  fix rows :: "(bool list\<times>'v) list" and k v
  assume sv: "single_valued (set rows)"
  show "store_lookup (path_store rows) k=Some v \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v)\<in>set rows)"
    using path_store_lookup[OF sv, of k v] by simp
qed

text \<open>Two stores whose lookups find the same values at a key have the same lookup there.\<close>

lemma lookup_eq_by_some:
  assumes same: "\<And>w. x=Some w \<longleftrightarrow> y=Some w"
  shows "x=y"
proof (cases x)
  case None
  show ?thesis
  proof (cases y)
    case None
    with \<open>x=None\<close> show ?thesis by simp
  next
    case (Some b)
    with same[of b] \<open>x=None\<close> show ?thesis by simp
  qed
next
  case (Some a)
  with same[of a] show ?thesis by simp
qed

section \<open>A path store restricted to a key set\<close>

text \<open>
  The restriction law: the path store of any listing filtered to a key set has the full store's lookup
  at every kept key, and finds nothing at a key outside the set. The store is the fold of its rows'
  replacements; filtering keeps every row at a kept key in its order and drops only replacements at
  other keys, which leave the lookup at the kept key unchanged. No single-valuedness is assumed. A call
  that carries the part of a store its reading can reach therefore reads the same values at every key
  it reaches.
\<close>

lemma path_store_fold_restrict:
  assumes kept: "k\<in>S" and same: "store_lookup T k=store_lookup T' k"
  shows "store_lookup (fold (\<lambda>(a,v) T. store_update T a (Some v)) (filter (\<lambda>r. fst r\<in>S) rows) T) k=
    store_lookup (fold (\<lambda>(a,v) T. store_update T a (Some v)) rows T') k"
  using same
proof (induction rows arbitrary: T T')
  case Nil
  then show ?case by simp
next
  case (Cons r rows)
  obtain a v where r: "r=(a,v)" by (cases r)
  show ?case
  proof (cases "a\<in>S")
    case True
    have eq: "store_lookup (store_update T a (Some v)) k=store_lookup (store_update T' a (Some v)) k"
      using Cons.prems by simp
    show ?thesis using True by (simp add: r) (rule Cons.IH[OF eq])
  next
    case False
    have eq: "store_lookup T k=store_lookup (store_update T' a (Some v)) k"
      using Cons.prems False kept by auto
    show ?thesis using False by (simp add: r) (rule Cons.IH[OF eq])
  qed
qed

lemma path_store_restrict:
  assumes kept: "k\<in>S"
  shows "store_lookup (path_store (filter (\<lambda>r. fst r\<in>S) rows)) k=store_lookup (path_store rows) k"
  unfolding path_store_def by (rule path_store_fold_restrict[OF kept refl])

lemma path_store_restrict_outside:
  assumes outside: "k\<notin>S"
  shows "store_lookup (path_store (filter (\<lambda>r. fst r\<in>S) rows)) k=None"
proof (cases "store_lookup (path_store (filter (\<lambda>r. fst r\<in>S) rows)) k")
  case (Some w)
  then have "(k,w)\<in>set (filter (\<lambda>r. fst r\<in>S) rows)" by (rule path_store_found)
  with outside show ?thesis by simp
qed


context native_store_search_program
begin

theorem index_sound:
  "index_search_sound (\<lambda>x t j. (k,Pair_Term x (Pair_Term t j))\<in>positive_meaning P) path_term
    (store_term val) (\<lambda>T bs v. store_lookup T bs=Some v) (\<lambda>x v. (ch,Pair_Term x (val v))\<in>positive_meaning P)"
  by (rule index_search_sound.intro) (erule sound)

theorem index:
  assumes valued: "\<And>y. term_formed (val y)"
  shows "native_carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>rows. single_valued (set rows)) UNIV id
    path_store (\<lambda>T bs v. store_lookup T bs=Some v) (\<lambda>x t j. (k,Pair_Term x (Pair_Term t j))\<in>positive_meaning P)
    term_formed path_term (store_term val) (\<lambda>x v. (ch,Pair_Term x (val v))\<in>positive_meaning P)"
proof (rule native_carrier_index.intro)
  show "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>rows. single_valued (set rows)) UNIV id path_store
      (\<lambda>T bs v. store_lookup T bs=Some v)"
    by (rule path_store_carrier_index)
next
  show "native_carrier_index_axioms (\<lambda>T bs v. store_lookup T bs=Some v)
      (\<lambda>x t j. (k,Pair_Term x (Pair_Term t j))\<in>positive_meaning P) term_formed path_term (store_term val)
      (\<lambda>x v. (ch,Pair_Term x (val v))\<in>positive_meaning P)"
  proof (rule native_carrier_index_axioms.intro)
    fix x t T
    show "(k,Pair_Term x (Pair_Term t (store_term val T)))\<in>positive_meaning P \<longleftrightarrow>
        term_formed x \<and> (\<exists>bs v. t=path_term bs \<and> store_lookup T bs=Some v \<and>
          (ch,Pair_Term x (val v))\<in>positive_meaning P)"
      by (rule exact[OF valued])
  next
    show "inj path_term" by (rule injI) (erule path_term_injective[THEN iffD1])
  qed
qed

end

text \<open>
  An interpretation @{text X} of @{text native_store_search_program} made in a theory importing this one
  inherits @{text "X.index"} and @{text "X.index_sound"}. Facts stated here do not reach an interpretation
  made in a theory this one does not precede; such a use names
  @{text "native_store_search_program.index[OF X.native_store_search_program_axioms]"} under the formation
  of its values, and @{text index_sound} likewise without it, whence @{text query_search},
  @{text site_query} and the other laws of the notion at the use's program.
\<close>

end
