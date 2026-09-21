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
