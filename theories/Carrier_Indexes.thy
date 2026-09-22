theory Carrier_Indexes
imports Main
begin

section \<open>An index of a carrier by a key\<close>

text \<open>
  This is the notion stated in DECISIONS.md, "A refinement applies a notion; an index is one", checked.
  A \emph{carrier} is what is searched: a finite set, a finite relation, an addressed structure. Its
  content is a relation from queries to values, @{text "holds c q v"}: a finite set is the relation of
  its members to one value, a single-valued store a partial map, a relation store any relation, a
  demand the relation of its members to their positions. A \emph{key} maps a query into what the index
  is searched by, and \emph{distinguishes} on the queries the contract is claimed for. An \emph{index}
  is built once from the carrier and searched at a key. The contract is that every operation through
  the index returns the original set, relation, list or truth value.

  A formation condition on the carrier is a parameter: the contract is claimed under it, and no search
  assumes it. It is single-valuedness for a path store, functionality for a functional relation, and
  nothing for a relation store or a finite set.

  A carrier discharges two obligations by interpreting the locale. (1) The key distinguishes on the
  queries: it is injective there, of which a left inverse is a sufficient condition
  (@{text distinguishes_by_left_inverse}). (2) The index represents the carrier: one member equation,
  stated at every key, so that a key no query maps to finds nothing. The third obligation, one equation
  per operation a use needs, is not an assumption: a use proves it from the facts below. The fourth, for
  an index updated rather than built once, is the extension @{text updated_carrier_index}; a native
  carrier's one thing more is the extension @{text native_carrier_index}.

  The laws are theorems here, never assumptions. The first, \emph{only the key is ordered}, is stated by
  the signature: the locale constrains neither queries nor values, and nothing but the key's type is
  searched by; @{text Finite_Functional_Enumeration} and @{text Finite_Ordered_Representatives} are where
  it already stands for a functional relation. The second, \emph{the index is built once and shared}, is
  @{text query_search}: every query of one carrier reads the one index @{text "build c"}, and its search
  at a query's key is the carrier's fibre there. The third, \emph{the index presents its carrier and
  nothing else}, is @{text content_determines_search}: two formed carriers with equal content have
  equal search at every key, so the order of rows or of insertions is not a subject. Nothing here is
  about cost: which key to choose, and whether an index pays, are observations of a use.
\<close>

lemma distinguishes_by_left_inverse:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "inj_on key Q"
proof (rule inj_onI)
  fix x y assume "key x=key y"
  then have "unkey (key x)=unkey (key y)" by (rule arg_cong)
  then show "x=y" by (simp only: inverse)
qed

locale carrier_index =
  fixes holds :: "'c \<Rightarrow> 'q \<Rightarrow> 'v \<Rightarrow> bool" and formed :: "'c \<Rightarrow> bool" and Q :: "'q set"
    and key :: "'q \<Rightarrow> 'k" and build :: "'c \<Rightarrow> 'i" and search :: "'i \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool"
  assumes distinguishes: "inj_on key Q"
    and represents: "formed c \<Longrightarrow> search (build c) k v \<longleftrightarrow> (\<exists>q\<in>Q. key q=k \<and> holds c q v)"
begin

theorem query_search:
  assumes c: "formed c" and q: "q\<in>Q"
  shows "search (build c) (key q) v \<longleftrightarrow> holds c q v"
proof
  assume "search (build c) (key q) v"
  then obtain q' where member: "q'\<in>Q" and same: "key q'=key q" and held: "holds c q' v"
    using represents[OF c] by blast
  have "q'=q" by (rule inj_onD[OF distinguishes same member q])
  then show "holds c q v" using held by (simp only:)
next
  assume "holds c q v"
  then show "search (build c) (key q) v" using represents[OF c] q by blast
qed

corollary query_fibre:
  assumes "formed c" "q\<in>Q"
  shows "search (build c) (key q)=holds c q"
  by (rule ext) (rule query_search[OF assms])

theorem unkeyed_search:
  assumes c: "formed c" and absent: "k\<notin>key ` Q"
  shows "\<not> search (build c) k v"
  unfolding represents[OF c] using absent by blast

theorem content_determines_search:
  assumes c: "formed c" and d: "formed d"
    and same: "\<And>q v. q\<in>Q \<Longrightarrow> holds c q v \<longleftrightarrow> holds d q v"
  shows "search (build c) k v \<longleftrightarrow> search (build d) k v"
proof -
  have "(\<exists>q\<in>Q. key q=k \<and> holds c q v) \<longleftrightarrow> (\<exists>q\<in>Q. key q=k \<and> holds d q v)"
    using same by blast
  then show ?thesis by (simp only: represents[OF c] represents[OF d])
qed

text \<open>
  Three forms the uses ask of the notion, stated once so that no instance makes their argument again.
  Every query of a set of queries is found exactly when each holds some value in the carrier
  (@{text queries_search}). Where the search is an optional lookup, the lookup at a query's key finds
  something exactly when the query holds some value (@{text lookup_found}), and so for every query of a
  set (@{text lookup_queries_found}). The pairs an index finds are the keyed image of the carrier's
  content (@{text found_pairs}), so a use needing a carrier's whole-set contract takes it from the notion
  in one step.
\<close>

corollary queries_search:
  assumes c: "formed c" and B: "B\<subseteq>Q"
  shows "(\<forall>q\<in>B. \<exists>v. search (build c) (key q) v) \<longleftrightarrow> (\<forall>q\<in>B. \<exists>v. holds c q v)"
proof (rule ball_cong[OF refl])
  fix q assume "q\<in>B"
  with B have q: "q\<in>Q" by blast
  show "(\<exists>v. search (build c) (key q) v) \<longleftrightarrow> (\<exists>v. holds c q v)" by (simp only: query_search[OF c q])
qed

corollary lookup_found:
  assumes lookup: "\<And>i k v. search i k v \<longleftrightarrow> look i k=Some v" and c: "formed c" and q: "q\<in>Q"
  shows "look (build c) (key q)\<noteq>None \<longleftrightarrow> (\<exists>v. holds c q v)"
proof -
  have "look (build c) (key q)\<noteq>None \<longleftrightarrow> (\<exists>v. search (build c) (key q) v)" by (simp only: lookup not_None_eq)
  also have "\<dots> \<longleftrightarrow> (\<exists>v. holds c q v)" by (simp only: query_search[OF c q])
  finally show ?thesis .
qed

corollary lookup_queries_found:
  assumes lookup: "\<And>i k v. search i k v \<longleftrightarrow> look i k=Some v" and c: "formed c" and B: "B\<subseteq>Q"
  shows "(\<forall>q\<in>B. look (build c) (key q)\<noteq>None) \<longleftrightarrow> (\<forall>q\<in>B. \<exists>v. holds c q v)"
proof -
  have "(\<forall>q\<in>B. look (build c) (key q)\<noteq>None) \<longleftrightarrow> (\<forall>q\<in>B. \<exists>v. search (build c) (key q) v)"
    by (simp only: lookup not_None_eq)
  also have "\<dots> \<longleftrightarrow> (\<forall>q\<in>B. \<exists>v. holds c q v)" by (rule queries_search[OF c B])
  finally show ?thesis .
qed

theorem found_pairs:
  assumes c: "formed c"
  shows "{(k,v). search (build c) k v}=(\<lambda>(q,v). (key q,v)) ` {(q,v). q\<in>Q \<and> holds c q v}"
  unfolding represents[OF c] by auto

end

text \<open>
  An index of the image of the queries under a key, searched by the keys themselves, is an index of
  the carrier read through that key, when the key distinguishes: the argument
  the keyed set makes over the ordered member tree (@{text Member_Tree_Indexes.keyed_set_index.carrier}),
  stated once.
\<close>

lemma carrier_index_through_key:
  assumes inner: "carrier_index holds' formed' UNIV id build search"
    and image: "\<And>c. formed c \<Longrightarrow> formed' (img c)"
    and image_content: "\<And>c k v. formed c \<Longrightarrow> holds' (img c) k v \<longleftrightarrow> (\<exists>q\<in>Q. key q=k \<and> holds c q v)"
    and injective: "inj_on key Q"
  shows "carrier_index holds formed Q key (\<lambda>c. build (img c)) search"
proof (rule carrier_index.intro)
  show "inj_on key Q" by (rule injective)
  fix c k v assume c: "formed c"
  have "search (build (img c)) k v \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> holds' (img c) q v)"
    by (rule carrier_index.represents[OF inner image[OF c]])
  also have "\<dots> \<longleftrightarrow> holds' (img c) k v" by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>q\<in>Q. key q=k \<and> holds c q v)" by (rule image_content[OF c])
  finally show "search (build (img c)) k v \<longleftrightarrow> (\<exists>q\<in>Q. key q=k \<and> holds c q v)" .
qed

section \<open>An index updated rather than built once\<close>

text \<open>
  An update of an index at a key changes the fibre there by a stated change and preserves every other
  key. The replacement of a path store (@{text Binary_Path_Stores.store_lookup_update}: the change
  replaces the fibre by the optional value), the insertion into a relation store and a nested store
  (@{text relation_store_lookup_insert}, @{text nested_relation_lookup_insert}: the change adds one
  value) and an insertion into an ordered member tree, which @{text Keyed_Demanded_Sites.keyed_fold_insert}
  folds (the change makes the one value found), are its instances. An update applied to the index of a
  carrier is the index of the carrier changed in the same way at that query (@{text update_represents}).
\<close>

locale updated_carrier_index = carrier_index holds formed Q key build search
  for holds :: "'c \<Rightarrow> 'q \<Rightarrow> 'v \<Rightarrow> bool" and formed :: "'c \<Rightarrow> bool" and Q :: "'q set"
    and key :: "'q \<Rightarrow> 'k" and build :: "'c \<Rightarrow> 'i" and search :: "'i \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes update :: "'i \<Rightarrow> 'k \<Rightarrow> 'u \<Rightarrow> 'i" and change :: "'u \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> bool"
  assumes updated: "search (update i k u) k' v \<longleftrightarrow> (if k'=k then change u (search i k) v else search i k' v)"
begin

theorem update_at: "search (update i k u) k v \<longleftrightarrow> change u (search i k) v"
  by (simp only: updated simp_thms if_True)

theorem update_preserves_else:
  assumes "k'\<noteq>k"
  shows "search (update i k u) k' v \<longleftrightarrow> search i k' v"
  using updated[of i k u k' v] assms by (simp only: if_False)

theorem update_represents:
  assumes c: "formed c" and q: "q\<in>Q" and c': "formed c'"
    and changed: "\<And>v. holds c' q v \<longleftrightarrow> change u (holds c q) v"
    and kept: "\<And>q' v. q'\<in>Q \<Longrightarrow> q'\<noteq>q \<Longrightarrow> holds c' q' v \<longleftrightarrow> holds c q' v"
  shows "search (update (build c) (key q) u) k v \<longleftrightarrow> search (build c') k v"
proof (cases "k=key q")
  case True
  have "search (update (build c) (key q) u) (key q) v \<longleftrightarrow> change u (search (build c) (key q)) v"
    by (rule update_at)
  also have "\<dots> \<longleftrightarrow> change u (holds c q) v" by (simp only: query_fibre[OF c q])
  also have "\<dots> \<longleftrightarrow> holds c' q v" by (rule changed[symmetric])
  also have "\<dots> \<longleftrightarrow> search (build c') (key q) v" by (rule query_search[OF c' q, symmetric])
  finally show ?thesis by (simp only: True)
next
  case False
  have "search (update (build c) (key q) u) k v \<longleftrightarrow> search (build c) k v"
    by (rule update_preserves_else[OF False])
  also have "\<dots> \<longleftrightarrow> (\<exists>q'\<in>Q. key q'=k \<and> holds c q' v)" by (rule represents[OF c])
  also have "\<dots> \<longleftrightarrow> (\<exists>q'\<in>Q. key q'=k \<and> holds c' q' v)"
  proof (rule bex_cong[OF refl])
    fix q' assume member: "q'\<in>Q"
    show "key q'=k \<and> holds c q' v \<longleftrightarrow> key q'=k \<and> holds c' q' v"
    proof (cases "q'=q")
      case True
      then show ?thesis using False by blast
    next
      case other: False
      show ?thesis using kept[OF member other, of v] by blast
    qed
  qed
  also have "\<dots> \<longleftrightarrow> search (build c') k v" by (rule represents[OF c', symmetric])
  finally show ?thesis .
qed

end

section \<open>A native carrier searches at every key term\<close>

text \<open>
  A native carrier is searched by a site of a program: it holds at a context, a key term and a presented
  index. Its one thing more is that its contract holds for every argument the site can be called with,
  every key term and every index, not only for the keys a use presents: the site holds exactly when the
  context is formed, the key term presents a key, the host search finds a value there and a checker
  holds of it. This is the shape of @{text Native_Path_Stores.native_store_search_program.exact}; its
  one-directional form without a premise on the values, @{text index_search_sound}, is the shape of
  @{text native_store_search_program.sound}. The program is abstract: the site is any relation.
\<close>

locale index_search_sound =
  fixes site :: "'x \<Rightarrow> 't \<Rightarrow> 'j \<Rightarrow> bool" and present :: "'k \<Rightarrow> 't" and index_term :: "'i \<Rightarrow> 'j"
    and search :: "'i \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" and checker :: "'x \<Rightarrow> 'v \<Rightarrow> bool"
  assumes site_sound: "site x t (index_term i) \<Longrightarrow> \<exists>k v. t=present k \<and> search i k v \<and> checker x v"

locale native_carrier_index = carrier_index holds formed Q key build search
  for holds :: "'c \<Rightarrow> 'q \<Rightarrow> 'v \<Rightarrow> bool" and formed :: "'c \<Rightarrow> bool" and Q :: "'q set"
    and key :: "'q \<Rightarrow> 'k" and build :: "'c \<Rightarrow> 'i" and search :: "'i \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes site :: "'x \<Rightarrow> 't \<Rightarrow> 'j \<Rightarrow> bool" and context_formed :: "'x \<Rightarrow> bool"
    and present :: "'k \<Rightarrow> 't" and index_term :: "'i \<Rightarrow> 'j" and checker :: "'x \<Rightarrow> 'v \<Rightarrow> bool"
  assumes site_exact: "site x t (index_term i) \<longleftrightarrow>
      context_formed x \<and> (\<exists>k v. t=present k \<and> search i k v \<and> checker x v)"
    and presents_distinguish: "inj present"
begin

sublocale sound: index_search_sound site present index_term search checker
  by (rule index_search_sound.intro) (simp only: site_exact)

theorem site_refuses_unpresented:
  assumes "\<nexists>k. t=present k"
  shows "\<not> site x t (index_term i)"
  using site_exact assms by blast

theorem site_query:
  assumes c: "formed c" and q: "q\<in>Q"
  shows "site x (present (key q)) (index_term (build c)) \<longleftrightarrow>
    context_formed x \<and> (\<exists>v. holds c q v \<and> checker x v)"
proof -
  have "(\<exists>k v. present (key q)=present k \<and> search (build c) k v \<and> checker x v) \<longleftrightarrow>
      (\<exists>v. search (build c) (key q) v \<and> checker x v)"
    using injD[OF presents_distinguish] by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>v. holds c q v \<and> checker x v)" by (simp only: query_search[OF c q])
  finally show ?thesis by (simp only: site_exact)
qed

end

end
