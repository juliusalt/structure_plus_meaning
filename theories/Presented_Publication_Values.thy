theory Presented_Publication_Values
  imports Shared_Call_Closures Development_Publication Ordered_Term_Comparison
begin

section \<open>The publication notions' presenters over a term presentation\<close>

text \<open>
  DECISIONS.md, "The published state holds its targets once, and a report's word is read off them", B3.
  The presenters of generations, snapshots, transaction results and observations, and the data list,
  pair, option, sequence and collection presentations they are composed of, are stated once over a term
  presentation (@{text Presented_Term_Matching}), the target presenter an argument. Over a domain of
  presented terms each value lies in the domain and decodes to the plain presenter at the decoded value;
  at the plain presentation with @{const Finite_Target} each is the existing presenter.
\<close>

subsection \<open>The head and the children a view gives\<close>

fun term_view_head :: "'p Presented_Term_Matching.term_view \<Rightarrow> finite_term_atom" where
  "term_view_head (View_Payload v)=(0,None,v)"
| "term_view_head (View_Target (Finite_Whole a))=(1,Some (Ordered_Complete_Artifact a),[])"
| "term_view_head (View_Target (Finite_Anchor a r))=(2,Some (Ordered_Complete_Artifact a),r)"
| "term_view_head (View_Pair x y)=(3,None,[])"

fun term_view_children :: "'p Presented_Term_Matching.term_view \<Rightarrow> 'p list" where
  "term_view_children (View_Pair x y)=[x,y]"
| "term_view_children (View_Payload v)=[]"
| "term_view_children (View_Target a)=[]"

lemma term_view_head_plain: "term_view_head (finite_term_view t)=hd (finite_term_key t)"
  by (cases t rule: finite_term_key.cases) simp_all

lemma term_view_children_plain: "term_view_children (finite_term_view t)=finite_term_children t"
  by (cases t) simp_all

lemma term_view_head_map: "term_view_head (map_term_view g v)=term_view_head v"
  by (cases v rule: term_view_head.cases) simp_all

lemma term_view_children_map: "term_view_children (map_term_view g v)=map g (term_view_children v)"
  by (cases v) simp_all

lemma term_view_head_arity:
  "term_view_head v=term_view_head w \<Longrightarrow> length (term_view_children v)=length (term_view_children w)"
  by (cases v rule: term_view_head.cases; cases w rule: term_view_head.cases) simp_all

subsection \<open>Presented terms compare through their views\<close>

text \<open>
  A head is compared as the atom of the plain key, each field once. Two presented terms are compared
  through a list of pending pairs: an equal pair compares equal without its view, and a pair whose heads
  are equal is replaced by the pairs of its children. The comparison is tail recursive over any
  presentation; over a domain of presented terms it is the order of the plain keys of the decoded terms,
  so the structural comparison of the decoded terms.
\<close>

fun compare_artifact_option :: "ordered_complete_artifact option \<Rightarrow> ordered_complete_artifact option \<Rightarrow> linear_comparison" where
  "compare_artifact_option None None=Linear_Equal"
| "compare_artifact_option None (Some b)=Linear_Less"
| "compare_artifact_option (Some a) None=Linear_Greater"
| "compare_artifact_option (Some (Ordered_Complete_Artifact a)) (Some (Ordered_Complete_Artifact b))=compare_artifacts a b"

lemma compare_linear_none_some:
  "compare_linear None (Some (b::'a::linorder))=Linear_Less"
  "compare_linear (Some (a::'a::linorder)) None=Linear_Greater"
  by (simp_all add: compare_linear_def)

lemma compare_artifact_option_linear: "compare_artifact_option x y=compare_linear x y"
  by (induct x y rule: compare_artifact_option.induct)
    (simp_all only: compare_artifact_option.simps compare_linear_option compare_linear_ordered_artifact
      compare_linear_none_some)

definition compare_term_atom :: "finite_term_atom \<Rightarrow> finite_term_atom \<Rightarrow> linear_comparison" where
  "compare_term_atom=compare_paired compare_natural (compare_paired compare_artifact_option compare_address)"

lemma compare_term_atom_linear: "compare_term_atom x y=compare_linear x y"
  unfolding compare_term_atom_def
  by (rule compare_paired_linear[OF compare_natural_linear
    compare_paired_linear[OF compare_artifact_option_linear compare_address_linear]])

partial_function (tailrec) presented_compare_pending :: "'p term_presentation \<Rightarrow> ('p\<times>'p) list \<Rightarrow> linear_comparison" where
  "presented_compare_pending P zs=(case zs of [] \<Rightarrow> Linear_Equal
    | (x,y)#rest \<Rightarrow> if x=y then presented_compare_pending P rest else
      (case (presented_view P x,presented_view P y) of (vx,vy) \<Rightarrow>
        (case compare_term_atom (term_view_head vx) (term_view_head vy) of
          Linear_Equal \<Rightarrow> presented_compare_pending P (zip (term_view_children vx) (term_view_children vy)@rest)
        | c \<Rightarrow> c)))"

declare presented_compare_pending.simps [code]

lemma presented_compare_pending_nil: "presented_compare_pending P []=Linear_Equal"
  by (subst presented_compare_pending.simps[of P "[]"]) simp

lemma presented_compare_pending_cons:
  "presented_compare_pending P ((x,y)#rest)=(if x=y then presented_compare_pending P rest else
    (case compare_term_atom (term_view_head (presented_view P x)) (term_view_head (presented_view P y)) of
      Linear_Equal \<Rightarrow> presented_compare_pending P
        (zip (term_view_children (presented_view P x)) (term_view_children (presented_view P y))@rest)
    | c \<Rightarrow> c))"
  by (subst presented_compare_pending.simps[of P "(x,y)#rest"]) simp

definition presented_compare :: "'p term_presentation \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> linear_comparison" where
  "presented_compare P x y=presented_compare_pending P [(x,y)]"

lemma presented_compare_same: "presented_compare P x x=Linear_Equal"
  by (simp add: presented_compare_def presented_compare_pending_cons presented_compare_pending_nil)

definition pending_key :: "('p \<Rightarrow> finite_factor_term) \<Rightarrow> 'p list \<Rightarrow> finite_term_atom list" where
  "pending_key d xs=concat (map (\<lambda>x. finite_term_key (d x)) xs)"

lemma pending_key_simps [simp]:
  "pending_key d []=[]"
  "pending_key d (x#xs)=finite_term_key (d x)@pending_key d xs"
  "pending_key d (xs@ys)=pending_key d xs@pending_key d ys"
  by (simp_all add: pending_key_def)

lemma compare_linear_append_same:
  fixes k xs ys :: "'a::linorder list"
  shows "compare_linear (k@xs) (k@ys)=compare_linear xs ys"
  by (induct k) (simp_all add: compare_linear_prefix)

context presented_terms
begin

lemma view_children_domain:
  assumes x: "x\<in>D"
  shows "set (term_view_children (presented_view P x))\<subseteq>D"
proof (cases "presented_view P x")
  case (View_Pair a b)
  then show ?thesis using components[OF x View_Pair] by simp
qed simp_all

lemma view_key:
  assumes x: "x\<in>D"
  shows "finite_term_key (presented_decode P x)=
    term_view_head (presented_view P x)#pending_key (presented_decode P) (term_view_children (presented_view P x))"
proof -
  have v: "finite_term_view (presented_decode P x)=map_term_view (presented_decode P) (presented_view P x)"
    using view[OF x] by simp
  have k: "finite_term_key (presented_decode P x)=hd (finite_term_key (presented_decode P x))#
      concat (map finite_term_key (finite_term_children (presented_decode P x)))"
    by (rule finite_term_keys.key_node)
  have h: "hd (finite_term_key (presented_decode P x))=term_view_head (presented_view P x)"
    by (simp only: term_view_head_plain[symmetric] v term_view_head_map)
  have c: "finite_term_children (presented_decode P x)=map (presented_decode P) (term_view_children (presented_view P x))"
    by (simp only: term_view_children_plain[symmetric] v term_view_children_map)
  show ?thesis
    by (subst k) (simp only: h c, simp add: pending_key_def comp_def)
qed

theorem presented_compare_pending_keys:
  "set (map fst zs)\<subseteq>D \<Longrightarrow> set (map snd zs)\<subseteq>D \<Longrightarrow>
    presented_compare_pending P zs=compare_linear (pending_key (presented_decode P) (map fst zs))
      (pending_key (presented_decode P) (map snd zs))"
proof (induct zs rule: measure_induct_rule[where f="\<lambda>zs. length (pending_key (presented_decode P) (map fst zs))"])
  case (less zs)
  show ?case
  proof (cases zs)
    case Nil
    then show ?thesis by (simp add: presented_compare_pending_nil)
  next
    case (Cons z rest)
    obtain x y where z: "z=(x,y)" by (cases z)
    have x: "x\<in>D" and y: "y\<in>D" using less.prems by (simp_all add: Cons z)
    have rest: "set (map fst rest)\<subseteq>D" "set (map snd rest)\<subseteq>D" using less.prems by (simp_all add: Cons)
    show ?thesis
    proof (cases "x=y")
      case True
      have smaller: "length (pending_key (presented_decode P) (map fst rest))<
          length (pending_key (presented_decode P) (map fst zs))"
        using finite_term_key_nonempty[of "presented_decode P x"] by (simp add: Cons z)
      show ?thesis
        using less.hyps[OF smaller rest] by (simp add: presented_compare_pending_cons Cons z True compare_linear_append_same)
    next
      case False
      define vx vy where "vx=presented_view P x" and "vy=presented_view P y"
      define cx cy where "cx=term_view_children vx" and "cy=term_view_children vy"
      have kx: "finite_term_key (presented_decode P x)=term_view_head vx#pending_key (presented_decode P) cx"
        using view_key[OF x] by (simp add: vx_def cx_def)
      have ky: "finite_term_key (presented_decode P y)=term_view_head vy#pending_key (presented_decode P) cy"
        using view_key[OF y] by (simp add: vy_def cy_def)
      have cxD: "set cx\<subseteq>D" "set cy\<subseteq>D"
        using view_children_domain[OF x] view_children_domain[OF y] by (simp_all add: cx_def cy_def vx_def vy_def)
      have step: "presented_compare_pending P zs=(case compare_term_atom (term_view_head vx) (term_view_head vy) of
          Linear_Equal \<Rightarrow> presented_compare_pending P (zip cx cy@rest) | c \<Rightarrow> c)"
        unfolding cx_def cy_def vx_def vy_def by (simp add: presented_compare_pending_cons Cons z False)
      have spec: "compare_linear (pending_key (presented_decode P) (map fst zs)) (pending_key (presented_decode P) (map snd zs))=
        (case compare_linear (term_view_head vx) (term_view_head vy) of
          Linear_Equal \<Rightarrow> compare_linear (pending_key (presented_decode P) cx@pending_key (presented_decode P) (map fst rest))
            (pending_key (presented_decode P) cy@pending_key (presented_decode P) (map snd rest))
        | c \<Rightarrow> c)"
        by (simp add: Cons z kx ky compare_linear_prefix)
      show ?thesis
      proof (cases "compare_linear (term_view_head vx) (term_view_head vy)")
        case Linear_Equal
        have heads: "term_view_head vx=term_view_head vy" using Linear_Equal by (simp add: compare_linear_cases)
        have lengths: "length cx=length cy" using term_view_head_arity[OF heads] by (simp add: cx_def cy_def)
        have smaller: "length (pending_key (presented_decode P) (map fst (zip cx cy@rest)))<
            length (pending_key (presented_decode P) (map fst zs))"
          using lengths by (simp add: Cons z kx)
        have ih: "presented_compare_pending P (zip cx cy@rest)=
            compare_linear (pending_key (presented_decode P) (map fst (zip cx cy@rest)))
              (pending_key (presented_decode P) (map snd (zip cx cy@rest)))"
          by (rule less.hyps[OF smaller]) (use cxD rest lengths in simp_all)
        show ?thesis using step spec ih Linear_Equal by (simp add: compare_term_atom_linear lengths)
      next
        case Linear_Less
        then show ?thesis using step spec by (simp add: compare_term_atom_linear)
      next
        case Linear_Greater
        then show ?thesis using step spec by (simp add: compare_term_atom_linear)
      qed
    qed
  qed
qed

theorem presented_compare_decode:
  "x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow> presented_compare P x y=finite_term_compare (presented_decode P x) (presented_decode P y)"
  using presented_compare_pending_keys[of "[(x,y)]"] by (simp add: presented_compare_def finite_term_compare_order)

lemma presented_compare_less:
  "x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow> presented_compare P x y=Linear_Less \<longleftrightarrow>
    Ordered_Factor_Term (presented_decode P x)<Ordered_Factor_Term (presented_decode P y)"
  by (simp add: presented_compare_decode less_ordered_factor_term_structural_code)

end

lemma plain_presented_compare: "presented_compare plain_term_presentation=finite_term_compare"
  using plain_terms.presented_compare_decode by (simp add: fun_eq_iff)

subsection \<open>A finite set of presented terms is listed in the order of its decoded terms\<close>

text \<open>
  An element's rank is the number of elements less than it; the elements are listed by rank through the
  guarded functional enumeration (@{text Finite_Functional_Enumeration}), so the listing is defined for
  any presentation and depends on no enumeration of the set. Over a domain the comparison is a strict
  total order, the ranks are distinct, and the listing is the decoded terms' canonical order.
\<close>

definition presented_rank :: "'p term_presentation \<Rightarrow> 'p fset \<Rightarrow> 'p \<Rightarrow> nat" where
  "presented_rank P B x=fcard (ffilter (\<lambda>y. presented_compare P y x=Linear_Less) B)"

definition presented_listing :: "'p term_presentation \<Rightarrow> 'p fset \<Rightarrow> 'p list" where
  "presented_listing P B=map snd (finite_functional_rows (fimage (\<lambda>x. (presented_rank P B x,x)) B))"

context presented_terms
begin

theorem presented_listing_exact:
  assumes B: "fset B\<subseteq>D"
  shows "set (presented_listing P B)=fset B"
    and "map (\<lambda>x. Ordered_Factor_Term (presented_decode P x)) (presented_listing P B)=
      sorted_list_of_fset (fimage (\<lambda>x. Ordered_Factor_Term (presented_decode P x)) B)"
proof -
  let ?w="\<lambda>x. Ordered_Factor_Term (presented_decode P x)"
  let ?r="presented_rank P B"
  have w_inj: "x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow> ?w x=?w y \<Longrightarrow> x=y" for x y using decides by simp
  have less: "x\<in>fset B \<Longrightarrow> y\<in>fset B \<Longrightarrow> presented_compare P y x=Linear_Less \<longleftrightarrow> ?w y<?w x" for x y
    using B by (intro presented_compare_less) auto
  have rank: "x\<in>fset B \<Longrightarrow> ?r x=card {y\<in>fset B. ?w y<?w x}" for x
  proof -
    assume x: "x\<in>fset B"
    have "fset (ffilter (\<lambda>y. presented_compare P y x=Linear_Less) B)={y\<in>fset B. ?w y<?w x}"
      using less[OF x] by auto
    then show ?thesis by (simp add: presented_rank_def fcard.rep_eq)
  qed
  have mono: "x\<in>fset B \<Longrightarrow> y\<in>fset B \<Longrightarrow> \<not> ?w x<?w y \<Longrightarrow> ?r y\<le>?r x" for x y
  proof -
    assume x: "x\<in>fset B" and y: "y\<in>fset B" and le: "\<not> ?w x<?w y"
    have "{z\<in>fset B. ?w z<?w y}\<subseteq>{z\<in>fset B. ?w z<?w x}" using le by (auto simp: not_less intro: less_le_trans)
    then have "card {z\<in>fset B. ?w z<?w y}\<le>card {z\<in>fset B. ?w z<?w x}" by (intro card_mono) simp_all
    then show ?thesis by (simp only: rank[OF x] rank[OF y])
  qed
  have strict: "x\<in>fset B \<Longrightarrow> y\<in>fset B \<Longrightarrow> ?w y<?w x \<Longrightarrow> ?r y<?r x" for x y
  proof -
    assume x: "x\<in>fset B" and y: "y\<in>fset B" and lt: "?w y<?w x"
    have sub: "{z\<in>fset B. ?w z<?w y}\<subseteq>{z\<in>fset B. ?w z<?w x}" using lt by (auto intro: less_trans)
    have ne: "{z\<in>fset B. ?w z<?w y}\<noteq>{z\<in>fset B. ?w z<?w x}" using y lt by blast
    have "card {z\<in>fset B. ?w z<?w y}<card {z\<in>fset B. ?w z<?w x}"
      by (rule psubset_card_mono) (simp_all add: psubsetI[OF sub ne])
    then show ?thesis by (simp only: rank[OF x] rank[OF y])
  qed
  have rank_inj: "x\<in>fset B \<Longrightarrow> y\<in>fset B \<Longrightarrow> ?r x=?r y \<Longrightarrow> x=y" for x y
  proof (rule ccontr)
    assume x: "x\<in>fset B" and y: "y\<in>fset B" and eq: "?r x=?r y" and ne: "x\<noteq>y"
    have "?w x\<noteq>?w y" using w_inj[of x y] ne x y B by blast
    then have "?w x<?w y \<or> ?w y<?w x" by (rule linorder_neq_iff[THEN iffD1])
    then show False using strict[OF x y] strict[OF y x] eq by auto
  qed
  define R where "R=fimage (\<lambda>x. (?r x,x)) B"
  have functional: "finite_relation_functional R"
    unfolding finite_relation_functional_correct single_valued_def R_def
    by (auto simp: fimage.rep_eq intro: rank_inj)
  define rows where "rows=finite_functional_rows R"
  have listing: "presented_listing P B=map snd rows" by (simp add: presented_listing_def rows_def R_def)
  have rows_set: "set rows=fset R" by (simp add: rows_def finite_functional_rows_exact[OF functional])
  have keys: "sorted_wrt (<) (map fst rows)"
    by (simp add: rows_def finite_functional_rows_keys[OF functional] strict_sorted_iff sorted_list_of_fset.rep_eq)
  have row_shape: "r\<in>set rows \<Longrightarrow> snd r\<in>fset B \<and> fst r=?r (snd r)" for r
    using rows_set by (auto simp: R_def fimage.rep_eq)
  have "sorted_wrt (\<lambda>r s. fst r<fst s) rows" using keys by (simp add: sorted_wrt_map)
  then have ordered: "sorted_wrt (\<lambda>r s. ?w (snd r)<?w (snd s)) rows"
  proof (rule sorted_wrt_mono_rel[rotated])
    fix r s assume r: "r\<in>set rows" and s: "s\<in>set rows" and lt: "fst r<fst s"
    show "?w (snd r)<?w (snd s)"
    proof (rule ccontr)
      assume "\<not> ?w (snd r)<?w (snd s)"
      then have "?r (snd s)\<le>?r (snd r)" using mono row_shape[OF r] row_shape[OF s] by blast
      then show False using lt row_shape[OF r] row_shape[OF s] by simp
    qed
  qed
  have set_listing: "set (presented_listing P B)=fset B"
    using rows_set by (simp add: listing R_def fimage.rep_eq image_image)
  have sorted: "sorted_wrt (<) (map ?w (presented_listing P B))"
    using ordered by (simp add: listing sorted_wrt_map)
  show "set (presented_listing P B)=fset B" by (rule set_listing)
  show "map ?w (presented_listing P B)=sorted_list_of_fset (fimage ?w B)"
    using sorted set_listing
    by (intro sorted_distinct_set_unique) (simp_all add: strict_sorted_iff sorted_list_of_fset.rep_eq fimage.rep_eq)
qed

end

subsection \<open>The data list, pair, option, sequence and collection presentations\<close>

fun presented_data_list :: "'p term_presentation \<Rightarrow> 'p list \<Rightarrow> 'p" where
  "presented_data_list P []=presented_payload P []"
| "presented_data_list P (t#ts)=presented_pair P t (presented_data_list P ts)"

definition presented_pair_value :: "'p term_presentation \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> ('b \<Rightarrow> 'p) \<Rightarrow> 'a\<times>'b \<Rightarrow> 'p" where
  "presented_pair_value P f g z=presented_pair P (f (fst z)) (g (snd z))"

definition presented_sequence :: "'p term_presentation \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> 'a list \<Rightarrow> 'p" where
  "presented_sequence P f xs=presented_data_list P (map f xs)"

definition presented_option :: "'p term_presentation \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> 'a option \<Rightarrow> 'p" where
  "presented_option P f x=presented_sequence P f (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"

definition presented_collection :: "'p term_presentation \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> 'a fset \<Rightarrow> 'p" where
  "presented_collection P f A=presented_data_list P (presented_listing P (fimage f A))"

fun presented_natural :: "'p term_presentation \<Rightarrow> nat \<Rightarrow> 'p" where
  "presented_natural P 0=presented_payload P []"
| "presented_natural P (Suc n)=presented_pair P (presented_payload P []) (presented_natural P n)"

definition presented_boolean :: "'p term_presentation \<Rightarrow> bool \<Rightarrow> 'p" where
  "presented_boolean P b=presented_natural P (if b then 1 else 0)"

lemma finite_collection_presentation_cong:
  assumes same: "\<And>a. a\<in>fset A \<Longrightarrow> f a=g a"
  shows "finite_collection_presentation f A=finite_collection_presentation g A"
proof -
  have "fimage f A=fimage g A" by (rule fset.map_cong0) (rule same)
  then show ?thesis by (simp add: finite_collection_presentation_def)
qed

lemma finite_collection_presentation_image:
  "finite_collection_presentation f (fimage g A)=finite_collection_presentation (f \<circ> g) A"
  by (simp add: finite_collection_presentation_def fset.map_comp)

context presented_terms
begin

lemma presented_data_list_decode:
  "set ts\<subseteq>D \<Longrightarrow> presented_data_list P ts\<in>D \<and>
    presented_decode P (presented_data_list P ts)=finite_data_list (map (presented_decode P) ts)"
  by (induct ts) (simp_all add: payload pair)

lemma presented_pair_value_decode:
  "f (fst z)\<in>D \<Longrightarrow> g (snd z)\<in>D \<Longrightarrow> presented_pair_value P f g z\<in>D \<and>
    presented_decode P (presented_pair_value P f g z)=finite_pair_presentation (presented_decode P \<circ> f) (presented_decode P \<circ> g) z"
  by (simp add: presented_pair_value_def finite_pair_presentation_def pair)

lemma presented_sequence_decode:
  "(\<forall>a\<in>set xs. f a\<in>D) \<Longrightarrow> presented_sequence P f xs\<in>D \<and>
    presented_decode P (presented_sequence P f xs)=finite_sequence_presentation (presented_decode P \<circ> f) xs"
  using presented_data_list_decode[of "map f xs"]
  by (auto simp: presented_sequence_def finite_sequence_presentation_def)

lemma presented_option_decode:
  "(\<And>a. x=Some a \<Longrightarrow> f a\<in>D) \<Longrightarrow> presented_option P f x\<in>D \<and>
    presented_decode P (presented_option P f x)=finite_option_presentation (presented_decode P \<circ> f) x"
  by (cases x) (simp_all add: presented_option_def presented_sequence_def payload pair)

theorem presented_collection_decode:
  assumes members: "\<forall>a\<in>fset A. f a\<in>D"
  shows "presented_collection P f A\<in>D \<and>
    presented_decode P (presented_collection P f A)=finite_collection_presentation (presented_decode P \<circ> f) A"
proof -
  have B: "fset (fimage f A)\<subseteq>D" using members by (auto simp: fimage.rep_eq)
  have listed: "set (presented_listing P (fimage f A))\<subseteq>D" using presented_listing_exact(1)[OF B] B by simp
  have "map (presented_decode P) (presented_listing P (fimage f A))=
      map unordered_factor_term (map (\<lambda>x. Ordered_Factor_Term (presented_decode P x)) (presented_listing P (fimage f A)))"
    by (simp add: comp_def)
  also have "\<dots>=map unordered_factor_term
      (sorted_list_of_fset (fimage (\<lambda>x. Ordered_Factor_Term (presented_decode P x)) (fimage f A)))"
    by (simp only: presented_listing_exact(2)[OF B])
  also have "\<dots>=ordered_finite_terms (fimage (presented_decode P \<circ> f) A)"
    by (simp add: ordered_finite_terms_def fset.map_comp comp_def)
  finally have order: "map (presented_decode P) (presented_listing P (fimage f A))=
    ordered_finite_terms (fimage (presented_decode P \<circ> f) A)" .
  show ?thesis
    using presented_data_list_decode[OF listed] order
    by (simp add: presented_collection_def finite_collection_presentation_def)
qed

lemma presented_natural_decode:
  "presented_natural P n\<in>D \<and> presented_decode P (presented_natural P n)=finite_natural_data n"
  by (induct n) (simp_all add: payload pair)

lemma presented_boolean_decode:
  "presented_boolean P b\<in>D \<and> presented_decode P (presented_boolean P b)=finite_boolean_data b"
  by (simp add: presented_boolean_def finite_boolean_data_def presented_natural_decode)

end

subsection \<open>Generations, snapshots, observations and transaction results\<close>

text \<open>
  A generation presents its locus, the collection of its predecessors' presentations, its payload and its
  cause, each target through the supplied target presenter, as @{const finite_generation_value} does. A
  transaction result is held as what it holds: an applied snapshot or a conflict's observation, the
  plain result read into that form by @{text finite_transaction_result_held}.
\<close>

primrec presented_generation_value ::
  "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> 't generation_structure \<Rightarrow> 'p" where
  "presented_generation_value P f (Generation l Q p c)=presented_pair P (f l)
    (presented_pair P (presented_collection P id (fimage (presented_generation_value P f) Q))
      (presented_pair P (f p) (f c)))"

definition presented_snapshot_value :: "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> 't generation_structure fset \<Rightarrow> 'p" where
  "presented_snapshot_value P f=presented_collection P (presented_generation_value P f)"

definition presented_observation_value ::
  "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> ('t\<times>'t generation_structure option) fset \<Rightarrow> 'p" where
  "presented_observation_value P f=
    presented_collection P (presented_pair_value P f (presented_option P (presented_generation_value P f)))"

type_synonym 't held_transaction_result =
  "'t generation_structure fset + ('t\<times>'t generation_structure option) fset"

fun presented_result_value :: "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> 't held_transaction_result \<Rightarrow> 'p" where
  "presented_result_value P f (Inl S)=presented_pair P (presented_payload P [0]) (presented_snapshot_value P f S)"
| "presented_result_value P f (Inr C)=presented_pair P (presented_payload P [1]) (presented_observation_value P f C)"

fun finite_transaction_result_held :: "finite_transaction_result \<Rightarrow> finite_exact_target held_transaction_result" where
  "finite_transaction_result_held (Finite_Applied U)=Inl U"
| "finite_transaction_result_held (Finite_Conflict C)=Inr C"

definition snapshot_targets :: "'t generation_structure fset \<Rightarrow> 't set" where
  "snapshot_targets S=(\<Union>G\<in>fset S. set_generation_structure G)"

definition observation_targets :: "('t\<times>'t generation_structure option) fset \<Rightarrow> 't set" where
  "observation_targets C=(\<Union>z\<in>fset C. insert (fst z) (\<Union>H\<in>set_option (snd z). set_generation_structure H))"

fun held_result_targets :: "'t held_transaction_result \<Rightarrow> 't set" where
  "held_result_targets (Inl S)=snapshot_targets S"
| "held_result_targets (Inr C)=observation_targets C"

definition presented_targets ::
  "'p term_presentation \<Rightarrow> 'p set \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> ('t \<Rightarrow> finite_exact_target) \<Rightarrow> 't set \<Rightarrow> bool" where
  "presented_targets P D f t A \<longleftrightarrow> (\<forall>a\<in>A. f a\<in>D \<and> presented_decode P (f a)=Finite_Target (t a))"

lemma finite_generation_value_mapped:
  "(\<forall>a\<in>set_generation_structure G. g a=Finite_Target (t a)) \<Longrightarrow>
    finite_generation_value g G=finite_target_generation_value (map_generation_structure t G)"
proof (induct G)
  case (Generation l Q p c)
  have "fimage (finite_generation_value g) Q=fimage finite_target_generation_value (fimage (map_generation_structure t) Q)"
    unfolding fset.map_comp
  proof (rule fset.map_cong0)
    fix z assume z: "z\<in>fset Q"
    have "\<forall>a\<in>set_generation_structure z. g a=Finite_Target (t a)" using Generation.prems z by auto
    then show "finite_generation_value g z=(finite_target_generation_value \<circ> map_generation_structure t) z"
      using Generation.hyps[OF z] by simp
  qed
  then show ?case using Generation.prems by (simp add: finite_target_generation_value_def)
qed

context presented_terms
begin

theorem presented_generation_value_decode:
  "(\<forall>a\<in>set_generation_structure G. f a\<in>D) \<Longrightarrow> presented_generation_value P f G\<in>D \<and>
    presented_decode P (presented_generation_value P f G)=finite_generation_value (presented_decode P \<circ> f) G"
proof (induct G)
  case (Generation l Q p c)
  have fields: "f l\<in>D" "f p\<in>D" "f c\<in>D" using Generation.prems by simp_all
  have preds: "presented_generation_value P f H\<in>D \<and>
      presented_decode P (presented_generation_value P f H)=finite_generation_value (presented_decode P \<circ> f) H"
    if H: "H\<in>fset Q" for H
  proof -
    have "\<forall>a\<in>set_generation_structure H. f a\<in>D" using Generation.prems H by auto
    then show ?thesis by (rule Generation.hyps[OF H])
  qed
  have members: "\<forall>x\<in>fset (fimage (presented_generation_value P f) Q). id x\<in>D"
    using preds by (auto simp: fimage.rep_eq)
  note coll=presented_collection_decode[of "fimage (presented_generation_value P f) Q" id, OF members]
  have "presented_decode P (presented_collection P id (fimage (presented_generation_value P f) Q))=
      finite_collection_presentation ((presented_decode P \<circ> id) \<circ> presented_generation_value P f) Q"
    using coll by (simp only: finite_collection_presentation_image)
  also have "\<dots>=finite_collection_presentation (finite_generation_value (presented_decode P \<circ> f)) Q"
    by (rule finite_collection_presentation_cong) (simp add: preds)
  also have "\<dots>=finite_collection_presentation id (fimage (finite_generation_value (presented_decode P \<circ> f)) Q)"
    by (simp only: finite_collection_presentation_image id_comp)
  finally have cdec: "presented_decode P (presented_collection P id (fimage (presented_generation_value P f) Q))=
    finite_collection_presentation id (fimage (finite_generation_value (presented_decode P \<circ> f)) Q)" .
  have inD: "presented_pair P (f p) (f c)\<in>D" "presented_collection P id (fimage (presented_generation_value P f) Q)\<in>D"
    using fields coll by (simp_all add: pair)
  show ?case
    by (simp only: presented_generation_value.simps finite_generation_value.simps pair inD fields cdec comp_apply
      simp_thms comp_def)
qed

corollary presented_generation_value_targets:
  assumes targets: "presented_targets P D f t (set_generation_structure G)"
  shows "presented_generation_value P f G\<in>D \<and>
    presented_decode P (presented_generation_value P f G)=finite_target_generation_value (map_generation_structure t G)"
proof -
  have "\<forall>a\<in>set_generation_structure G. f a\<in>D" using targets by (simp add: presented_targets_def)
  note gen=presented_generation_value_decode[OF this]
  have mapped: "finite_generation_value (presented_decode P \<circ> f) G=finite_target_generation_value (map_generation_structure t G)"
    by (rule finite_generation_value_mapped) (use targets in \<open>simp add: presented_targets_def\<close>)
  show ?thesis using gen mapped by simp
qed

theorem presented_snapshot_value_decode:
  assumes targets: "presented_targets P D f t (snapshot_targets S)"
  shows "presented_snapshot_value P f S\<in>D \<and>
    presented_decode P (presented_snapshot_value P f S)=finite_snapshot_value (fimage (map_generation_structure t) S)"
proof -
  have each: "presented_generation_value P f G\<in>D \<and>
      presented_decode P (presented_generation_value P f G)=finite_target_generation_value (map_generation_structure t G)"
    if G: "G\<in>fset S" for G
    using targets G by (intro presented_generation_value_targets) (auto simp: presented_targets_def snapshot_targets_def)
  have members: "\<forall>G\<in>fset S. presented_generation_value P f G\<in>D" using each by blast
  note coll=presented_collection_decode[OF members]
  have "finite_collection_presentation (presented_decode P \<circ> presented_generation_value P f) S=
      finite_collection_presentation (finite_target_generation_value \<circ> map_generation_structure t) S"
    by (rule finite_collection_presentation_cong) (simp add: each)
  then show ?thesis
    using coll by (simp add: presented_snapshot_value_def finite_snapshot_value_def finite_collection_presentation_image)
qed

theorem presented_observation_value_decode:
  assumes targets: "presented_targets P D f t (observation_targets C)"
  shows "presented_observation_value P f C\<in>D \<and>
    presented_decode P (presented_observation_value P f C)=
      finite_collection_presentation (finite_pair_presentation Finite_Target
        (finite_option_presentation finite_target_generation_value))
        (fimage (map_prod t (map_option (map_generation_structure t))) C)"
proof -
  let ?e="presented_pair_value P f (presented_option P (presented_generation_value P f))"
  let ?q="finite_pair_presentation Finite_Target (finite_option_presentation finite_target_generation_value)"
  have each: "?e z\<in>D \<and> presented_decode P (?e z)=?q (map_prod t (map_option (map_generation_structure t)) z)"
    if z: "z\<in>fset C" for z
  proof -
    obtain a G where za: "z=(a,G)" by (cases z)
    have a: "f a\<in>D" "presented_decode P (f a)=Finite_Target (t a)"
      using targets z by (auto simp: presented_targets_def observation_targets_def za)
    have gen: "presented_generation_value P f H\<in>D \<and>
        presented_decode P (presented_generation_value P f H)=finite_target_generation_value (map_generation_structure t H)"
      if "G=Some H" for H
      using targets z that by (intro presented_generation_value_targets)
        (auto simp: presented_targets_def observation_targets_def za)
    have opt: "presented_option P (presented_generation_value P f) G\<in>D \<and>
        presented_decode P (presented_option P (presented_generation_value P f) G)=
          finite_option_presentation finite_target_generation_value (map_option (map_generation_structure t) G)"
      using gen by (cases G) (simp_all add: presented_option_def presented_sequence_def payload pair)
    show ?thesis
      using a opt by (simp add: za presented_pair_value_def finite_pair_presentation_def pair)
  qed
  have members: "\<forall>z\<in>fset C. ?e z\<in>D" using each by blast
  note coll=presented_collection_decode[OF members]
  have "finite_collection_presentation (presented_decode P \<circ> ?e) C=
      finite_collection_presentation (?q \<circ> map_prod t (map_option (map_generation_structure t))) C"
    by (rule finite_collection_presentation_cong) (simp add: each)
  then show ?thesis
    using coll by (simp add: presented_observation_value_def finite_collection_presentation_image)
qed

end

subsection \<open>At the plain presentation each presenter is the existing one\<close>

lemma presented_data_list_plain: "presented_data_list plain_term_presentation ts=finite_data_list ts"
  by (induct ts) simp_all

lemma presented_pair_value_plain: "presented_pair_value plain_term_presentation=finite_pair_presentation"
  by (simp add: fun_eq_iff presented_pair_value_def finite_pair_presentation_def)

lemma presented_sequence_plain: "presented_sequence plain_term_presentation=finite_sequence_presentation"
  by (simp add: fun_eq_iff presented_sequence_def finite_sequence_presentation_def presented_data_list_plain)

lemma presented_option_plain: "presented_option plain_term_presentation=finite_option_presentation"
  by (simp add: fun_eq_iff presented_option_def finite_option_presentation_def presented_sequence_plain)

lemma presented_collection_plain: "presented_collection plain_term_presentation=finite_collection_presentation"
proof (intro ext)
  fix f A
  show "presented_collection plain_term_presentation f A=finite_collection_presentation f A"
    using plain_terms.presented_collection_decode[of A f] by simp
qed

lemma presented_natural_plain: "presented_natural plain_term_presentation=finite_natural_data"
proof
  fix n
  show "presented_natural plain_term_presentation n=finite_natural_data n"
    using plain_terms.presented_natural_decode[of n] by simp
qed

lemma presented_boolean_plain: "presented_boolean plain_term_presentation=finite_boolean_data"
proof
  fix b
  show "presented_boolean plain_term_presentation b=finite_boolean_data b"
    using plain_terms.presented_boolean_decode[of b] by simp
qed

lemma presented_generation_value_plain:
  "presented_generation_value plain_term_presentation Finite_Target=finite_target_generation_value"
proof
  fix G
  show "presented_generation_value plain_term_presentation Finite_Target G=finite_target_generation_value G"
    using plain_terms.presented_generation_value_decode[of G Finite_Target]
    by (simp add: finite_target_generation_value_def)
qed

lemma presented_snapshot_value_plain:
  "presented_snapshot_value plain_term_presentation Finite_Target=finite_snapshot_value"
  by (simp add: fun_eq_iff presented_snapshot_value_def finite_snapshot_value_def presented_collection_plain
    presented_generation_value_plain)

lemma presented_observation_value_plain:
  "presented_observation_value plain_term_presentation Finite_Target=
    finite_collection_presentation (finite_pair_presentation Finite_Target
      (finite_option_presentation finite_target_generation_value))"
  by (simp add: presented_observation_value_def presented_collection_plain presented_pair_value_plain
    presented_option_plain presented_generation_value_plain)

lemma presented_result_value_plain:
  "presented_result_value plain_term_presentation Finite_Target (finite_transaction_result_held r)=
    finite_transaction_result_value r"
  by (cases r) (simp_all add: presented_snapshot_value_plain presented_observation_value_plain)

context presented_terms
begin

theorem presented_result_value_decode:
  assumes targets: "presented_targets P D f t (held_result_targets r)"
  shows "presented_result_value P f r\<in>D \<and>
    presented_decode P (presented_result_value P f r)=presented_result_value plain_term_presentation Finite_Target
      (map_sum (fimage (map_generation_structure t)) (fimage (map_prod t (map_option (map_generation_structure t)))) r)"
proof (cases r)
  case (Inl S)
  then show ?thesis
    using presented_snapshot_value_decode[of f t S] targets
    by (simp add: payload pair presented_snapshot_value_plain)
next
  case (Inr C)
  then show ?thesis
    using presented_observation_value_decode[of f t C] targets
    by (simp add: payload pair presented_observation_value_plain)
qed

end

subsection \<open>The domain at a formed table\<close>

text \<open>
  The presentation of a formed table meets the obligations over its canonical shared terms
  (@{thm [source] shared_presentation_terms}); every law above holds there. Nothing is stated of
  references or tables beyond this.
\<close>

lemma table_presentation_terms:
  "table_formed T \<Longrightarrow> presented_terms (table_presentation T) {s. shared_canonical T s}"
  unfolding table_presentation_def by (rule shared_presentation_terms)

export_code presented_compare presented_listing presented_data_list presented_pair_value presented_sequence
  presented_option presented_collection presented_natural presented_boolean presented_generation_value
  presented_snapshot_value presented_observation_value presented_result_value finite_transaction_result_held
  checking SML

end
