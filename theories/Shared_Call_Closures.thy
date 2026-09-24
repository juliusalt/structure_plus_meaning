theory Shared_Call_Closures
  imports Formed_Call_Closures Presented_Program_Applications Shared_Term_Tables
begin

section \<open>The demand of an evaluation is read over the shared subterms of its requests\<close>

text \<open>
  DECISIONS.md, "An evaluation's calls are built over the shared subterms of its requests", B4. The
  closure of a demand at the call key compares its calls as whole terms, and calls that carry one large
  subterm of the requests compare it whole at every insertion and lookup. Here the table of the
  requests' distinct subterms (@{text Shared_Term_Tables}) is built once, after the program and the
  requests are checked formed (@{thm [source] native_call_closure_code}); the requests become references
  into it, every application is built over that one table by @{text Presented_Program_Applications}, so
  every call held is canonical over it, and the calls are keyed by their site and shared term, the
  identity their left inverse (@{thm [source] shared_call_demanded_sites}): what two calls share is one
  reference, compared in one step. The demand is decoded once, where it leaves. Its result is exactly
  the demand at the call key (@{text shared_call_closure_exact}), and the closure's code equation reads
  it (@{text native_call_closure_shared_code}).
\<close>

subsection \<open>A formed table presents its canonical shared terms\<close>

text \<open>
  The presentation reads a table through a positional read, a shape search and a decoding of references,
  so that an evaluation supplies each as an index of its own; at the table's own reads it meets the
  obligations of a presentation over the canonical shared terms, each discharged from the table's
  contract.
\<close>

fun leaf_view where
  "leaf_view (Payload_Leaf v)=View_Payload v"
| "leaf_view (Target_Leaf a)=View_Target a"

lemma leaf_view_term: "finite_term_view (leaf_term l)=leaf_view l"
  by (cases l) simp_all

lemma leaf_view_map: "map_term_view f (leaf_view l)=leaf_view l"
  by (cases l) simp_all

lemma leaf_view_not_pair: "leaf_view l\<noteq>View_Pair a b"
  by (cases l) simp_all

fun shared_view_at where
  "shared_view_at rd (Shared_Reference i)=(case rd i of None \<Rightarrow> View_Payload []
    | Some (Leaf_Shape l) \<Rightarrow> leaf_view l
    | Some (Pair_Shape j k) \<Rightarrow> View_Pair (Shared_Reference j) (Shared_Reference k))"
| "shared_view_at rd (Shared_Leaf l)=leaf_view l"
| "shared_view_at rd (Shared_Pair a b)=View_Pair a b"

fun shared_decode_at :: "(nat \<Rightarrow> finite_factor_term option) \<Rightarrow> shared_term \<Rightarrow> finite_factor_term option" where
  "shared_decode_at dec (Shared_Reference i)=dec i"
| "shared_decode_at dec (Shared_Leaf l)=Some (leaf_term l)"
| "shared_decode_at dec (Shared_Pair a b)=pair_decoded (shared_decode_at dec a) (shared_decode_at dec b)"

lemma shared_view_at_read:
  "shared_view_at (value_reference_read T) s=(case shared_view T s of None \<Rightarrow> View_Payload []
    | Some (Leaf_View l) \<Rightarrow> leaf_view l | Some (Pair_View a b) \<Rightarrow> View_Pair a b)"
  by (cases s) (simp_all split: option.split shape.split)

lemma shared_decode_at_reference [simp]: "shared_decode_at (reference_term T) s=shared_decode T s"
  by (induction s) simp_all

definition shared_presentation :: "(nat \<Rightarrow> shape option) \<Rightarrow> (shape \<Rightarrow> nat option) \<Rightarrow>
    (nat \<Rightarrow> finite_factor_term option) \<Rightarrow> shared_term term_presentation" where
  "shared_presentation rd look dec=\<lparr>presented_view=shared_view_at rd,
    presented_target=\<lambda>a. shared_leaf look (Target_Leaf a), presented_payload=\<lambda>v. shared_leaf look (Payload_Leaf v),
    presented_pair=shared_pair look,
    presented_decode=\<lambda>s. case shared_decode_at dec s of Some t \<Rightarrow> t | None \<Rightarrow> Finite_Payload []\<rparr>"

lemma shared_presentation_fields [simp]:
  "presented_view (shared_presentation rd look dec)=shared_view_at rd"
  "presented_target (shared_presentation rd look dec)=(\<lambda>a. shared_leaf look (Target_Leaf a))"
  "presented_payload (shared_presentation rd look dec)=(\<lambda>v. shared_leaf look (Payload_Leaf v))"
  "presented_pair (shared_presentation rd look dec)=shared_pair look"
  "presented_decode (shared_presentation rd look dec)=
    (\<lambda>s. case shared_decode_at dec s of Some t \<Rightarrow> t | None \<Rightarrow> Finite_Payload [])"
  by (simp_all add: shared_presentation_def)

theorem shared_presentation_terms:
  assumes formed: "table_formed T"
  shows "presented_terms (shared_presentation (value_reference_read T) (table_find T) (reference_term T))
    {s. shared_canonical T s}"
proof -
  have decodes: "\<exists>t. shared_decode T s=Some t" if "shared_canonical T s" for s
    by (rule canonical_decodes[OF formed that])
  show ?thesis
    apply unfold_locales
    subgoal premises prems for x y
    proof -
      have cx: "shared_canonical T x" and cy: "shared_canonical T y" using prems by simp_all
      obtain u v where u: "shared_decode T x=Some u" and v: "shared_decode T y=Some v"
        using decodes[OF cx] decodes[OF cy] by blast
      have "u=v" using prems(3) u v by simp
      then show ?thesis using shared_canonical_equality[OF formed cx cy] u v by simp
    qed
    subgoal for a using shared_leaf_exact[OF formed, of "Target_Leaf a"] by simp
    subgoal for a using shared_leaf_exact[OF formed, of "Target_Leaf a"] by simp
    subgoal for v using shared_leaf_exact[OF formed, of "Payload_Leaf v"] by simp
    subgoal for v using shared_leaf_exact[OF formed, of "Payload_Leaf v"] by simp
    subgoal for x y using shared_pair_exact[OF formed, of x y] by simp
    subgoal premises prems for x y
    proof -
      have cx: "shared_canonical T x" and cy: "shared_canonical T y" using prems by simp_all
      obtain u v where u: "shared_decode T x=Some u" and v: "shared_decode T y=Some v"
        using decodes[OF cx] decodes[OF cy] by blast
      show ?thesis using shared_pair_exact[OF formed cx cy] u v by (simp add: pair_decoded_def)
    qed
    subgoal premises prems for x a b
    proof -
      have cx: "shared_canonical T x" using prems(1) by simp
      have "shared_view T x=Some (Pair_View a b)"
        using prems(2) by (auto simp: shared_view_at_read leaf_view_not_pair
          split: option.splits Shared_Term_Tables.term_view.splits)
      then show ?thesis using shared_view_canonical[OF formed cx] by simp
    qed
    subgoal premises prems for x
    proof -
      have cx: "shared_canonical T x" using prems by simp
      obtain t where t: "shared_decode T x=Some t" using decodes[OF cx] by blast
      from shared_view_decode[OF t] show ?thesis
      proof
        assume "\<exists>l. shared_view T x=Some (Leaf_View l) \<and> t=leaf_term l"
        then obtain l where "shared_view T x=Some (Leaf_View l)" "t=leaf_term l" by blast
        then show ?thesis using t by (simp add: shared_view_at_read leaf_view_map leaf_view_term)
      next
        assume "\<exists>a b u v. shared_view T x=Some (Pair_View a b) \<and> shared_decode T a=Some u \<and>
          shared_decode T b=Some v \<and> t=Finite_Pair u v"
        then obtain a b u v where "shared_view T x=Some (Pair_View a b)" "shared_decode T a=Some u"
          "shared_decode T b=Some v" "t=Finite_Pair u v" by blast
        then show ?thesis using t by (simp add: shared_view_at_read)
      qed
    qed
    done
qed

subsection \<open>A table is read by position through a tree, and decoded once\<close>

text \<open>
  A reference is read at its position in the table, and the view of a reference reads it at every fit;
  the positions are the rows of an ordered tree, so a read is a lookup. The table is decoded once, each
  entry from the entries of its components, which stand before it: a decoded shared term is built from
  those entries and never walks the table again. Both trees are read through the index notion's
  instance at the red-black tree (@{text Tree_Map_Indexes}): the positions by its search of a formed
  carrier (@{text tree_map_index.query_search}), the decoded entries by its update law
  (@{text tree_map_updates.updated}).
\<close>

definition table_positions :: "shape list \<Rightarrow> (nat,shape) rbt" where
  "table_positions T=RBT.bulkload (zip [0..<length T] T)"

lemma table_positions_lookup: "RBT.lookup (table_positions T)=value_reference_read T"
proof
  fix i
  have formed: "distinct (map fst (zip [0..<length T] T))" by (simp add: map_fst_zip)
  have found: "RBT.lookup (table_positions T) i=Some v \<longleftrightarrow> value_reference_read T i=Some v" for v
  proof -
    have "RBT.lookup (table_positions T) i=Some v \<longleftrightarrow> (i,v)\<in>set (zip [0..<length T] T)"
      unfolding table_positions_def using tree_map_index.query_search[OF formed, of i v] by simp
    also have "\<dots> \<longleftrightarrow> i<length T \<and> T!i=v" by (auto simp: set_zip intro!: exI[where x=i])
    also have "\<dots> \<longleftrightarrow> value_reference_read T i=Some v" by (simp only: read_some)
    finally show ?thesis .
  qed
  show "RBT.lookup (table_positions T) i=value_reference_read T i"
    using found by (metis option.exhaust)
qed

fun decoded_step :: "nat\<times>shape \<Rightarrow> (nat,finite_factor_term) rbt \<Rightarrow> (nat,finite_factor_term) rbt" where
  "decoded_step (i,Leaf_Shape l) M=RBT.insert i (leaf_term l) M"
| "decoded_step (i,Pair_Shape j k) M=(case RBT.lookup M j of None \<Rightarrow> M
    | Some a \<Rightarrow> (case RBT.lookup M k of None \<Rightarrow> M | Some b \<Rightarrow> RBT.insert i (Finite_Pair a b) M))"

definition decoded_positions :: "shape list \<Rightarrow> (nat,finite_factor_term) rbt" where
  "decoded_positions T=fold decoded_step (zip [0..<length T] T) RBT.empty"

lemma decoded_prefix:
  assumes formed: "table_formed T" and bound: "n\<le>length T"
  shows "RBT.lookup (fold decoded_step (zip [0..<n] (take n T)) RBT.empty) i=
    (if i<n then reference_term T i else None)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?M="fold decoded_step (zip [0..<n] (take n T)) RBT.empty"
  have n: "n<length T" using Suc.prems by simp
  have before: "RBT.lookup ?M i=(if i<n then reference_term T i else None)" for i
    using Suc.IH n by simp
  have step: "fold decoded_step (zip [0..<Suc n] (take (Suc n) T)) RBT.empty=decoded_step (n,T!n) ?M"
    using n by (simp add: take_Suc_conv_app_nth)
  have read: "value_reference_read T n=Some (T!n)" using read_some[of T n "T!n"] n by simp
  show ?case
  proof (cases "T!n")
    case (Leaf_Shape l)
    have leaf: "reference_term T n=Some (leaf_term l)" using reference_factor_leaf read Leaf_Shape by simp
    have found: "RBT.lookup (decoded_step (n,T!n) ?M) i=Some v \<longleftrightarrow>
        (if i<Suc n then reference_term T i else None)=Some v" for v
      using tree_map_updates.updated[where i="?M" and k=n and u="leaf_term l" and k'=i and v=v] before[of i] leaf
      by (auto simp del: RBT.lookup_insert simp: Leaf_Shape)
    show ?thesis unfolding step using found by (metis option.exhaust)
  next
    case (Pair_Shape j k)
    have jk: "j<n" "k<n" using formed read Pair_Shape by (auto simp: table_formed_def)
    obtain a where a: "reference_term T j=Some a" using table_formed_decodes[OF formed, of j] jk n by auto
    obtain b where b: "reference_term T k=Some b" using table_formed_decodes[OF formed, of k] jk n by auto
    have pair: "reference_term T n=Some (Finite_Pair a b)"
      using reference_term_pair[of T n j k] read Pair_Shape jk a b by (simp add: pair_decoded_def)
    have left: "RBT.lookup ?M j=Some a" and right: "RBT.lookup ?M k=Some b" using before[of j] before[of k] jk a b by simp_all
    have found: "RBT.lookup (decoded_step (n,T!n) ?M) i=Some v \<longleftrightarrow>
        (if i<Suc n then reference_term T i else None)=Some v" for v
      using tree_map_updates.updated[where i="?M" and k=n and u="Finite_Pair a b" and k'=i and v=v] before[of i]
        pair left right
      by (auto simp del: RBT.lookup_insert simp: Pair_Shape)
    show ?thesis unfolding step using found by (metis option.exhaust)
  qed
qed

lemma decoded_positions_lookup:
  assumes formed: "table_formed T"
  shows "RBT.lookup (decoded_positions T)=reference_term T"
proof
  fix i
  have "RBT.lookup (decoded_positions T) i=(if i<length T then reference_term T i else None)"
    using decoded_prefix[OF formed, of "length T" i] by (simp add: decoded_positions_def)
  then show "RBT.lookup (decoded_positions T) i=reference_term T i"
    by (cases "reference_term T i") (auto dest: reference_term_bound)
qed

subsection \<open>A traversal carried by an injective map\<close>

text \<open>
  A traversal of demanded sites whose reading and successors an injective map carries, on a set of
  sites closed under the successors, returns the image of the sites the original traversal returns.
\<close>

lemma finite_row_successors_union:
  "finite_row_successors read succ T=ffUnion (fimage (\<lambda>q. ffUnion (fimage succ (read q))) T)"
  by (rule fset_eqI) (auto simp: finite_row_successors_member ffUnion.rep_eq fimage.rep_eq)

theorem finite_demanded_sites_image:
  assumes injective: "inj_on h Q" and roots: "fset roots\<subseteq>Q"
    and closed: "\<And>q x e. q\<in>Q \<Longrightarrow> x |\<in>| read q \<Longrightarrow> e |\<in>| succ x \<Longrightarrow> e\<in>Q"
    and rows: "\<And>q. q\<in>Q \<Longrightarrow> ffUnion (fimage succ' (read' (h q)))=fimage h (ffUnion (fimage succ (read q)))"
  shows "finite_demanded_sites read' succ' (fimage h roots)=map_option (fimage h) (finite_demanded_sites read succ roots)"
proof -
  have successors_in: "fset (finite_row_successors read succ T)\<subseteq>Q" if T: "fset T\<subseteq>Q" for T
  proof
    fix e assume "e\<in>fset (finite_row_successors read succ T)"
    then obtain d x where "d |\<in>| T" "x |\<in>| read d" "e |\<in>| succ x" by (auto simp: finite_row_successors_member)
    then show "e\<in>Q" using T closed by blast
  qed
  have successors: "finite_row_successors read' succ' (fimage h T)=fimage h (finite_row_successors read succ T)"
    if T: "fset T\<subseteq>Q" for T
  proof -
    have "fimage (\<lambda>q. ffUnion (fimage succ' (read' (h q)))) T=fimage (\<lambda>q. fimage h (ffUnion (fimage succ (read q)))) T"
      by (rule fimage_cong[OF refl]) (use T rows in auto)
    then show ?thesis by (simp add: finite_row_successors_union fset.map_comp comp_def fimage_ffUnion_member)
  qed
  have difference: "fimage h (A |-| B)=fimage h A |-| fimage h B" if "fset A\<subseteq>Q" "fset B\<subseteq>Q" for A B
  proof -
    have "h ` (fset A-fset B)=h ` fset A-h ` fset B" using that by (intro inj_on_image_set_diff[OF injective]) auto
    then show ?thesis by (metis fimage.rep_eq minus_fset.rep_eq fset_inject)
  qed
  have commute: "map_option (map_prod (fimage h) (fimage h))
      (while_option (\<lambda>(S,T). T\<noteq>{||}) (finite_demanded_sites_step read succ) ({||},roots))=
    while_option (\<lambda>(S,T). T\<noteq>{||}) (finite_demanded_sites_step read' succ') (map_prod (fimage h) (fimage h) ({||},roots))"
    apply (rule while_option_commute_invariant[where P="\<lambda>(S,T). fset S\<subseteq>Q \<and> fset T\<subseteq>Q"])
    subgoal for s using successors_in
      by (cases s) (auto simp: finite_demanded_sites_step_def Let_def minus_fset.rep_eq sup_fset.rep_eq)
    subgoal for s by (cases s) simp
    subgoal premises prems for s
    proof -
      obtain S T where s: "s=(S,T)" by (cases s)
      have S: "fset S\<subseteq>Q" and T: "fset T\<subseteq>Q" using prems(1) by (simp_all add: s)
      have ST: "fset (S |\<union>| T)\<subseteq>Q" using S T by (simp add: sup_fset.rep_eq)
      show ?thesis
        by (simp add: s finite_demanded_sites_step_def Let_def successors[OF T]
          difference[OF successors_in[OF T] ST] fimage_funion)
    qed
    subgoal using roots by simp
    done
  have "finite_demanded_sites read' succ' (fimage h roots)=map_option fst (map_option (map_prod (fimage h) (fimage h))
      (while_option (\<lambda>(S,T). T\<noteq>{||}) (finite_demanded_sites_step read succ) ({||},roots)))"
    by (simp add: finite_demanded_sites_def commute)
  then show ?thesis by (simp add: finite_demanded_sites_def option.map_comp comp_def)
qed

subsection \<open>The demand over shared calls\<close>

lemma finite_application_premise_calls_decode:
  "finite_application_premise_calls (presented_application_decode P a)=
    fimage (map_prod id (presented_decode P)) (finite_application_premise_calls a)"
  by (cases a rule: prod_cases5)
    (simp only: presented_application_premise_calls_decode, simp add: finite_application_premise_calls_def)

text \<open>
  The requests are listed once through their keys, their terms shared into one table with its index of
  shapes, and each request becomes its site and its reference. The applications of a shared call are
  built by the canonical constructors over that table's index; the traversal keys a shared call by
  itself, and the demand it returns is decoded through the table decoded once.
\<close>

definition shared_call_closure ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset" where
  "shared_call_closure P R=(let rs=keyed_rows native_call_key native_call_unkey R in
    case keyed_shared_family (map snd rs) of (ns,T,M) \<Rightarrow>
    let S=shared_presentation (RBT.lookup (table_positions T)) (\<lambda>s. RBT.lookup M (shape_key s))
        (RBT.lookup (decoded_positions T));
      Q=prepare_program S P in
    case keyed_demanded_sites id id (\<lambda>q. presented_constructed_applications S Q (fst q) (snd q))
      finite_application_premise_calls (fset_of_list (zip (map fst rs) (map Shared_Reference ns))) of None \<Rightarrow> R
    | Some C \<Rightarrow> fimage (map_prod id (presented_decode S)) C)"

text \<open>
  The table of a family of requests is read through its positions, its index of shapes and its decoded
  entries, each built once as a tree; so read it is the presentation of that table, and the requests
  become canonical shared calls that decode to them (@{text shared_request_table_exact}). Every
  evaluation over the table of its requests starts from here.
\<close>

definition table_presentation :: "shape list \<Rightarrow> shared_term term_presentation" where
  "table_presentation T=shared_presentation (value_reference_read T) (table_find T) (reference_term T)"

definition shared_request_table ::
    "(local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>shared_term) fset\<times>shape list\<times>shared_term term_presentation" where
  "shared_request_table R=(let rs=keyed_rows native_call_key native_call_unkey R in
    case keyed_shared_family (map snd rs) of (ns,T,M) \<Rightarrow>
    (fset_of_list (zip (map fst rs) (map Shared_Reference ns)),T,
      shared_presentation (RBT.lookup (table_positions T)) (\<lambda>s. RBT.lookup M (shape_key s))
        (RBT.lookup (decoded_positions T))))"

theorem shared_request_table_exact:
  assumes table: "shared_request_table R=(C,T,S)"
  shows "table_formed T" "S=table_presentation T" "fset C\<subseteq>{q. shared_canonical T (snd q)}"
    "fimage (map_prod id (presented_decode S)) C=R"
proof -
  define rs where "rs=keyed_rows native_call_key native_call_unkey R"
  obtain ns T' M where family': "keyed_shared_family (map snd rs)=(ns,T',M)" using prod_cases3 by blast
  have T': "T'=T" using table by (simp add: shared_request_table_def Let_def rs_def[symmetric] family')
  have family: "keyed_shared_family (map snd rs)=(ns,T,M)" using family' by (simp only: T')
  have fields: "C=fset_of_list (zip (map fst rs) (map Shared_Reference ns))"
      "S=shared_presentation (RBT.lookup (table_positions T)) (\<lambda>s. RBT.lookup M (shape_key s))
        (RBT.lookup (decoded_positions T))"
    using table by (simp_all add: shared_request_table_def Let_def rs_def[symmetric] family)
  have shared: "share_terms (map snd rs) []=(ns,T)" using keyed_shared_family_exact[OF family] by simp
  have formed: "table_formed T" and decoded: "map (reference_term T) ns=map Some (map snd rs)"
    using share_terms_exact[OF table_formed_empty, of "map snd rs"] by (simp_all add: shared)
  show "table_formed T" by (rule formed)
  have presentation: "S=table_presentation T"
    unfolding fields(2) table_presentation_def
    by (simp only: table_positions_lookup decoded_positions_lookup[OF formed] keyed_shared_family_find[OF family])
  show "S=table_presentation T" by (rule presentation)
  have length: "length ns=length rs" using arg_cong[OF decoded, of length] by simp
  have reference: "reference_term T (ns!n)=Some (snd (rs!n))" if "n<length rs" for n
  proof -
    have "map (reference_term T) ns!n=map Some (map snd rs)!n" using decoded by simp
    then show ?thesis using that length by simp
  qed
  have bound: "i<length T" if "i\<in>set ns" for i
  proof -
    have "reference_term T i\<in>set (map (reference_term T) ns)" using that by simp
    then have "reference_term T i\<in>set (map Some (map snd rs))" by (simp only: decoded)
    then obtain u where "reference_term T i=Some u" by auto
    then show ?thesis by (rule reference_term_bound)
  qed
  show "fset C\<subseteq>{q. shared_canonical T (snd q)}"
  proof
    fix q assume "q\<in>fset C"
    then have "q\<in>set (zip (map fst rs) (map Shared_Reference ns))" by (simp add: fields(1) fset_of_list.rep_eq)
    then have "snd q\<in>set (map Shared_Reference ns)" by (metis set_zip_rightD prod.collapse)
    then show "q\<in>{q. shared_canonical T (snd q)}" using bound by auto
  qed
  have listed: "map (map_prod id (presented_decode S)) (zip (map fst rs) (map Shared_Reference ns))=rs"
  proof (rule nth_equalityI)
    show "length (map (map_prod id (presented_decode S)) (zip (map fst rs) (map Shared_Reference ns)))=length rs"
      using length by simp
  next
    fix n assume "n<length (map (map_prod id (presented_decode S)) (zip (map fst rs) (map Shared_Reference ns)))"
    then have n: "n<length rs" using length by simp
    show "map (map_prod id (presented_decode S)) (zip (map fst rs) (map Shared_Reference ns))!n=rs!n"
      using n length reference[OF n] by (simp add: presentation table_presentation_def)
  qed
  have "fimage (map_prod id (presented_decode S)) C=fset_of_list rs"
    using arg_cong[OF listed, of fset_of_list] by (simp add: fields(1))
  also have "fset_of_list rs=R" unfolding rs_def by (rule keyed_rows_fset) (rule native_call_inverse)
  finally show "fimage (map_prod id (presented_decode S)) C=R" .
qed

lemma shared_call_closure_table:
  "shared_call_closure P R=(case shared_request_table R of (C,T,S) \<Rightarrow>
    case keyed_demanded_sites id id (\<lambda>q. presented_constructed_applications S (prepare_program S P) (fst q) (snd q))
      finite_application_premise_calls C of None \<Rightarrow> R | Some D \<Rightarrow> fimage (map_prod id (presented_decode S)) D)"
  by (cases "keyed_shared_family (map snd (keyed_rows native_call_key native_call_unkey R))" rule: prod_cases3)
    (simp add: shared_call_closure_def shared_request_table_def Let_def)

theorem shared_call_closure_formed: "shared_call_closure P R=formed_call_closure P R"
proof -
  obtain roots T S where table: "shared_request_table R=(roots,T,S)" using prod_cases3 by blast
  note fields=shared_request_table_exact[OF table]
  interpret shared: presented_terms S "{s. shared_canonical T s}"
    unfolding fields(2) table_presentation_def by (rule shared_presentation_terms[OF fields(1)])
  define h where "h=map_prod (id::local_address option definition_site \<Rightarrow> _) (presented_decode S)"
  define Q where "Q={q::local_address option definition_site\<times>shared_term. shared_canonical T (snd q)}"
  define readS where "readS=(\<lambda>q::local_address option definition_site\<times>shared_term.
    presented_constructed_applications S (prepare_program S P) (fst q) (snd q))"
  have roots_in: "fset roots\<subseteq>Q" using fields(3) by (simp add: Q_def)
  have roots_image: "fimage h roots=R" using fields(4) by (simp add: h_def)
  have injective: "inj_on h Q"
  proof (rule inj_onI)
    fix p q assume p: "p\<in>Q" and q: "q\<in>Q" and same: "h p=h q"
    obtain a s where ps: "p=(a,s)" by (cases p)
    obtain b u where qs: "q=(b,u)" by (cases q)
    have ab: "a=b" and decoded_same: "presented_decode S s=presented_decode S u" using same by (simp_all add: h_def ps qs)
    have "s=u" by (rule shared.decides) (use p q decoded_same in \<open>simp_all add: Q_def ps qs\<close>)
    then show "p=q" by (simp add: ps qs ab)
  qed
  have closed: "e\<in>Q" if "q\<in>Q" "x |\<in>| readS q" "e |\<in>| finite_application_premise_calls x" for q x e
  proof -
    obtain d t where q: "q=(d,t)" by (cases q)
    obtain e' c y V H where x: "x=(e',c,y,V,H)" using prod_cases5 by blast
    have t: "t\<in>{s. shared_canonical T s}" using that(1) by (simp add: Q_def q)
    have member: "(e',c,y,V,H) |\<in>| presented_constructed_applications S (prepare_program S P) d t"
      using that(2) by (simp add: readS_def q x)
    have "\<forall>s e'' z. (s,e'',z) |\<in>| H \<longrightarrow> z\<in>{s. shared_canonical T s}"
      using shared.presented_constructed_application_domain[OF t member] by blast
    then show ?thesis using that(3) by (auto simp: x finite_application_premise_calls_def Q_def fimage.rep_eq)
  qed
  have rows: "ffUnion (fimage finite_application_premise_calls (finite_constructed_applications P (fst (h q)) (snd (h q))))=
      fimage h (ffUnion (fimage finite_application_premise_calls (readS q)))" if "q\<in>Q" for q
  proof -
    obtain d t where q: "q=(d,t)" by (cases q)
    have t: "t\<in>{s. shared_canonical T s}" using that by (simp add: Q_def q)
    have "finite_constructed_applications P d (presented_decode S t)=
        fimage (presented_application_decode S) (readS (d,t))"
      unfolding readS_def fst_conv snd_conv by (rule shared.presented_constructed_applications_decode[OF t, symmetric])
    then show ?thesis
      by (simp add: q h_def fimage_ffUnion_member fset.map_comp comp_def finite_application_premise_calls_decode)
  qed
  have unfolded: "shared_call_closure P R=(case keyed_demanded_sites id id readS finite_application_premise_calls roots of
      None \<Rightarrow> R | Some C \<Rightarrow> fimage h C)"
    unfolding h_def by (simp add: shared_call_closure_table table readS_def)
  have sites: "keyed_demanded_sites id id readS finite_application_premise_calls roots=
      finite_demanded_sites readS finite_application_premise_calls roots"
    by (rule shared_call_demanded_sites)
  have plain: "keyed_demanded_sites native_call_key native_call_unkey
      (\<lambda>q. finite_constructed_applications P (fst q) (snd q)) finite_application_premise_calls R=
    finite_demanded_sites (\<lambda>q. finite_constructed_applications P (fst q) (snd q)) finite_application_premise_calls R"
    by (rule keyed_demanded_sites_exact) (rule native_call_inverse)
  have image: "finite_demanded_sites (\<lambda>q. finite_constructed_applications P (fst q) (snd q))
      finite_application_premise_calls R=map_option (fimage h) (finite_demanded_sites readS finite_application_premise_calls roots)"
    using finite_demanded_sites_image[where read'="\<lambda>q. finite_constructed_applications P (fst q) (snd q)"
      and succ'=finite_application_premise_calls, OF injective roots_in closed rows] roots_image by simp
  show ?thesis
  proof (cases "finite_demanded_sites readS finite_application_premise_calls roots")
    case None
    then show ?thesis using image by (simp add: unfolded sites formed_call_closure_def plain)
  next
    case (Some C)
    then show ?thesis using image by (simp add: unfolded sites formed_call_closure_def plain)
  qed
qed

corollary shared_call_closure_exact:
  assumes system: "finite_system_formed P" and requests: "fBall R (\<lambda>q. finite_term_formed (snd q))"
  shows "shared_call_closure P R=finite_program_call_closure P R"
  by (simp add: shared_call_closure_formed keyed_call_closure_formed[OF system requests, symmetric]
    keyed_call_closure_exact[OF native_call_inverse])

text \<open>
  The closure at the call key checks the program and the requests at its entry, as before, and a formed
  closure is computed over shared calls; every result is the original closure's.
\<close>


lemma native_call_closure_shared_code [code]:
  "native_call_closure P R=(if finite_system_formed P \<and> fBall R (\<lambda>q. finite_term_formed (snd q))
    then shared_call_closure P R
    else (case keyed_demanded_sites native_call_key native_call_unkey (\<lambda>q. finite_program_applications P {|q|})
      finite_application_premise_calls R of None \<Rightarrow> R | Some S \<Rightarrow> S))"
  by (simp only: native_call_closure_code shared_call_closure_formed)

end
