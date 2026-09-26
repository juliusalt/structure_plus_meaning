theory Factor_Instantiation_Declarations
  imports Factor_Resolution_Carriers Factor_Application_Reading
begin

text \<open>
  The instantiation family's first part (R6c of DECISIONS.md "The native evaluator constructs the missing witnesses
  by resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", (a) and (b)):
  quotation admission (50), binding admission (52), pattern instantiation (55), scoped instantiation (56),
  prospective instantiation (57) and application reading (58) declared at their metadata views, each producer
  discharged at its notion's own system from its exact contract; the free sockets their clauses hold of one another,
  each discharged along the clause's carriers (@{text socket_discharged_carried}); the carriers 46 and 55 at its
  scope. Every view reads a call's shape and where its variables occur; no clause of any program changes, and the
  declarations are read by the committed search alone.
\<close>

section \<open>Bags and tuples of corresponding outputs\<close>

text \<open>
  The family's metadata outputs (tables, interiors, slots, used variables, scopes) are bags: two data lists
  correspond when they hold the same elements with the same multiplicities, every order admitted. A view whose output
  is a tuple of holes has the product of its holes' correspondences (@{text tuple_corresponds}), following
  @{const finite_pattern_tuple}.
\<close>

definition bag_corresponds :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "bag_corresponds x y \<longleftrightarrow> x = y \<or> (\<exists>xs ys. x = data_list_term xs \<and> y = data_list_term ys \<and> mset xs = mset ys)"

lemma bag_corresponds_refl [simp]: "bag_corresponds x x"
  by (simp add: bag_corresponds_def)

lemma bag_corresponds_lists:
  assumes "mset xs = mset ys"
  shows "bag_corresponds (data_list_term xs) (data_list_term ys)"
  unfolding bag_corresponds_def using assms by blast

lemma bag_corresponds_mapped:
  assumes "mset A = mset B"
  shows "bag_corresponds (data_list_term (map f A)) (data_list_term (map f B))"
  by (rule bag_corresponds_lists) (simp add: assms)

lemma bag_corresponds_distinct_payloads:
  assumes "distinct A" "distinct B" "set A = set B"
  shows "bag_corresponds (data_list_term (map Payload_Term A)) (data_list_term (map Payload_Term B))"
  by (rule bag_corresponds_mapped) (use assms set_eq_iff_mset_eq_distinct in blast)

lemma bag_comparison_corresponds:
  assumes "(6,Pair_Term x y) \<in> positive_meaning bag_comparison_system"
  shows "bag_corresponds x y"
proof -
  obtain xs ys where "x = data_list_term xs" "y = data_list_term ys" "mset xs = mset ys"
    using assms by (auto simp: bag_comparison_exact)
  then show ?thesis by (simp add: bag_corresponds_lists)
qed

fun tuple_corresponds :: "(factor_term \<Rightarrow> factor_term \<Rightarrow> bool) list \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "tuple_corresponds [] x y \<longleftrightarrow> x = y"
| "tuple_corresponds [c] x y \<longleftrightarrow> c x y"
| "tuple_corresponds (c#d#cs) x y \<longleftrightarrow>
    (\<exists>a b a' b'. x = Pair_Term a b \<and> y = Pair_Term a' b' \<and> c a a' \<and> tuple_corresponds (d#cs) b b')"

lemma tuple_corresponds_evaluate:
  assumes "length cs = length hs"
    and "\<forall>i<length hs. (cs ! i) (evaluate_pattern g (decode_finite_pattern (hs ! i)))
      (evaluate_pattern g' (decode_finite_pattern (hs ! i)))"
  shows "tuple_corresponds cs (evaluate_pattern g (decode_finite_pattern (finite_pattern_tuple hs)))
    (evaluate_pattern g' (decode_finite_pattern (finite_pattern_tuple hs)))"
  using assms
proof (induction hs arbitrary: cs rule: finite_pattern_tuple.induct)
  case 1
  then show ?case by simp
next
  case (2 p)
  then obtain c where "cs = [c]" by (cases cs) auto
  then show ?case using 2 by simp
next
  case (3 p q ps)
  obtain c d ds where cs: "cs = c#d#ds" using 3(2) by (metis length_Suc_conv)
  have tail: "tuple_corresponds (d#ds) (evaluate_pattern g (decode_finite_pattern (finite_pattern_tuple (q#ps))))
      (evaluate_pattern g' (decode_finite_pattern (finite_pattern_tuple (q#ps))))"
  proof (rule 3(1))
    show "length (d#ds) = length (q#ps)" using 3(2) cs by simp
    show "\<forall>i<length (q#ps). ((d#ds) ! i) (evaluate_pattern g (decode_finite_pattern ((q#ps) ! i)))
        (evaluate_pattern g' (decode_finite_pattern ((q#ps) ! i)))"
    proof (intro allI impI)
      fix i assume "i < length (q#ps)"
      then show "((d#ds) ! i) (evaluate_pattern g (decode_finite_pattern ((q#ps) ! i)))
          (evaluate_pattern g' (decode_finite_pattern ((q#ps) ! i)))"
        using 3(3)[rule_format, of "Suc i"] cs by simp
    qed
  qed
  have head: "c (evaluate_pattern g (decode_finite_pattern p)) (evaluate_pattern g' (decode_finite_pattern p))"
    using 3(3)[rule_format, of 0] cs by simp
  show ?case using head tail cs by simp
qed

section \<open>A view's answers read through valuations\<close>

text \<open>
  A formed view reads a term exactly when the term is a value of its pattern, its parts the same valuation's values
  of the input and output patterns; its holes are that valuation's values of the hole patterns. So a producer is
  discharged by relating any two valuations whose pattern values are answers and whose input values agree.
\<close>

theorem producer_discharged_valuations:
  assumes formed: "view_formed V"
    and answers: "\<And>g g' i. (d,evaluate_pattern g (decode_finite_pattern (fst V))) \<in> M \<Longrightarrow>
      (d,evaluate_pattern g' (decode_finite_pattern (fst V))) \<in> M \<Longrightarrow>
      evaluate_pattern g (decode_finite_pattern (fst (snd V))) = evaluate_pattern g' (decode_finite_pattern (fst (snd V))) \<Longrightarrow>
      i < length hs \<Longrightarrow>
      corr i (evaluate_pattern g (decode_finite_pattern (hs ! i))) (evaluate_pattern g' (decode_finite_pattern (hs ! i)))"
  shows "producer_discharged M d V hs corr"
  unfolding producer_discharged_def
proof (intro allI impI)
  fix a b u v v' w w' i
  assume inm: "(d,a) \<in> M" "(d,b) \<in> M"
    and va: "resolution_view_term V a = Some (u,v)" and vb: "resolution_view_term V b = Some (u,v')"
    and wa: "resolution_view_holes V hs a = Some w" and wb: "resolution_view_holes V hs b = Some w'"
    and i: "i < length hs"
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  have lin: "distinct (finite_pattern_occurrences p)" using formed V by (simp add: view_formed_def)
  obtain l where la: "view_match p a = Some l" and ua: "u = evaluate_pattern (view_valuation l) (decode_finite_pattern pi)"
    using va V by (auto simp: resolution_view_term_def split: option.splits)
  obtain l' where lb: "view_match p b = Some l'" and ub: "u = evaluate_pattern (view_valuation l') (decode_finite_pattern pi)"
    using vb V by (auto simp: resolution_view_term_def split: option.splits)
  have ea: "a = evaluate_pattern (view_valuation l) (decode_finite_pattern p)" using view_match_sound[OF lin la] by simp
  have eb: "b = evaluate_pattern (view_valuation l') (decode_finite_pattern p)" using view_match_sound[OF lin lb] by simp
  have w: "w = map (\<lambda>h. evaluate_pattern (view_valuation l) (decode_finite_pattern h)) hs"
    using wa la V by (simp add: resolution_view_holes_def)
  have w': "w' = map (\<lambda>h. evaluate_pattern (view_valuation l') (decode_finite_pattern h)) hs"
    using wb lb V by (simp add: resolution_view_holes_def)
  have "corr i (evaluate_pattern (view_valuation l) (decode_finite_pattern (hs ! i)))
      (evaluate_pattern (view_valuation l') (decode_finite_pattern (hs ! i)))"
    by (rule answers) (use inm ea eb ua ub i V in simp_all)
  then show "corr i (w ! i) (w' ! i)" using w w' i by simp
qed

text \<open>
  A view whose output is the tuple of its holes has, at its one whole output, the product of the holes'
  correspondences: the form a socket's producer takes (@{text socket_carried}).
\<close>

theorem producer_discharged_tuple:
  assumes discharged: "producer_discharged M d V hs corr" and holes: "view_holes V hs"
  shows "producer_discharged M d V [snd (snd V)] (\<lambda>_. tuple_corresponds (map corr [0..<length hs]))"
  unfolding producer_discharged_single
proof (intro allI impI)
  fix a b u v v'
  assume inm: "(d,a) \<in> M" "(d,b) \<in> M"
    and va: "resolution_view_term V a = Some (u,v)" and vb: "resolution_view_term V b = Some (u,v')"
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  obtain l where la: "view_match p a = Some l" and v: "v = evaluate_pattern (view_valuation l) (decode_finite_pattern po)"
    using va V by (auto simp: resolution_view_term_def split: option.splits)
  obtain l' where lb: "view_match p b = Some l'" and v': "v' = evaluate_pattern (view_valuation l') (decode_finite_pattern po)"
    using vb V by (auto simp: resolution_view_term_def split: option.splits)
  let ?w = "map (\<lambda>h. evaluate_pattern (view_valuation l) (decode_finite_pattern h)) hs"
  let ?w' = "map (\<lambda>h. evaluate_pattern (view_valuation l') (decode_finite_pattern h)) hs"
  have wa: "resolution_view_holes V hs a = Some ?w" using la V by (simp add: resolution_view_holes_def)
  have wb: "resolution_view_holes V hs b = Some ?w'" using lb V by (simp add: resolution_view_holes_def)
  have each: "\<forall>i<length hs. corr i (?w ! i) (?w' ! i)"
    using discharged inm va vb wa wb unfolding producer_discharged_def by blast
  have po: "po = finite_pattern_tuple hs" using holes V by (simp add: view_holes_def)
  have "tuple_corresponds (map corr [0..<length hs])
      (evaluate_pattern (view_valuation l) (decode_finite_pattern (finite_pattern_tuple hs)))
      (evaluate_pattern (view_valuation l') (decode_finite_pattern (finite_pattern_tuple hs)))"
    by (rule tuple_corresponds_evaluate) (use each in simp_all)
  then show "tuple_corresponds (map corr [0..<length (hs::nat finite_term_pattern list)]) v v'" using v v' po by simp
qed

section \<open>The correspondence at each hole\<close>

text \<open>
  A quoted or instantiated term and a callee site are determined by their inputs: their holes correspond by equality.
  Every other hole of the family is a bag.
\<close>

definition instantiation_correspondence :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "instantiation_correspondence d i =
    (if d \<in> {50,55,57,58} \<and> i = 0 then (=) else bag_corresponds)"

section \<open>The metadata views\<close>

text \<open>
  Quotation admission (50) at ((e,u),(r,(t,(i,k)))): the source environment, use and root in, the term, interior and
  slots out. Binding admission (52) at (v,b) is read at @{const view_swap}: the table in, its scope out.
  Pattern instantiation (55) at ((e,u),(r,((v,b),(t,(w,(i,k)))))): the source, root, scope and table in, the term,
  used variables, interior and slots out. Scoped instantiation (56) at ((e,u),(r,((b,t),(i,k)))): the source, root
  and term in, the table, interior and slots out. Prospective instantiation (57) at
  ((e,u),(r,((v,b),((d,t),(w,(i,k)))))): as 55, with the callee site beside the term. Application reading (58) at
  ((e,u),(r,((d,t),(i,k)))): the source and root in, the callee site, term, interior and slots out.
\<close>

definition quotation_view :: "nat resolution_view" where
  "quotation_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3)
        (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)))"

definition quotation_holes :: "nat finite_term_pattern list" where
  "quotation_holes = [Finite_Variable 3,Finite_Variable 4,Finite_Variable 5]"

definition binding_holes :: "nat finite_term_pattern list" where
  "binding_holes = [Finite_Variable 0]"

definition instantiation_view :: "nat resolution_view" where
  "instantiation_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6)
          (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 8)))))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6)
      (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 8))))"

definition instantiation_holes :: "nat finite_term_pattern list" where
  "instantiation_holes = [Finite_Variable 5,Finite_Variable 6,Finite_Variable 7,Finite_Variable 8]"

definition scoped_view :: "nat resolution_view" where
  "scoped_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4)),
    Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))"

definition scoped_holes :: "nat finite_term_pattern list" where
  "scoped_holes = [Finite_Variable 3,Finite_Variable 5,Finite_Variable 6]"

definition prospective_view :: "nat resolution_view" where
  "prospective_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))
          (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 9)))))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))
      (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 9))))"

definition prospective_holes :: "nat finite_term_pattern list" where
  "prospective_holes = [Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6),Finite_Variable 7,
    Finite_Variable 8,Finite_Variable 9]"

definition application_view :: "nat resolution_view" where
  "application_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
      (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))"

definition application_holes :: "nat finite_term_pattern list" where
  "application_holes = [Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4),Finite_Variable 5,Finite_Variable 6]"

lemma instantiation_views_formed:
  "view_formed quotation_view" "view_formed instantiation_view" "view_formed scoped_view"
  "view_formed prospective_view" "view_formed application_view"
  by (auto simp: view_formed_def quotation_view_def instantiation_view_def scoped_view_def prospective_view_def
    application_view_def fset_eq_iff)

lemma instantiation_views_holes:
  "view_holes quotation_view quotation_holes" "view_holes view_swap binding_holes"
  "view_holes instantiation_view instantiation_holes" "view_holes scoped_view scoped_holes"
  "view_holes prospective_view prospective_holes" "view_holes application_view application_holes"
  by (simp_all add: view_holes_def quotation_view_def quotation_holes_def view_swap_def swapped_view_def
    binding_holes_def instantiation_view_def instantiation_holes_def scoped_view_def scoped_holes_def
    prospective_view_def prospective_holes_def application_view_def application_holes_def)

section \<open>Two answers at one input, from each notion's contract\<close>

lemma quotation_answers:
  assumes first: "(50,term_quotation_argument e u r t i k) \<in> positive_meaning quotation_admission_system"
    and second: "(50,term_quotation_argument e u r t' i' k') \<in> positive_meaning quotation_admission_system"
  shows "t = t' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: quotation_admission_exact)
  have "t = t' \<and> (6,Pair_Term i i') \<in> positive_meaning bag_comparison_system \<and>
      (6,Pair_Term k k') \<in> positive_meaning bag_comparison_system"
    by (rule quotation_admission_result_unique[OF source first second])
  then show ?thesis using bag_comparison_corresponds by blast
qed

lemma binding_answers:
  assumes first: "(52,Pair_Term v b) \<in> positive_meaning binding_admission_system"
    and second: "(52,Pair_Term v' b) \<in> positive_meaning binding_admission_system"
  shows "bag_corresponds v v'"
proof -
  obtain Vs xs where left: "v = data_list_term (map Payload_Term Vs)" "b = binding_rows_term xs" "distinct Vs"
      "term_bindings_formed (set Vs) (set xs)"
    using first by (auto simp: binding_admission_exact)
  obtain Ws ys where right: "v' = data_list_term (map Payload_Term Ws)" "b = binding_rows_term ys" "distinct Ws"
      "term_bindings_formed (set Ws) (set ys)"
    using second by (auto simp: binding_admission_exact)
  have rows: "ys = xs" using left(2) right(2) binding_rows_term_injective by (metis injD)
  have "set Vs = set Ws" using left(4) right(4) rows by (simp add: term_bindings_formed_def)
  then show ?thesis using left(1,3) right(1,3) by (simp add: bag_corresponds_distinct_payloads)
qed

lemma instantiation_answers:
  assumes first: "(55,pattern_instantiation_argument e u v b r t w i k) \<in> positive_meaning pattern_instantiation_system"
    and second: "(55,pattern_instantiation_argument e u v b r t' w' i' k') \<in> positive_meaning pattern_instantiation_system"
  shows "t = t' \<and> bag_corresponds w w' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: pattern_instantiation_exact)
  obtain q Vs xs a Us Is Ks where parts: "u = use_data_term q" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = Payload_Term a" "w = data_list_term (map Payload_Term Us)"
      "i = data_list_term (map Payload_Term Is)" "k = data_list_term (map Payload_Term Ks)"
    using first by (auto simp: pattern_instantiation_at_source[OF source])
  obtain Us' Is' Ks' where parts': "w' = data_list_term (map Payload_Term Us')"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using second by (auto simp: pattern_instantiation_at_source[OF source])
  have f: "(55,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) t (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning pattern_instantiation_system"
    using first parts by simp
  have s: "(55,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) t' (data_list_term (map Payload_Term Us'))
      (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning pattern_instantiation_system"
    using second parts parts' by simp
  have "t = t' \<and> mset Us = mset Us' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule pattern_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_mapped)
qed

text \<open>
  A complete table of a pattern's own variables is determined by the pattern and its instance: every variable's value
  is the instance's subterm there.
\<close>

lemma pattern_instance_scope_unique:
  assumes formed: "term_bindings_formed (pattern_variables p) V" "term_bindings_formed (pattern_variables p) W"
    and instances: "pattern_instance V p t" "pattern_instance W p t"
  shows "V = W"
proof -
  have shared: "pattern_instance V p s \<Longrightarrow> pattern_instance W p s \<Longrightarrow> a \<in> pattern_variables p \<Longrightarrow>
      \<exists>x. (a,x) \<in> V \<and> (a,x) \<in> W" for a s
  proof (induction p arbitrary: s)
    case (Pattern_Pair p q)
    then obtain x y where "s = Pair_Term x y" "pattern_instance V p x" "pattern_instance V q y"
        "pattern_instance W p x" "pattern_instance W q y" by auto
    then show ?case using Pattern_Pair.IH Pattern_Pair.prems(3) by auto
  qed auto
  have fv: "single_valued V" "rel_dom V = pattern_variables p" and fw: "single_valued W" "rel_dom W = pattern_variables p"
    using formed by (auto simp: term_bindings_formed_def)
  have vw: "(a,x) \<in> W" if "(a,x) \<in> V" for a x
  proof -
    have "a \<in> pattern_variables p" using that fv(2) by (auto simp: rel_dom_def)
    then obtain y where "(a,y) \<in> V" "(a,y) \<in> W" using shared instances by blast
    then show ?thesis using that fv(1) by (auto simp: single_valued_def)
  qed
  have wv: "(a,x) \<in> V" if "(a,x) \<in> W" for a x
  proof -
    have "a \<in> pattern_variables p" using that fw(2) by (auto simp: rel_dom_def)
    then obtain y where "(a,y) \<in> V" "(a,y) \<in> W" using shared instances by blast
    then show ?thesis using that fw(1) by (auto simp: single_valued_def)
  qed
  show ?thesis using vw wv by (auto simp: set_eq_iff)
qed

lemma scoped_answers:
  assumes first: "(56,scoped_instantiation_argument e u r b t i k) \<in> positive_meaning scoped_instantiation_system"
    and second: "(56,scoped_instantiation_argument e u r b' t i' k') \<in> positive_meaning scoped_instantiation_system"
  shows "bag_corresponds b b' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: scoped_instantiation_exact)
  obtain v a xs p Is Ks where parts: "u = use_data_term v" "r = Payload_Term a" "b = binding_rows_term xs"
      "i = data_list_term (map Payload_Term Is)" "k = data_list_term (map Payload_Term Ks)"
      "distinct xs" "distinct Is" "distinct Ks" "scoped_pattern_at E v a p (set Is) (set Ks)"
      "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p t"
    using first by (auto simp: scoped_instantiation_at_source[OF source])
  obtain ys Js Ls where parts': "b' = binding_rows_term ys" "i' = data_list_term (map Payload_Term Js)"
      "k' = data_list_term (map Payload_Term Ls)"
    using second by (auto simp: scoped_instantiation_at_source[OF source])
  have s: "(56,scoped_instantiation_argument e (use_data_term v) (Payload_Term a) (binding_rows_term ys) t
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))
      \<in> positive_meaning scoped_instantiation_system"
    using second parts parts' by simp
  obtain p' where right: "distinct ys" "distinct Js" "distinct Ls" "scoped_pattern_at E v a p' (set Js) (set Ls)"
      "term_bindings_formed (pattern_variables p') (set ys)" "pattern_instance (set ys) p' t"
    using s by (simp only: scoped_instantiation_on_values[OF source]) blast
  have same: "p' = p" "set Js = set Is" "set Ls = set Ks" using scoped_pattern_unique[OF right(4) parts(9)] by auto
  have "set ys = set xs"
    by (rule pattern_instance_scope_unique) (use right(5,6) parts(10,11) same(1) in simp_all)
  then have "mset xs = mset ys" using parts(6) right(1) set_eq_iff_mset_eq_distinct by blast
  then show ?thesis using parts parts' right same
    by (simp add: bag_corresponds_mapped bag_corresponds_distinct_payloads)
qed

lemma prospective_answers:
  assumes first: "(57,prospective_instantiation_argument e u v b r d t w i k)
      \<in> positive_meaning prospective_instantiation_system"
    and second: "(57,prospective_instantiation_argument e u v b r d' t' w' i' k')
      \<in> positive_meaning prospective_instantiation_system"
  shows "d = d' \<and> t = t' \<and> bag_corresponds w w' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: prospective_instantiation_exact)
  obtain q Vs xs a du da Us Is Ks where parts: "u = use_data_term q" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = Payload_Term a" "d = site_data_term du da"
      "w = data_list_term (map Payload_Term Us)" "i = data_list_term (map Payload_Term Is)"
      "k = data_list_term (map Payload_Term Ks)"
    using first by (auto simp: prospective_instantiation_at_source[OF source])
  obtain eu ea Us' Is' Ks' where parts': "d' = site_data_term eu ea" "w' = data_list_term (map Payload_Term Us')"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using second by (auto simp: prospective_instantiation_at_source[OF source])
  have f: "(57,prospective_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) (site_data_term du da) t (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning prospective_instantiation_system"
    using first parts by simp
  have s: "(57,prospective_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) (site_data_term eu ea) t' (data_list_term (map Payload_Term Us'))
      (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning prospective_instantiation_system"
    using second parts parts' by simp
  have "du = eu \<and> da = ea \<and> t = t' \<and> mset Us = mset Us' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule prospective_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_mapped)
qed

lemma application_answers:
  assumes first: "(58,application_reading_argument e u r d t i k) \<in> positive_meaning application_reading_system"
    and second: "(58,application_reading_argument e u r d' t' i' k') \<in> positive_meaning application_reading_system"
  shows "d = d' \<and> t = t' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: application_reading_exact)
  obtain q a du da Is Ks where parts: "u = use_data_term q" "r = Payload_Term a" "d = site_data_term du da"
      "i = data_list_term (map Payload_Term Is)" "k = data_list_term (map Payload_Term Ks)"
    using first by (auto simp: application_reading_at_source[OF source])
  obtain eu ea Is' Ks' where parts': "d' = site_data_term eu ea"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using second by (auto simp: application_reading_at_source[OF source])
  have f: "(58,application_reading_argument e (use_data_term q) (Payload_Term a) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning application_reading_system"
    using first parts by simp
  have s: "(58,application_reading_argument e (use_data_term q) (Payload_Term a) (site_data_term eu ea) t'
      (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning application_reading_system"
    using second parts parts' by simp
  have "du = eu \<and> da = ea \<and> t = t' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule application_reading_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_mapped)
qed

section \<open>Each producer discharged at its notion's system\<close>

theorem quotation_producer_discharged:
  "producer_discharged (positive_meaning quotation_admission_system) 50 quotation_view quotation_holes
    (instantiation_correspondence 50)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(1)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(50,evaluate_pattern g (decode_finite_pattern (fst quotation_view))) \<in> positive_meaning quotation_admission_system"
    and b: "(50,evaluate_pattern g' (decode_finite_pattern (fst quotation_view))) \<in> positive_meaning quotation_admission_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd quotation_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd quotation_view)))"
    and i: "i < length quotation_holes"
  have a': "(50,term_quotation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)) \<in> positive_meaning quotation_admission_system"
    using a by (simp add: quotation_view_def)
  have b': "(50,term_quotation_argument (g 0) (g 1) (g 2) (g' 3) (g' 4) (g' 5)) \<in> positive_meaning quotation_admission_system"
    using b same by (simp add: quotation_view_def)
  have "g 3 = g' 3 \<and> bag_corresponds (g 4) (g' 4) \<and> bag_corresponds (g 5) (g' 5)" by (rule quotation_answers[OF a' b'])
  then show "instantiation_correspondence 50 i (evaluate_pattern g (decode_finite_pattern (quotation_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (quotation_holes ! i)))"
    using i by (auto simp: quotation_holes_def instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem binding_producer_discharged:
  "producer_discharged (positive_meaning binding_admission_system) 52 view_swap binding_holes
    (instantiation_correspondence 52)"
proof (rule producer_discharged_valuations[OF view_swap_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(52,evaluate_pattern g (decode_finite_pattern (fst view_swap))) \<in> positive_meaning binding_admission_system"
    and b: "(52,evaluate_pattern g' (decode_finite_pattern (fst view_swap))) \<in> positive_meaning binding_admission_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd view_swap))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd view_swap)))"
    and i: "i < length binding_holes"
  have a': "(52,Pair_Term (g 0) (g 1)) \<in> positive_meaning binding_admission_system"
    using a by (simp add: view_swap_def swapped_view_def)
  have b': "(52,Pair_Term (g' 0) (g 1)) \<in> positive_meaning binding_admission_system"
    using b same by (simp add: view_swap_def swapped_view_def)
  have "bag_corresponds (g 0) (g' 0)" by (rule binding_answers[OF a' b'])
  then show "instantiation_correspondence 52 i (evaluate_pattern g (decode_finite_pattern (binding_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (binding_holes ! i)))"
    using i by (simp add: binding_holes_def instantiation_correspondence_def)
qed

theorem instantiation_producer_discharged:
  "producer_discharged (positive_meaning pattern_instantiation_system) 55 instantiation_view instantiation_holes
    (instantiation_correspondence 55)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(2)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(55,evaluate_pattern g (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning pattern_instantiation_system"
    and b: "(55,evaluate_pattern g' (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning pattern_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd instantiation_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd instantiation_view)))"
    and i: "i < length instantiation_holes"
  have a': "(55,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8))
      \<in> positive_meaning pattern_instantiation_system"
    using a by (simp add: instantiation_view_def)
  have b': "(55,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g' 7) (g' 8))
      \<in> positive_meaning pattern_instantiation_system"
    using b same by (simp add: instantiation_view_def)
  have "g 5 = g' 5 \<and> bag_corresponds (g 6) (g' 6) \<and> bag_corresponds (g 7) (g' 7) \<and> bag_corresponds (g 8) (g' 8)"
    by (rule instantiation_answers[OF a' b'])
  then show "instantiation_correspondence 55 i (evaluate_pattern g (decode_finite_pattern (instantiation_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (instantiation_holes ! i)))"
    using i by (auto simp: instantiation_holes_def instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem scoped_producer_discharged:
  "producer_discharged (positive_meaning scoped_instantiation_system) 56 scoped_view scoped_holes
    (instantiation_correspondence 56)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(3)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(56,evaluate_pattern g (decode_finite_pattern (fst scoped_view))) \<in> positive_meaning scoped_instantiation_system"
    and b: "(56,evaluate_pattern g' (decode_finite_pattern (fst scoped_view))) \<in> positive_meaning scoped_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd scoped_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd scoped_view)))"
    and i: "i < length scoped_holes"
  have a': "(56,scoped_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
      \<in> positive_meaning scoped_instantiation_system"
    using a by (simp add: scoped_view_def)
  have b': "(56,scoped_instantiation_argument (g 0) (g 1) (g 2) (g' 3) (g 4) (g' 5) (g' 6))
      \<in> positive_meaning scoped_instantiation_system"
    using b same by (simp add: scoped_view_def)
  have "bag_corresponds (g 3) (g' 3) \<and> bag_corresponds (g 5) (g' 5) \<and> bag_corresponds (g 6) (g' 6)"
    by (rule scoped_answers[OF a' b'])
  then show "instantiation_correspondence 56 i (evaluate_pattern g (decode_finite_pattern (scoped_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (scoped_holes ! i)))"
    using i by (auto simp: scoped_holes_def instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem prospective_producer_discharged:
  "producer_discharged (positive_meaning prospective_instantiation_system) 57 prospective_view prospective_holes
    (instantiation_correspondence 57)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(4)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(57,evaluate_pattern g (decode_finite_pattern (fst prospective_view))) \<in> positive_meaning prospective_instantiation_system"
    and b: "(57,evaluate_pattern g' (decode_finite_pattern (fst prospective_view))) \<in> positive_meaning prospective_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd prospective_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd prospective_view)))"
    and i: "i < length prospective_holes"
  have a': "(57,prospective_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8) (g 9))
      \<in> positive_meaning prospective_instantiation_system"
    using a by (simp add: prospective_view_def)
  have b': "(57,prospective_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g' 7) (g' 8) (g' 9))
      \<in> positive_meaning prospective_instantiation_system"
    using b same by (simp add: prospective_view_def)
  have "g 5 = g' 5 \<and> g 6 = g' 6 \<and> bag_corresponds (g 7) (g' 7) \<and> bag_corresponds (g 8) (g' 8) \<and>
      bag_corresponds (g 9) (g' 9)"
    by (rule prospective_answers[OF a' b'])
  then have "Pair_Term (g 5) (g 6) = Pair_Term (g' 5) (g' 6) \<and> bag_corresponds (g 7) (g' 7) \<and>
      bag_corresponds (g 8) (g' 8) \<and> bag_corresponds (g 9) (g' 9)" by simp
  then show "instantiation_correspondence 57 i (evaluate_pattern g (decode_finite_pattern (prospective_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (prospective_holes ! i)))"
    using i by (auto simp: prospective_holes_def instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem application_producer_discharged:
  "producer_discharged (positive_meaning application_reading_system) 58 application_view application_holes
    (instantiation_correspondence 58)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(5)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(58,evaluate_pattern g (decode_finite_pattern (fst application_view))) \<in> positive_meaning application_reading_system"
    and b: "(58,evaluate_pattern g' (decode_finite_pattern (fst application_view))) \<in> positive_meaning application_reading_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd application_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd application_view)))"
    and i: "i < length application_holes"
  have a': "(58,application_reading_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
      \<in> positive_meaning application_reading_system"
    using a by (simp add: application_view_def)
  have b': "(58,application_reading_argument (g 0) (g 1) (g 2) (g' 3) (g' 4) (g' 5) (g' 6))
      \<in> positive_meaning application_reading_system"
    using b same by (simp add: application_view_def)
  have "g 3 = g' 3 \<and> g 4 = g' 4 \<and> bag_corresponds (g 5) (g' 5) \<and> bag_corresponds (g 6) (g' 6)"
    by (rule application_answers[OF a' b'])
  then have "Pair_Term (g 3) (g 4) = Pair_Term (g' 3) (g' 4) \<and> bag_corresponds (g 5) (g' 5) \<and>
      bag_corresponds (g 6) (g' 6)" by simp
  then show "instantiation_correspondence 58 i (evaluate_pattern g (decode_finite_pattern (application_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (application_holes ! i)))"
    using i by (auto simp: application_holes_def instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

text \<open>The whole output of each view, its holes' product: the form a socket's producer takes.\<close>

lemma instantiation_output_correspondences:
  "map (instantiation_correspondence 50) [0..<length quotation_holes] = [(=),bag_corresponds,bag_corresponds]"
  "map (instantiation_correspondence 55) [0..<length instantiation_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  "map (instantiation_correspondence 57) [0..<length prospective_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  by (simp_all add: quotation_holes_def instantiation_holes_def prospective_holes_def instantiation_correspondence_def
    upt_rec)

lemmas instantiation_output_producers =
  producer_discharged_tuple[OF quotation_producer_discharged instantiation_views_holes(1),
    unfolded instantiation_output_correspondences(1)]
  producer_discharged_tuple[OF instantiation_producer_discharged instantiation_views_holes(3),
    unfolded instantiation_output_correspondences(2)]
  producer_discharged_tuple[OF prospective_producer_discharged instantiation_views_holes(5),
    unfolded instantiation_output_correspondences(3)]

section \<open>Carriers\<close>

text \<open>
  Concatenation (46) carries its two input lists to its output at @{const join_view}: each input replaced by a bag
  of it gives an answer whose output is a bag of the old one. A consumer is the carrier with no output
  (@{const consumer_carrier_view}): bag comparison (6) and payload disjointness (49) at the identity view, the union
  (48) at its inputs at @{const join_view}. Pattern instantiation (55) at its scope (@{text instantiation_scope_view})
  carries a bag of its scope to the same outputs.
\<close>

abbreviation bag_pair :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "bag_pair \<equiv> tuple_corresponds [bag_corresponds,bag_corresponds]"

lemma bag_corresponds_list:
  assumes "bag_corresponds (data_list_term xs) y"
  obtains ys where "y = data_list_term ys" "mset ys = mset xs"
  using assms unfolding bag_corresponds_def by (auto simp: data_list_term_injective)

lemma bag_corresponds_elements:
  assumes "bag_corresponds (data_list_term xs) y" "data_elements xs"
  obtains ys where "y = data_list_term ys" "mset ys = mset xs" "data_elements ys"
proof -
  obtain ys where ys: "y = data_list_term ys" "mset ys = mset xs" using assms(1) by (rule bag_corresponds_list)
  have "data_elements ys" using assms(2) mset_eq_setD[OF ys(2)] by simp
  then show ?thesis using that ys by blast
qed

lemma bag_corresponds_payload_list:
  assumes "bag_corresponds (data_list_term (map Payload_Term A)) y"
  obtains B where "y = data_list_term (map Payload_Term B)" "mset B = mset A"
proof -
  obtain zs where zs: "y = data_list_term zs" "mset zs = mset (map Payload_Term A)"
    using assms by (rule bag_corresponds_list)
  have "\<forall>z\<in>set zs. \<exists>a. z = Payload_Term a" using mset_eq_setD[OF zs(2)] by auto
  then obtain B where B: "zs = map Payload_Term B" by (auto simp: ex_map_conv[symmetric])
  have "mset B = mset A" using zs(2) B injective_mapped_multisets[OF payload_term_inj] by simp
  then show ?thesis using that zs(1) B by blast
qed

theorem append_carrier_discharged:
  "carrier_discharged (positive_meaning data_append_system) 46 join_view bag_pair bag_corresponds"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(46,a) \<in> positive_meaning data_append_system"
    and va: "resolution_view_term join_view a = Some (x,y)" and cx: "bag_pair x x'"
  obtain a1 a2 where a: "a = Pair_Term a1 (Pair_Term a2 y)" and x: "x = Pair_Term a1 a2"
    using va by (auto simp: join_view_term)
  obtain xs ys where fields: "a1 = data_list_term xs" "a2 = data_list_term ys" "y = data_list_term (xs@ys)"
      "data_elements xs" "data_elements ys"
    using holds a by (auto simp: data_append_exact)
  obtain a1' a2' where x': "x' = Pair_Term a1' a2'" "bag_corresponds a1 a1'" "bag_corresponds a2 a2'"
    using cx x by auto
  obtain xs' where xs': "a1' = data_list_term xs'" "mset xs' = mset xs" "data_elements xs'"
    using x'(2) fields(1,4) bag_corresponds_elements by metis
  obtain ys' where ys': "a2' = data_list_term ys'" "mset ys' = mset ys" "data_elements ys'"
    using x'(3) fields(2,5) bag_corresponds_elements by metis
  have "(46,Pair_Term a1' (Pair_Term a2' (data_list_term (xs'@ys')))) \<in> positive_meaning data_append_system"
    by (simp only: data_append_exact) (use xs' ys' in blast)
  moreover have "resolution_view_term join_view (Pair_Term a1' (Pair_Term a2' (data_list_term (xs'@ys')))) =
      Some (x',data_list_term (xs'@ys'))"
    using x'(1) by (simp add: join_view_term)
  moreover have "bag_corresponds y (data_list_term (xs'@ys'))"
    using fields(3) xs'(2) ys'(2) by (simp add: bag_corresponds_lists)
  ultimately show "\<exists>b y'. (46,b) \<in> positive_meaning data_append_system \<and>
      resolution_view_term join_view b = Some (x',y') \<and> bag_corresponds y y'" by blast
qed

lemma identity_consumer_view_term:
  "resolution_view_term (consumer_carrier_view view_identity) t = Some (x,y) \<longleftrightarrow>
    (\<exists>u v. t = Pair_Term u v \<and> x = Pair_Term u v \<and> y = Payload_Term [])"
  by (cases t) (auto simp: consumer_carrier_view_term view_identity_term pair_view_def)

lemma join_consumer_view_term:
  "resolution_view_term (consumer_carrier_view join_view) t = Some (x,y) \<longleftrightarrow>
    (\<exists>a b c. t = Pair_Term a (Pair_Term b c) \<and> x = Pair_Term (Pair_Term a b) c \<and> y = Payload_Term [])"
proof
  assume "resolution_view_term (consumer_carrier_view join_view) t = Some (x,y)"
  then obtain z where z: "resolution_view_term join_view t = Some z" "x = Pair_Term (fst z) (snd z)"
      "y = Payload_Term []"
    by (auto simp: consumer_carrier_view_term)
  then show "\<exists>a b c. t = Pair_Term a (Pair_Term b c) \<and> x = Pair_Term (Pair_Term a b) c \<and> y = Payload_Term []"
    by (cases z) (auto simp: join_view_term)
next
  assume "\<exists>a b c. t = Pair_Term a (Pair_Term b c) \<and> x = Pair_Term (Pair_Term a b) c \<and> y = Payload_Term []"
  then obtain a b c where "t = Pair_Term a (Pair_Term b c)" "x = Pair_Term (Pair_Term a b) c" "y = Payload_Term []"
    by blast
  then show "resolution_view_term (consumer_carrier_view join_view) t = Some (x,y)"
    by (simp add: consumer_carrier_view_term join_view_term)
qed

theorem comparison_consumer_carrier:
  "carrier_discharged (positive_meaning bag_comparison_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(6,a) \<in> positive_meaning bag_comparison_system"
    and va: "resolution_view_term (consumer_carrier_view view_identity) a = Some (x,y)" and cx: "bag_pair x x'"
  obtain u v where a: "a = Pair_Term u v" and x: "x = Pair_Term u v" and y: "y = Payload_Term []"
    using va by (auto simp: identity_consumer_view_term)
  obtain xs ys where fields: "u = data_list_term xs" "v = data_list_term ys" "data_elements xs" "data_elements ys"
      "mset xs = mset ys"
    using holds a by (auto simp: bag_comparison_lists bag_comparison_exact)
  obtain u' v' where x': "x' = Pair_Term u' v'" "bag_corresponds u u'" "bag_corresponds v v'" using cx x by auto
  obtain xs' where xs': "u' = data_list_term xs'" "mset xs' = mset xs" "data_elements xs'"
    using x'(2) fields(1,3) bag_corresponds_elements by metis
  obtain ys' where ys': "v' = data_list_term ys'" "mset ys' = mset ys" "data_elements ys'"
    using x'(3) fields(2,4) bag_corresponds_elements by metis
  have "(6,Pair_Term u' v') \<in> positive_meaning bag_comparison_system"
    using xs' ys' fields(5) by (simp add: bag_comparison_lists)
  moreover have "resolution_view_term (consumer_carrier_view view_identity) (Pair_Term u' v') = Some (x',y)"
    using x'(1) y by (simp add: identity_consumer_view_term)
  ultimately show "\<exists>b y'. (6,b) \<in> positive_meaning bag_comparison_system \<and>
      resolution_view_term (consumer_carrier_view view_identity) b = Some (x',y') \<and> y = y'" by blast
qed

theorem disjoint_consumer_carrier:
  "carrier_discharged (positive_meaning payload_disjoint_system) 49 (consumer_carrier_view view_identity) bag_pair (=)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(49,a) \<in> positive_meaning payload_disjoint_system"
    and va: "resolution_view_term (consumer_carrier_view view_identity) a = Some (x,y)" and cx: "bag_pair x x'"
  obtain u v where a: "a = Pair_Term u v" and x: "x = Pair_Term u v" and y: "y = Payload_Term []"
    using va by (auto simp: identity_consumer_view_term)
  obtain A B where fields: "u = data_list_term (map Payload_Term A)" "v = data_list_term (map Payload_Term B)"
      "distinct A" "distinct B" "set A \<inter> set B = {}" "\<forall>c\<in>set A \<union> set B. octets_formed c"
    using holds a by (auto simp: payload_disjoint_exact)
  obtain u' v' where x': "x' = Pair_Term u' v'" "bag_corresponds u u'" "bag_corresponds v v'" using cx x by auto
  obtain A' where A': "u' = data_list_term (map Payload_Term A')" "mset A' = mset A"
    using x'(2) fields(1) bag_corresponds_payload_list by metis
  obtain B' where B': "v' = data_list_term (map Payload_Term B')" "mset B' = mset B"
    using x'(3) fields(2) bag_corresponds_payload_list by metis
  have "distinct A'" "distinct B'" "set A' = set A" "set B' = set B"
    using fields(3,4) mset_eq_imp_distinct_iff[OF A'(2)] mset_eq_imp_distinct_iff[OF B'(2)]
      mset_eq_setD[OF A'(2)] mset_eq_setD[OF B'(2)] by simp_all
  then have "(49,Pair_Term u' v') \<in> positive_meaning payload_disjoint_system"
    using A'(1) B'(1) fields(5,6) by (simp only: payload_disjoint_exact) blast
  moreover have "resolution_view_term (consumer_carrier_view view_identity) (Pair_Term u' v') = Some (x',y)"
    using x'(1) y by (simp add: identity_consumer_view_term)
  ultimately show "\<exists>b y'. (49,b) \<in> positive_meaning payload_disjoint_system \<and>
      resolution_view_term (consumer_carrier_view view_identity) b = Some (x',y') \<and> y = y'" by blast
qed

theorem union_consumer_carrier:
  "carrier_discharged (positive_meaning data_union_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(48,a) \<in> positive_meaning data_union_system"
    and va: "resolution_view_term (consumer_carrier_view join_view) a = Some (x,y)"
    and cx: "tuple_corresponds [bag_pair,bag_corresponds] x x'"
  obtain a1 a2 a3 where a: "a = Pair_Term a1 (Pair_Term a2 a3)" and x: "x = Pair_Term (Pair_Term a1 a2) a3"
      and y: "y = Payload_Term []"
    using va by (auto simp: join_consumer_view_term)
  obtain xs ys zs where fields: "a1 = data_list_term xs" "a2 = data_list_term ys" "a3 = data_list_term zs"
      "data_elements xs" "data_elements ys" "data_elements zs" "set zs = set xs \<union> set ys"
    using holds a by (auto simp: data_union_exact)
  obtain a1' a2' a3' where x': "x' = Pair_Term (Pair_Term a1' a2') a3'" "bag_corresponds a1 a1'"
      "bag_corresponds a2 a2'" "bag_corresponds a3 a3'"
    using cx x by auto
  obtain xs' where xs': "a1' = data_list_term xs'" "mset xs' = mset xs" "data_elements xs'"
    using x'(2) fields(1,4) bag_corresponds_elements by metis
  obtain ys' where ys': "a2' = data_list_term ys'" "mset ys' = mset ys" "data_elements ys'"
    using x'(3) fields(2,5) bag_corresponds_elements by metis
  obtain zs' where zs': "a3' = data_list_term zs'" "mset zs' = mset zs" "data_elements zs'"
    using x'(4) fields(3,6) bag_corresponds_elements by metis
  have "set zs' = set xs' \<union> set ys'"
    using fields(7) mset_eq_setD[OF xs'(2)] mset_eq_setD[OF ys'(2)] mset_eq_setD[OF zs'(2)] by simp
  then have "(48,Pair_Term a1' (Pair_Term a2' a3')) \<in> positive_meaning data_union_system"
    using xs' ys' zs' by (simp only: data_union_exact) blast
  moreover have "resolution_view_term (consumer_carrier_view join_view) (Pair_Term a1' (Pair_Term a2' a3')) = Some (x',y)"
    using x'(1) y by (simp add: join_consumer_view_term)
  ultimately show "\<exists>b y'. (48,b) \<in> positive_meaning data_union_system \<and>
      resolution_view_term (consumer_carrier_view join_view) b = Some (x',y') \<and> y = y'" by blast
qed

text \<open>Pattern instantiation (55) at its scope: the source, root, table and term fixed, the scope carried.\<close>

definition instantiation_scope_view :: "nat resolution_view" where
  "instantiation_scope_view = (fst instantiation_view,
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)) (Finite_Variable 5))),
    Finite_Pattern_Pair (Finite_Variable 6) (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 8)))"

abbreviation scope_input :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "scope_input \<equiv> tuple_corresponds [(=),tuple_corresponds [(=),tuple_corresponds [bag_corresponds,(=)],(=)]]"

lemma instantiation_scope_view_formed: "view_formed instantiation_scope_view"
  by (auto simp: view_formed_def instantiation_scope_view_def instantiation_view_def fset_eq_iff)

theorem scope_carrier_discharged:
  "carrier_discharged (positive_meaning pattern_instantiation_system) 55 instantiation_scope_view scope_input (=)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(55,a) \<in> positive_meaning pattern_instantiation_system"
    and va: "resolution_view_term instantiation_scope_view a = Some (x,y)" and cx: "scope_input x x'"
  obtain h :: "nat \<Rightarrow> factor_term" where
      h: "a = pattern_instantiation_argument (h 0) (h 1) (h 3) (h 4) (h 2) (h 5) (h 6) (h 7) (h 8)"
      "x = Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (Pair_Term (h 3) (h 4)) (h 5)))"
      "y = Pair_Term (h 6) (Pair_Term (h 7) (h 8))"
    using va resolution_view_term_valuation[OF instantiation_scope_view_formed[unfolded instantiation_scope_view_def]]
    by (auto simp: instantiation_scope_view_def instantiation_view_def)
  obtain v' where x': "x' = Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (Pair_Term v' (h 4)) (h 5)))"
      and v': "bag_corresponds (h 3) v'"
    using cx h(2) by auto
  obtain E where source: "environment_value_presents E (h 0)" using holds h(1) by (auto simp: pattern_instantiation_exact)
  obtain q Vs xs r Us Is Ks where parts: "h 1 = use_data_term q" "h 3 = data_list_term (map Payload_Term Vs)"
      "h 4 = binding_rows_term xs" "h 2 = Payload_Term r" "h 6 = data_list_term (map Payload_Term Us)"
      "h 7 = data_list_term (map Payload_Term Is)" "h 8 = data_list_term (map Payload_Term Ks)"
    using holds h(1) by (auto simp: pattern_instantiation_at_source[OF source])
  obtain Ws where Ws: "v' = data_list_term (map Payload_Term Ws)" "mset Ws = mset Vs"
    using v' parts(2) bag_corresponds_payload_list by metis
  let ?b = "pattern_instantiation_argument (h 0) (h 1) v' (h 4) (h 2) (h 5) (h 6) (h 7) (h 8)"
  have "(55,pattern_instantiation_argument (h 0) (use_data_term q) (data_list_term (map Payload_Term Ws))
      (binding_rows_term xs) (Payload_Term r) (h 5) (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning pattern_instantiation_system"
    using iffD1[OF pattern_instantiation_orders[OF source, of Vs Ws xs xs Us Us Is Is Ks Ks]] holds h(1) parts Ws(2)
    by simp
  then have "(55,?b) \<in> positive_meaning pattern_instantiation_system" using parts Ws(1) by simp
  moreover have "resolution_view_term instantiation_scope_view ?b = Some (x',y)"
    using resolution_view_term_valuation[OF instantiation_scope_view_formed[unfolded instantiation_scope_view_def]] x' h(3)
    by (simp add: instantiation_scope_view_def instantiation_view_def)
      (intro exI[of _ "h(3 := v')"], simp)
  ultimately show "\<exists>b y'. (55,b) \<in> positive_meaning pattern_instantiation_system \<and>
      resolution_view_term instantiation_scope_view b = Some (x',y') \<and> y = y'" by blast
qed

section \<open>The carriers read at the socket systems\<close>

text \<open>
  A socket is carried along its clause's carriers by the one shape of @{text Factor_Resolution_Carriers}
  (@{text socket_carried_listed}); what a socket's proof names is its producer, the renaming of its output and the
  facts its carriers are discharged by, read here at the socket systems.
\<close>

lemmas instantiation_listed_simps = socket_listed_simps view_listed[OF quotation_view_def]
  view_listed[OF instantiation_view_def] view_listed[OF scoped_view_def] view_listed[OF prospective_view_def]
  view_listed[OF application_view_def] instantiation_views_formed

lemma quotation_carriers:
  "carrier_discharged (positive_meaning quotation_admission_system) 46 join_view bag_pair bag_corresponds"
  "carrier_discharged (positive_meaning quotation_admission_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  "carrier_discharged (positive_meaning quotation_admission_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  using append_carrier_discharged comparison_consumer_carrier union_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF quotation_admission_components(7)]
    carrier_discharged_site[OF quotation_admission_components(8)]
    carrier_discharged_site[OF quotation_admission_components(9)])

section \<open>The sockets of 50's pair clause\<close>

text \<open>
  50's pair clause reads both children through 50 itself (sockets 2 and 3), each at @{const quotation_view}: a
  child's term goes to the head's term, its interior through the two concatenations (46) to the bag comparison (6)
  with the head's interior, its slots to the union (48) at its inputs. The head is committed at its own view.
\<close>

definition quotation_pair_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "quotation_pair_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of
      (term_quotation_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
        (Pattern_Variable 5) (Pattern_Variable 6)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 7))),
      (1,34,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z)
        (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10),
          Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 11)]))),
      (2,50,finite_pattern_of (term_quotation_pattern data_x data_y (Pattern_Variable 10) data_w
        (Pattern_Variable 12) (Pattern_Variable 13))),
      (3,50,finite_pattern_of (term_quotation_pattern data_x data_y (Pattern_Variable 11) (Pattern_Variable 4)
        (Pattern_Variable 14) (Pattern_Variable 15))),
      (4,46,finite_pattern_of (collection_join_pattern (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9])
        (Pattern_Variable 12) (Pattern_Variable 16))),
      (5,46,finite_pattern_of (collection_join_pattern (Pattern_Variable 16) (Pattern_Variable 14) (Pattern_Variable 17))),
      (6,6,finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 5))),
      (7,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 15) (Pattern_Variable 6))),
      (8,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)))|},
    finite_schema_materials = {||}\<rparr>"

lemma quotation_pair_socket_decoded: "decode_finite_schema quotation_pair_socket_schema = quotation_pair_schema"
  by (simp add: quotation_pair_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def quotation_pair_schema_def)

definition quotation_left_carriers :: "nat clause_carrier list" where
  "quotation_left_carriers = [(4,join_view,bag_pair,bag_corresponds),(5,join_view,bag_pair,bag_corresponds),
    (6,consumer_carrier_view view_identity,bag_pair,(=)),
    (7,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

theorem quotation_left_socket_carried:
  "socket_carried (positive_meaning quotation_admission_system) quotation_pair_socket_schema 2 False
    quotation_view quotation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds]) quotation_left_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(1) instantiation_output_producers(1), where \<sigma> = "\<lambda>v. if v = 12 then 4 else if v = 13 then 5 else v"])
    (simp add: instantiation_listed_simps quotation_pair_socket_schema_def quotation_left_carriers_def join_view_formed quotation_carriers(1) quotation_carriers(2) quotation_carriers(3))

theorem quotation_left_socket_discharged:
  "socket_discharged (positive_meaning quotation_admission_system) quotation_pair_socket_schema 2 False
    quotation_view quotation_view"
  by (rule socket_discharged_carried[OF quotation_left_socket_carried])

definition quotation_right_carriers :: "nat clause_carrier list" where
  "quotation_right_carriers = [(5,join_view,bag_pair,bag_corresponds),
    (6,consumer_carrier_view view_identity,bag_pair,(=)),
    (7,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

theorem quotation_right_socket_carried:
  "socket_carried (positive_meaning quotation_admission_system) quotation_pair_socket_schema 3 False
    quotation_view quotation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds]) quotation_right_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(1) instantiation_output_producers(1), where \<sigma> = "\<lambda>v. if v = 4 then 3 else if v = 14 then 4 else if v = 15 then 5 else v"])
    (simp add: instantiation_listed_simps quotation_pair_socket_schema_def quotation_right_carriers_def join_view_formed quotation_carriers(1) quotation_carriers(2) quotation_carriers(3))

theorem quotation_right_socket_discharged:
  "socket_discharged (positive_meaning quotation_admission_system) quotation_pair_socket_schema 3 False
    quotation_view quotation_view"
  by (rule socket_discharged_carried[OF quotation_right_socket_carried])

section \<open>The socket of 55's constant clause\<close>

text \<open>
  55's constant clause reads its term through quotation admission (50) at @{const quotation_view}: the quoted term,
  interior and slots are the head's, the interior also held by payload disjointness (49) against the scope.
\<close>

lemma instantiation_system_carriers:
  "carrier_discharged (positive_meaning pattern_instantiation_system) 46 join_view bag_pair bag_corresponds"
  "carrier_discharged (positive_meaning pattern_instantiation_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  "carrier_discharged (positive_meaning pattern_instantiation_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  "carrier_discharged (positive_meaning pattern_instantiation_system) 49 (consumer_carrier_view view_identity) bag_pair (=)"
  using append_carrier_discharged comparison_consumer_carrier union_consumer_carrier disjoint_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF pattern_instantiation_components(8)]
    carrier_discharged_site[OF pattern_instantiation_components(9)]
    carrier_discharged_site[OF pattern_instantiation_components(10)]
    carrier_discharged_site[OF pattern_instantiation_components(4)])

lemma instantiation_socket_producer:
  "producer_discharged (positive_meaning pattern_instantiation_system) 50 quotation_view [snd (snd quotation_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds])"
  using instantiation_output_producers(1)
  by (simp add: producer_discharged_site[OF pattern_instantiation_components(5)])

definition instantiation_constant_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "instantiation_constant_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of
      (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
        (Pattern_Payload []) (Pattern_Variable 6) (Pattern_Variable 7)),
    finite_schema_premises = {|(0,52,finite_pattern_of (Pattern_Pair data_z data_w)),
      (1,50,finite_pattern_of (term_quotation_pattern data_x data_y (Pattern_Variable 4) (Pattern_Variable 5)
        (Pattern_Variable 6) (Pattern_Variable 7))),
      (2,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 6) data_z))|},
    finite_schema_materials = {||}\<rparr>"

lemma instantiation_constant_socket_decoded:
  "decode_finite_schema instantiation_constant_socket_schema = instantiation_constant_schema"
  by (simp add: instantiation_constant_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def instantiation_constant_schema_def)

definition instantiation_constant_carriers :: "nat clause_carrier list" where
  "instantiation_constant_carriers = [(2,consumer_carrier_view view_identity,bag_pair,(=))]"

theorem instantiation_constant_socket_carried:
  "socket_carried (positive_meaning pattern_instantiation_system) instantiation_constant_socket_schema 1 False
    quotation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds])
    instantiation_constant_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(1) instantiation_socket_producer, where \<sigma> = "\<lambda>v. if v = 5 then 3 else if v = 6 then 4 else if v = 7 then 5 else v"])
    (simp add: instantiation_listed_simps instantiation_constant_socket_schema_def instantiation_constant_carriers_def instantiation_system_carriers(4))

theorem instantiation_constant_socket_discharged:
  "socket_discharged (positive_meaning pattern_instantiation_system) instantiation_constant_socket_schema 1 False
    quotation_view instantiation_view"
  by (rule socket_discharged_carried[OF instantiation_constant_socket_carried])

section \<open>The sockets of 55's pair clause\<close>

text \<open>
  55's pair clause reads both children through 55 itself (sockets 2 and 3) at @{const instantiation_view}: a child's
  term goes to the head's term, its interior through the two concatenations (46) to the bag comparison (6), its used
  variables and slots to the unions (48) at their inputs.
\<close>

definition instantiation_pair_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "instantiation_pair_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of
      (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4)
        (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 10))),
      (1,34,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 4))
        (data_list_pattern [Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 13),
          Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 14)]))),
      (2,55,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 13)
        (Pattern_Variable 5) (Pattern_Variable 15) (Pattern_Variable 17) (Pattern_Variable 19))),
      (3,55,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 14)
        (Pattern_Variable 6) (Pattern_Variable 16) (Pattern_Variable 18) (Pattern_Variable 20))),
      (4,46,finite_pattern_of (collection_join_pattern (data_list_pattern [Pattern_Variable 4,Pattern_Variable 11,
        Pattern_Variable 12]) (Pattern_Variable 17) (Pattern_Variable 21))),
      (5,46,finite_pattern_of (collection_join_pattern (Pattern_Variable 21) (Pattern_Variable 18) (Pattern_Variable 22))),
      (6,6,finite_pattern_of (Pattern_Pair (Pattern_Variable 22) (Pattern_Variable 8))),
      (7,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 19) (Pattern_Variable 20) (Pattern_Variable 9))),
      (8,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 7))),
      (9,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))),
      (10,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 8) data_z)),
      (11,1,finite_pattern_of (Pattern_Variable 7))|},
    finite_schema_materials = {||}\<rparr>"

lemma instantiation_pair_socket_decoded: "decode_finite_schema instantiation_pair_socket_schema = instantiation_pair_schema"
  by (simp add: instantiation_pair_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def instantiation_pair_schema_def)

definition instantiation_left_carriers :: "nat clause_carrier list" where
  "instantiation_left_carriers = [(4,join_view,bag_pair,bag_corresponds),(5,join_view,bag_pair,bag_corresponds),
    (6,consumer_carrier_view view_identity,bag_pair,(=)),
    (7,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=)),
    (8,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

theorem instantiation_left_socket_carried:
  "socket_carried (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 2 False
    instantiation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])
    instantiation_left_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(2) instantiation_output_producers(2), where \<sigma> = "\<lambda>v. if v = 15 then 6 else if v = 17 then 7 else if v = 19 then 8 else v"])
    (simp add: instantiation_listed_simps instantiation_pair_socket_schema_def instantiation_left_carriers_def join_view_formed instantiation_system_carriers(1) instantiation_system_carriers(2) instantiation_system_carriers(3))

theorem instantiation_left_socket_discharged:
  "socket_discharged (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 2 False
    instantiation_view instantiation_view"
  by (rule socket_discharged_carried[OF instantiation_left_socket_carried])

definition instantiation_right_carriers :: "nat clause_carrier list" where
  "instantiation_right_carriers = [(5,join_view,bag_pair,bag_corresponds),
    (6,consumer_carrier_view view_identity,bag_pair,(=)),
    (7,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=)),
    (8,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

theorem instantiation_right_socket_carried:
  "socket_carried (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 3 False
    instantiation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])
    instantiation_right_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(2) instantiation_output_producers(2), where \<sigma> = "\<lambda>v. if v = 6 then 5 else if v = 16 then 6 else if v = 18 then 7 else if v = 20 then 8 else v"])
    (simp add: instantiation_listed_simps instantiation_pair_socket_schema_def instantiation_right_carriers_def join_view_formed instantiation_system_carriers(1) instantiation_system_carriers(2) instantiation_system_carriers(3))

theorem instantiation_right_socket_discharged:
  "socket_discharged (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 3 False
    instantiation_view instantiation_view"
  by (rule socket_discharged_carried[OF instantiation_right_socket_carried])

section \<open>The socket of 57's clause\<close>

text \<open>
  57's clause reads its argument through 55 (socket 4) at @{const instantiation_view}: the term and used variables
  go to the head's, the interior through the second concatenation (46) to the bag comparison (6), the slots to the
  union (48) at its second input.
\<close>

lemma prospective_system_carriers:
  "carrier_discharged (positive_meaning prospective_instantiation_system) 46 join_view bag_pair bag_corresponds"
  "carrier_discharged (positive_meaning prospective_instantiation_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  "carrier_discharged (positive_meaning prospective_instantiation_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  using append_carrier_discharged comparison_consumer_carrier union_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF prospective_instantiation_components(6)]
    carrier_discharged_site[OF prospective_instantiation_components(7)]
    carrier_discharged_site[OF prospective_instantiation_components(8)])

lemma prospective_socket_producer:
  "producer_discharged (positive_meaning prospective_instantiation_system) 55 instantiation_view
    [snd (snd instantiation_view)] (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  using instantiation_output_producers(2)
  by (simp add: producer_discharged_site[OF prospective_instantiation_components(5)])

definition prospective_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "prospective_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of
      (prospective_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
        (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 10))),
      (1,34,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 4))
        (data_list_pattern [Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 13),
          Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 14)]))),
      (2,42,finite_pattern_of (citation_reading_pattern data_x data_y (Pattern_Variable 13)
        (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 18)) (Pattern_Variable 15))),
      (3,41,finite_pattern_of (citation_observation_pattern data_x data_y
        (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 18)) (Pattern_Variable 5))),
      (4,55,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 14)
        (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 16) (Pattern_Variable 19))),
      (5,46,finite_pattern_of (collection_join_pattern (data_list_pattern [Pattern_Variable 4,Pattern_Variable 11,
        Pattern_Variable 12]) (Pattern_Variable 15) (Pattern_Variable 20))),
      (6,46,finite_pattern_of (collection_join_pattern (Pattern_Variable 20) (Pattern_Variable 16) (Pattern_Variable 21))),
      (7,6,finite_pattern_of (Pattern_Pair (Pattern_Variable 21) (Pattern_Variable 8))),
      (8,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 17) (Pattern_Variable 19) (Pattern_Variable 9))),
      (9,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))),
      (10,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 8) data_z))|},
    finite_schema_materials = {||}\<rparr>"

lemma prospective_socket_decoded: "decode_finite_schema prospective_socket_schema = prospective_instantiation_schema"
  by (simp add: prospective_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def prospective_instantiation_schema_def)

definition prospective_carriers :: "nat clause_carrier list" where
  "prospective_carriers = [(6,join_view,bag_pair,bag_corresponds),
    (7,consumer_carrier_view view_identity,bag_pair,(=)),
    (8,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

theorem prospective_socket_carried:
  "socket_carried (positive_meaning prospective_instantiation_system) prospective_socket_schema 4 False
    instantiation_view prospective_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])
    prospective_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(2) prospective_socket_producer, where \<sigma> = "\<lambda>v. if v = 6 then 5 else if v = 7 then 6 else if v = 16 then 7 else if v = 19 then 8 else v"])
    (simp add: instantiation_listed_simps prospective_socket_schema_def prospective_carriers_def join_view_formed prospective_system_carriers(1) prospective_system_carriers(2) prospective_system_carriers(3))

theorem prospective_socket_discharged:
  "socket_discharged (positive_meaning prospective_instantiation_system) prospective_socket_schema 4 False
    instantiation_view prospective_view"
  by (rule socket_discharged_carried[OF prospective_socket_carried])

section \<open>The socket of 58's clause\<close>

text \<open>
  58's clause reads the application through 57 (socket 0) with an empty scope, table and used-variable collection,
  all ground: 57 is read there at @{text prospective_used_view}, whose input holds its used variables beside the
  source, root, scope and table, and whose output (the callee site and term, interior and slots) is the head's own.
  No carrier stands between them.
\<close>

definition prospective_used_view :: "nat resolution_view" where
  "prospective_used_view = (fst prospective_view,
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)) (Finite_Variable 7))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))
      (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 9)))"

lemma prospective_used_view_formed: "view_formed prospective_used_view"
  by (auto simp: view_formed_def prospective_used_view_def prospective_view_def fset_eq_iff)

theorem prospective_used_producer_discharged:
  "producer_discharged (positive_meaning prospective_instantiation_system) 57 prospective_used_view
    [snd (snd prospective_used_view)] (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds])"
proof (rule producer_discharged_valuations[OF prospective_used_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(57,evaluate_pattern g (decode_finite_pattern (fst prospective_used_view)))
      \<in> positive_meaning prospective_instantiation_system"
    and b: "(57,evaluate_pattern g' (decode_finite_pattern (fst prospective_used_view)))
      \<in> positive_meaning prospective_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd prospective_used_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd prospective_used_view)))"
    and i: "i < length [snd (snd prospective_used_view)]"
  have a': "(57,prospective_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8) (g 9))
      \<in> positive_meaning prospective_instantiation_system"
    using a by (simp add: prospective_used_view_def prospective_view_def)
  have b': "(57,prospective_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g 7) (g' 8) (g' 9))
      \<in> positive_meaning prospective_instantiation_system"
    using b same by (simp add: prospective_used_view_def prospective_view_def)
  have "g 5 = g' 5 \<and> g 6 = g' 6 \<and> bag_corresponds (g 7) (g 7) \<and> bag_corresponds (g 8) (g' 8) \<and>
      bag_corresponds (g 9) (g' 9)"
    by (rule prospective_answers[OF a' b'])
  then show "tuple_corresponds [(=),bag_corresponds,bag_corresponds]
      (evaluate_pattern g (decode_finite_pattern ([snd (snd prospective_used_view)] ! i)))
      (evaluate_pattern g' (decode_finite_pattern ([snd (snd prospective_used_view)] ! i)))"
    using i by (simp add: prospective_used_view_def)
qed

lemma application_socket_producer:
  "producer_discharged (positive_meaning application_reading_system) 57 prospective_used_view
    [snd (snd prospective_used_view)] (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds])"
proof -
  have agree: "\<And>t. (57,t) \<in> positive_meaning application_reading_system \<longleftrightarrow>
      (57,t) \<in> positive_meaning prospective_instantiation_system"
    by (rule application_reading_old_meaning) (simp only: prospective_instantiation_definitions insertI1)
  show ?thesis using prospective_used_producer_discharged by (simp add: producer_discharged_site[OF agree])
qed

definition application_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "application_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of
      (application_reading_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)
        (Pattern_Variable 6)),
    finite_schema_premises = {|(0,57,finite_pattern_of (prospective_instantiation_pattern data_x data_y
      (Pattern_Payload []) (Pattern_Payload []) data_z data_w (Pattern_Variable 4) (Pattern_Payload [])
      (Pattern_Variable 5) (Pattern_Variable 6)))|},
    finite_schema_materials = {||}\<rparr>"

lemma application_socket_decoded: "decode_finite_schema application_socket_schema = application_reading_schema"
  by (simp add: application_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def application_reading_schema_def)

theorem application_socket_carried:
  "socket_carried (positive_meaning application_reading_system) application_socket_schema 0 False
    prospective_used_view application_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds]) []"
  by (rule socket_carried_listed[OF meaning_answers_formed prospective_used_view_formed application_socket_producer, where \<sigma> = "\<lambda>v. if v = 3 then 5 else if v = 4 then 6 else if v = 5 then 8 else if v = 6 then 9 else v"])
    (simp add: instantiation_listed_simps application_socket_schema_def view_listed[OF prospective_used_view_def] prospective_used_view_formed)

theorem application_socket_discharged:
  "socket_discharged (positive_meaning application_reading_system) application_socket_schema 0 False
    prospective_used_view application_view"
  by (rule socket_discharged_carried[OF application_socket_carried])

section \<open>The family's declarations\<close>

text \<open>
  Each notion's declarations, discharged at its own system with the correspondence
  @{const instantiation_correspondence}: its producer at its metadata view and the free sockets its clauses hold of
  the family's producers. Carrying them to the given's programs is R6c's carrying part.
\<close>

definition quotation_declarations :: "(nat,nat,nat) resolution_declarations" where
  "quotation_declarations = \<lparr>declared_producers = {|(50,quotation_view,quotation_holes)|}, declared_consumers = {||},
    declared_sockets = {|(50,quotation_pair_socket_schema,2,False,quotation_view,quotation_view),
      (50,quotation_pair_socket_schema,3,False,quotation_view,quotation_view)|}\<rparr>"

definition binding_declarations :: "(nat,nat,nat) resolution_declarations" where
  "binding_declarations = \<lparr>declared_producers = {|(52,view_swap,binding_holes)|}, declared_consumers = {||},
    declared_sockets = {||}\<rparr>"

definition instantiation_declarations :: "(nat,nat,nat) resolution_declarations" where
  "instantiation_declarations = \<lparr>declared_producers = {|(55,instantiation_view,instantiation_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(55,instantiation_constant_socket_schema,1,False,quotation_view,instantiation_view),
      (55,instantiation_pair_socket_schema,2,False,instantiation_view,instantiation_view),
      (55,instantiation_pair_socket_schema,3,False,instantiation_view,instantiation_view)|}\<rparr>"

definition scoped_declarations :: "(nat,nat,nat) resolution_declarations" where
  "scoped_declarations = \<lparr>declared_producers = {|(56,scoped_view,scoped_holes)|}, declared_consumers = {||},
    declared_sockets = {||}\<rparr>"

definition prospective_declarations :: "(nat,nat,nat) resolution_declarations" where
  "prospective_declarations = \<lparr>declared_producers = {|(57,prospective_view,prospective_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(57,prospective_socket_schema,4,False,instantiation_view,prospective_view)|}\<rparr>"

definition application_declarations :: "(nat,nat,nat) resolution_declarations" where
  "application_declarations = \<lparr>declared_producers = {|(58,application_view,application_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(58,application_socket_schema,0,False,prospective_used_view,application_view)|}\<rparr>"

theorem instantiation_notion_declarations_discharged:
  "declarations_discharged (positive_meaning quotation_admission_system) quotation_declarations
    instantiation_correspondence"
  "declarations_discharged (positive_meaning binding_admission_system) binding_declarations
    instantiation_correspondence"
  "declarations_discharged (positive_meaning pattern_instantiation_system) instantiation_declarations
    instantiation_correspondence"
  "declarations_discharged (positive_meaning scoped_instantiation_system) scoped_declarations
    instantiation_correspondence"
  "declarations_discharged (positive_meaning prospective_instantiation_system) prospective_declarations
    instantiation_correspondence"
  "declarations_discharged (positive_meaning application_reading_system) application_declarations
    instantiation_correspondence"
  using quotation_producer_discharged quotation_left_socket_discharged quotation_right_socket_discharged
    binding_producer_discharged instantiation_producer_discharged instantiation_constant_socket_discharged[simplified]
    instantiation_left_socket_discharged instantiation_right_socket_discharged scoped_producer_discharged
    prospective_producer_discharged prospective_socket_discharged application_producer_discharged
    application_socket_discharged
  by (simp_all add: declarations_discharged_def declarations_formed_def instantiation_views_formed view_swap_formed
    prospective_used_view_formed quotation_declarations_def binding_declarations_def instantiation_declarations_def
    scoped_declarations_def prospective_declarations_def application_declarations_def)

end
