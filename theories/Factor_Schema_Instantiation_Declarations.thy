theory Factor_Schema_Instantiation_Declarations
  imports Factor_Instantiation_Declarations Factor_Schema_Instantiation Development_Given_Declarations
begin

text \<open>
  The instantiation family's second part (R6c of DECISIONS.md "The native evaluator constructs the missing witnesses
  by resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", (a) and (b)):
  row values (59), vector instantiation (60), record instantiation (61), material instantiation (62), premise rows
  (63), premise family instantiation (64) and schema instantiation (65) declared at their metadata views, each
  producer discharged at its notion's own system from its exact contract; the free sockets their clauses hold, each
  discharged along the clause's carriers (@{text socket_discharged_carried}); the carrier 63. The views, holes,
  bags, tuples and carriers of the first part (@{text Factor_Instantiation_Declarations}) are cited as it names
  them, and the family's rows (32) at premise family instantiation's clause as R6 declares them
  (@{text Development_Given_Declarations}). No clause of any program changes, and the declarations are read by the
  committed search alone.
\<close>

section \<open>The correspondence at each hole\<close>

text \<open>
  A record's values, an instantiated term list, a material tuple, a schema's conclusion and the call and material
  rows of an ordered row list are determined by their inputs: their holes correspond by equality. Every other hole of
  these notions is a bag.
\<close>

definition schema_instantiation_correspondence :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "schema_instantiation_correspondence d i =
    (if (d \<in> {59,60,61,62,65} \<and> i = 0) \<or> (d = 63 \<and> i \<in> {0,1}) then (=) else bag_corresponds)"

section \<open>The metadata views\<close>

text \<open>
  Row values (59) at R5's identity view: the rows in, the values out. Vector instantiation (60), record instantiation
  (61) and material instantiation (62) have pattern instantiation's argument and are read at its view
  (@{const instantiation_view}): the source, root or roots, scope and table in, the term, term list or material
  tuple, used variables, interior and slots out. Record instantiation is also read at
  @{text record_material_view}, its term list the five fields of a material record: the view at which material
  instantiation's clause reads it.
\<close>

definition row_values_holes :: "nat finite_term_pattern list" where
  "row_values_holes = [Finite_Variable 1]"

definition five_fields_list :: "nat finite_term_pattern" where
  "five_fields_list = Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6)
    (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Variable 8)
      (Finite_Pattern_Pair (Finite_Variable 9) (Finite_Pattern_Payload [])))))"

definition five_fields_tuple :: "nat finite_term_pattern" where
  "five_fields_tuple = Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6)
    (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 9))))"

definition record_material_view :: "nat resolution_view" where
  "record_material_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair five_fields_list (Finite_Pattern_Pair (Finite_Variable 10)
          (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12)))))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    Finite_Pattern_Pair five_fields_tuple (Finite_Pattern_Pair (Finite_Variable 10)
      (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12))))"

definition record_material_holes :: "nat finite_term_pattern list" where
  "record_material_holes = [five_fields_tuple,Finite_Variable 10,Finite_Variable 11,Finite_Variable 12]"

text \<open>
  Premise rows (63) and premise family instantiation (64) at ((e,(u,(v,b))),(r,(q,(c,w)))): the source, scope, table
  and rows or root in, the call rows, material rows and used variables out. Schema instantiation (65) at
  ((e,u),(r,(b,(t,(q,c))))): the source, root and table in, the conclusion, call rows and material rows out.
\<close>

definition premise_rows_view :: "nat resolution_view" where
  "premise_rows_view = (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))))
      (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 5)
        (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 7)))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))) (Finite_Variable 4),
    Finite_Pattern_Pair (Finite_Variable 5) (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 7)))"

definition premise_rows_holes :: "nat finite_term_pattern list" where
  "premise_rows_holes = [Finite_Variable 5,Finite_Variable 6,Finite_Variable 7]"

definition schema_view :: "nat resolution_view" where
  "schema_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3)
        (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))"

definition schema_holes :: "nat finite_term_pattern list" where
  "schema_holes = [Finite_Variable 4,Finite_Variable 5,Finite_Variable 6]"

lemma premise_views_formed: "view_formed premise_rows_view" "view_formed schema_view"
  by (auto simp: view_formed_def premise_rows_view_def schema_view_def fset_eq_iff)

lemma premise_views_holes:
  "view_holes premise_rows_view premise_rows_holes" "view_holes schema_view schema_holes"
  by (simp_all add: view_holes_def premise_rows_view_def premise_rows_holes_def schema_view_def schema_holes_def)

lemma record_material_view_formed: "view_formed record_material_view"
  by (auto simp: view_formed_def record_material_view_def five_fields_list_def five_fields_tuple_def fset_eq_iff)

lemma schema_instantiation_views_holes:
  "view_holes view_identity row_values_holes" "view_holes record_material_view record_material_holes"
  by (simp_all add: view_holes_def view_identity_def identity_view_def row_values_holes_def record_material_view_def
    record_material_holes_def)

section \<open>Two answers at one input, from each notion's contract\<close>

lemma vector_answers:
  assumes one: "(60,pattern_instantiation_argument e u v b r t w i k) \<in> positive_meaning vector_instantiation_system"
    and two: "(60,pattern_instantiation_argument e u v b r t' w' i' k') \<in> positive_meaning vector_instantiation_system"
  shows "t = t' \<and> bag_corresponds w w' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using one by (auto simp: vector_instantiation_exact)
  obtain q Vs xs rs ts Us Is Ks where parts: "u = use_data_term q" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = data_list_term (map Payload_Term rs)" "t = data_list_term ts"
      "w = data_list_term (map Payload_Term Us)" "i = data_list_term (map Payload_Term Is)"
      "k = data_list_term (map Payload_Term Ks)"
    using one by (auto simp: vector_instantiation_at_source[OF source])
  obtain ts' Us' Is' Ks' where parts': "t' = data_list_term ts'" "w' = data_list_term (map Payload_Term Us')"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using two by (auto simp: vector_instantiation_at_source[OF source])
  have f: "(60,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (data_list_term (map Payload_Term rs)) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning vector_instantiation_system"
    using one parts by simp
  have s: "(60,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (data_list_term (map Payload_Term rs)) (data_list_term ts')
      (data_list_term (map Payload_Term Us')) (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning vector_instantiation_system"
    using two parts parts' by simp
  have "ts = ts' \<and> mset Us = mset Us' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule vector_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_mapped)
qed

lemma record_answers:
  assumes one: "(61,pattern_instantiation_argument e u v b r t w i k) \<in> positive_meaning record_instantiation_system"
    and two: "(61,pattern_instantiation_argument e u v b r t' w' i' k') \<in> positive_meaning record_instantiation_system"
  shows "t = t' \<and> bag_corresponds w w' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E where source: "environment_value_presents E e" using one by (auto simp: record_instantiation_exact)
  obtain q Vs xs a ts Us Is Ks where parts: "u = use_data_term q" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = Payload_Term a" "t = data_list_term ts"
      "w = data_list_term (map Payload_Term Us)" "i = data_list_term (map Payload_Term Is)"
      "k = data_list_term (map Payload_Term Ks)"
    using one by (auto simp: record_instantiation_at_source[OF source])
  obtain ts' Us' Is' Ks' where parts': "t' = data_list_term ts'" "w' = data_list_term (map Payload_Term Us')"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using two by (auto simp: record_instantiation_at_source[OF source])
  have f: "(61,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning record_instantiation_system"
    using one parts by simp
  have s: "(61,pattern_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term a) (data_list_term ts')
      (data_list_term (map Payload_Term Us')) (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning record_instantiation_system"
    using two parts parts' by simp
  have "ts = ts' \<and> mset Us = mset Us' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule record_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_mapped)
qed

lemma material_answers:
  assumes one: "(62,pattern_instantiation_argument e u v b r t w i k) \<in> positive_meaning material_instantiation_system"
    and two: "(62,pattern_instantiation_argument e u v b r t' w' i' k') \<in> positive_meaning material_instantiation_system"
  shows "t = t' \<and> bag_corresponds w w' \<and> bag_corresponds i i' \<and> bag_corresponds k k'"
proof -
  obtain E s1 a1 d1 c1 f1 where source: "environment_value_presents E e" and tuple: "t = material_tuple s1 a1 d1 c1 f1"
    using one by (auto simp: material_instantiation_exact)
  obtain s2 a2 d2 c2 f2 where tuple': "t' = material_tuple s2 a2 d2 c2 f2"
    using two by (auto simp: material_instantiation_exact)
  obtain q Vs xs l Us Is Ks where parts: "u = use_data_term q" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = Payload_Term l" "w = data_list_term (map Payload_Term Us)"
      "i = data_list_term (map Payload_Term Is)" "k = data_list_term (map Payload_Term Ks)"
    using one tuple by (auto simp: material_instantiation_at_source[OF source])
  obtain Us' Is' Ks' where parts': "w' = data_list_term (map Payload_Term Us')"
      "i' = data_list_term (map Payload_Term Is')" "k' = data_list_term (map Payload_Term Ks')"
    using two tuple' by (auto simp: material_instantiation_at_source[OF source])
  have f: "(62,material_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term l) s1 a1 d1 c1 f1 (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in> positive_meaning material_instantiation_system"
    using one parts tuple by simp
  have s: "(62,material_instantiation_argument e (use_data_term q) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term l) s2 a2 d2 c2 f2 (data_list_term (map Payload_Term Us'))
      (data_list_term (map Payload_Term Is')) (data_list_term (map Payload_Term Ks')))
      \<in> positive_meaning material_instantiation_system"
    using two parts parts' tuple' by simp
  have "(s1,a1,d1,c1,f1) = (s2,a2,d2,c2,f2) \<and> mset Us = mset Us' \<and> mset Is = mset Is' \<and> mset Ks = mset Ks'"
    by (rule material_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' tuple tuple' by (simp add: bag_corresponds_mapped)
qed

text \<open>
  An ordered premise row list is determined by its source, scope, table and rows: every row reads as the one call or
  the one material premise at its root, and each has one instance under a functional table.
\<close>

lemma instantiated_premise_rows_cons:
  "instantiated_premise_rows E u V B ((s,r)#rs) qs cs U \<longleftrightarrow>
    (\<exists>d p I K t qs' U'. prospective_call_at E u V r d p I K \<and> pattern_instance B p t \<and>
      instantiated_premise_rows E u V B rs qs' cs U' \<and> qs = (s,d,t)#qs' \<and> U = pattern_variables p \<union> U') \<or>
    (\<exists>M I K x a e b f cs' U'. native_material_at E u V r M I K \<and> material_pattern_instance B M x a e b f \<and>
      instantiated_premise_rows E u V B rs qs cs' U' \<and> cs = (s,material_tuple x a e b f)#cs' \<and>
      U = material_variables M \<union> U')"
proof
  assume "instantiated_premise_rows E u V B ((s,r)#rs) qs cs U"
  then show "(\<exists>d p I K t qs' U'. prospective_call_at E u V r d p I K \<and> pattern_instance B p t \<and>
      instantiated_premise_rows E u V B rs qs' cs U' \<and> qs = (s,d,t)#qs' \<and> U = pattern_variables p \<union> U') \<or>
    (\<exists>M I K x a e b f cs' U'. native_material_at E u V r M I K \<and> material_pattern_instance B M x a e b f \<and>
      instantiated_premise_rows E u V B rs qs cs' U' \<and> cs = (s,material_tuple x a e b f)#cs' \<and>
      U = material_variables M \<union> U')"
    by (cases rule: instantiated_premise_rows.cases) fastforce+
qed (auto intro: instantiated_premise_rows.intros)

lemma instantiated_premise_rows_unique:
  assumes single: "single_valued B"
    and first: "instantiated_premise_rows E u V B rs qs cs U"
    and second: "instantiated_premise_rows E u V B rs qs' cs' U'"
  shows "qs = qs' \<and> cs = cs' \<and> U = U'"
  using first second
proof (induction arbitrary: qs' cs' U' rule: instantiated_premise_rows.induct)
  case empty
  from empty.prems show ?case by (cases rule: instantiated_premise_rows.cases) simp_all
next
  case (call r d p I K t rs qs cs U s)
  from call.prems[unfolded instantiated_premise_rows_cons] show ?case
  proof (elim disjE exE conjE)
    fix d' p' I' K' t' qs'' U''
    assume other: "prospective_call_at E u V r d' p' I' K'" "pattern_instance B p' t'"
      "instantiated_premise_rows E u V B rs qs'' cs' U''" "qs' = (s,d',t')#qs''" "U' = pattern_variables p' \<union> U''"
    have same: "d' = d" "p' = p" using prospective_call_unique[OF call.hyps(1) other(1)] by auto
    have instance_eq: "t' = t" using pattern_instance_unique[OF single call.hyps(2)] other(2) same(2) by simp
    have tail: "qs = qs'' \<and> cs = cs' \<and> U = U''" by (rule call.IH[OF other(3)])
    show ?thesis using other same instance_eq tail by auto
  next
    fix M I' K' x a e b f cs'' U''
    assume "native_material_at E u V r M I' K'"
    then show ?thesis using native_call_material_disjoint[OF call.hyps(1)] by blast
  qed
next
  case (material r M I K x a e b f rs qs cs U s)
  from material.prems[unfolded instantiated_premise_rows_cons] show ?case
  proof (elim disjE exE conjE)
    fix d' p' I' K' t' qs'' U''
    assume "prospective_call_at E u V r d' p' I' K'"
    then show ?thesis using native_call_material_disjoint[OF _ material.hyps(1)] by blast
  next
    fix M' I' K' x' a' e' b' f' cs'' U''
    assume other: "native_material_at E u V r M' I' K'" "material_pattern_instance B M' x' a' e' b' f'"
      "instantiated_premise_rows E u V B rs qs' cs'' U''" "cs' = (s,material_tuple x' a' e' b' f')#cs''"
      "U' = material_variables M' \<union> U''"
    have same: "M' = M" using native_material_unique[OF material.hyps(1) other(1)] by auto
    have tuple: "(x,a,e,b,f) = (x',a',e',b',f')"
      using material_pattern_instance_unique[OF single material.hyps(2)] other(2) same by simp
    have tail: "qs = qs' \<and> cs = cs'' \<and> U = U''" by (rule material.IH[OF other(3)])
    show ?thesis using other same tuple tail by auto
  qed
qed

lemma bag_corresponds_rows:
  assumes "mset A = mset B"
  shows "bag_corresponds (data_list_term (map f (map g A))) (data_list_term (map f (map g B)))"
  by (rule bag_corresponds_lists) (simp add: assms)

lemma premise_rows_answers:
  assumes one: "(63,premise_instantiation_argument e u v b r q c w) \<in> positive_meaning premise_rows_system"
    and two: "(63,premise_instantiation_argument e u v b r q2 c2 w2) \<in> positive_meaning premise_rows_system"
  shows "q = q2 \<and> c = c2 \<and> bag_corresponds w w2"
proof -
  obtain E a Vs xs rs qs cs Us where parts: "u = use_data_term a" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = data_list_term (map address_pair_data rs)" "q = call_instance_rows_term qs"
      "c = binding_rows_term cs" "w = data_list_term (map Payload_Term Us)" "environment_value_presents E e"
      "term_bindings_formed (set Vs) (set xs)" "distinct Us" "instantiated_premise_rows E a (set Vs) (set xs) rs qs cs (set Us)"
    using one unfolding premise_rows_exact by (simp only: factor_term.inject) blast
  obtain E' a' Vs' xs' rs' qs' cs' Us' where parts': "u = use_data_term a'" "v = data_list_term (map Payload_Term Vs')"
      "b = binding_rows_term xs'" "r = data_list_term (map address_pair_data rs')" "q2 = call_instance_rows_term qs'"
      "c2 = binding_rows_term cs'" "w2 = data_list_term (map Payload_Term Us')" "environment_value_presents E' e"
      "distinct Us'" "instantiated_premise_rows E' a' (set Vs') (set xs') rs' qs' cs' (set Us')"
    using two unfolding premise_rows_exact by (simp only: factor_term.inject) blast
  have use: "use_data_term a' = use_data_term a" using parts(1) parts'(1) by simp
  have scope: "data_list_term (map Payload_Term Vs') = data_list_term (map Payload_Term Vs)" using parts(2) parts'(2) by simp
  have table: "binding_rows_term xs' = binding_rows_term xs" using parts(3) parts'(3) by simp
  have rows: "data_list_term (map address_pair_data rs') = data_list_term (map address_pair_data rs)"
    using parts(4) parts'(4) by simp
  have same: "a' = a" "Vs' = Vs" "xs' = xs" "rs' = rs" "E' = E"
    using use apply (simp only: inj_eq[OF use_data_term_injective])
    using scope apply (simp only: data_list_term_injective injective_mapped_lists[OF payload_term_inj])
    using table apply (simp only: binding_rows_term_injective)
    using rows apply (simp only: data_list_term_injective injective_mapped_lists[OF address_pair_data_injective])
    using environment_value_presents_unique[OF parts'(8) parts(8)] by simp
  have single: "single_valued (set xs)" using parts(9) by (simp add: term_bindings_formed_def)
  have "qs = qs' \<and> cs = cs' \<and> set Us = set Us'"
    by (rule instantiated_premise_rows_unique[OF single parts(11)]) (use parts'(10) same in simp)
  then show ?thesis using parts parts' by (simp add: bag_corresponds_distinct_payloads)
qed

lemma premise_family_answers:
  assumes one: "(64,premise_instantiation_argument e u v b r q c w) \<in> positive_meaning premise_family_instantiation_system"
    and two: "(64,premise_instantiation_argument e u v b r q2 c2 w2) \<in> positive_meaning premise_family_instantiation_system"
  shows "bag_corresponds q q2 \<and> bag_corresponds c c2 \<and> bag_corresponds w w2"
proof -
  obtain E where source: "environment_value_presents E e" using one by (auto simp: premise_family_instantiation_exact)
  obtain a Vs xs l qs cs Us where parts: "u = use_data_term a" "v = data_list_term (map Payload_Term Vs)"
      "b = binding_rows_term xs" "r = Payload_Term l" "q = call_instance_rows_term qs" "c = binding_rows_term cs"
      "w = data_list_term (map Payload_Term Us)"
    using one by (auto simp: premise_family_instantiation_at_source[OF source])
  obtain qs' cs' Us' where parts': "q2 = call_instance_rows_term qs'" "c2 = binding_rows_term cs'"
      "w2 = data_list_term (map Payload_Term Us')"
    using two by (auto simp: premise_family_instantiation_at_source[OF source])
  have f: "(64,premise_instantiation_argument e (use_data_term a) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term l) (call_instance_rows_term qs) (binding_rows_term cs)
      (data_list_term (map Payload_Term Us))) \<in> positive_meaning premise_family_instantiation_system"
    using one parts by simp
  have s: "(64,premise_instantiation_argument e (use_data_term a) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term l) (call_instance_rows_term qs') (binding_rows_term cs')
      (data_list_term (map Payload_Term Us'))) \<in> positive_meaning premise_family_instantiation_system"
    using two parts parts' by simp
  have "mset qs = mset qs' \<and> mset cs = mset cs' \<and> mset Us = mset Us'"
    by (rule premise_family_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_rows bag_corresponds_mapped)
qed

lemma schema_answers:
  assumes one: "(65,schema_instantiation_argument e u r b t q c) \<in> positive_meaning schema_instantiation_system"
    and two: "(65,schema_instantiation_argument e u r b t2 q2 c2) \<in> positive_meaning schema_instantiation_system"
  shows "t = t2 \<and> bag_corresponds q q2 \<and> bag_corresponds c c2"
proof -
  obtain E where source: "environment_value_presents E e" using one by (auto simp: schema_instantiation_exact)
  obtain a l xs qs cs where parts: "u = use_data_term a" "r = Payload_Term l" "b = binding_rows_term xs"
      "q = call_instance_rows_term qs" "c = binding_rows_term cs"
    using one by (auto simp: schema_instantiation_at_source[OF source])
  obtain qs' cs' where parts': "q2 = call_instance_rows_term qs'" "c2 = binding_rows_term cs'"
    using two by (auto simp: schema_instantiation_at_source[OF source])
  have f: "(65,schema_instantiation_argument e (use_data_term a) (Payload_Term l) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs)) \<in> positive_meaning schema_instantiation_system"
    using one parts by simp
  have s: "(65,schema_instantiation_argument e (use_data_term a) (Payload_Term l) (binding_rows_term xs) t2
      (call_instance_rows_term qs') (binding_rows_term cs')) \<in> positive_meaning schema_instantiation_system"
    using two parts parts' by simp
  have "t = t2 \<and> mset qs = mset qs' \<and> mset cs = mset cs'"
    by (rule schema_instantiation_result_unique[OF source f s])
  then show ?thesis using parts parts' by (simp add: bag_corresponds_rows bag_corresponds_mapped)
qed

section \<open>Each producer discharged at its notion's system\<close>

theorem row_values_producer_discharged:
  "producer_discharged (positive_meaning row_values_system) 59 view_identity row_values_holes
    (schema_instantiation_correspondence 59)"
proof (rule producer_discharged_valuations[OF view_identity_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(59,evaluate_pattern g (decode_finite_pattern (fst view_identity))) \<in> positive_meaning row_values_system"
    and b: "(59,evaluate_pattern g' (decode_finite_pattern (fst view_identity))) \<in> positive_meaning row_values_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd view_identity))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd view_identity)))"
    and i: "i < length row_values_holes"
  have a': "(59,Pair_Term (g 0) (g 1)) \<in> positive_meaning row_values_system"
    using a by (simp add: view_identity_def identity_view_def)
  have b': "(59,Pair_Term (g 0) (g' 1)) \<in> positive_meaning row_values_system"
    using b same by (simp add: view_identity_def identity_view_def)
  obtain xs where rows: "g 0 = pair_list_term xs" "g 1 = data_list_term (map snd xs)"
    using a' by (auto simp: row_values_exact)
  have "g' 1 = g 1" using b' rows by (simp add: row_values_at_rows)
  then show "schema_instantiation_correspondence 59 i (evaluate_pattern g (decode_finite_pattern (row_values_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (row_values_holes ! i)))"
    using i by (simp add: row_values_holes_def schema_instantiation_correspondence_def)
qed

theorem vector_producer_discharged:
  "producer_discharged (positive_meaning vector_instantiation_system) 60 instantiation_view instantiation_holes
    (schema_instantiation_correspondence 60)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(2)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(60,evaluate_pattern g (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning vector_instantiation_system"
    and b: "(60,evaluate_pattern g' (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning vector_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd instantiation_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd instantiation_view)))"
    and i: "i < length instantiation_holes"
  have a': "(60,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8))
      \<in> positive_meaning vector_instantiation_system"
    using a by (simp add: instantiation_view_def)
  have b': "(60,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g' 7) (g' 8))
      \<in> positive_meaning vector_instantiation_system"
    using b same by (simp add: instantiation_view_def)
  have "g 5 = g' 5 \<and> bag_corresponds (g 6) (g' 6) \<and> bag_corresponds (g 7) (g' 7) \<and> bag_corresponds (g 8) (g' 8)"
    by (rule vector_answers[OF a' b'])
  then show "schema_instantiation_correspondence 60 i (evaluate_pattern g (decode_finite_pattern (instantiation_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (instantiation_holes ! i)))"
    using i by (auto simp: instantiation_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem record_producer_discharged:
  "producer_discharged (positive_meaning record_instantiation_system) 61 instantiation_view instantiation_holes
    (schema_instantiation_correspondence 61)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(2)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(61,evaluate_pattern g (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning record_instantiation_system"
    and b: "(61,evaluate_pattern g' (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning record_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd instantiation_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd instantiation_view)))"
    and i: "i < length instantiation_holes"
  have a': "(61,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8))
      \<in> positive_meaning record_instantiation_system"
    using a by (simp add: instantiation_view_def)
  have b': "(61,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g' 7) (g' 8))
      \<in> positive_meaning record_instantiation_system"
    using b same by (simp add: instantiation_view_def)
  have "g 5 = g' 5 \<and> bag_corresponds (g 6) (g' 6) \<and> bag_corresponds (g 7) (g' 7) \<and> bag_corresponds (g 8) (g' 8)"
    by (rule record_answers[OF a' b'])
  then show "schema_instantiation_correspondence 61 i (evaluate_pattern g (decode_finite_pattern (instantiation_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (instantiation_holes ! i)))"
    using i by (auto simp: instantiation_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem record_material_producer_discharged:
  "producer_discharged (positive_meaning record_instantiation_system) 61 record_material_view record_material_holes
    (schema_instantiation_correspondence 61)"
proof (rule producer_discharged_valuations[OF record_material_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(61,evaluate_pattern g (decode_finite_pattern (fst record_material_view))) \<in> positive_meaning record_instantiation_system"
    and b: "(61,evaluate_pattern g' (decode_finite_pattern (fst record_material_view))) \<in> positive_meaning record_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd record_material_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd record_material_view)))"
    and i: "i < length record_material_holes"
  have a': "(61,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (data_list_term [g 5,g 6,g 7,g 8,g 9])
      (g 10) (g 11) (g 12)) \<in> positive_meaning record_instantiation_system"
    using a by (simp add: record_material_view_def five_fields_list_def)
  have b': "(61,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (data_list_term [g' 5,g' 6,g' 7,g' 8,g' 9])
      (g' 10) (g' 11) (g' 12)) \<in> positive_meaning record_instantiation_system"
    using b same by (simp add: record_material_view_def five_fields_list_def)
  have "data_list_term [g 5,g 6,g 7,g 8,g 9] = data_list_term [g' 5,g' 6,g' 7,g' 8,g' 9] \<and>
      bag_corresponds (g 10) (g' 10) \<and> bag_corresponds (g 11) (g' 11) \<and> bag_corresponds (g 12) (g' 12)"
    by (rule record_answers[OF a' b'])
  then show "schema_instantiation_correspondence 61 i (evaluate_pattern g (decode_finite_pattern (record_material_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (record_material_holes ! i)))"
    using i by (auto simp: record_material_holes_def five_fields_tuple_def schema_instantiation_correspondence_def
      numeral_eq_Suc less_Suc_eq)
qed

theorem material_producer_discharged:
  "producer_discharged (positive_meaning material_instantiation_system) 62 instantiation_view instantiation_holes
    (schema_instantiation_correspondence 62)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(2)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(62,evaluate_pattern g (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning material_instantiation_system"
    and b: "(62,evaluate_pattern g' (decode_finite_pattern (fst instantiation_view))) \<in> positive_meaning material_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd instantiation_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd instantiation_view)))"
    and i: "i < length instantiation_holes"
  have a': "(62,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g 5) (g 6) (g 7) (g 8))
      \<in> positive_meaning material_instantiation_system"
    using a by (simp add: instantiation_view_def)
  have b': "(62,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2) (g' 5) (g' 6) (g' 7) (g' 8))
      \<in> positive_meaning material_instantiation_system"
    using b same by (simp add: instantiation_view_def)
  have "g 5 = g' 5 \<and> bag_corresponds (g 6) (g' 6) \<and> bag_corresponds (g 7) (g' 7) \<and> bag_corresponds (g 8) (g' 8)"
    by (rule material_answers[OF a' b'])
  then show "schema_instantiation_correspondence 62 i (evaluate_pattern g (decode_finite_pattern (instantiation_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (instantiation_holes ! i)))"
    using i by (auto simp: instantiation_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem premise_rows_producer_discharged:
  "producer_discharged (positive_meaning premise_rows_system) 63 premise_rows_view premise_rows_holes
    (schema_instantiation_correspondence 63)"
proof (rule producer_discharged_valuations[OF premise_views_formed(1)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(63,evaluate_pattern g (decode_finite_pattern (fst premise_rows_view))) \<in> positive_meaning premise_rows_system"
    and b: "(63,evaluate_pattern g' (decode_finite_pattern (fst premise_rows_view))) \<in> positive_meaning premise_rows_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd premise_rows_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd premise_rows_view)))"
    and i: "i < length premise_rows_holes"
  have a': "(63,premise_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7))
      \<in> positive_meaning premise_rows_system"
    using a by (simp add: premise_rows_view_def)
  have b': "(63,premise_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g' 5) (g' 6) (g' 7))
      \<in> positive_meaning premise_rows_system"
    using b same by (simp add: premise_rows_view_def)
  have "g 5 = g' 5 \<and> g 6 = g' 6 \<and> bag_corresponds (g 7) (g' 7)" by (rule premise_rows_answers[OF a' b'])
  then show "schema_instantiation_correspondence 63 i (evaluate_pattern g (decode_finite_pattern (premise_rows_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (premise_rows_holes ! i)))"
    using i by (auto simp: premise_rows_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem premise_family_producer_discharged:
  "producer_discharged (positive_meaning premise_family_instantiation_system) 64 premise_rows_view premise_rows_holes
    (schema_instantiation_correspondence 64)"
proof (rule producer_discharged_valuations[OF premise_views_formed(1)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(64,evaluate_pattern g (decode_finite_pattern (fst premise_rows_view)))
      \<in> positive_meaning premise_family_instantiation_system"
    and b: "(64,evaluate_pattern g' (decode_finite_pattern (fst premise_rows_view)))
      \<in> positive_meaning premise_family_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd premise_rows_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd premise_rows_view)))"
    and i: "i < length premise_rows_holes"
  have a': "(64,premise_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7))
      \<in> positive_meaning premise_family_instantiation_system"
    using a by (simp add: premise_rows_view_def)
  have b': "(64,premise_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g' 5) (g' 6) (g' 7))
      \<in> positive_meaning premise_family_instantiation_system"
    using b same by (simp add: premise_rows_view_def)
  have "bag_corresponds (g 5) (g' 5) \<and> bag_corresponds (g 6) (g' 6) \<and> bag_corresponds (g 7) (g' 7)"
    by (rule premise_family_answers[OF a' b'])
  then show "schema_instantiation_correspondence 64 i (evaluate_pattern g (decode_finite_pattern (premise_rows_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (premise_rows_holes ! i)))"
    using i by (auto simp: premise_rows_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

theorem schema_producer_discharged:
  "producer_discharged (positive_meaning schema_instantiation_system) 65 schema_view schema_holes
    (schema_instantiation_correspondence 65)"
proof (rule producer_discharged_valuations[OF premise_views_formed(2)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(65,evaluate_pattern g (decode_finite_pattern (fst schema_view))) \<in> positive_meaning schema_instantiation_system"
    and b: "(65,evaluate_pattern g' (decode_finite_pattern (fst schema_view))) \<in> positive_meaning schema_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd schema_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd schema_view)))"
    and i: "i < length schema_holes"
  have a': "(65,schema_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
      \<in> positive_meaning schema_instantiation_system"
    using a by (simp add: schema_view_def)
  have b': "(65,schema_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g' 4) (g' 5) (g' 6))
      \<in> positive_meaning schema_instantiation_system"
    using b same by (simp add: schema_view_def)
  have "g 4 = g' 4 \<and> bag_corresponds (g 5) (g' 5) \<and> bag_corresponds (g 6) (g' 6)" by (rule schema_answers[OF a' b'])
  then show "schema_instantiation_correspondence 65 i (evaluate_pattern g (decode_finite_pattern (schema_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (schema_holes ! i)))"
    using i by (auto simp: schema_holes_def schema_instantiation_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

text \<open>The whole output of each view, its holes' product: the form a socket's producer takes.\<close>

lemma schema_instantiation_output_correspondences:
  "map (schema_instantiation_correspondence 60) [0..<length instantiation_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  "map (schema_instantiation_correspondence 61) [0..<length instantiation_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  "map (schema_instantiation_correspondence 61) [0..<length record_material_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  "map (schema_instantiation_correspondence 62) [0..<length instantiation_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  "map (schema_instantiation_correspondence 63) [0..<length premise_rows_holes] = [(=),(=),bag_corresponds]"
  "map (schema_instantiation_correspondence 64) [0..<length premise_rows_holes] =
    [bag_corresponds,bag_corresponds,bag_corresponds]"
  by (simp_all add: instantiation_holes_def record_material_holes_def premise_rows_holes_def
    schema_instantiation_correspondence_def upt_rec)

lemmas schema_instantiation_output_producers =
  producer_discharged_tuple[OF vector_producer_discharged instantiation_views_holes(3),
    unfolded schema_instantiation_output_correspondences(1)]
  producer_discharged_tuple[OF record_producer_discharged instantiation_views_holes(3),
    unfolded schema_instantiation_output_correspondences(2)]
  producer_discharged_tuple[OF record_material_producer_discharged schema_instantiation_views_holes(2),
    unfolded schema_instantiation_output_correspondences(3)]
  producer_discharged_tuple[OF material_producer_discharged instantiation_views_holes(3),
    unfolded schema_instantiation_output_correspondences(4)]
  producer_discharged_tuple[OF premise_rows_producer_discharged premise_views_holes(1),
    unfolded schema_instantiation_output_correspondences(5)]
  producer_discharged_tuple[OF premise_family_producer_discharged premise_views_holes(1),
    unfolded schema_instantiation_output_correspondences(6)]

section \<open>Material instantiation at its tuple view\<close>

text \<open>
  Material instantiation (62) is also read at @{text material_view}, its term the tuple of the five material
  fields: every answer's term is such a tuple, and the premise rows' material clause reads it there.
\<close>

definition material_view :: "nat resolution_view" where
  "material_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair five_fields_tuple (Finite_Pattern_Pair (Finite_Variable 10)
          (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12)))))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    Finite_Pattern_Pair five_fields_tuple (Finite_Pattern_Pair (Finite_Variable 10)
      (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12))))"

lemma material_view_formed: "view_formed material_view"
  by (auto simp: view_formed_def material_view_def five_fields_tuple_def fset_eq_iff)

lemma material_view_holes: "view_holes material_view record_material_holes"
  by (simp add: view_holes_def material_view_def record_material_holes_def)

theorem material_tuple_producer_discharged:
  "producer_discharged (positive_meaning material_instantiation_system) 62 material_view record_material_holes
    (schema_instantiation_correspondence 62)"
proof (rule producer_discharged_valuations[OF material_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(62,evaluate_pattern g (decode_finite_pattern (fst material_view))) \<in> positive_meaning material_instantiation_system"
    and b: "(62,evaluate_pattern g' (decode_finite_pattern (fst material_view))) \<in> positive_meaning material_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd material_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd material_view)))"
    and i: "i < length record_material_holes"
  have a': "(62,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2)
      (Pair_Term (g 5) (Pair_Term (g 6) (Pair_Term (g 7) (Pair_Term (g 8) (g 9))))) (g 10) (g 11) (g 12))
      \<in> positive_meaning material_instantiation_system"
    using a by (simp add: material_view_def five_fields_tuple_def)
  have b': "(62,pattern_instantiation_argument (g 0) (g 1) (g 3) (g 4) (g 2)
      (Pair_Term (g' 5) (Pair_Term (g' 6) (Pair_Term (g' 7) (Pair_Term (g' 8) (g' 9))))) (g' 10) (g' 11) (g' 12))
      \<in> positive_meaning material_instantiation_system"
    using b same by (simp add: material_view_def five_fields_tuple_def)
  have "Pair_Term (g 5) (Pair_Term (g 6) (Pair_Term (g 7) (Pair_Term (g 8) (g 9)))) =
      Pair_Term (g' 5) (Pair_Term (g' 6) (Pair_Term (g' 7) (Pair_Term (g' 8) (g' 9)))) \<and>
      bag_corresponds (g 10) (g' 10) \<and> bag_corresponds (g 11) (g' 11) \<and> bag_corresponds (g 12) (g' 12)"
    by (rule material_answers[OF a' b'])
  then show "schema_instantiation_correspondence 62 i (evaluate_pattern g (decode_finite_pattern (record_material_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (record_material_holes ! i)))"
    using i by (auto simp: record_material_holes_def five_fields_tuple_def schema_instantiation_correspondence_def
      numeral_eq_Suc less_Suc_eq)
qed

lemma material_output_correspondence:
  "map (schema_instantiation_correspondence 62) [0..<length record_material_holes] =
    [(=),bag_corresponds,bag_corresponds,bag_corresponds]"
  by (simp add: record_material_holes_def schema_instantiation_correspondence_def upt_rec)

lemmas material_output_producer =
  producer_discharged_tuple[OF material_tuple_producer_discharged material_view_holes,
    unfolded material_output_correspondence]

section \<open>The carrier 63\<close>

text \<open>
  Premise rows (63) carry their rows to their outputs at @{const premise_rows_view}: the source, scope and table
  fixed and the rows replaced by a bag of them, an answer exists whose call rows, material rows and used variables
  are bags of the old ones. The rows are read one by one, so a row list splits where it is cut and is read in any
  order.
\<close>

lemma instantiated_premise_rows_split:
  assumes "instantiated_premise_rows E u V B (rs @ ts) qs cs U"
  shows "\<exists>qs1 qs2 cs1 cs2 U1 U2. instantiated_premise_rows E u V B rs qs1 cs1 U1 \<and>
    instantiated_premise_rows E u V B ts qs2 cs2 U2 \<and> qs = qs1 @ qs2 \<and> cs = cs1 @ cs2 \<and> U = U1 \<union> U2"
  using assms
proof (induction rs arbitrary: qs cs U)
  case Nil
  then show ?case using instantiated_premise_rows.empty by fastforce
next
  case (Cons x rs)
  obtain s r where x: "x = (s,r)" by (cases x)
  from Cons.prems[unfolded x append_Cons instantiated_premise_rows_cons] show ?case
  proof (elim disjE exE conjE)
    fix d p I K t qs' U'
    assume c: "prospective_call_at E u V r d p I K" "pattern_instance B p t"
      "instantiated_premise_rows E u V B (rs @ ts) qs' cs U'" "qs = (s,d,t)#qs'" "U = pattern_variables p \<union> U'"
    obtain qs1 qs2 cs1 cs2 U1 U2 where split: "instantiated_premise_rows E u V B rs qs1 cs1 U1"
        "instantiated_premise_rows E u V B ts qs2 cs2 U2" "qs' = qs1 @ qs2" "cs = cs1 @ cs2" "U' = U1 \<union> U2"
      using Cons.IH[OF c(3)] by blast
    have head: "instantiated_premise_rows E u V B (x#rs) ((s,d,t)#qs1) cs1 (pattern_variables p \<union> U1)"
      unfolding x by (rule instantiated_premise_rows.call[OF c(1,2) split(1)])
    show ?thesis
      by (rule exI[of _ "(s,d,t)#qs1"], rule exI[of _ qs2], rule exI[of _ cs1], rule exI[of _ cs2],
        rule exI[of _ "pattern_variables p \<union> U1"], rule exI[of _ U2]) (use head split c in auto)
  next
    fix M I K a1 a2 a3 a4 a5 cs' U'
    assume c: "native_material_at E u V r M I K" "material_pattern_instance B M a1 a2 a3 a4 a5"
      "instantiated_premise_rows E u V B (rs @ ts) qs cs' U'" "cs = (s,material_tuple a1 a2 a3 a4 a5)#cs'"
      "U = material_variables M \<union> U'"
    obtain qs1 qs2 cs1 cs2 U1 U2 where split: "instantiated_premise_rows E u V B rs qs1 cs1 U1"
        "instantiated_premise_rows E u V B ts qs2 cs2 U2" "qs = qs1 @ qs2" "cs' = cs1 @ cs2" "U' = U1 \<union> U2"
      using Cons.IH[OF c(3)] by blast
    have head: "instantiated_premise_rows E u V B (x#rs) qs1 ((s,material_tuple a1 a2 a3 a4 a5)#cs1)
        (material_variables M \<union> U1)"
      unfolding x by (rule instantiated_premise_rows.material[OF c(1,2) split(1)])
    show ?thesis
      by (rule exI[of _ qs1], rule exI[of _ qs2], rule exI[of _ "(s,material_tuple a1 a2 a3 a4 a5)#cs1"],
        rule exI[of _ cs2], rule exI[of _ "material_variables M \<union> U1"], rule exI[of _ U2]) (use head split c in auto)
  qed
qed

lemma instantiated_premise_rows_perm:
  assumes read: "instantiated_premise_rows E u V B rs qs cs U" and same: "mset ts = mset rs"
  shows "\<exists>qs' cs'. instantiated_premise_rows E u V B ts qs' cs' U \<and> mset qs' = mset qs \<and> mset cs' = mset cs"
  using same read
proof (induction ts arbitrary: rs qs cs U)
  case Nil
  then have "rs = []" by simp
  then have "qs = [] \<and> cs = [] \<and> U = {}" using Nil.prems(2) by (auto elim: instantiated_premise_rows.cases)
  then show ?case using instantiated_premise_rows.empty by auto
next
  case (Cons x ts)
  have "x \<in> set rs" using mset_eq_setD[OF Cons.prems(1)] by auto
  then obtain pre post where rs: "rs = pre @ x # post" by (meson split_list)
  have whole: "instantiated_premise_rows E u V B (pre @ x # post) qs cs U" using Cons.prems(2) rs by simp
  obtain qs1 qs2 cs1 cs2 U1 U2 where first: "instantiated_premise_rows E u V B pre qs1 cs1 U1"
      "instantiated_premise_rows E u V B (x # post) qs2 cs2 U2" "qs = qs1 @ qs2" "cs = cs1 @ cs2" "U = U1 \<union> U2"
    using instantiated_premise_rows_split[OF whole] by blast
  have single: "instantiated_premise_rows E u V B ([x] @ post) qs2 cs2 U2" using first(2) by simp
  obtain qx qp cx cp Ux Up where second: "instantiated_premise_rows E u V B [x] qx cx Ux"
      "instantiated_premise_rows E u V B post qp cp Up" "qs2 = qx @ qp" "cs2 = cx @ cp" "U2 = Ux \<union> Up"
    using instantiated_premise_rows_split[OF single] by blast
  have rest: "instantiated_premise_rows E u V B (pre @ post) (qs1 @ qp) (cs1 @ cp) (U1 \<union> Up)"
    by (rule instantiated_premise_rows_append[OF first(1) second(2)])
  have "mset ts = mset (pre @ post)" using Cons.prems(1) rs by simp
  then obtain qs' cs' where moved: "instantiated_premise_rows E u V B ts qs' cs' (U1 \<union> Up)"
      "mset qs' = mset (qs1 @ qp)" "mset cs' = mset (cs1 @ cp)"
    using Cons.IH rest by blast
  have "instantiated_premise_rows E u V B ([x] @ ts) (qx @ qs') (cx @ cs') (Ux \<union> (U1 \<union> Up))"
    by (rule instantiated_premise_rows_append[OF second(1) moved(1)])
  then show ?case using first second moved
    by (intro exI[of _ "qx @ qs'"] exI[of _ "cx @ cs'"]) (auto simp: Un_ac add_ac)
qed

theorem premise_rows_carrier_discharged:
  "carrier_discharged (positive_meaning premise_rows_system) 63 premise_rows_view
    (tuple_corresponds [(=),bag_corresponds]) (tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds])"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(63,a) \<in> positive_meaning premise_rows_system"
    and va: "resolution_view_term premise_rows_view a = Some (x,y)"
    and cx: "tuple_corresponds [(=),bag_corresponds] x x'"
  obtain h :: "nat \<Rightarrow> factor_term" where
      h: "a = premise_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)"
      "x = Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))) (h 4)"
      "y = Pair_Term (h 5) (Pair_Term (h 6) (h 7))"
    using va resolution_view_term_valuation[OF premise_views_formed(1)[unfolded premise_rows_view_def]]
    by (auto simp: premise_rows_view_def)
  obtain r' where x': "x' = Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))) r'"
      and r': "bag_corresponds (h 4) r'"
    using cx h(2) by auto
  obtain E u0 Vs xs rs qs cs Us where parts: "h 1 = use_data_term u0" "h 2 = data_list_term (map Payload_Term Vs)"
      "h 3 = binding_rows_term xs" "h 4 = data_list_term (map address_pair_data rs)" "h 5 = call_instance_rows_term qs"
      "h 6 = binding_rows_term cs" "h 7 = data_list_term (map Payload_Term Us)" "environment_value_presents E (h 0)"
    using holds h(1) unfolding premise_rows_exact by (simp only: factor_term.inject) blast
  have old: "(63,premise_instantiation_argument (h 0) (use_data_term u0) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (data_list_term (map address_pair_data rs)) (call_instance_rows_term qs)
      (binding_rows_term cs) (data_list_term (map Payload_Term Us))) \<in> positive_meaning premise_rows_system"
    using holds h(1) parts by simp
  have conds: "distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct Us \<and> (\<forall>s\<in>rel_dom (set rs). octets_formed s) \<and>
      instantiated_premise_rows E u0 (set Vs) (set xs) rs qs cs (set Us)"
    using old[unfolded premise_rows_on_values[OF parts(8)]] by blast
  obtain zs where zs: "r' = data_list_term zs" "mset zs = mset (map address_pair_data rs)"
    using r' parts(4) bag_corresponds_list by metis
  have "\<exists>rs'. zs = map address_pair_data rs'" unfolding ex_map_conv using mset_eq_setD[OF zs(2)] by auto
  then obtain rs' where rs': "zs = map address_pair_data rs'" by blast
  have perm: "mset rs' = mset rs" using zs(2) rs' injective_mapped_multisets[OF address_pair_data_injective] by simp
  obtain qs' cs' where moved: "instantiated_premise_rows E u0 (set Vs) (set xs) rs' qs' cs' (set Us)"
      "mset qs' = mset qs" "mset cs' = mset cs"
    using instantiated_premise_rows_perm[OF _ perm] conds by (meson conjunct2)
  have keys: "rel_dom (set rs') = rel_dom (set rs)" using mset_eq_setD[OF perm] by simp
  let ?b = "premise_instantiation_argument (h 0) (use_data_term u0) (data_list_term (map Payload_Term Vs))
    (binding_rows_term xs) (data_list_term (map address_pair_data rs')) (call_instance_rows_term qs')
    (binding_rows_term cs') (data_list_term (map Payload_Term Us))"
  have "(63,?b) \<in> positive_meaning premise_rows_system"
    unfolding premise_rows_on_values[OF parts(8)] using conds moved(1) keys by simp
  moreover have "resolution_view_term premise_rows_view ?b = Some (x',Pair_Term (call_instance_rows_term qs')
      (Pair_Term (binding_rows_term cs') (data_list_term (map Payload_Term Us))))"
    using resolution_view_term_valuation[OF premise_views_formed(1)[unfolded premise_rows_view_def]] x' parts zs rs'
    by (simp add: premise_rows_view_def)
      (intro exI[of _ "h(4 := r', 5 := call_instance_rows_term qs', 6 := binding_rows_term cs')"], simp)
  moreover have "tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds] y
      (Pair_Term (call_instance_rows_term qs') (Pair_Term (binding_rows_term cs') (data_list_term (map Payload_Term Us))))"
    using h(3) parts moved(2,3) by (simp add: bag_corresponds_rows bag_corresponds_mapped)
  ultimately show "\<exists>b y'. (63,b) \<in> positive_meaning premise_rows_system \<and>
      resolution_view_term premise_rows_view b = Some (x',y') \<and>
      tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds] y y'" by blast
qed

section \<open>The producers and carriers read at the socket systems\<close>

text \<open>
  A socket's producer and its clause's carriers are discharged at their notions' systems and read at the clause's
  system through the components' meaning equations (@{text producer_discharged_site},
  @{text carrier_discharged_site}). The family's rows (32) at R6's view correspond as two enumerations of one set of
  rows, so as bags.
\<close>

lemma family_rows_bag_corresponds:
  assumes "given_correspondence 32 x y"
  shows "bag_corresponds x y"
proof -
  obtain A where presents: "family_rows_presents A x" "family_rows_presents A y"
    using assms by (auto simp: given_correspondence_def presentation_transport_def)
  obtain xs where left: "distinct xs" "set xs = A" "x = data_list_term (map address_pair_data xs)"
    using presents(1) by (auto simp: data_collection_presents_def list_all2_function)
  obtain ys where right: "distinct ys" "set ys = A" "y = data_list_term (map address_pair_data ys)"
    using presents(2) by (auto simp: data_collection_presents_def list_all2_function)
  have "mset xs = mset ys" using left right set_eq_iff_mset_eq_distinct by metis
  then show ?thesis using left(3) right(3) by (simp add: bag_corresponds_mapped)
qed

lemma vector_socket_producer:
  "producer_discharged (positive_meaning vector_instantiation_system) 55 instantiation_view [snd (snd instantiation_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  using instantiation_output_producers(2) by (simp add: producer_discharged_site[OF vector_instantiation_components(1)])

lemma record_socket_producer:
  "producer_discharged (positive_meaning record_instantiation_system) 60 instantiation_view [snd (snd instantiation_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  using schema_instantiation_output_producers(1)
  by (simp add: producer_discharged_site[OF record_instantiation_components(5)])

lemma material_socket_producer:
  "producer_discharged (positive_meaning material_instantiation_system) 61 record_material_view
    [snd (snd record_material_view)] (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  using schema_instantiation_output_producers(3)
  by (simp add: producer_discharged_site[OF material_instantiation_previous_entry])

lemma premise_rows_socket_producers:
  "producer_discharged (positive_meaning premise_rows_system) 57 prospective_view [snd (snd prospective_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  "producer_discharged (positive_meaning premise_rows_system) 62 material_view [snd (snd material_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  using instantiation_output_producers(3) material_output_producer
  by (simp_all add: producer_discharged_site[OF premise_rows_components(1)]
    producer_discharged_site[OF premise_rows_components(2)])

lemma family_socket_producer:
  "producer_discharged (positive_meaning premise_family_instantiation_system) 32 view_identity
    [snd (snd view_identity)] (\<lambda>_. given_correspondence 32)"
  using family_producer_discharged
  by (simp add: producer_discharged_site[OF premise_family_instantiation_components(2)] view_identity_def
    identity_view_def view_output_def)

lemma family_body_producer:
  "producer_discharged (positive_meaning premise_family_instantiation_system) 63 premise_rows_view
    [snd (snd premise_rows_view)] (\<lambda>_. tuple_corresponds [(=),(=),bag_corresponds])"
  using schema_instantiation_output_producers(5)
  by (simp add: producer_discharged_site[OF premise_family_instantiation_components(3)])

lemma schema_socket_producers:
  "producer_discharged (positive_meaning schema_instantiation_system) 55 instantiation_view [snd (snd instantiation_view)]
    (\<lambda>_. tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds])"
  "producer_discharged (positive_meaning schema_instantiation_system) 64 premise_rows_view [snd (snd premise_rows_view)]
    (\<lambda>_. tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds])"
  using instantiation_output_producers(2) schema_instantiation_output_producers(6)
  by (simp_all add: producer_discharged_site[OF schema_instantiation_components(4)]
    producer_discharged_site[OF schema_instantiation_components(5)])

lemma vector_carriers:
  "carrier_discharged (positive_meaning vector_instantiation_system) 46 join_view bag_pair bag_corresponds"
  "carrier_discharged (positive_meaning vector_instantiation_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  "carrier_discharged (positive_meaning vector_instantiation_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  using append_carrier_discharged comparison_consumer_carrier union_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF vector_instantiation_components(3)]
    carrier_discharged_site[OF vector_instantiation_components(4)]
    carrier_discharged_site[OF vector_instantiation_components(5)])

lemma record_carriers:
  "carrier_discharged (positive_meaning record_instantiation_system) 46 join_view bag_pair bag_corresponds"
  "carrier_discharged (positive_meaning record_instantiation_system) 6 (consumer_carrier_view view_identity) bag_pair (=)"
  "carrier_discharged (positive_meaning record_instantiation_system) 49 (consumer_carrier_view view_identity) bag_pair (=)"
  using append_carrier_discharged comparison_consumer_carrier disjoint_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF record_instantiation_components(6)]
    carrier_discharged_site[OF record_instantiation_components(7)]
    carrier_discharged_site[OF record_instantiation_components(8)])

lemma premise_rows_carriers:
  "carrier_discharged (positive_meaning premise_rows_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  using union_consumer_carrier by (simp add: carrier_discharged_site[OF premise_rows_components(4)])

lemma premise_family_carrier:
  "carrier_discharged (positive_meaning premise_family_instantiation_system) 63 premise_rows_view
    (tuple_corresponds [(=),bag_corresponds]) (tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds])"
  using premise_rows_carrier_discharged
  by (simp add: carrier_discharged_site[OF premise_family_instantiation_components(3)])

lemma schema_carriers:
  "carrier_discharged (positive_meaning schema_instantiation_system) 48 (consumer_carrier_view join_view)
    (tuple_corresponds [bag_pair,bag_corresponds]) (=)"
  "carrier_discharged (positive_meaning schema_instantiation_system) 49 (consumer_carrier_view view_identity) bag_pair (=)"
  using union_consumer_carrier disjoint_consumer_carrier
  by (simp_all add: carrier_discharged_site[OF schema_instantiation_components(6)]
    carrier_discharged_site[OF schema_instantiation_components(7)])

section \<open>The free sockets, each discharged along its clause's carriers\<close>

text \<open>
  Each clause of 60–65 is written as a finite value, proved equal to the installed schema. A socket's carried
  variables are derived from the clause (@{const carried_variables}); its carriers are the clause's premises that
  take them: concatenation (46), bag comparison (6), the union at its inputs (48), payload disjointness (49) and,
  at the family's rows, the premise rows (63).
\<close>

definition vector_cons_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "vector_cons_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10)),
    finite_schema_premises = {|(0,55,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 6) (Pattern_Variable 11) (Pattern_Variable 13) (Pattern_Variable 15))),
      (1,60,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 16))),
      (2,46,finite_pattern_of (collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 17))),
      (3,6,finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9))),
      (4,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 10))),
      (5,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 8))),
      (6,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10))),
      (7,1,finite_pattern_of (Pattern_Variable 8))|},
    finite_schema_materials = {||}\<rparr>"

lemma vector_cons_socket_decoded: "decode_finite_schema vector_cons_socket_schema = vector_instantiation_cons_schema"
  by (simp add: vector_cons_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def vector_instantiation_cons_schema_def)

lemma vector_cons_socket_functional: "finite_relation_functional (finite_schema_premises vector_cons_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def vector_cons_socket_schema_def)

lemma vector_cons_socket_premise:
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 0 = Some (55,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 6) (Pattern_Variable 11) (Pattern_Variable 13) (Pattern_Variable 15)))"
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 1 = Some (60,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 16)))"
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 2 = Some (46,finite_pattern_of (collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 17)))"
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 3 = Some (6,finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9)))"
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 4 = Some (48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 10)))"
  "finite_relation_option (finite_schema_premises vector_cons_socket_schema) 5 = Some (48,finite_pattern_of (collection_join_pattern (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 8)))"
  by ((rule finite_relation_option_at[OF vector_cons_socket_functional], simp add: vector_cons_socket_schema_def)+)

lemmas vector_cons_socket_premise_one = vector_cons_socket_premise[unfolded One_nat_def]

lemmas vector_cons_socket_simps = vector_cons_socket_premise vector_cons_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition record_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "record_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 9))),
      (1,34,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 4)) (Pattern_Variable 10))),
      (2,51,finite_pattern_of (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11))),
      (3,59,finite_pattern_of (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 12))),
      (4,60,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 12) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 13) (Pattern_Variable 8))),
      (5,46,finite_pattern_of (collection_join_pattern (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 11)) (Pattern_Variable 13) (Pattern_Variable 14))),
      (6,6,finite_pattern_of (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 7))),
      (7,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8))),
      (8,49,finite_pattern_of (Pattern_Pair (Pattern_Variable 7) data_z))|},
    finite_schema_materials = {||}\<rparr>"

lemma record_socket_decoded: "decode_finite_schema record_socket_schema = record_instantiation_schema"
  by (simp add: record_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def record_instantiation_schema_def)

lemma record_socket_functional: "finite_relation_functional (finite_schema_premises record_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def record_socket_schema_def)

lemma record_socket_premise:
  "finite_relation_option (finite_schema_premises record_socket_schema) 4 = Some (60,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 12) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 13) (Pattern_Variable 8)))"
  "finite_relation_option (finite_schema_premises record_socket_schema) 5 = Some (46,finite_pattern_of (collection_join_pattern (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 11)) (Pattern_Variable 13) (Pattern_Variable 14)))"
  "finite_relation_option (finite_schema_premises record_socket_schema) 6 = Some (6,finite_pattern_of (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 7)))"
  "finite_relation_option (finite_schema_premises record_socket_schema) 7 = Some (49,finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))"
  by ((rule finite_relation_option_at[OF record_socket_functional], simp add: record_socket_schema_def)+)

lemmas record_socket_premise_one = record_socket_premise[unfolded One_nat_def]

lemmas record_socket_simps = record_socket_premise record_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition material_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "material_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (material_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)),
    finite_schema_premises = {|(0,61,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (data_list_pattern [(Pattern_Variable 5),(Pattern_Variable 6),(Pattern_Variable 7),(Pattern_Variable 8),(Pattern_Variable 9)]) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)))|},
    finite_schema_materials = {||}\<rparr>"

lemma material_socket_decoded: "decode_finite_schema material_socket_schema = material_instantiation_schema"
  by (simp add: material_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def material_instantiation_schema_def)

lemma material_socket_functional: "finite_relation_functional (finite_schema_premises material_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def material_socket_schema_def)

lemma material_socket_premise:
  "finite_relation_option (finite_schema_premises material_socket_schema) 0 = Some (61,finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (data_list_pattern [(Pattern_Variable 5),(Pattern_Variable 6),(Pattern_Variable 7),(Pattern_Variable 8),(Pattern_Variable 9)]) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)))"
  by ((rule finite_relation_option_at[OF material_socket_functional], simp add: material_socket_schema_def)+)

lemmas material_socket_premise_one = material_socket_premise[unfolded One_nat_def]

lemmas material_socket_simps = material_socket_premise material_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition premise_call_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "premise_call_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8))) (Pattern_Variable 9)) (Pattern_Variable 10) (Pattern_Variable 11)),
    finite_schema_premises = {|(0,57,finite_pattern_of (prospective_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 15))),
      (1,63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 13))),
      (2,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 11))),
      (3,1,finite_pattern_of (Pattern_Variable 11)),
      (4,1,finite_pattern_of (data_list_pattern [(Pattern_Variable 4)]))|},
    finite_schema_materials = {||}\<rparr>"

lemma premise_call_socket_decoded: "decode_finite_schema premise_call_socket_schema = premise_rows_call_schema"
  by (simp add: premise_call_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def premise_rows_call_schema_def)

lemma premise_call_socket_functional: "finite_relation_functional (finite_schema_premises premise_call_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def premise_call_socket_schema_def)

lemma premise_call_socket_premise:
  "finite_relation_option (finite_schema_premises premise_call_socket_schema) 0 = Some (57,finite_pattern_of (prospective_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 15)))"
  "finite_relation_option (finite_schema_premises premise_call_socket_schema) 1 = Some (63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 13)))"
  "finite_relation_option (finite_schema_premises premise_call_socket_schema) 2 = Some (48,finite_pattern_of (collection_join_pattern (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 11)))"
  by ((rule finite_relation_option_at[OF premise_call_socket_functional], simp add: premise_call_socket_schema_def)+)

lemmas premise_call_socket_premise_one = premise_call_socket_premise[unfolded One_nat_def]

lemmas premise_call_socket_simps = premise_call_socket_premise premise_call_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition premise_material_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "premise_material_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6)) (Pattern_Variable 7) (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 10) (Pattern_Pair (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14)))))) (Pattern_Variable 8)) (Pattern_Variable 9)),
    finite_schema_premises = {|(0,62,finite_pattern_of (material_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 17) (Pattern_Variable 18))),
      (1,63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 16))),
      (2,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 9))),
      (3,1,finite_pattern_of (Pattern_Variable 9)),
      (4,1,finite_pattern_of (data_list_pattern [(Pattern_Variable 4)]))|},
    finite_schema_materials = {||}\<rparr>"

lemma premise_material_socket_decoded: "decode_finite_schema premise_material_socket_schema = premise_rows_material_schema"
  by (simp add: premise_material_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def premise_rows_material_schema_def)

lemma premise_material_socket_functional: "finite_relation_functional (finite_schema_premises premise_material_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def premise_material_socket_schema_def)

lemma premise_material_socket_premise:
  "finite_relation_option (finite_schema_premises premise_material_socket_schema) 0 = Some (62,finite_pattern_of (material_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 17) (Pattern_Variable 18)))"
  "finite_relation_option (finite_schema_premises premise_material_socket_schema) 1 = Some (63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 16)))"
  "finite_relation_option (finite_schema_premises premise_material_socket_schema) 2 = Some (48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 9)))"
  by ((rule finite_relation_option_at[OF premise_material_socket_functional], simp add: premise_material_socket_schema_def)+)

lemmas premise_material_socket_premise_one = premise_material_socket_premise[unfolded One_nat_def]

lemmas premise_material_socket_simps = premise_material_socket_premise premise_material_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition premise_family_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "premise_family_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 8))),
      (1,32,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)) (Pattern_Variable 9))),
      (2,63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 9) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)))|},
    finite_schema_materials = {||}\<rparr>"

lemma premise_family_socket_decoded: "decode_finite_schema premise_family_socket_schema = premise_family_instantiation_schema"
  by (simp add: premise_family_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def premise_family_instantiation_schema_def)

lemma premise_family_socket_functional: "finite_relation_functional (finite_schema_premises premise_family_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def premise_family_socket_schema_def)

lemma premise_family_socket_premise:
  "finite_relation_option (finite_schema_premises premise_family_socket_schema) 1 = Some (32,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)) (Pattern_Variable 9)))"
  "finite_relation_option (finite_schema_premises premise_family_socket_schema) 2 = Some (63,finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 9) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)))"
  by ((rule finite_relation_option_at[OF premise_family_socket_functional], simp add: premise_family_socket_schema_def)+)

lemmas premise_family_socket_premise_one = premise_family_socket_premise[unfolded One_nat_def]

lemmas premise_family_socket_simps = premise_family_socket_premise premise_family_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

definition schema_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "schema_socket_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (schema_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)),
    finite_schema_premises = {|(0,37,finite_pattern_of (artifact_lookup_pattern data_x data_y (Pattern_Variable 7))),
      (1,34,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z) (data_list_pattern [(Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 11)),(Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12)),(Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 13))]))),
      (2,54,finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 11)) (Pattern_Variable 14))),
      (3,55,finite_pattern_of (pattern_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 12) (Pattern_Variable 4) (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 17))),
      (4,64,finite_pattern_of (premise_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 13) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 18))),
      (5,48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 18) (Pattern_Variable 14))),
      (6,49,finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 14)))),
      (7,49,finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (Pattern_Variable 16))),
      (8,49,finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (data_list_pattern [(Pattern_Variable 13)]))),
      (9,49,finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 11)]) (Pattern_Variable 16))),
      (10,49,finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 11)]) (data_list_pattern [(Pattern_Variable 13)]))),
      (11,49,finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 13)]) (Pattern_Variable 16)))|},
    finite_schema_materials = {||}\<rparr>"

lemma schema_socket_decoded: "decode_finite_schema schema_socket_schema = schema_instantiation_schema"
  by (simp add: schema_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def schema_instantiation_schema_def)

lemma schema_socket_functional: "finite_relation_functional (finite_schema_premises schema_socket_schema)"
  by (auto simp: finite_relation_functional_correct single_valued_def schema_socket_schema_def)

lemma schema_socket_premise:
  "finite_relation_option (finite_schema_premises schema_socket_schema) 3 = Some (55,finite_pattern_of (pattern_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 12) (Pattern_Variable 4) (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 17)))"
  "finite_relation_option (finite_schema_premises schema_socket_schema) 4 = Some (64,finite_pattern_of (premise_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 13) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 18)))"
  "finite_relation_option (finite_schema_premises schema_socket_schema) 5 = Some (48,finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 18) (Pattern_Variable 14)))"
  "finite_relation_option (finite_schema_premises schema_socket_schema) 7 = Some (49,finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (Pattern_Variable 16)))"
  "finite_relation_option (finite_schema_premises schema_socket_schema) 9 = Some (49,finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 11)]) (Pattern_Variable 16)))"
  "finite_relation_option (finite_schema_premises schema_socket_schema) 11 = Some (49,finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 13)]) (Pattern_Variable 16)))"
  by ((rule finite_relation_option_at[OF schema_socket_functional], simp add: schema_socket_schema_def)+)

lemmas schema_socket_premise_one = schema_socket_premise[unfolded One_nat_def]

lemmas schema_socket_simps = schema_socket_premise schema_socket_premise_one premise_parts_def output_variables_def resolution_view_pattern_def view_lookup_def
  instantiation_view_def prospective_view_def premise_rows_view_def schema_view_def record_material_view_def
  material_view_def five_fields_list_def five_fields_tuple_def join_view_def consumer_carrier_view_def view_identity_def
  identity_view_def carried_correspond_def output_corresponds_def

section \<open>The socket 0 of vector cons (vector head)\<close>

definition vector_head_carriers :: "nat clause_carrier list" where
  "vector_head_carriers = [(2,join_view,bag_pair,bag_corresponds),
    (3,consumer_carrier_view view_identity,bag_pair,(=)),
    (4,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=)),
    (5,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma vector_head_carried:
  "carried_variables vector_cons_socket_schema 0 instantiation_view vector_head_carriers = {6,11,13,15,17}"
  "carried_variables vector_cons_socket_schema 0 instantiation_view [] = {6,11,13,15}"
  "carried_variables vector_cons_socket_schema 0 instantiation_view (take (Suc (0)) vector_head_carriers) = {6,11,13,15,17}"
  "carried_variables vector_cons_socket_schema 0 instantiation_view (take (Suc (Suc (0))) vector_head_carriers) = {6,11,13,15,17}"
  "carried_variables vector_cons_socket_schema 0 instantiation_view (take (Suc (Suc (Suc (0)))) vector_head_carriers) = {6,11,13,15,17}"
  by (auto simp: vector_head_carriers_def carried_variables_def vector_cons_socket_simps)

lemmas vector_head_carried_one = vector_head_carried[unfolded One_nat_def]

lemma vector_head_keys: "fst ` set vector_head_carriers = {2,3,4,5}"
  by (simp add: vector_head_carriers_def)

lemma vector_head_steps:
  assumes "i < length vector_head_carriers"
  shows "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers i"
proof -
  have s0: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "join_view" and cin = "bag_pair" and cout = "bag_corresponds" and d = 46
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 17))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14))" and op = "Finite_Variable 17"])
    subgoal premises prems for g g'
      using prems(1)[of 14, unfolded vector_head_carried(1)] prems(2)
      by (simp add: vector_head_carried vector_head_carried_one vector_head_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_head_carriers_def)
    apply (rule join_view_formed)
    apply (rule vector_cons_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def join_view_def)
    apply (rule vector_carriers(1))
    apply (rule output_covered_variable)
    apply (simp_all add: vector_head_carried vector_head_carried_one)
    done
  have s1: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers (Suc (0))"
    apply (rule carrier_stepI[where k = 3 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 6
      and p = "finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 9, unfolded vector_head_carried(1)] prems(2)
      by (simp add: vector_head_carried vector_head_carried_one vector_head_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule vector_cons_socket_premise(4))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule vector_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_head_carried vector_head_carried_one)
    done
  have s2: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers (Suc (Suc (0)))"
    apply (rule carrier_stepI[where k = 4 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 10))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 16)) (Pattern_Variable 10))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 16, unfolded vector_head_carried(1)] prems(1)[of 10, unfolded vector_head_carried(1)] prems(2)
      by (simp add: vector_head_carried vector_head_carried_one vector_head_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule vector_cons_socket_premise(5))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule vector_carriers(3))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_head_carried vector_head_carried_one)
    done
  have s3: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers (Suc (Suc (Suc (0))))"
    apply (rule carrier_stepI[where k = 5 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 8))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)) (Pattern_Variable 8))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 12, unfolded vector_head_carried(1)] prems(1)[of 8, unfolded vector_head_carried(1)] prems(2)
      by (simp add: vector_head_carried vector_head_carried_one vector_head_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule vector_cons_socket_premise(6))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule vector_carriers(3))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_head_carried vector_head_carried_one)
    done
  have "i = 0 \<or> i = Suc 0 \<or> i = Suc (Suc 0) \<or> i = Suc (Suc (Suc 0))"
    using assms by (simp add: vector_head_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 s1 s2 s3 by blast
qed

theorem vector_head_socket_carried:
  "socket_carried (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 False instantiation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_head_carriers"
proof -
  have parts: "resolution_view_pattern instantiation_view (finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 6) (Pattern_Variable 11) (Pattern_Variable 13) (Pattern_Variable 15)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 15)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def instantiation_view_def)
  have covered: "output_covered (positive_meaning vector_instantiation_system) 55 instantiation_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 15)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF instantiation_views_formed(2), where \<sigma> = "\<lambda>v. if v = 6 then 5 else if v = 11 then 6 else if v = 13 then 7 else if v = 15 then 8 else v"])
      (simp add: instantiation_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables vector_cons_socket_schema 0 instantiation_view vector_head_carriers = {}"
    unfolding vector_head_carried(1) by simp
  have material: "\<And>N. (0,N) \<notin> schema_material_premises (decode_finite_schema vector_cons_socket_schema)"
    by (simp add: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema vector_cons_socket_schema) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow>
      q \<notin> fst ` set vector_head_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables vector_cons_socket_schema 0 instantiation_view vector_head_carriers = {}"
    unfolding vector_head_carried(1) vector_head_keys by (auto simp: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema vector_cons_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables vector_cons_socket_schema 0 instantiation_view vector_head_carriers = {}"
    by (simp add: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have head: "head_apart False instantiation_view vector_cons_socket_schema (carried_variables vector_cons_socket_schema 0 instantiation_view vector_head_carriers)"
    unfolding vector_head_carried(1)
    by (simp add: head_apart_def vector_cons_socket_schema_def instantiation_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed instantiation_views_formed(2) vector_cons_socket_premise(1) parts
      vector_socket_producer covered input material vector_head_steps others materials head])
qed

theorem vector_head_socket_discharged: "socket_discharged (positive_meaning vector_instantiation_system) vector_cons_socket_schema 0 False instantiation_view instantiation_view"
  by (rule socket_discharged_carried[OF vector_head_socket_carried])

section \<open>The socket 1 of vector cons (vector tail)\<close>

definition vector_tail_carriers :: "nat clause_carrier list" where
  "vector_tail_carriers = [(2,join_view,bag_pair,bag_corresponds),
    (3,consumer_carrier_view view_identity,bag_pair,(=)),
    (4,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=)),
    (5,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma vector_tail_carried:
  "carried_variables vector_cons_socket_schema 1 instantiation_view vector_tail_carriers = {7,12,14,16,17}"
  "carried_variables vector_cons_socket_schema 1 instantiation_view [] = {7,12,14,16}"
  "carried_variables vector_cons_socket_schema 1 instantiation_view (take (Suc (0)) vector_tail_carriers) = {7,12,14,16,17}"
  "carried_variables vector_cons_socket_schema 1 instantiation_view (take (Suc (Suc (0))) vector_tail_carriers) = {7,12,14,16,17}"
  "carried_variables vector_cons_socket_schema 1 instantiation_view (take (Suc (Suc (Suc (0)))) vector_tail_carriers) = {7,12,14,16,17}"
  by (auto simp: vector_tail_carriers_def carried_variables_def vector_cons_socket_simps)

lemmas vector_tail_carried_one = vector_tail_carried[unfolded One_nat_def]

lemma vector_tail_keys: "fst ` set vector_tail_carriers = {2,3,4,5}"
  by (simp add: vector_tail_carriers_def)

lemma vector_tail_steps:
  assumes "i < length vector_tail_carriers"
  shows "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers i"
proof -
  have s0: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "join_view" and cin = "bag_pair" and cout = "bag_corresponds" and d = 46
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 17))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14))" and op = "Finite_Variable 17"])
    subgoal premises prems for g g'
      using prems(1)[of 13, unfolded vector_tail_carried(1)] prems(2)
      by (simp add: vector_tail_carried vector_tail_carried_one vector_tail_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_tail_carriers_def)
    apply (rule join_view_formed)
    apply (rule vector_cons_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def join_view_def)
    apply (rule vector_carriers(1))
    apply (rule output_covered_variable)
    apply (simp_all add: vector_tail_carried vector_tail_carried_one)
    done
  have s1: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers (Suc (0))"
    apply (rule carrier_stepI[where k = 3 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 6
      and p = "finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 9))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 9, unfolded vector_tail_carried(1)] prems(2)
      by (simp add: vector_tail_carried vector_tail_carried_one vector_tail_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_tail_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule vector_cons_socket_premise(4))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule vector_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_tail_carried vector_tail_carried_one)
    done
  have s2: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers (Suc (Suc (0)))"
    apply (rule carrier_stepI[where k = 4 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 10))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 16)) (Pattern_Variable 10))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 15, unfolded vector_tail_carried(1)] prems(1)[of 10, unfolded vector_tail_carried(1)] prems(2)
      by (simp add: vector_tail_carried vector_tail_carried_one vector_tail_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_tail_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule vector_cons_socket_premise(5))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule vector_carriers(3))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_tail_carried vector_tail_carried_one)
    done
  have s3: "carrier_step (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers (Suc (Suc (Suc (0))))"
    apply (rule carrier_stepI[where k = 5 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 8))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)) (Pattern_Variable 8))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 11, unfolded vector_tail_carried(1)] prems(1)[of 8, unfolded vector_tail_carried(1)] prems(2)
      by (simp add: vector_tail_carried vector_tail_carried_one vector_tail_carriers_def vector_cons_socket_simps)
    apply (simp add: vector_tail_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule vector_cons_socket_premise(6))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule vector_carriers(3))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: vector_tail_carried vector_tail_carried_one)
    done
  have "i = 0 \<or> i = Suc 0 \<or> i = Suc (Suc 0) \<or> i = Suc (Suc (Suc 0))"
    using assms by (simp add: vector_tail_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 s1 s2 s3 by blast
qed

theorem vector_tail_socket_carried:
  "socket_carried (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 False instantiation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) vector_tail_carriers"
proof -
  have parts: "resolution_view_pattern instantiation_view (finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 16)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 16)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def instantiation_view_def)
  have covered: "output_covered (positive_meaning vector_instantiation_system) 60 instantiation_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 16)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF instantiation_views_formed(2), where \<sigma> = "\<lambda>v. if v = 7 then 5 else if v = 12 then 6 else if v = 14 then 7 else if v = 16 then 8 else v"])
      (simp add: instantiation_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables vector_cons_socket_schema 1 instantiation_view vector_tail_carriers = {}"
    unfolding vector_tail_carried(1) by simp
  have material: "\<And>N. (1,N) \<notin> schema_material_premises (decode_finite_schema vector_cons_socket_schema)"
    by (simp add: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema vector_cons_socket_schema) \<Longrightarrow> q \<noteq> 1 \<Longrightarrow>
      q \<notin> fst ` set vector_tail_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables vector_cons_socket_schema 1 instantiation_view vector_tail_carriers = {}"
    unfolding vector_tail_carried(1) vector_tail_keys by (auto simp: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema vector_cons_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables vector_cons_socket_schema 1 instantiation_view vector_tail_carriers = {}"
    by (simp add: vector_cons_socket_decoded vector_instantiation_cons_schema_def)
  have head: "head_apart False instantiation_view vector_cons_socket_schema (carried_variables vector_cons_socket_schema 1 instantiation_view vector_tail_carriers)"
    unfolding vector_tail_carried(1)
    by (simp add: head_apart_def vector_cons_socket_schema_def instantiation_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed instantiation_views_formed(2) vector_cons_socket_premise(2) parts
      schema_instantiation_output_producers(1) covered input material vector_tail_steps others materials head])
qed

theorem vector_tail_socket_discharged: "socket_discharged (positive_meaning vector_instantiation_system) vector_cons_socket_schema 1 False instantiation_view instantiation_view"
  by (rule socket_discharged_carried[OF vector_tail_socket_carried])

section \<open>The socket 4 of record (record fields)\<close>

definition record_fields_carriers :: "nat clause_carrier list" where
  "record_fields_carriers = [(5,join_view,bag_pair,bag_corresponds),
    (6,consumer_carrier_view view_identity,bag_pair,(=)),
    (7,consumer_carrier_view view_identity,bag_pair,(=))]"

lemma record_fields_carried:
  "carried_variables record_socket_schema 4 instantiation_view record_fields_carriers = {5,6,8,13,14}"
  "carried_variables record_socket_schema 4 instantiation_view [] = {5,6,8,13}"
  "carried_variables record_socket_schema 4 instantiation_view (take (Suc (0)) record_fields_carriers) = {5,6,8,13,14}"
  "carried_variables record_socket_schema 4 instantiation_view (take (Suc (Suc (0))) record_fields_carriers) = {5,6,8,13,14}"
  by (auto simp: record_fields_carriers_def carried_variables_def record_socket_simps)

lemmas record_fields_carried_one = record_fields_carried[unfolded One_nat_def]

lemma record_fields_keys: "fst ` set record_fields_carriers = {5,6,7}"
  by (simp add: record_fields_carriers_def)

lemma record_fields_steps:
  assumes "i < length record_fields_carriers"
  shows "carrier_step (positive_meaning record_instantiation_system) record_socket_schema 4 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) record_fields_carriers i"
proof -
  have s0: "carrier_step (positive_meaning record_instantiation_system) record_socket_schema 4 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) record_fields_carriers 0"
    apply (rule carrier_stepI[where k = 5 and V = "join_view" and cin = "bag_pair" and cout = "bag_corresponds" and d = 46
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 11)) (Pattern_Variable 13) (Pattern_Variable 14))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 11)) (Pattern_Variable 13))" and op = "Finite_Variable 14"])
    subgoal premises prems for g g'
      using prems(1)[of 4, unfolded record_fields_carried(1)] prems(1)[of 11, unfolded record_fields_carried(1)] prems(2)
      by (simp add: record_fields_carried record_fields_carried_one record_fields_carriers_def record_socket_simps)
    apply (simp add: record_fields_carriers_def)
    apply (rule join_view_formed)
    apply (rule record_socket_premise(2))
    apply (simp add: resolution_view_pattern_def view_lookup_def join_view_def)
    apply (rule record_carriers(1))
    apply (rule output_covered_variable)
    apply (simp_all add: record_fields_carried record_fields_carried_one)
    done
  have s1: "carrier_step (positive_meaning record_instantiation_system) record_socket_schema 4 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) record_fields_carriers (Suc (0))"
    apply (rule carrier_stepI[where k = 6 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 6
      and p = "finite_pattern_of (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 7))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 7))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 7, unfolded record_fields_carried(1)] prems(2)
      by (simp add: record_fields_carried record_fields_carried_one record_fields_carriers_def record_socket_simps)
    apply (simp add: record_fields_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule record_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule record_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: record_fields_carried record_fields_carried_one)
    done
  have s2: "carrier_step (positive_meaning record_instantiation_system) record_socket_schema 4 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) record_fields_carriers (Suc (Suc (0)))"
    apply (rule carrier_stepI[where k = 7 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 49
      and p = "finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 7, unfolded record_fields_carried(1)] prems(2)
      by (simp add: record_fields_carried record_fields_carried_one record_fields_carriers_def record_socket_simps)
    apply (simp add: record_fields_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule record_socket_premise(4))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule record_carriers(3))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: record_fields_carried record_fields_carried_one)
    done
  have "i = 0 \<or> i = Suc 0 \<or> i = Suc (Suc 0)"
    using assms by (simp add: record_fields_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 s1 s2 by blast
qed

theorem record_fields_socket_carried:
  "socket_carried (positive_meaning record_instantiation_system) record_socket_schema 4 False instantiation_view instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) record_fields_carriers"
proof -
  have parts: "resolution_view_pattern instantiation_view (finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 12) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 13) (Pattern_Variable 8)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 8)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def instantiation_view_def)
  have covered: "output_covered (positive_meaning record_instantiation_system) 60 instantiation_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 8)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF instantiation_views_formed(2), where \<sigma> = "\<lambda>v. if v = 13 then 7 else v"])
      (simp add: instantiation_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables record_socket_schema 4 instantiation_view record_fields_carriers = {}"
    unfolding record_fields_carried(1) by simp
  have material: "\<And>N. (4,N) \<notin> schema_material_premises (decode_finite_schema record_socket_schema)"
    by (simp add: record_socket_decoded record_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema record_socket_schema) \<Longrightarrow> q \<noteq> 4 \<Longrightarrow>
      q \<notin> fst ` set record_fields_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables record_socket_schema 4 instantiation_view record_fields_carriers = {}"
    unfolding record_fields_carried(1) record_fields_keys by (auto simp: record_socket_decoded record_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema record_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables record_socket_schema 4 instantiation_view record_fields_carriers = {}"
    by (simp add: record_socket_decoded record_instantiation_schema_def)
  have head: "head_apart False instantiation_view record_socket_schema (carried_variables record_socket_schema 4 instantiation_view record_fields_carriers)"
    unfolding record_fields_carried(1)
    by (simp add: head_apart_def record_socket_schema_def instantiation_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed instantiation_views_formed(2) record_socket_premise(1) parts
      record_socket_producer covered input material record_fields_steps others materials head])
qed

theorem record_fields_socket_discharged: "socket_discharged (positive_meaning record_instantiation_system) record_socket_schema 4 False instantiation_view instantiation_view"
  by (rule socket_discharged_carried[OF record_fields_socket_carried])

section \<open>The socket 0 of material (material record)\<close>

definition material_record_carriers :: "nat clause_carrier list" where "material_record_carriers = []"

lemma material_record_carried:
  "carried_variables material_socket_schema 0 record_material_view material_record_carriers = {5,6,7,8,9,10,11,12}"
  by (auto simp: material_record_carriers_def carried_variables_def material_socket_simps)

lemmas material_record_carried_one = material_record_carried[unfolded One_nat_def]

lemma material_record_keys: "fst ` set material_record_carriers = {}"
  by (simp add: material_record_carriers_def)

lemma material_record_steps:
  assumes "i < length material_record_carriers"
  shows "carrier_step (positive_meaning material_instantiation_system) material_socket_schema 0 record_material_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) material_record_carriers i"
  using assms by (simp add: material_record_carriers_def)

theorem material_record_socket_carried:
  "socket_carried (positive_meaning material_instantiation_system) material_socket_schema 0 False record_material_view material_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) material_record_carriers"
proof -
  have parts: "resolution_view_pattern record_material_view (finite_pattern_of (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (data_list_pattern [(Pattern_Variable 5),(Pattern_Variable 6),(Pattern_Variable 7),(Pattern_Variable 8),(Pattern_Variable 9)]) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))))) (Pattern_Pair (Pattern_Variable 10) (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def record_material_view_def five_fields_list_def five_fields_tuple_def)
  have covered: "output_covered (positive_meaning material_instantiation_system) 61 record_material_view (finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))))) (Pattern_Pair (Pattern_Variable 10) (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF record_material_view_formed, where \<sigma> = "id"])
      (simp add: record_material_view_def five_fields_list_def five_fields_tuple_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables material_socket_schema 0 record_material_view material_record_carriers = {}"
    unfolding material_record_carried(1) by simp
  have material: "\<And>N. (0,N) \<notin> schema_material_premises (decode_finite_schema material_socket_schema)"
    by (simp add: material_socket_decoded material_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema material_socket_schema) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow>
      q \<notin> fst ` set material_record_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables material_socket_schema 0 record_material_view material_record_carriers = {}"
    unfolding material_record_carried(1) material_record_keys by (auto simp: material_socket_decoded material_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema material_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables material_socket_schema 0 record_material_view material_record_carriers = {}"
    by (simp add: material_socket_decoded material_instantiation_schema_def)
  have head: "head_apart False material_view material_socket_schema (carried_variables material_socket_schema 0 record_material_view material_record_carriers)"
    unfolding material_record_carried(1)
    by (simp add: head_apart_def material_socket_schema_def material_view_def five_fields_tuple_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed record_material_view_formed material_socket_premise(1) parts
      material_socket_producer covered input material material_record_steps others materials head])
qed

theorem material_record_socket_discharged: "socket_discharged (positive_meaning material_instantiation_system) material_socket_schema 0 False record_material_view material_view"
  by (rule socket_discharged_carried[OF material_record_socket_carried])

section \<open>The socket 0 of premise call (premise call head)\<close>

definition premise_call_head_carriers :: "nat clause_carrier list" where
  "premise_call_head_carriers = [(2,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma premise_call_head_carried:
  "carried_variables premise_call_socket_schema 0 prospective_view premise_call_head_carriers = {7,8,12,14,15}"
  "carried_variables premise_call_socket_schema 0 prospective_view [] = {7,8,12,14,15}"
  by (auto simp: premise_call_head_carriers_def carried_variables_def premise_call_socket_simps)

lemmas premise_call_head_carried_one = premise_call_head_carried[unfolded One_nat_def]

lemma premise_call_head_keys: "fst ` set premise_call_head_carriers = {2}"
  by (simp add: premise_call_head_carriers_def)

lemma premise_call_head_steps:
  assumes "i < length premise_call_head_carriers"
  shows "carrier_step (positive_meaning premise_rows_system) premise_call_socket_schema 0 prospective_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_call_head_carriers i"
proof -
  have s0: "carrier_step (positive_meaning premise_rows_system) premise_call_socket_schema 0 prospective_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_call_head_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 11))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13)) (Pattern_Variable 11))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 13, unfolded premise_call_head_carried(1)] prems(1)[of 11, unfolded premise_call_head_carried(1)] prems(2)
      by (simp add: premise_call_head_carried premise_call_head_carried_one premise_call_head_carriers_def premise_call_socket_simps)
    apply (simp add: premise_call_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule premise_call_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule premise_rows_carriers)
    apply (rule consumer_carrier_covered)
    apply (simp_all add: premise_call_head_carried premise_call_head_carried_one)
    done
  have "i = 0"
    using assms by (simp add: premise_call_head_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem premise_call_head_socket_carried:
  "socket_carried (positive_meaning premise_rows_system) premise_call_socket_schema 0 False prospective_view premise_rows_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_call_head_carriers"
proof -
  have parts: "resolution_view_pattern prospective_view (finite_pattern_of (prospective_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 12) (Pattern_Variable 14) (Pattern_Variable 15)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 15)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def prospective_view_def)
  have covered: "output_covered (positive_meaning premise_rows_system) 57 prospective_view (finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 15)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF instantiation_views_formed(4), where \<sigma> = "\<lambda>v. if v = 7 then 5 else if v = 8 then 6 else if v = 12 then 7 else if v = 14 then 8 else if v = 15 then 9 else v"])
      (simp add: prospective_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables premise_call_socket_schema 0 prospective_view premise_call_head_carriers = {}"
    unfolding premise_call_head_carried(1) by simp
  have material: "\<And>N. (0,N) \<notin> schema_material_premises (decode_finite_schema premise_call_socket_schema)"
    by (simp add: premise_call_socket_decoded premise_rows_call_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_call_socket_schema) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow>
      q \<notin> fst ` set premise_call_head_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_call_socket_schema 0 prospective_view premise_call_head_carriers = {}"
    unfolding premise_call_head_carried(1) premise_call_head_keys by (auto simp: premise_call_socket_decoded premise_rows_call_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_call_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_call_socket_schema 0 prospective_view premise_call_head_carriers = {}"
    by (simp add: premise_call_socket_decoded premise_rows_call_schema_def)
  have head: "head_apart False premise_rows_view premise_call_socket_schema (carried_variables premise_call_socket_schema 0 prospective_view premise_call_head_carriers)"
    unfolding premise_call_head_carried(1)
    by (simp add: head_apart_def premise_call_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed instantiation_views_formed(4) premise_call_socket_premise(1) parts
      premise_rows_socket_producers(1) covered input material premise_call_head_steps others materials head])
qed

theorem premise_call_head_socket_discharged: "socket_discharged (positive_meaning premise_rows_system) premise_call_socket_schema 0 False prospective_view premise_rows_view"
  by (rule socket_discharged_carried[OF premise_call_head_socket_carried])

section \<open>The socket 1 of premise call (premise call tail)\<close>

definition premise_call_tail_carriers :: "nat clause_carrier list" where
  "premise_call_tail_carriers = [(2,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma premise_call_tail_carried:
  "carried_variables premise_call_socket_schema 1 premise_rows_view premise_call_tail_carriers = {9,10,13}"
  "carried_variables premise_call_socket_schema 1 premise_rows_view [] = {9,10,13}"
  by (auto simp: premise_call_tail_carriers_def carried_variables_def premise_call_socket_simps)

lemmas premise_call_tail_carried_one = premise_call_tail_carried[unfolded One_nat_def]

lemma premise_call_tail_keys: "fst ` set premise_call_tail_carriers = {2}"
  by (simp add: premise_call_tail_carriers_def)

lemma premise_call_tail_steps:
  assumes "i < length premise_call_tail_carriers"
  shows "carrier_step (positive_meaning premise_rows_system) premise_call_socket_schema 1 premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_call_tail_carriers i"
proof -
  have s0: "carrier_step (positive_meaning premise_rows_system) premise_call_socket_schema 1 premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_call_tail_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 11))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13)) (Pattern_Variable 11))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 12, unfolded premise_call_tail_carried(1)] prems(1)[of 11, unfolded premise_call_tail_carried(1)] prems(2)
      by (simp add: premise_call_tail_carried premise_call_tail_carried_one premise_call_tail_carriers_def premise_call_socket_simps)
    apply (simp add: premise_call_tail_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule premise_call_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule premise_rows_carriers)
    apply (rule consumer_carrier_covered)
    apply (simp_all add: premise_call_tail_carried premise_call_tail_carried_one)
    done
  have "i = 0"
    using assms by (simp add: premise_call_tail_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem premise_call_tail_socket_carried:
  "socket_carried (positive_meaning premise_rows_system) premise_call_socket_schema 1 False premise_rows_view premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_call_tail_carriers"
proof -
  have parts: "resolution_view_pattern premise_rows_view (finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 13)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 6)),finite_pattern_of (Pattern_Pair (Pattern_Variable 9) (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 13))))"
    by (simp add: resolution_view_pattern_def view_lookup_def premise_rows_view_def)
  have covered: "output_covered (positive_meaning premise_rows_system) 63 premise_rows_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 9) (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 13))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF premise_views_formed(1), where \<sigma> = "\<lambda>v. if v = 9 then 5 else if v = 10 then 6 else if v = 13 then 7 else v"])
      (simp add: premise_rows_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 6)) :: nat finite_term_pattern)) \<inter> carried_variables premise_call_socket_schema 1 premise_rows_view premise_call_tail_carriers = {}"
    unfolding premise_call_tail_carried(1) by simp
  have material: "\<And>N. (1,N) \<notin> schema_material_premises (decode_finite_schema premise_call_socket_schema)"
    by (simp add: premise_call_socket_decoded premise_rows_call_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_call_socket_schema) \<Longrightarrow> q \<noteq> 1 \<Longrightarrow>
      q \<notin> fst ` set premise_call_tail_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_call_socket_schema 1 premise_rows_view premise_call_tail_carriers = {}"
    unfolding premise_call_tail_carried(1) premise_call_tail_keys by (auto simp: premise_call_socket_decoded premise_rows_call_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_call_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_call_socket_schema 1 premise_rows_view premise_call_tail_carriers = {}"
    by (simp add: premise_call_socket_decoded premise_rows_call_schema_def)
  have head: "head_apart False premise_rows_view premise_call_socket_schema (carried_variables premise_call_socket_schema 1 premise_rows_view premise_call_tail_carriers)"
    unfolding premise_call_tail_carried(1)
    by (simp add: head_apart_def premise_call_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed premise_views_formed(1) premise_call_socket_premise(2) parts
      schema_instantiation_output_producers(5) covered input material premise_call_tail_steps others materials head])
qed

theorem premise_call_tail_socket_discharged: "socket_discharged (positive_meaning premise_rows_system) premise_call_socket_schema 1 False premise_rows_view premise_rows_view"
  by (rule socket_discharged_carried[OF premise_call_tail_socket_carried])

section \<open>The socket 0 of premise material (premise material head)\<close>

definition premise_material_head_carriers :: "nat clause_carrier list" where
  "premise_material_head_carriers = [(2,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma premise_material_head_carried:
  "carried_variables premise_material_socket_schema 0 material_view premise_material_head_carriers = {10,11,12,13,14,15,17,18}"
  "carried_variables premise_material_socket_schema 0 material_view [] = {10,11,12,13,14,15,17,18}"
  by (auto simp: premise_material_head_carriers_def carried_variables_def premise_material_socket_simps)

lemmas premise_material_head_carried_one = premise_material_head_carried[unfolded One_nat_def]

lemma premise_material_head_keys: "fst ` set premise_material_head_carriers = {2}"
  by (simp add: premise_material_head_carriers_def)

lemma premise_material_head_steps:
  assumes "i < length premise_material_head_carriers"
  shows "carrier_step (positive_meaning premise_rows_system) premise_material_socket_schema 0 material_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_material_head_carriers i"
proof -
  have s0: "carrier_step (positive_meaning premise_rows_system) premise_material_socket_schema 0 material_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_material_head_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 9))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 16)) (Pattern_Variable 9))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 16, unfolded premise_material_head_carried(1)] prems(1)[of 9, unfolded premise_material_head_carried(1)] prems(2)
      by (simp add: premise_material_head_carried premise_material_head_carried_one premise_material_head_carriers_def premise_material_socket_simps)
    apply (simp add: premise_material_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule premise_material_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule premise_rows_carriers)
    apply (rule consumer_carrier_covered)
    apply (simp_all add: premise_material_head_carried premise_material_head_carried_one)
    done
  have "i = 0"
    using assms by (simp add: premise_material_head_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem premise_material_head_socket_carried:
  "socket_carried (positive_meaning premise_rows_system) premise_material_socket_schema 0 False material_view premise_rows_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) premise_material_head_carriers"
proof -
  have parts: "resolution_view_pattern material_view (finite_pattern_of (material_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 5) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 17) (Pattern_Variable 18)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))),finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Pair (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14))))) (Pattern_Pair (Pattern_Variable 15) (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 18)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def material_view_def five_fields_tuple_def)
  have covered: "output_covered (positive_meaning premise_rows_system) 62 material_view (finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Pair (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14))))) (Pattern_Pair (Pattern_Variable 15) (Pattern_Pair (Pattern_Variable 17) (Pattern_Variable 18)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF material_view_formed, where \<sigma> = "\<lambda>v. if v = 10 then 5 else if v = 11 then 6 else if v = 12 then 7 else if v = 13 then 8 else if v = 14 then 9 else if v = 15 then 10 else if v = 17 then 11 else if v = 18 then 12 else v"])
      (simp add: material_view_def five_fields_tuple_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_z data_w))) :: nat finite_term_pattern)) \<inter> carried_variables premise_material_socket_schema 0 material_view premise_material_head_carriers = {}"
    unfolding premise_material_head_carried(1) by simp
  have material: "\<And>N. (0,N) \<notin> schema_material_premises (decode_finite_schema premise_material_socket_schema)"
    by (simp add: premise_material_socket_decoded premise_rows_material_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_material_socket_schema) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow>
      q \<notin> fst ` set premise_material_head_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_material_socket_schema 0 material_view premise_material_head_carriers = {}"
    unfolding premise_material_head_carried(1) premise_material_head_keys by (auto simp: premise_material_socket_decoded premise_rows_material_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_material_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_material_socket_schema 0 material_view premise_material_head_carriers = {}"
    by (simp add: premise_material_socket_decoded premise_rows_material_schema_def)
  have head: "head_apart False premise_rows_view premise_material_socket_schema (carried_variables premise_material_socket_schema 0 material_view premise_material_head_carriers)"
    unfolding premise_material_head_carried(1)
    by (simp add: head_apart_def premise_material_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed material_view_formed premise_material_socket_premise(1) parts
      premise_rows_socket_producers(2) covered input material premise_material_head_steps others materials head])
qed

theorem premise_material_head_socket_discharged: "socket_discharged (positive_meaning premise_rows_system) premise_material_socket_schema 0 False material_view premise_rows_view"
  by (rule socket_discharged_carried[OF premise_material_head_socket_carried])

section \<open>The socket 1 of premise material (premise material tail)\<close>

definition premise_material_tail_carriers :: "nat clause_carrier list" where
  "premise_material_tail_carriers = [(2,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma premise_material_tail_carried:
  "carried_variables premise_material_socket_schema 1 premise_rows_view premise_material_tail_carriers = {7,8,16}"
  "carried_variables premise_material_socket_schema 1 premise_rows_view [] = {7,8,16}"
  by (auto simp: premise_material_tail_carriers_def carried_variables_def premise_material_socket_simps)

lemmas premise_material_tail_carried_one = premise_material_tail_carried[unfolded One_nat_def]

lemma premise_material_tail_keys: "fst ` set premise_material_tail_carriers = {2}"
  by (simp add: premise_material_tail_carriers_def)

lemma premise_material_tail_steps:
  assumes "i < length premise_material_tail_carriers"
  shows "carrier_step (positive_meaning premise_rows_system) premise_material_socket_schema 1 premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_material_tail_carriers i"
proof -
  have s0: "carrier_step (positive_meaning premise_rows_system) premise_material_socket_schema 1 premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_material_tail_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 9))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 16)) (Pattern_Variable 9))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 15, unfolded premise_material_tail_carried(1)] prems(1)[of 9, unfolded premise_material_tail_carried(1)] prems(2)
      by (simp add: premise_material_tail_carried premise_material_tail_carried_one premise_material_tail_carriers_def premise_material_socket_simps)
    apply (simp add: premise_material_tail_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule premise_material_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule premise_rows_carriers)
    apply (rule consumer_carrier_covered)
    apply (simp_all add: premise_material_tail_carried premise_material_tail_carried_one)
    done
  have "i = 0"
    using assms by (simp add: premise_material_tail_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem premise_material_tail_socket_carried:
  "socket_carried (positive_meaning premise_rows_system) premise_material_socket_schema 1 False premise_rows_view premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_material_tail_carriers"
proof -
  have parts: "resolution_view_pattern premise_rows_view (finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 16)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 6)),finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 16))))"
    by (simp add: resolution_view_pattern_def view_lookup_def premise_rows_view_def)
  have covered: "output_covered (positive_meaning premise_rows_system) 63 premise_rows_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 16))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF premise_views_formed(1), where \<sigma> = "\<lambda>v. if v = 7 then 5 else if v = 8 then 6 else if v = 16 then 7 else v"])
      (simp add: premise_rows_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 6)) :: nat finite_term_pattern)) \<inter> carried_variables premise_material_socket_schema 1 premise_rows_view premise_material_tail_carriers = {}"
    unfolding premise_material_tail_carried(1) by simp
  have material: "\<And>N. (1,N) \<notin> schema_material_premises (decode_finite_schema premise_material_socket_schema)"
    by (simp add: premise_material_socket_decoded premise_rows_material_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_material_socket_schema) \<Longrightarrow> q \<noteq> 1 \<Longrightarrow>
      q \<notin> fst ` set premise_material_tail_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_material_socket_schema 1 premise_rows_view premise_material_tail_carriers = {}"
    unfolding premise_material_tail_carried(1) premise_material_tail_keys by (auto simp: premise_material_socket_decoded premise_rows_material_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_material_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_material_socket_schema 1 premise_rows_view premise_material_tail_carriers = {}"
    by (simp add: premise_material_socket_decoded premise_rows_material_schema_def)
  have head: "head_apart False premise_rows_view premise_material_socket_schema (carried_variables premise_material_socket_schema 1 premise_rows_view premise_material_tail_carriers)"
    unfolding premise_material_tail_carried(1)
    by (simp add: head_apart_def premise_material_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed premise_views_formed(1) premise_material_socket_premise(2) parts
      schema_instantiation_output_producers(5) covered input material premise_material_tail_steps others materials head])
qed

theorem premise_material_tail_socket_discharged: "socket_discharged (positive_meaning premise_rows_system) premise_material_socket_schema 1 False premise_rows_view premise_rows_view"
  by (rule socket_discharged_carried[OF premise_material_tail_socket_carried])

section \<open>The socket 1 of premise family (premise family rows)\<close>

definition premise_family_rows_carriers :: "nat clause_carrier list" where
  "premise_family_rows_carriers = [(2,premise_rows_view,tuple_corresponds [(=),bag_corresponds],tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds])]"

lemma premise_family_rows_carried:
  "carried_variables premise_family_socket_schema 1 view_identity premise_family_rows_carriers = {5,6,7,9}"
  "carried_variables premise_family_socket_schema 1 view_identity [] = {9}"
  by (auto simp: premise_family_rows_carriers_def carried_variables_def premise_family_socket_simps)

lemmas premise_family_rows_carried_one = premise_family_rows_carried[unfolded One_nat_def]

lemma premise_family_rows_keys: "fst ` set premise_family_rows_carriers = {2}"
  by (simp add: premise_family_rows_carriers_def)

lemma premise_family_rows_steps:
  assumes "i < length premise_family_rows_carriers"
  shows "carrier_step (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 1 view_identity (given_correspondence 32) premise_family_rows_carriers i"
proof -
  have s0: "carrier_step (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 1 view_identity (given_correspondence 32) premise_family_rows_carriers 0"
    apply (rule carrier_stepI[where k = 2 and V = "premise_rows_view" and cin = "tuple_corresponds [(=),bag_corresponds]" and cout = "tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds]" and d = 63
      and p = "finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 9) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 9))" and op = "finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))"])
    subgoal premises prems for g g'
    proof -
      have "given_correspondence 32 (g 9) (g' 9)" using prems(2) by (simp add: premise_family_socket_simps)
      then have "bag_corresponds (g 9) (g' 9)" by (rule family_rows_bag_corresponds)
      then show ?thesis using prems(1)[of 0, unfolded premise_family_rows_carried(1)] prems(1)[of 1, unfolded premise_family_rows_carried(1)] prems(1)[of 2, unfolded premise_family_rows_carried(1)] prems(1)[of 3, unfolded premise_family_rows_carried(1)]
        by (simp add: premise_family_rows_carried premise_family_rows_carried_one premise_family_rows_carriers_def premise_family_socket_simps)
    qed
    apply (simp add: premise_family_rows_carriers_def)
    apply (rule premise_views_formed(1))
    apply (rule premise_family_socket_premise(2))
    apply (simp add: resolution_view_pattern_def view_lookup_def premise_rows_view_def)
    apply (rule premise_family_carrier)
    apply (rule output_covered_renamed[OF premise_views_formed(1), where \<sigma> = id], simp add: premise_rows_view_def)
    apply (simp_all add: premise_family_rows_carried premise_family_rows_carried_one)
    done
  have "i = 0"
    using assms by (simp add: premise_family_rows_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem premise_family_rows_socket_carried:
  "socket_carried (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 1 False view_identity premise_rows_view (given_correspondence 32) premise_family_rows_carriers"
proof -
  have parts: "resolution_view_pattern view_identity (finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)) (Pattern_Variable 9)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)),finite_pattern_of (Pattern_Variable 9))"
    by (simp add: resolution_view_pattern_def view_lookup_def view_identity_def identity_view_def)
  have covered: "output_covered (positive_meaning premise_family_instantiation_system) 32 view_identity (finite_pattern_of (Pattern_Variable 9) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF view_identity_formed, where \<sigma> = "\<lambda>v. if v = 9 then 1 else v"])
      (simp add: view_identity_def identity_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)) :: nat finite_term_pattern)) \<inter> carried_variables premise_family_socket_schema 1 view_identity premise_family_rows_carriers = {}"
    unfolding premise_family_rows_carried(1) by simp
  have material: "\<And>N. (1,N) \<notin> schema_material_premises (decode_finite_schema premise_family_socket_schema)"
    by (simp add: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_family_socket_schema) \<Longrightarrow> q \<noteq> 1 \<Longrightarrow>
      q \<notin> fst ` set premise_family_rows_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_family_socket_schema 1 view_identity premise_family_rows_carriers = {}"
    unfolding premise_family_rows_carried(1) premise_family_rows_keys by (auto simp: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_family_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_family_socket_schema 1 view_identity premise_family_rows_carriers = {}"
    by (simp add: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have head: "head_apart False premise_rows_view premise_family_socket_schema (carried_variables premise_family_socket_schema 1 view_identity premise_family_rows_carriers)"
    unfolding premise_family_rows_carried(1)
    by (simp add: head_apart_def premise_family_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed view_identity_formed premise_family_socket_premise(1) parts
      family_socket_producer covered input material premise_family_rows_steps others materials head])
qed

theorem premise_family_rows_socket_discharged: "socket_discharged (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 1 False view_identity premise_rows_view"
  by (rule socket_discharged_carried[OF premise_family_rows_socket_carried])

section \<open>The socket 2 of premise family (premise family body)\<close>

definition premise_family_body_carriers :: "nat clause_carrier list" where "premise_family_body_carriers = []"

lemma premise_family_body_carried:
  "carried_variables premise_family_socket_schema 2 premise_rows_view premise_family_body_carriers = {5,6,7}"
  by (auto simp: premise_family_body_carriers_def carried_variables_def premise_family_socket_simps)

lemmas premise_family_body_carried_one = premise_family_body_carried[unfolded One_nat_def]

lemma premise_family_body_keys: "fst ` set premise_family_body_carriers = {}"
  by (simp add: premise_family_body_carriers_def)

lemma premise_family_body_steps:
  assumes "i < length premise_family_body_carriers"
  shows "carrier_step (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 2 premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_family_body_carriers i"
  using assms by (simp add: premise_family_body_carriers_def)

theorem premise_family_body_socket_carried:
  "socket_carried (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 2 False premise_rows_view premise_rows_view (tuple_corresponds [(=),(=),bag_corresponds]) premise_family_body_carriers"
proof -
  have parts: "resolution_view_pattern premise_rows_view (finite_pattern_of (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 9) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 9)),finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))))"
    by (simp add: resolution_view_pattern_def view_lookup_def premise_rows_view_def)
  have covered: "output_covered (positive_meaning premise_family_instantiation_system) 63 premise_rows_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF premise_views_formed(1), where \<sigma> = "id"])
      (simp add: premise_rows_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))) (Pattern_Variable 9)) :: nat finite_term_pattern)) \<inter> carried_variables premise_family_socket_schema 2 premise_rows_view premise_family_body_carriers = {}"
    unfolding premise_family_body_carried(1) by simp
  have material: "\<And>N. (2,N) \<notin> schema_material_premises (decode_finite_schema premise_family_socket_schema)"
    by (simp add: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema premise_family_socket_schema) \<Longrightarrow> q \<noteq> 2 \<Longrightarrow>
      q \<notin> fst ` set premise_family_body_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables premise_family_socket_schema 2 premise_rows_view premise_family_body_carriers = {}"
    unfolding premise_family_body_carried(1) premise_family_body_keys by (auto simp: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema premise_family_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables premise_family_socket_schema 2 premise_rows_view premise_family_body_carriers = {}"
    by (simp add: premise_family_socket_decoded premise_family_instantiation_schema_def)
  have head: "head_apart False premise_rows_view premise_family_socket_schema (carried_variables premise_family_socket_schema 2 premise_rows_view premise_family_body_carriers)"
    unfolding premise_family_body_carried(1)
    by (simp add: head_apart_def premise_family_socket_schema_def premise_rows_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed premise_views_formed(1) premise_family_socket_premise(2) parts
      family_body_producer covered input material premise_family_body_steps others materials head])
qed

theorem premise_family_body_socket_discharged: "socket_discharged (positive_meaning premise_family_instantiation_system) premise_family_socket_schema 2 False premise_rows_view premise_rows_view"
  by (rule socket_discharged_carried[OF premise_family_body_socket_carried])

section \<open>The socket 3 of schema (schema head)\<close>

definition schema_head_carriers :: "nat clause_carrier list" where
  "schema_head_carriers = [(5,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=)),
    (7,consumer_carrier_view view_identity,bag_pair,(=)),
    (9,consumer_carrier_view view_identity,bag_pair,(=)),
    (11,consumer_carrier_view view_identity,bag_pair,(=))]"

lemma schema_head_carried:
  "carried_variables schema_socket_schema 3 instantiation_view schema_head_carriers = {4,15,16,17}"
  "carried_variables schema_socket_schema 3 instantiation_view [] = {4,15,16,17}"
  "carried_variables schema_socket_schema 3 instantiation_view (take (Suc (0)) schema_head_carriers) = {4,15,16,17}"
  "carried_variables schema_socket_schema 3 instantiation_view (take (Suc (Suc (0))) schema_head_carriers) = {4,15,16,17}"
  "carried_variables schema_socket_schema 3 instantiation_view (take (Suc (Suc (Suc (0)))) schema_head_carriers) = {4,15,16,17}"
  by (auto simp: schema_head_carriers_def carried_variables_def schema_socket_simps)

lemmas schema_head_carried_one = schema_head_carried[unfolded One_nat_def]

lemma schema_head_keys: "fst ` set schema_head_carriers = {5,7,9,11}"
  by (simp add: schema_head_carriers_def)

lemma schema_head_steps:
  assumes "i < length schema_head_carriers"
  shows "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 3 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers i"
proof -
  have s0: "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 3 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers 0"
    apply (rule carrier_stepI[where k = 5 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 18) (Pattern_Variable 14))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 18)) (Pattern_Variable 14))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 18, unfolded schema_head_carried(1)] prems(1)[of 14, unfolded schema_head_carried(1)] prems(2)
      by (simp add: schema_head_carried schema_head_carried_one schema_head_carriers_def schema_socket_simps)
    apply (simp add: schema_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule schema_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule schema_carriers(1))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: schema_head_carried schema_head_carried_one)
    done
  have s1: "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 3 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers (Suc (0))"
    apply (rule carrier_stepI[where k = 7 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 49
      and p = "finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (Pattern_Variable 16))" and ip = "finite_pattern_of (Pattern_Pair (data_list_pattern [data_z,(Pattern_Variable 8),(Pattern_Variable 9),(Pattern_Variable 10)]) (Pattern_Variable 16))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 2, unfolded schema_head_carried(1)] prems(1)[of 8, unfolded schema_head_carried(1)] prems(1)[of 9, unfolded schema_head_carried(1)] prems(1)[of 10, unfolded schema_head_carried(1)] prems(2)
      by (simp add: schema_head_carried schema_head_carried_one schema_head_carriers_def schema_socket_simps)
    apply (simp add: schema_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule schema_socket_premise(4))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule schema_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: schema_head_carried schema_head_carried_one)
    done
  have s2: "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 3 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers (Suc (Suc (0)))"
    apply (rule carrier_stepI[where k = 9 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 49
      and p = "finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 11)]) (Pattern_Variable 16))" and ip = "finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 11)]) (Pattern_Variable 16))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 11, unfolded schema_head_carried(1)] prems(2)
      by (simp add: schema_head_carried schema_head_carried_one schema_head_carriers_def schema_socket_simps)
    apply (simp add: schema_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule schema_socket_premise(5))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule schema_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: schema_head_carried schema_head_carried_one)
    done
  have s3: "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 3 instantiation_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers (Suc (Suc (Suc (0))))"
    apply (rule carrier_stepI[where k = 11 and V = "consumer_carrier_view view_identity" and cin = "bag_pair" and cout = "(=)" and d = 49
      and p = "finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 13)]) (Pattern_Variable 16))" and ip = "finite_pattern_of (Pattern_Pair (data_list_pattern [(Pattern_Variable 13)]) (Pattern_Variable 16))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 13, unfolded schema_head_carried(1)] prems(2)
      by (simp add: schema_head_carried schema_head_carried_one schema_head_carriers_def schema_socket_simps)
    apply (simp add: schema_head_carriers_def)
    apply (simp add: consumer_carrier_view_formed view_identity_formed)
    apply (rule schema_socket_premise(6))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def view_identity_def identity_view_def)
    apply (rule schema_carriers(2))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: schema_head_carried schema_head_carried_one)
    done
  have "i = 0 \<or> i = Suc 0 \<or> i = Suc (Suc 0) \<or> i = Suc (Suc (Suc 0))"
    using assms by (simp add: schema_head_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 s1 s2 s3 by blast
qed

theorem schema_head_socket_carried:
  "socket_carried (positive_meaning schema_instantiation_system) schema_socket_schema 3 False instantiation_view schema_view (tuple_corresponds [(=),bag_corresponds,bag_corresponds,bag_corresponds]) schema_head_carriers"
proof -
  have parts: "resolution_view_pattern instantiation_view (finite_pattern_of (pattern_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 12) (Pattern_Variable 4) (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 17)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) data_w))),finite_pattern_of (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 15) (Pattern_Pair (Pattern_Variable 16) (Pattern_Variable 17)))))"
    by (simp add: resolution_view_pattern_def view_lookup_def instantiation_view_def)
  have covered: "output_covered (positive_meaning schema_instantiation_system) 55 instantiation_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 15) (Pattern_Pair (Pattern_Variable 16) (Pattern_Variable 17)))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF instantiation_views_formed(2), where \<sigma> = "\<lambda>v. if v = 4 then 5 else if v = 15 then 6 else if v = 16 then 7 else if v = 17 then 8 else v"])
      (simp add: instantiation_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Variable 12) (Pattern_Pair (Pattern_Variable 14) data_w))) :: nat finite_term_pattern)) \<inter> carried_variables schema_socket_schema 3 instantiation_view schema_head_carriers = {}"
    unfolding schema_head_carried(1) by simp
  have material: "\<And>N. (3,N) \<notin> schema_material_premises (decode_finite_schema schema_socket_schema)"
    by (simp add: schema_socket_decoded schema_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema schema_socket_schema) \<Longrightarrow> q \<noteq> 3 \<Longrightarrow>
      q \<notin> fst ` set schema_head_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables schema_socket_schema 3 instantiation_view schema_head_carriers = {}"
    unfolding schema_head_carried(1) schema_head_keys by (auto simp: schema_socket_decoded schema_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema schema_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables schema_socket_schema 3 instantiation_view schema_head_carriers = {}"
    by (simp add: schema_socket_decoded schema_instantiation_schema_def)
  have head: "head_apart False schema_view schema_socket_schema (carried_variables schema_socket_schema 3 instantiation_view schema_head_carriers)"
    unfolding schema_head_carried(1)
    by (simp add: head_apart_def schema_socket_schema_def schema_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed instantiation_views_formed(2) schema_socket_premise(1) parts
      schema_socket_producers(1) covered input material schema_head_steps others materials head])
qed

theorem schema_head_socket_discharged: "socket_discharged (positive_meaning schema_instantiation_system) schema_socket_schema 3 False instantiation_view schema_view"
  by (rule socket_discharged_carried[OF schema_head_socket_carried])

section \<open>The socket 4 of schema (schema body)\<close>

definition schema_body_carriers :: "nat clause_carrier list" where
  "schema_body_carriers = [(5,consumer_carrier_view join_view,tuple_corresponds [bag_pair,bag_corresponds],(=))]"

lemma schema_body_carried:
  "carried_variables schema_socket_schema 4 premise_rows_view schema_body_carriers = {5,6,18}"
  "carried_variables schema_socket_schema 4 premise_rows_view [] = {5,6,18}"
  by (auto simp: schema_body_carriers_def carried_variables_def schema_socket_simps)

lemmas schema_body_carried_one = schema_body_carried[unfolded One_nat_def]

lemma schema_body_keys: "fst ` set schema_body_carriers = {5}"
  by (simp add: schema_body_carriers_def)

lemma schema_body_steps:
  assumes "i < length schema_body_carriers"
  shows "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 4 premise_rows_view (tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds]) schema_body_carriers i"
proof -
  have s0: "carrier_step (positive_meaning schema_instantiation_system) schema_socket_schema 4 premise_rows_view (tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds]) schema_body_carriers 0"
    apply (rule carrier_stepI[where k = 5 and V = "consumer_carrier_view join_view" and cin = "tuple_corresponds [bag_pair,bag_corresponds]" and cout = "(=)" and d = 48
      and p = "finite_pattern_of (collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 18) (Pattern_Variable 14))" and ip = "finite_pattern_of (Pattern_Pair (Pattern_Pair (Pattern_Variable 15) (Pattern_Variable 18)) (Pattern_Variable 14))" and op = "Finite_Pattern_Payload []"])
    subgoal premises prems for g g'
      using prems(1)[of 15, unfolded schema_body_carried(1)] prems(1)[of 14, unfolded schema_body_carried(1)] prems(2)
      by (simp add: schema_body_carried schema_body_carried_one schema_body_carriers_def schema_socket_simps)
    apply (simp add: schema_body_carriers_def)
    apply (simp add: consumer_carrier_view_formed join_view_formed)
    apply (rule schema_socket_premise(3))
    apply (simp add: resolution_view_pattern_def view_lookup_def consumer_carrier_view_def join_view_def)
    apply (rule schema_carriers(1))
    apply (rule consumer_carrier_covered)
    apply (simp_all add: schema_body_carried schema_body_carried_one)
    done
  have "i = 0"
    using assms by (simp add: schema_body_carriers_def less_Suc_eq numeral_eq_Suc)
  then show ?thesis using s0 by blast
qed

theorem schema_body_socket_carried:
  "socket_carried (positive_meaning schema_instantiation_system) schema_socket_schema 4 False premise_rows_view schema_view (tuple_corresponds [bag_corresponds,bag_corresponds,bag_corresponds]) schema_body_carriers"
proof -
  have parts: "resolution_view_pattern premise_rows_view (finite_pattern_of (premise_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w (Pattern_Variable 13) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 18)) :: nat finite_term_pattern) = Some (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 14) data_w))) (Pattern_Variable 13)),finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 18))))"
    by (simp add: resolution_view_pattern_def view_lookup_def premise_rows_view_def)
  have covered: "output_covered (positive_meaning schema_instantiation_system) 64 premise_rows_view (finite_pattern_of (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 18))) :: nat finite_term_pattern)"
    by (rule output_covered_renamed[OF premise_views_formed(1), where \<sigma> = "\<lambda>v. if v = 18 then 7 else v"])
      (simp add: premise_rows_view_def)
  have input: "fset (finite_pattern_variables (finite_pattern_of (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 14) data_w))) (Pattern_Variable 13)) :: nat finite_term_pattern)) \<inter> carried_variables schema_socket_schema 4 premise_rows_view schema_body_carriers = {}"
    unfolding schema_body_carried(1) by simp
  have material: "\<And>N. (4,N) \<notin> schema_material_premises (decode_finite_schema schema_socket_schema)"
    by (simp add: schema_socket_decoded schema_instantiation_schema_def)
  have others: "\<And>q e r. (q,e,r) \<in> schema_premises (decode_finite_schema schema_socket_schema) \<Longrightarrow> q \<noteq> 4 \<Longrightarrow>
      q \<notin> fst ` set schema_body_carriers \<Longrightarrow> pattern_variables r \<inter> carried_variables schema_socket_schema 4 premise_rows_view schema_body_carriers = {}"
    unfolding schema_body_carried(1) schema_body_keys by (auto simp: schema_socket_decoded schema_instantiation_schema_def)
  have materials: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema schema_socket_schema) \<Longrightarrow>
      material_variables N \<inter> carried_variables schema_socket_schema 4 premise_rows_view schema_body_carriers = {}"
    by (simp add: schema_socket_decoded schema_instantiation_schema_def)
  have head: "head_apart False schema_view schema_socket_schema (carried_variables schema_socket_schema 4 premise_rows_view schema_body_carriers)"
    unfolding schema_body_carried(1)
    by (simp add: head_apart_def schema_socket_schema_def schema_view_def resolution_view_pattern_def view_lookup_def)
  show ?thesis
    by (rule socket_carriedI[OF meaning_answers_formed premise_views_formed(1) schema_socket_premise(2) parts
      schema_socket_producers(2) covered input material schema_body_steps others materials head])
qed

theorem schema_body_socket_discharged: "socket_discharged (positive_meaning schema_instantiation_system) schema_socket_schema 4 False premise_rows_view schema_view"
  by (rule socket_discharged_carried[OF schema_body_socket_carried])

section \<open>The records at the notions' systems\<close>

definition row_values_declarations :: "(nat,nat,nat) resolution_declarations" where
  "row_values_declarations = \<lparr>declared_producers = {|(59,view_identity,row_values_holes)|},
    declared_consumers = {||}, declared_sockets = {||}\<rparr>"

definition vector_declarations :: "(nat,nat,nat) resolution_declarations" where
  "vector_declarations = \<lparr>declared_producers = {|(60,instantiation_view,instantiation_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(60,vector_cons_socket_schema,0,False,instantiation_view,instantiation_view),
      (60,vector_cons_socket_schema,1,False,instantiation_view,instantiation_view)|}\<rparr>"

definition record_declarations :: "(nat,nat,nat) resolution_declarations" where
  "record_declarations = \<lparr>declared_producers = {|(61,instantiation_view,instantiation_holes),
      (61,record_material_view,record_material_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(61,record_socket_schema,4,False,instantiation_view,instantiation_view)|}\<rparr>"

definition material_declarations :: "(nat,nat,nat) resolution_declarations" where
  "material_declarations = \<lparr>declared_producers = {|(62,instantiation_view,instantiation_holes),
      (62,material_view,record_material_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(62,material_socket_schema,0,False,record_material_view,material_view)|}\<rparr>"

definition premise_rows_declarations :: "(nat,nat,nat) resolution_declarations" where
  "premise_rows_declarations = \<lparr>declared_producers = {|(63,premise_rows_view,premise_rows_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(63,premise_call_socket_schema,0,False,prospective_view,premise_rows_view),
      (63,premise_call_socket_schema,1,False,premise_rows_view,premise_rows_view),
      (63,premise_material_socket_schema,0,False,material_view,premise_rows_view),
      (63,premise_material_socket_schema,1,False,premise_rows_view,premise_rows_view)|}\<rparr>"

definition premise_family_declarations :: "(nat,nat,nat) resolution_declarations" where
  "premise_family_declarations = \<lparr>declared_producers = {|(64,premise_rows_view,premise_rows_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(64,premise_family_socket_schema,1,False,view_identity,premise_rows_view),
      (64,premise_family_socket_schema,2,False,premise_rows_view,premise_rows_view)|}\<rparr>"

definition schema_declarations :: "(nat,nat,nat) resolution_declarations" where
  "schema_declarations = \<lparr>declared_producers = {|(65,schema_view,schema_holes)|}, declared_consumers = {||},
    declared_sockets = {|(65,schema_socket_schema,3,False,instantiation_view,schema_view),
      (65,schema_socket_schema,4,False,premise_rows_view,schema_view)|}\<rparr>"

theorem schema_instantiation_notion_declarations_discharged:
  "declarations_discharged (positive_meaning row_values_system) row_values_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning vector_instantiation_system) vector_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning record_instantiation_system) record_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning material_instantiation_system) material_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning premise_rows_system) premise_rows_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning premise_family_instantiation_system) premise_family_declarations
    schema_instantiation_correspondence"
  "declarations_discharged (positive_meaning schema_instantiation_system) schema_declarations
    schema_instantiation_correspondence"
  using row_values_producer_discharged vector_producer_discharged vector_head_socket_discharged
    vector_tail_socket_discharged record_producer_discharged record_material_producer_discharged
    record_fields_socket_discharged material_producer_discharged material_tuple_producer_discharged
    material_record_socket_discharged premise_rows_producer_discharged premise_call_head_socket_discharged
    premise_call_tail_socket_discharged premise_material_head_socket_discharged premise_material_tail_socket_discharged
    premise_family_producer_discharged premise_family_rows_socket_discharged premise_family_body_socket_discharged
    schema_producer_discharged schema_head_socket_discharged schema_body_socket_discharged
  by (simp_all add: declarations_discharged_def declarations_formed_def view_identity_formed instantiation_views_formed
    record_material_view_formed material_view_formed premise_views_formed row_values_declarations_def
    vector_declarations_def record_declarations_def material_declarations_def premise_rows_declarations_def
    premise_family_declarations_def schema_declarations_def)

end
