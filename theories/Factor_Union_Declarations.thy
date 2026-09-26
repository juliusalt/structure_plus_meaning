theory Factor_Union_Declarations
  imports Factor_Narrowed_Commitments Factor_Schema_Instantiation_Declarations
begin

text \<open>
  48, the union, produced at its eight narrowed sockets (R6c of DECISIONS.md "The native evaluator constructs the
  missing witnesses by resolution", its addition "The given's remaining producers: views, carriers and narrowed
  sockets", (c), and the correction closing it, task 725). 48's answers at one input are every list with the union's
  set; at each of its free uses in the instantiation family a consumer in the same clause narrows them: payload
  disjointness (49, @{thm [source] payload_disjoint_exact}) or distinct payloads (1,
  @{thm [source] distinct_payloads_positive_exact}), each giving a distinct list (@{text union_class}). Within that
  class two answers at one input are bags of each other, and the socket is carried along its consumer
  (@{thm [source] narrowed_socket_framed_carried}). The union is produced by one registration at 48.0's head variable
  x2 (@{text union_registration}): its base queries select an element from x0 and from x1 (site 5), the element its own
  key, identity by equality, and its value the data list of the elements in the order found, the distinct union, which
  48's clause checks (@{thm [source] data_union_exact}). The registration is held in the sockets' records beside the
  class (@{const produced}), not by the witness construction; its completeness at the eight sockets is
  @{thm [source] registration_complete_at_socket} at the construction reading it (@{text union_registration_complete}).
\<close>

section \<open>The union's clause, its class and its consumers\<close>

definition union_schema :: "(nat,nat,nat) finite_factor_schema" where
  "union_schema = \<lparr>finite_schema_conclusion = finite_pattern_of (collection_join_pattern data_x data_y data_z),
    finite_schema_premises = {|(0,46,finite_pattern_of (collection_join_pattern data_x data_y data_w)),
      (1,47,finite_pattern_of (Pattern_Pair data_w data_z)),(2,47,finite_pattern_of (Pattern_Pair data_z data_w))|},
    finite_schema_materials = {||}\<rparr>"

lemma union_schema_decoded: "decode_finite_schema union_schema = data_union_schema"
  by (simp add: union_schema_def decode_finite_schema_def decode_finite_call_pattern_def map_relation_values_def
    data_union_schema_def)

definition union_class :: "factor_term \<Rightarrow> bool" where
  "union_class y \<longleftrightarrow> (\<exists>zs. y = data_list_term zs \<and> distinct zs)"

lemma union_class_payloads:
  assumes "distinct A"
  shows "union_class (data_list_term (map Payload_Term A))"
  unfolding union_class_def by (rule exI[of _ "map Payload_Term A"]) (simp add: assms distinct_map inj_on_def)

lemma union_class_disjoint:
  assumes "(49,Pair_Term x y) \<in> positive_meaning payload_disjoint_system"
  shows "union_class y"
proof -
  obtain A B where "Pair_Term x y = Pair_Term (data_list_term (map Payload_Term A)) (data_list_term (map Payload_Term B))"
      "distinct B"
    using assms unfolding payload_disjoint_exact by blast
  then show ?thesis using union_class_payloads by simp
qed

lemma union_class_distinct:
  assumes "(1,y) \<in> positive_meaning distinct_payloads_system"
  shows "union_class y"
proof -
  obtain A where "distinct A" "y = data_list_term (map Payload_Term A)"
    using assms unfolding distinct_payloads_positive_exact by blast
  then show ?thesis using union_class_payloads by simp
qed

text \<open>The restricted meaning is the meaning at every other site.\<close>

lemma narrowed_meaning_other:
  assumes "e \<noteq> d"
  shows "(e,t) \<in> narrowed_meaning M d V N \<longleftrightarrow> (e,t) \<in> M"
  using assms by (simp add: narrowed_meaning_def)

lemma narrowed_meaning_answers_formed:
  "\<forall>e t. (e,t) \<in> narrowed_meaning (positive_meaning P) d V N \<longrightarrow> term_formed t"
proof (intro allI impI)
  fix e t assume "(e,t) \<in> narrowed_meaning (positive_meaning P) d V N"
  then have "(e,t) \<in> positive_meaning P" by (simp add: narrowed_meaning_def)
  then show "term_formed t" by (rule meaning_answers_formed[rule_format])
qed

lemma union_narrowed_output:
  fixes M :: "(nat \<times> factor_term) set"
  assumes union: "\<And>t. (48,t) \<in> M \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
    and holds: "(48,Pair_Term a (Pair_Term b y)) \<in> narrowed_meaning M 48 join_view union_class"
  obtains xs ys zs where "a = data_list_term xs" "b = data_list_term ys" "y = data_list_term zs"
    "data_elements xs" "data_elements ys" "data_elements zs" "set zs = set xs \<union> set ys" "distinct zs"
proof -
  have m: "(48,Pair_Term a (Pair_Term b y)) \<in> positive_meaning data_union_system"
    using holds union by (simp add: narrowed_meaning_def)
  have v: "resolution_view_term join_view (Pair_Term a (Pair_Term b y)) = Some (Pair_Term a b,y)"
    by (simp add: join_view_term)
  have n: "union_class y" using holds v by (simp add: narrowed_meaning_def)
  obtain xs ys zs where l: "a = data_list_term xs" "b = data_list_term ys" "y = data_list_term zs"
      "data_elements xs" "data_elements ys" "data_elements zs" "set zs = set xs \<union> set ys"
    using m unfolding data_union_exact by blast
  obtain zs' where "y = data_list_term zs'" "distinct zs'" using n unfolding union_class_def by blast
  then have "distinct zs" using l(3) by (simp add: data_list_term_injective)
  then show ?thesis using that l by blast
qed

text \<open>
  48 at @{const join_view} over its class: two answers at one input whose outputs are distinct lists hold the same
  elements once each, so the outputs are bags of each other.
\<close>

theorem union_narrowed_producer:
  fixes M :: "(nat \<times> factor_term) set"
  assumes union: "\<And>t. (48,t) \<in> M \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
  shows "producer_discharged (narrowed_meaning M 48 join_view union_class) 48 join_view [snd (snd join_view)]
    (\<lambda>_. bag_corresponds)"
proof (rule producer_discharged_valuations[OF join_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i
  assume a0: "(48,evaluate_pattern g (decode_finite_pattern (fst join_view))) \<in> narrowed_meaning M 48 join_view union_class"
    and b0: "(48,evaluate_pattern g' (decode_finite_pattern (fst join_view))) \<in> narrowed_meaning M 48 join_view union_class"
    and u0: "evaluate_pattern g (decode_finite_pattern (fst (snd join_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd join_view)))"
    and i: "i < length [snd (snd join_view)]"
  have a: "(48,Pair_Term (g 0) (Pair_Term (g 1) (g 2))) \<in> narrowed_meaning M 48 join_view union_class"
    using a0 by (simp add: join_view_def)
  have b: "(48,Pair_Term (g' 0) (Pair_Term (g' 1) (g' 2))) \<in> narrowed_meaning M 48 join_view union_class"
    using b0 by (simp add: join_view_def)
  have u: "g 0 = g' 0" "g 1 = g' 1" using u0 by (simp_all add: join_view_def)
  obtain xs ys zs where l: "g 0 = data_list_term xs" "g 1 = data_list_term ys" "g 2 = data_list_term zs"
      "set zs = set xs \<union> set ys" "distinct zs"
    by (rule union_narrowed_output[OF union a]) blast
  obtain xs' ys' zs' where l': "g' 0 = data_list_term xs'" "g' 1 = data_list_term ys'" "g' 2 = data_list_term zs'"
      "set zs' = set xs' \<union> set ys'" "distinct zs'"
    by (rule union_narrowed_output[OF union b]) blast
  have "xs' = xs" "ys' = ys" using u l(1,2) l'(1,2) by (simp_all add: data_list_term_injective)
  then have "set zs = set zs'" using l(4) l'(4) by simp
  then have "mset zs = mset zs'" using l(5) l'(5) set_eq_iff_mset_eq_distinct by blast
  then have "bag_corresponds (g 2) (g' 2)" using l(3) l'(3) by (simp add: bag_corresponds_lists)
  then show "bag_corresponds (evaluate_pattern g (decode_finite_pattern ([snd (snd join_view)] ! i)))
      (evaluate_pattern g' (decode_finite_pattern ([snd (snd join_view)] ! i)))"
    using i by (simp add: join_view_def)
qed

text \<open>
  The consumers carry a bag of the socket's output: payload disjointness at the identity view
  (@{thm [source] disjoint_consumer_carrier}), distinct payloads at the view reading its whole argument
  (@{text argument_view}, its output nothing).
\<close>

definition argument_view :: "nat resolution_view" where
  "argument_view = (Finite_Variable 0,Finite_Variable 0,Finite_Pattern_Payload [])"

lemma argument_view_formed: "view_formed argument_view"
  by (auto simp: view_formed_def argument_view_def fset_eq_iff)

lemma argument_view_term:
  "resolution_view_term argument_view t = Some (x,y) \<longleftrightarrow> x = t \<and> y = Payload_Term []"
  using resolution_view_term_values[OF argument_view_formed[unfolded argument_view_def], of 1 t x y]
  by (auto simp: argument_view_def view_values_simps)

lemma argument_view_covered: "output_covered M d argument_view (Finite_Pattern_Payload [])"
  by (auto simp: output_covered_def argument_view_term)

theorem distinct_consumer_carrier:
  "carrier_discharged (positive_meaning distinct_payloads_system) 1 argument_view bag_corresponds (=)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(1,a) \<in> positive_meaning distinct_payloads_system"
    and va: "resolution_view_term argument_view a = Some (x,y)" and cx: "bag_corresponds x x'"
  have x: "x = a" and y: "y = Payload_Term []" using va by (simp_all add: argument_view_term)
  obtain A where A: "a = data_list_term (map Payload_Term A)" "distinct A" "\<forall>c\<in>set A. octets_formed c"
    using holds unfolding distinct_payloads_positive_exact by blast
  obtain B where B: "x' = data_list_term (map Payload_Term B)" "mset B = mset A"
    using cx x A(1) bag_corresponds_payload_list by metis
  have "distinct B" "set B = set A"
    using A(2) mset_eq_imp_distinct_iff[OF B(2)] mset_eq_setD[OF B(2)] by simp_all
  then have "(1,x') \<in> positive_meaning distinct_payloads_system"
    using A(3) B(1) by (simp add: distinct_payload_list_exact[unfolded One_nat_def])
  moreover have "resolution_view_term argument_view x' = Some (x',y)" using y by (simp add: argument_view_term)
  ultimately show "\<exists>b y'. (1,b) \<in> positive_meaning distinct_payloads_system \<and>
      resolution_view_term argument_view b = Some (x',y') \<and> y = y'" by blast
qed

lemma union_disjoint_carrier:
  fixes M :: "(nat \<times> factor_term) set"
  assumes "\<And>t. (49,t) \<in> M \<longleftrightarrow> (49,t) \<in> positive_meaning payload_disjoint_system"
  shows "carrier_discharged (narrowed_meaning M 48 join_view N) 49 (consumer_carrier_view view_identity) bag_pair (=)"
proof -
  have ne: "(49::nat) \<noteq> 48" by simp
  have eq: "\<And>t. (49,t) \<in> narrowed_meaning M 48 join_view N \<longleftrightarrow> (49,t) \<in> positive_meaning payload_disjoint_system"
    by (simp only: narrowed_meaning_other[OF ne] assms)
  show ?thesis by (simp only: carrier_discharged_site[OF eq] disjoint_consumer_carrier)
qed

lemma union_distinct_carrier:
  fixes M :: "(nat \<times> factor_term) set"
  assumes "\<And>t. (1,t) \<in> M \<longleftrightarrow> (1,t) \<in> positive_meaning distinct_payloads_system"
  shows "carrier_discharged (narrowed_meaning M 48 join_view N) 1 argument_view bag_corresponds (=)"
proof -
  have ne: "(1::nat) \<noteq> 48" by simp
  have eq: "\<And>t. (1,t) \<in> narrowed_meaning M 48 join_view N \<longleftrightarrow> (1,t) \<in> positive_meaning distinct_payloads_system"
    by (simp only: narrowed_meaning_other[OF ne] assms)
  show ?thesis by (simp only: carrier_discharged_site[OF eq] distinct_consumer_carrier)
qed

text \<open>
  A clause whose every call of 48 reads its output at a variable its narrowing consumer holds in the class is narrowed
  (@{const clause_narrowed}); the socket carried along its consumer is then framed at its output over the class.
\<close>

lemma clause_true_premise_holds:
  assumes "clause_true M (decode_finite_schema S) h" and "(q,d,p) |\<in>| finite_schema_premises S"
  shows "(d,evaluate_pattern h (decode_finite_pattern p)) \<in> M"
  by (rule conjunct1[OF conjunct2[OF assms(1)[unfolded clause_true_def]], rule_format, OF decoded_premise[OF assms(2)]])

lemma union_clause_narrowed:
  assumes consumers: "\<And>h q p. clause_true M (decode_finite_schema S) h \<Longrightarrow>
      (q,48,p) \<in> schema_premises (decode_finite_schema S) \<Longrightarrow>
      \<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
        union_class (h c)"
  shows "clause_narrowed M S 48 join_view union_class"
  unfolding clause_narrowed_def
proof (intro allI impI)
  fix h q p x y
  assume h: "clause_true M (decode_finite_schema S) h" and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema S)"
    and v: "resolution_view_term join_view (evaluate_pattern h p) = Some (x,y)"
  obtain a b c where p: "p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c)"
      and n: "union_class (h c)"
    using consumers[OF h qp] by blast
  have "y = h c" using v p by (auto simp: join_view_term)
  then show "union_class y" using n by simp
qed

theorem union_socket_framed:
  assumes carried: "socket_carried (narrowed_meaning M 48 join_view union_class) S s keep join_view Vh bag_corresponds cs"
    and site: "finite_relation_option (finite_schema_premises S) s = Some (48,p0)"
    and narrowing: "clause_narrowed M S 48 join_view union_class"
    and frame: "carried_variables S s join_view cs = C"
  shows "narrowed_socket_framed M S s keep join_view Vh union_class C"
  using narrowed_socket_framed_carried[OF carried site narrowing] unfolding frame .

lemmas union_listed_simps = schema_instantiation_listed_simps view_listed[OF argument_view_def] argument_view_formed
  argument_view_covered

section \<open>The registration at 48.0's head variable\<close>

definition union_query :: "nat \<Rightarrow> (nat,nat,nat) collection_query" where
  "union_query a = \<lparr>query_equations = [(a,Finite_Variable 1)], query_site = 5,
    query_goal = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    query_element = 0\<rparr>"

definition union_family :: "(nat,nat,nat) collection_family" where
  "union_family = \<lparr>family_base = [union_query 0,union_query 1], family_step = None,
    family_key = (Finite_Variable 0,0), family_identity = None\<rparr>"

definition union_registration :: "(nat,nat,nat,nat) collection_registration" where
  "union_registration = \<lparr>registration_site = 48, registration_schema = union_schema, registration_variable = 2,
    registration_families = Single_Family union_family\<rparr>"

abbreviation union_construction :: "nat \<Rightarrow> (nat,nat,nat,'c) finite_witness_construction" where
  "union_construction n \<equiv> finite_collection_construction [union_registration] n"

lemma union_head_registration: "head_registration join_view union_schema 2"
  by (simp add: head_registration_def join_view_formed union_schema_def socket_listed_simps)

lemma union_registration_input:
  "head_registration_input join_view union_schema B =
    Some (Pair_Term (decode_finite_term (finite_binding_valuation B 0)) (decode_finite_term (finite_binding_valuation B 1)))"
  by (simp add: head_registration_input_def union_schema_def socket_listed_simps)

lemma union_construction_value:
  "witness_value (union_construction n) P 48 union_schema B 2 = finite_registration_value P n union_registration B"
  using finite_collection_construction_value_at[where Rs = "[union_registration]" and R = union_registration]
  by (simp add: finite_registrations_distinct_def union_registration_def)

lemma union_family_key: "finite_family_key union_family e = Some e"
proof -
  have m: "finite_inputs_matching [(e,Finite_Variable 0 :: nat finite_term_pattern)] = Some {|(0,e)|}"
    by (simp add: finite_inputs_matching_def finite_relation_functional_def)
  show ?thesis
    using finite_relation_option_at[of "{|(0::nat,e)|}" 0 e]
    by (simp add: finite_family_key_def union_family_def m finite_relation_functional_def)
qed

lemma union_collection_distinct:
  assumes collect: "finite_family_collection P n union_family B = Some (es,cs)"
  shows "cs = []" "distinct (map fst es)"
proof -
  show c: "cs = []"
  proof (rule ccontr)
    assume "cs \<noteq> []"
    then obtain z zs where "cs = z # zs" by (cases cs) auto
    moreover obtain x y where "z = (x,y)" by (cases z)
    ultimately have xy: "(x,y) \<in> set cs" by simp
    have "finite_family_key union_family x = finite_family_key union_family y" "x \<noteq> y"
      using finite_family_collection_conflicts[OF collect xy] by simp_all
    then show False by (simp add: union_family_key)
  qed
  show "distinct (map fst es)" using finite_family_collection_distinct[of P n union_family B es] collect c by simp
qed

lemma union_registration_collected:
  assumes "finite_registration_value P n union_registration B = Some v"
  obtains es where "finite_family_collection P n union_family B = Some (es,[])" "v = finite_family_value es"
proof -
  obtain es cs where c: "finite_family_collection P n union_family B = Some (es,cs)" "v = finite_family_value es"
    using assms by (auto simp: finite_registration_value_def union_registration_def finite_family_collected_some)
  have "cs = []" by (rule union_collection_distinct(1)[OF c(1)])
  then show ?thesis using that c by simp
qed

lemma union_value_distinct:
  assumes collect: "finite_family_collection P n union_family B = Some (es,cs)"
  shows "distinct (map (decode_finite_term \<circ> fst) es)"
  using union_collection_distinct(2)[OF collect] by (auto simp: distinct_map inj_on_def)

text \<open>(iii) Production: every value the registration returns is formed and a distinct list.\<close>

theorem union_registration_produces:
  "head_registration_produces (union_construction n) P 48 union_schema 2 union_class"
  unfolding head_registration_produces_def union_construction_value
proof (intro allI impI)
  fix B v assume val: "finite_registration_value P n union_registration B = Some v"
  obtain es where c: "finite_family_collection P n union_family B = Some (es,[])" "v = finite_family_value es"
    by (rule union_registration_collected[OF val])
  have "union_class (decode_finite_term v)"
    unfolding union_class_def c(2) finite_family_value_presents using union_value_distinct[OF c(1)] by blast
  then show "finite_term_formed v \<and> union_class (decode_finite_term v)"
    using finite_registration_value_formed[OF val] by simp
qed

text \<open>A base query answers exactly the members of the list its clause variable is bound to, by selection (5).\<close>

lemma union_query_holds:
  assumes selection: "\<And>t. (5,t) \<in> positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
    and list: "decode_finite_term (finite_binding_valuation B a) = data_list_term xs" and elements: "data_elements xs"
  shows "finite_query_holds P (union_query a) B [] e \<longleftrightarrow> decode_finite_term e \<in> set xs"
proof
  assume "finite_query_holds P (union_query a) B [] e"
  then obtain t0 and \<theta> :: "nat \<Rightarrow> finite_factor_term" where t0: "finite_relation_option B a = Some t0"
    and el: "\<theta> 0 = e" and one: "\<theta> 1 = t0"
    and goal: "(5,Pair_Term (decode_finite_term (\<theta> 0)) (Pair_Term (decode_finite_term (\<theta> 1))
      (decode_finite_term (\<theta> 2)))) \<in> positive_meaning (decode_finite_system P)"
    by (auto simp: finite_query_holds_def finite_query_inputs_def union_query_def split: option.splits)
  have "(5,Pair_Term (decode_finite_term e) (Pair_Term (decode_finite_term t0) (decode_finite_term (\<theta> 2))))
      \<in> positive_meaning bag_comparison_system"
    using goal selection el one by simp
  then obtain ws where ws: "decode_finite_term t0 = data_list_term ws" "decode_finite_term e \<in> set ws"
    using selected_data_member_exact[of "decode_finite_term e" "decode_finite_term t0"] by blast
  have "finite_binding_valuation B a = t0" using t0 by (simp add: finite_binding_valuation_def)
  then have "ws = xs" using ws(1) list by (simp add: data_list_term_injective)
  then show "decode_finite_term e \<in> set xs" using ws(2) by simp
next
  assume member: "decode_finite_term e \<in> set xs"
  obtain pre post where split: "xs = pre @ decode_finite_term e # post" using split_list[OF member] by blast
  have "finite_relation_option B a \<noteq> None"
  proof
    assume "finite_relation_option B a = None"
    then have "data_list_term xs = Payload_Term []" using list by (simp add: finite_binding_valuation_def)
    then show False using split by (cases pre) simp_all
  qed
  then obtain t0 where t0: "finite_relation_option B a = Some t0" by blast
  have dt0: "decode_finite_term t0 = data_list_term xs" using list t0 by (simp add: finite_binding_valuation_def)
  have formed: "term_formed (data_list_term (pre @ post))" using elements split by (auto simp: data_list_term_formed)
  have dr: "decode_finite_term (finite_term_of (data_list_term (pre @ post))) = data_list_term (pre @ post)"
    by (rule decode_finite_term_of[OF formed])
  have sel: "(5,Pair_Term (decode_finite_term e) (Pair_Term (data_list_term xs) (data_list_term (pre @ post))))
      \<in> positive_meaning bag_comparison_system"
    by (simp only: data_selection_exact) (use elements split in blast)
  define \<theta> where "\<theta> = (\<lambda>v::nat. if v = 0 then e else if v = 1 then t0 else finite_term_of (data_list_term (pre @ post)))"
  show "finite_query_holds P (union_query a) B [] e"
    unfolding finite_query_holds_def
    by (rule exI[of _ "[(t0,Finite_Variable 1)]"], rule exI[of _ \<theta>])
      (use t0 sel dr dt0 selection in \<open>simp add: finite_query_inputs_def union_query_def \<theta>_def\<close>)
qed

text \<open>The value at two bound lists is the distinct union of their elements, the answer 48's clause checks.\<close>

theorem union_registration_union:
  assumes selection: "\<And>t. (5,t) \<in> positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
    and valued: "finite_registration_value P n union_registration B = Some v"
    and first: "decode_finite_term (finite_binding_valuation B 0) = data_list_term xs" "data_elements xs"
    and second: "decode_finite_term (finite_binding_valuation B 1) = data_list_term ys" "data_elements ys"
  shows "\<exists>zs. decode_finite_term v = data_list_term zs \<and> data_elements zs \<and> distinct zs \<and> set zs = set xs \<union> set ys"
proof -
  obtain es where c: "finite_family_collection P n union_family B = Some (es,[])" "v = finite_family_value es"
    by (rule union_registration_collected[OF valued])
  have exact: "fst ` set es = (finite_family_step_answers P union_family B)\<^sup>* `` finite_family_base_answers P union_family B"
    by (rule finite_family_collection_exact[OF c(1)]) (simp add: union_family_def)
  have step: "finite_family_step_answers P union_family B = {}"
    by (simp add: finite_family_step_answers_def union_family_def)
  have base: "finite_family_base_answers P union_family B = {e. decode_finite_term e \<in> set xs \<union> set ys}"
    by (auto simp: finite_family_base_answers_def union_family_def union_query_holds[OF selection first]
      union_query_holds[OF selection second] union_query_holds[OF selection second, unfolded One_nat_def])
  have found: "fst ` set es = {e. decode_finite_term e \<in> set xs \<union> set ys}" using exact step base by simp
  have set: "set (map (decode_finite_term \<circ> fst) es) = set xs \<union> set ys"
  proof
    show "set (map (decode_finite_term \<circ> fst) es) \<subseteq> set xs \<union> set ys" using found by auto
    show "set xs \<union> set ys \<subseteq> set (map (decode_finite_term \<circ> fst) es)"
    proof
      fix y assume y: "y \<in> set xs \<union> set ys"
      have "term_formed y" using y first(2) second(2) by auto
      then have d: "decode_finite_term (finite_term_of y) = y" by (rule decode_finite_term_of)
      then have "finite_term_of y \<in> fst ` set es" using found y by simp
      then show "y \<in> set (map (decode_finite_term \<circ> fst) es)" using d by force
    qed
  qed
  have elements: "data_elements (map (decode_finite_term \<circ> fst) es)" using set first(2) second(2) by auto
  have v: "decode_finite_term v = data_list_term (map (decode_finite_term \<circ> fst) es)"
    using c(2) by (simp only: finite_family_value_presents)
  show ?thesis
    by (rule exI[of _ "map (decode_finite_term \<circ> fst) es"])
      (use v elements set union_value_distinct[OF c(1)] first(2) second(2) in auto)
qed

theorem union_registration_checked:
  assumes selection: "\<And>t. (5,t) \<in> positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
    and valued: "finite_registration_value P n union_registration B = Some v"
    and first: "decode_finite_term (finite_binding_valuation B 0) = data_list_term xs" "data_elements xs"
    and second: "decode_finite_term (finite_binding_valuation B 1) = data_list_term ys" "data_elements ys"
  shows "(48,collection_join_argument (data_list_term xs) (data_list_term ys) (decode_finite_term v))
    \<in> positive_meaning data_union_system"
  using union_registration_union[OF selection valued first second] first(2) second(2)
  by (auto simp: data_union_lists)

text \<open>The value is an answer of 48 wherever 48 has one at the same input.\<close>

theorem union_registration_answers:
  fixes M :: "(nat \<times> factor_term) set"
  assumes union: "\<And>t. (48,t) \<in> M \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
    and selection: "\<And>t. (5,t) \<in> positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
  shows "head_registration_answers M (union_construction n) P 48 union_schema join_view 2"
  unfolding head_registration_answers_def union_construction_value
proof (intro allI impI)
  fix B v x t y
  assume valued: "finite_registration_value P n union_registration B = Some v"
    and input: "head_registration_input join_view union_schema B = Some x"
    and holds: "(48,t) \<in> M" and view: "resolution_view_term join_view t = Some (x,y)"
  obtain a b where t: "t = Pair_Term a (Pair_Term b y)" and x: "x = Pair_Term a b" using view by (auto simp: join_view_term)
  obtain xs ys where lists: "a = data_list_term xs" "b = data_list_term ys" "data_elements xs" "data_elements ys"
    using holds union t unfolding data_union_exact by auto
  have "x = Pair_Term (decode_finite_term (finite_binding_valuation B 0)) (decode_finite_term (finite_binding_valuation B 1))"
    using input by (simp add: union_registration_input)
  then have first: "decode_finite_term (finite_binding_valuation B 0) = data_list_term xs"
    and second: "decode_finite_term (finite_binding_valuation B 1) = data_list_term ys"
    using x lists(1,2) by simp_all
  have "(48,Pair_Term a (Pair_Term b (decode_finite_term v))) \<in> M"
    using union_registration_checked[OF selection valued first lists(3) second lists(4)] union lists(1,2) by simp
  moreover have "resolution_view_term join_view (Pair_Term a (Pair_Term b (decode_finite_term v))) =
      Some (x,decode_finite_term v)"
    using x by (simp add: join_view_term)
  ultimately show "\<exists>t'. (48,t') \<in> M \<and> resolution_view_term join_view t' = Some (x,decode_finite_term v)" by blast
qed

text \<open>
  Completeness at a narrowed socket of 48 read at @{const join_view}: every true instance of the caller clause extends
  to one through the registration's value at its input, which is formed and a distinct list
  (@{thm [source] registration_complete_at_socket} at the construction reading the registration).
\<close>

theorem union_registration_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system" and C :: "(nat,nat,nat) finite_factor_schema"
    and M :: "(nat \<times> factor_term) set"
  assumes union: "\<And>t. (48,t) \<in> M \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
    and selection: "\<And>t. (5,t) \<in> positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
    and narrowed: "narrowed_socket_discharged M C s keep join_view Vh union_class"
    and premise: "(s,48,p) |\<in>| finite_schema_premises C" and viewed: "resolution_view_pattern join_view p = Some (xi,yo)"
    and h: "clause_true M (decode_finite_schema C) h"
    and input: "head_registration_input join_view union_schema B = Some (evaluate_pattern h (decode_finite_pattern xi))"
    and valued: "finite_registration_value P n union_registration B = Some v"
  shows "finite_term_formed v" "union_class (decode_finite_term v)"
    "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
proof -
  have w: "witness_value (union_construction n) P 48 union_schema B 2 = Some v"
    using valued by (simp only: union_construction_value)
  note c = registration_complete_at_socket[OF narrowed join_view_formed premise viewed union_registration_produces
    union_registration_answers[OF union selection] h input w]
  show "finite_term_formed v" "union_class (decode_finite_term v)" by (rule c(1), rule c(2))
  show "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
    by (rule c(3))
qed

section \<open>The socket of 50's pair clause: slots (50.2/7), narrowed by 49\<close>

definition quotation_union_carriers :: "nat clause_carrier list" where
  "quotation_union_carriers = [(8,consumer_carrier_view view_identity,bag_pair,(=))]"

theorem quotation_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning quotation_admission_system) 48 join_view union_class)
    quotation_pair_socket_schema 7 False join_view quotation_view bag_corresponds quotation_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF quotation_admission_components(9)], where \<sigma> = "\<lambda>v. if v = 6 then 2 else v"])
    (simp add: union_listed_simps quotation_pair_socket_schema_def quotation_union_carriers_def
      union_disjoint_carrier[OF quotation_admission_components(10)])

lemma quotation_union_narrowing:
  "clause_narrowed (positive_meaning quotation_admission_system) quotation_pair_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning quotation_admission_system) (decode_finite_schema quotation_pair_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema quotation_pair_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 13) (Pattern_Variable 15) (Pattern_Variable 6)"
    using qp by (auto simp: finite_premise_decoded quotation_pair_socket_schema_def)
  have "(49,Pair_Term (h 5) (h 6)) \<in> positive_meaning quotation_admission_system"
    using clause_true_premise_holds[OF h, of 8 49] by (simp add: quotation_pair_socket_schema_def)
  then have "union_class (h 6)" by (simp add: quotation_admission_components union_class_disjoint)
  then show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p by blast
qed

lemma quotation_union_socket_framed:
  "narrowed_socket_framed (positive_meaning quotation_admission_system) quotation_pair_socket_schema 7 False join_view
    quotation_view union_class {6}"
  by (rule union_socket_framed[OF quotation_union_socket_carried _ quotation_union_narrowing])
    (simp_all add: union_listed_simps quotation_pair_socket_schema_def quotation_union_carriers_def)

lemma quotation_union_socket_discharged:
  "narrowed_socket_discharged (positive_meaning quotation_admission_system) quotation_pair_socket_schema 7 False
    join_view quotation_view union_class"
  by (rule narrowed_socket_framed_discharged[OF quotation_union_socket_framed])

section \<open>The sockets of 55's pair clause: slots (55.2/7) narrowed by 49, used variables (55.2/8) by 1\<close>

definition instantiation_slots_union_carriers :: "nat clause_carrier list" where
  "instantiation_slots_union_carriers = [(9,consumer_carrier_view view_identity,bag_pair,(=))]"

definition instantiation_used_union_carriers :: "nat clause_carrier list" where
  "instantiation_used_union_carriers = [(11,argument_view,bag_corresponds,(=))]"

theorem instantiation_slots_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning pattern_instantiation_system) 48 join_view union_class)
    instantiation_pair_socket_schema 7 False join_view instantiation_view bag_corresponds instantiation_slots_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF pattern_instantiation_components(10)], where \<sigma> = "\<lambda>v. if v = 9 then 2 else v"])
    (simp add: union_listed_simps instantiation_pair_socket_schema_def instantiation_slots_union_carriers_def
      union_disjoint_carrier[OF pattern_instantiation_components(4)])

theorem instantiation_used_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning pattern_instantiation_system) 48 join_view union_class)
    instantiation_pair_socket_schema 8 False join_view instantiation_view bag_corresponds instantiation_used_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF pattern_instantiation_components(10)], where \<sigma> = "\<lambda>v. if v = 7 then 2 else v"])
    (simp add: union_listed_simps instantiation_pair_socket_schema_def instantiation_used_union_carriers_def
      union_distinct_carrier[OF pattern_instantiation_components(11)]
      union_distinct_carrier[OF pattern_instantiation_components(11), unfolded One_nat_def])

lemma instantiation_union_narrowing:
  "clause_narrowed (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning pattern_instantiation_system)
      (decode_finite_schema instantiation_pair_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema instantiation_pair_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 19) (Pattern_Variable 20) (Pattern_Variable 9) \<or>
      p = collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 7)"
    using qp by (auto simp: finite_premise_decoded instantiation_pair_socket_schema_def)
  have "(49,Pair_Term (h 8) (h 9)) \<in> positive_meaning pattern_instantiation_system"
    using clause_true_premise_holds[OF h, of 9 49] by (simp add: instantiation_pair_socket_schema_def)
  then have n9: "union_class (h 9)" by (simp add: pattern_instantiation_components union_class_disjoint)
  have "(1,h 7) \<in> positive_meaning pattern_instantiation_system"
    using clause_true_premise_holds[OF h, of 11 1] by (simp add: instantiation_pair_socket_schema_def)
  then have "(1,h 7) \<in> positive_meaning distinct_payloads_system" by (simp only: pattern_instantiation_components(11))
  then have n7: "union_class (h 7)" by (rule union_class_distinct)
  show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p n9 n7 by blast
qed

lemma instantiation_slots_union_socket_framed:
  "narrowed_socket_framed (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 7 False
    join_view instantiation_view union_class {9}"
  by (rule union_socket_framed[OF instantiation_slots_union_socket_carried _ instantiation_union_narrowing])
    (simp_all add: union_listed_simps instantiation_pair_socket_schema_def instantiation_slots_union_carriers_def)

lemma instantiation_used_union_socket_framed:
  "narrowed_socket_framed (positive_meaning pattern_instantiation_system) instantiation_pair_socket_schema 8 False
    join_view instantiation_view union_class {7}"
  by (rule union_socket_framed[OF instantiation_used_union_socket_carried _ instantiation_union_narrowing])
    (simp_all add: union_listed_simps instantiation_pair_socket_schema_def instantiation_used_union_carriers_def)

lemmas instantiation_union_socket_discharged =
  narrowed_socket_framed_discharged[OF instantiation_slots_union_socket_framed]
  narrowed_socket_framed_discharged[OF instantiation_used_union_socket_framed]

section \<open>The socket of 57's clause: slots (57.0/8), narrowed by 49\<close>

definition prospective_union_carriers :: "nat clause_carrier list" where
  "prospective_union_carriers = [(9,consumer_carrier_view view_identity,bag_pair,(=))]"

theorem prospective_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning prospective_instantiation_system) 48 join_view union_class)
    prospective_socket_schema 8 False join_view prospective_view bag_corresponds prospective_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF prospective_instantiation_components(8)], where \<sigma> = "\<lambda>v. if v = 9 then 2 else v"])
    (simp add: union_listed_simps prospective_socket_schema_def prospective_union_carriers_def
      union_disjoint_carrier[OF prospective_instantiation_components(9)])

lemma prospective_union_narrowing:
  "clause_narrowed (positive_meaning prospective_instantiation_system) prospective_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning prospective_instantiation_system) (decode_finite_schema prospective_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema prospective_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 17) (Pattern_Variable 19) (Pattern_Variable 9)"
    using qp by (auto simp: finite_premise_decoded prospective_socket_schema_def)
  have "(49,Pair_Term (h 8) (h 9)) \<in> positive_meaning prospective_instantiation_system"
    using clause_true_premise_holds[OF h, of 9 49] by (simp add: prospective_socket_schema_def)
  then have "union_class (h 9)" by (simp add: prospective_instantiation_components union_class_disjoint)
  then show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p by blast
qed

lemma prospective_union_socket_framed:
  "narrowed_socket_framed (positive_meaning prospective_instantiation_system) prospective_socket_schema 8 False
    join_view prospective_view union_class {9}"
  by (rule union_socket_framed[OF prospective_union_socket_carried _ prospective_union_narrowing])
    (simp_all add: union_listed_simps prospective_socket_schema_def prospective_union_carriers_def)

lemma prospective_union_socket_discharged:
  "narrowed_socket_discharged (positive_meaning prospective_instantiation_system) prospective_socket_schema 8 False
    join_view prospective_view union_class"
  by (rule narrowed_socket_framed_discharged[OF prospective_union_socket_framed])

section \<open>The sockets of 60's cons clause: slots (60.1/4) narrowed by 49, used variables (60.1/5) by 1\<close>

definition vector_slots_union_carriers :: "nat clause_carrier list" where
  "vector_slots_union_carriers = [(6,consumer_carrier_view view_identity,bag_pair,(=))]"

definition vector_used_union_carriers :: "nat clause_carrier list" where
  "vector_used_union_carriers = [(7,argument_view,bag_corresponds,(=))]"

theorem vector_slots_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning vector_instantiation_system) 48 join_view union_class)
    vector_cons_socket_schema 4 False join_view instantiation_view bag_corresponds vector_slots_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF vector_instantiation_components(5)], where \<sigma> = "\<lambda>v. if v = 10 then 2 else v"])
    (simp add: union_listed_simps vector_cons_socket_schema_def vector_slots_union_carriers_def
      union_disjoint_carrier[OF vector_instantiation_components(6)])

theorem vector_used_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning vector_instantiation_system) 48 join_view union_class)
    vector_cons_socket_schema 5 False join_view instantiation_view bag_corresponds vector_used_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF vector_instantiation_components(5)], where \<sigma> = "\<lambda>v. if v = 8 then 2 else v"])
    (simp add: union_listed_simps vector_cons_socket_schema_def vector_used_union_carriers_def
      union_distinct_carrier[OF vector_instantiation_components(7)]
      union_distinct_carrier[OF vector_instantiation_components(7), unfolded One_nat_def])

lemma vector_union_narrowing:
  "clause_narrowed (positive_meaning vector_instantiation_system) vector_cons_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning vector_instantiation_system) (decode_finite_schema vector_cons_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema vector_cons_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 10) \<or>
      p = collection_join_pattern (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 8)"
    using qp by (auto simp: finite_premise_decoded vector_cons_socket_schema_def)
  have "(49,Pair_Term (h 9) (h 10)) \<in> positive_meaning vector_instantiation_system"
    using clause_true_premise_holds[OF h, of 6 49] by (simp add: vector_cons_socket_schema_def)
  then have n10: "union_class (h 10)" by (simp add: vector_instantiation_components union_class_disjoint)
  have "(1,h 8) \<in> positive_meaning vector_instantiation_system"
    using clause_true_premise_holds[OF h, of 7 1] by (simp add: vector_cons_socket_schema_def)
  then have "(1,h 8) \<in> positive_meaning distinct_payloads_system" by (simp only: vector_instantiation_components(7))
  then have n8: "union_class (h 8)" by (rule union_class_distinct)
  show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p n10 n8 by blast
qed

lemma vector_slots_union_socket_framed:
  "narrowed_socket_framed (positive_meaning vector_instantiation_system) vector_cons_socket_schema 4 False
    join_view instantiation_view union_class {10}"
  by (rule union_socket_framed[OF vector_slots_union_socket_carried _ vector_union_narrowing])
    (simp_all add: union_listed_simps vector_cons_socket_schema_def vector_slots_union_carriers_def)

lemma vector_used_union_socket_framed:
  "narrowed_socket_framed (positive_meaning vector_instantiation_system) vector_cons_socket_schema 5 False
    join_view instantiation_view union_class {8}"
  by (rule union_socket_framed[OF vector_used_union_socket_carried _ vector_union_narrowing])
    (simp_all add: union_listed_simps vector_cons_socket_schema_def vector_used_union_carriers_def)

lemmas vector_union_socket_discharged =
  narrowed_socket_framed_discharged[OF vector_slots_union_socket_framed]
  narrowed_socket_framed_discharged[OF vector_used_union_socket_framed]

section \<open>The sockets of 63's call and material clauses: slots (63.1/2, 63.2/2), narrowed by 1\<close>

definition premise_call_union_carriers :: "nat clause_carrier list" where
  "premise_call_union_carriers = [(3,argument_view,bag_corresponds,(=))]"

definition premise_material_union_carriers :: "nat clause_carrier list" where
  "premise_material_union_carriers = [(3,argument_view,bag_corresponds,(=))]"

theorem premise_call_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning premise_rows_system) 48 join_view union_class)
    premise_call_socket_schema 2 False join_view premise_rows_view bag_corresponds premise_call_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF premise_rows_components(4)], where \<sigma> = "\<lambda>v. if v = 11 then 2 else v"])
    (simp add: union_listed_simps premise_call_socket_schema_def premise_call_union_carriers_def
      union_distinct_carrier[OF premise_rows_components(5)]
      union_distinct_carrier[OF premise_rows_components(5), unfolded One_nat_def])

theorem premise_material_union_socket_carried:
  "socket_carried (narrowed_meaning (positive_meaning premise_rows_system) 48 join_view union_class)
    premise_material_socket_schema 2 False join_view premise_rows_view bag_corresponds premise_material_union_carriers"
  by (rule socket_carried_listed[OF narrowed_meaning_answers_formed join_view_formed
      union_narrowed_producer[OF premise_rows_components(4)], where \<sigma> = "\<lambda>v. if v = 9 then 2 else v"])
    (simp add: union_listed_simps premise_material_socket_schema_def premise_material_union_carriers_def
      union_distinct_carrier[OF premise_rows_components(5)]
      union_distinct_carrier[OF premise_rows_components(5), unfolded One_nat_def])

lemma premise_call_union_narrowing:
  "clause_narrowed (positive_meaning premise_rows_system) premise_call_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning premise_rows_system) (decode_finite_schema premise_call_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema premise_call_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 12) (Pattern_Variable 13) (Pattern_Variable 11)"
    using qp by (auto simp: finite_premise_decoded premise_call_socket_schema_def)
  have "(1,h 11) \<in> positive_meaning premise_rows_system"
    using clause_true_premise_holds[OF h, of 3 1] by (simp add: premise_call_socket_schema_def)
  then have "(1,h 11) \<in> positive_meaning distinct_payloads_system" by (simp only: premise_rows_components(5))
  then have "union_class (h 11)" by (rule union_class_distinct)
  then show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p by blast
qed

lemma premise_material_union_narrowing:
  "clause_narrowed (positive_meaning premise_rows_system) premise_material_socket_schema 48 join_view union_class"
proof (rule union_clause_narrowed)
  fix h q p
  assume h: "clause_true (positive_meaning premise_rows_system) (decode_finite_schema premise_material_socket_schema) h"
    and qp: "(q,48,p) \<in> schema_premises (decode_finite_schema premise_material_socket_schema)"
  have p: "p = collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 9)"
    using qp by (auto simp: finite_premise_decoded premise_material_socket_schema_def)
  have "(1,h 9) \<in> positive_meaning premise_rows_system"
    using clause_true_premise_holds[OF h, of 3 1] by (simp add: premise_material_socket_schema_def)
  then have "(1,h 9) \<in> positive_meaning distinct_payloads_system" by (simp only: premise_rows_components(5))
  then have "union_class (h 9)" by (rule union_class_distinct)
  then show "\<exists>a b c. p = collection_join_pattern (Pattern_Variable a) (Pattern_Variable b) (Pattern_Variable c) \<and>
      union_class (h c)" using p by blast
qed

lemma premise_call_union_socket_framed:
  "narrowed_socket_framed (positive_meaning premise_rows_system) premise_call_socket_schema 2 False
    join_view premise_rows_view union_class {11}"
  by (rule union_socket_framed[OF premise_call_union_socket_carried _ premise_call_union_narrowing])
    (simp_all add: union_listed_simps premise_call_socket_schema_def premise_call_union_carriers_def)

lemma premise_material_union_socket_framed:
  "narrowed_socket_framed (positive_meaning premise_rows_system) premise_material_socket_schema 2 False
    join_view premise_rows_view union_class {9}"
  by (rule union_socket_framed[OF premise_material_union_socket_carried _ premise_material_union_narrowing])
    (simp_all add: union_listed_simps premise_material_socket_schema_def premise_material_union_carriers_def)

lemmas premise_rows_union_socket_discharged =
  narrowed_socket_framed_discharged[OF premise_call_union_socket_framed]
  narrowed_socket_framed_discharged[OF premise_material_union_socket_framed]

section \<open>The records at the notions' systems and the production they hold\<close>

text \<open>
  Each record declares the union's narrowed sockets at one notion's system, no producer and no consumer: 48 is not
  presentation-free, and is produced, not committed. Its class is @{const union_class} at every socket and its
  production @{const union_registration} (@{const produced}); a frame family beside it holds each socket's carried set.
  A use of 48 whose clause holds no narrowing consumer declares nothing and stays unresolved.
\<close>

type_synonym union_sockets =
  "(nat \<times> (nat,nat,nat) finite_factor_schema \<times> nat \<times> bool \<times> nat resolution_view \<times> nat resolution_view) fset"

definition union_narrowed :: "union_sockets \<Rightarrow> (nat,nat,nat) narrowed_declarations" where
  "union_narrowed Z = narrowed \<lparr>declared_producers = {||}, declared_consumers = {||}, declared_sockets = Z\<rparr>
    (\<lambda>_ _ _. union_class)"

definition union_produced :: "union_sockets \<Rightarrow> (nat,nat,nat,nat) produced_declarations" where
  "union_produced Z = produced (union_narrowed Z) (\<lambda>_ _ _. Some union_registration)"

lemma union_produced_fields [simp]:
  "narrowed_declarations.truncate (union_produced Z) = union_narrowed Z"
  "declared_production (union_produced Z) e S s = Some union_registration"
  by (simp_all add: union_produced_def)

definition quotation_union_sockets :: union_sockets where
  "quotation_union_sockets = {|(50,quotation_pair_socket_schema,7,False,join_view,quotation_view)|}"

definition instantiation_union_sockets :: union_sockets where
  "instantiation_union_sockets = {|(55,instantiation_pair_socket_schema,7,False,join_view,instantiation_view),
    (55,instantiation_pair_socket_schema,8,False,join_view,instantiation_view)|}"

definition prospective_union_sockets :: union_sockets where
  "prospective_union_sockets = {|(57,prospective_socket_schema,8,False,join_view,prospective_view)|}"

definition vector_union_sockets :: union_sockets where
  "vector_union_sockets = {|(60,vector_cons_socket_schema,4,False,join_view,instantiation_view),
    (60,vector_cons_socket_schema,5,False,join_view,instantiation_view)|}"

definition premise_rows_union_sockets :: union_sockets where
  "premise_rows_union_sockets = {|(63,premise_call_socket_schema,2,False,join_view,premise_rows_view),
    (63,premise_material_socket_schema,2,False,join_view,premise_rows_view)|}"

theorem union_declarations_discharged:
  "narrowed_declarations_discharged (positive_meaning quotation_admission_system) (union_narrowed quotation_union_sockets)
    instantiation_correspondence"
  "narrowed_declarations_discharged (positive_meaning pattern_instantiation_system)
    (union_narrowed instantiation_union_sockets) instantiation_correspondence"
  "narrowed_declarations_discharged (positive_meaning prospective_instantiation_system)
    (union_narrowed prospective_union_sockets) instantiation_correspondence"
  "narrowed_declarations_discharged (positive_meaning vector_instantiation_system) (union_narrowed vector_union_sockets)
    schema_instantiation_correspondence"
  "narrowed_declarations_discharged (positive_meaning premise_rows_system) (union_narrowed premise_rows_union_sockets)
    schema_instantiation_correspondence"
  using quotation_union_socket_discharged instantiation_union_socket_discharged prospective_union_socket_discharged
    vector_union_socket_discharged premise_rows_union_socket_discharged
  by (simp_all add: narrowed_declarations_discharged_def union_narrowed_def declarations_formed_def
    quotation_union_sockets_def instantiation_union_sockets_def prospective_union_sockets_def vector_union_sockets_def
    premise_rows_union_sockets_def join_view_formed instantiation_views_formed premise_views_formed)

definition quotation_union_frames :: "(nat,nat,nat) resolution_frames" where
  "quotation_union_frames = {|(50,quotation_pair_socket_schema,7,{|6|})|}"

definition instantiation_union_frames :: "(nat,nat,nat) resolution_frames" where
  "instantiation_union_frames = {|(55,instantiation_pair_socket_schema,7,{|9|}),
    (55,instantiation_pair_socket_schema,8,{|7|})|}"

definition prospective_union_frames :: "(nat,nat,nat) resolution_frames" where
  "prospective_union_frames = {|(57,prospective_socket_schema,8,{|9|})|}"

definition vector_union_frames :: "(nat,nat,nat) resolution_frames" where
  "vector_union_frames = {|(60,vector_cons_socket_schema,4,{|10|}),(60,vector_cons_socket_schema,5,{|8|})|}"

definition premise_rows_union_frames :: "(nat,nat,nat) resolution_frames" where
  "premise_rows_union_frames = {|(63,premise_call_socket_schema,2,{|11|}),(63,premise_material_socket_schema,2,{|9|})|}"

theorem union_frames_discharged:
  "narrowed_frames_discharged (positive_meaning quotation_admission_system) (union_narrowed quotation_union_sockets)
    quotation_union_frames"
  "narrowed_frames_discharged (positive_meaning pattern_instantiation_system) (union_narrowed instantiation_union_sockets)
    instantiation_union_frames"
  "narrowed_frames_discharged (positive_meaning prospective_instantiation_system)
    (union_narrowed prospective_union_sockets) prospective_union_frames"
  "narrowed_frames_discharged (positive_meaning vector_instantiation_system) (union_narrowed vector_union_sockets)
    vector_union_frames"
  "narrowed_frames_discharged (positive_meaning premise_rows_system) (union_narrowed premise_rows_union_sockets)
    premise_rows_union_frames"
  using quotation_union_socket_framed instantiation_slots_union_socket_framed instantiation_used_union_socket_framed
    prospective_union_socket_framed vector_slots_union_socket_framed vector_used_union_socket_framed
    premise_call_union_socket_framed premise_material_union_socket_framed
  by (auto simp: narrowed_frames_discharged_def union_narrowed_def quotation_union_sockets_def
    instantiation_union_sockets_def prospective_union_sockets_def vector_union_sockets_def premise_rows_union_sockets_def
    quotation_union_frames_def instantiation_union_frames_def prospective_union_frames_def vector_union_frames_def
    premise_rows_union_frames_def)

text \<open>
  The registration's completeness at the eight sockets: at each, every true instance of the caller clause extends to one
  through the registration's value at its input, formed and a distinct list, wherever the program searched reads
  selection (5) as the given's does.
\<close>

lemmas union_registration_complete_sockets =
  union_registration_complete[OF quotation_admission_components(9) _ quotation_union_socket_discharged]
  union_registration_complete[OF pattern_instantiation_components(10) _ instantiation_union_socket_discharged(1)]
  union_registration_complete[OF pattern_instantiation_components(10) _ instantiation_union_socket_discharged(2)]
  union_registration_complete[OF prospective_instantiation_components(8) _ prospective_union_socket_discharged]
  union_registration_complete[OF vector_instantiation_components(5) _ vector_union_socket_discharged(1)]
  union_registration_complete[OF vector_instantiation_components(5) _ vector_union_socket_discharged(2)]
  union_registration_complete[OF premise_rows_components(4) _ premise_rows_union_socket_discharged(1)]
  union_registration_complete[OF premise_rows_components(4) _ premise_rows_union_socket_discharged(2)]

end
