theory Factor_Definition_Reading_Declarations
  imports Factor_Schema_Instantiation_Declarations Factor_Stated_Leaves Factor_Row_Selection_Socket_Declarations
begin

text \<open>
  The instantiation family's third part (R6c of DECISIONS.md "The native evaluator constructs the missing witnesses
  by resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", (a) and (b)):
  the definition readings and the stated clause. Scoped instantiation (56), declared by the first part at its scoped
  view, is committed directly at definition call admission's clause (72.0/2), payload disjointness (49) its consumer;
  the emptiness checks 500–502 are the consumers of schema instantiation (65) at the clause payload audit (503.0/0);
  56 is kept at the interface slot clause (105.0/2), its term free; the stated clause (587) is
  declared at its report view with the free socket 65 at its ground clause; the element-wise traversals 584 and 586
  are carriers from their contracts. Each record is discharged at the system where its clause stands. No clause of
  any program changes, and the declarations are read by the committed search alone.
\<close>

section \<open>72.0/2: scoped instantiation committed directly, payload disjointness its consumer\<close>

text \<open>
  At 72.0/2 scoped instantiation reads its source, root and term (72's operand, an input of the head) and gives the
  table, interior and slots (@{const scoped_view}); the interior is held by payload disjointness at 72.0/4 and 72.0/6,
  each at R5's identity view, the interior its right side, and nothing else holds an output. Payload disjointness
  reads its right list as a set of distinct payloads (@{thm [source] payload_disjoint_exact}), so a bag of it is
  answered as it is.
\<close>

lemma interior_disjoint_consumer:
  "consumer_discharged (positive_meaning payload_disjoint_system) 49 view_identity bag_corresponds"
proof -
  have sym: "symp bag_corresponds" unfolding symp_def bag_corresponds_def by (metis (no_types))
  have "carrier_discharged (positive_meaning payload_disjoint_system) 49 (consumer_carrier_view view_identity)
      (consumer_input view_identity bag_corresponds) (=)"
    by (rule carrier_discharged_mono[OF disjoint_consumer_carrier]) (auto simp: consumer_input_def)
  then show ?thesis by (rule consumer_discharged_carrier[OF view_identity_formed sym, THEN iffD2])
qed

text \<open>
  56's producer declaration is the first part's (@{text scoped_declarations}), reaching this clause's system by
  agreement; this record holds what the clause newly needs, the consumer of the interior hole.
\<close>

definition call_admission_declarations :: "(nat,nat,nat) resolution_declarations" where
  "call_admission_declarations = \<lparr>declared_producers = {||},
    declared_consumers = {|(56,49,view_identity,1)|}, declared_sockets = {||}\<rparr>"

theorem call_admission_declarations_discharged:
  "declarations_discharged (positive_meaning definition_call_admission_system) call_admission_declarations
    instantiation_correspondence"
proof -
  have consumer: "consumer_discharged (positive_meaning definition_call_admission_system) 49 view_identity
      (instantiation_correspondence 56 1)"
    using interior_disjoint_consumer
    by (simp add: consumer_discharged_site[OF definition_call_admission_components(5)] instantiation_correspondence_def)
  show ?thesis using consumer
    by (simp add: declarations_discharged_def declarations_formed_def call_admission_declarations_def
      view_identity_formed)
qed

section \<open>503.0/0: the emptiness checks as consumers of schema instantiation's holes\<close>

text \<open>
  The clause payload audit (503) gives schema instantiation's term, call rows and material rows (the second part's
  @{const schema_holes}) to 500, 502 and 501, each reading its whole argument (@{const whole_view}). The term's hole
  corresponds by equality; the rows' holes by bags, and each row check holds of a list exactly when every row does
  (@{text empty_payload_rows_list}, @{text empty_payload_calls_list}, from the checks' clauses and
  @{thm [source] empty_payloads_exact}), so a bag of rows is answered as the rows are.
\<close>

lemma empty_payload_rows_list:
  "(501,data_list_term zs) \<in> positive_meaning empty_payload_rows_system \<longleftrightarrow>
    term_formed (data_list_term zs) \<and>
      (\<forall>z\<in>set zs. \<exists>k x. z = Pair_Term k x \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
proof (induction zs)
  case Nil
  have "(501,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion (data_list_nil_schema::(nat,nat,nat) factor_schema)))
      \<in>positive_meaning empty_payload_rows_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (auto simp: empty_payload_rows_clauses_def data_list_nil_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def empty_payload_rows_call)
  then show ?case by (simp add: data_list_nil_schema_def octets_formed_def)
next
  case (Cons z zs)
  show ?case
  proof
    assume holds: "(501,data_list_term (z#zs)) \<in> positive_meaning empty_payload_rows_system"
    have formed: "term_formed (data_list_term (z#zs))"
      using positive_meaning_formed[OF holds] by (simp add: empty_payload_rows_call)
    obtain k x where z: "z = Pair_Term k x" "(500,x) \<in> positive_meaning empty_payloads_system"
        "(501,data_list_term zs) \<in> positive_meaning empty_payload_rows_system"
      using empty_payload_rows_cases[OF holds] by auto
    then show "term_formed (data_list_term (z#zs)) \<and>
        (\<forall>z\<in>set (z#zs). \<exists>k x. z = Pair_Term k x \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
      using formed Cons.IH by auto
  next
    assume given: "term_formed (data_list_term (z#zs)) \<and>
      (\<forall>z\<in>set (z#zs). \<exists>k x. z = Pair_Term k x \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
    then obtain k x where z: "z = Pair_Term k x" "(500,x) \<in> positive_meaning empty_payloads_system" by auto
    have parts: "term_formed k" "term_formed x" "term_formed (data_list_term zs)"
      "(501,data_list_term zs) \<in> positive_meaning empty_payload_rows_system"
      using given Cons.IH by (auto simp: z)
    let ?h="\<lambda>n::nat. if n=0 then k else if n=1 then x else data_list_term zs"
    have "(501,evaluate_pattern ?h (schema_conclusion empty_payload_rows_schema))\<in>positive_meaning empty_payload_rows_system"
      by (rule ordinary_positive_formed_step[where c=1])
        (use parts z in \<open>auto simp: empty_payload_rows_clauses_def empty_payload_rows_schema_def
          schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payload_rows_call
          empty_payload_rows_empty\<close>)
    then show "(501,data_list_term (z#zs)) \<in> positive_meaning empty_payload_rows_system"
      by (simp add: z empty_payload_rows_schema_def)
  qed
qed

lemma empty_payload_calls_list:
  "(502,data_list_term zs) \<in> positive_meaning empty_payload_calls_system \<longleftrightarrow>
    term_formed (data_list_term zs) \<and>
      (\<forall>z\<in>set zs. \<exists>k d x. z = Pair_Term k (Pair_Term d x) \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
proof (induction zs)
  case Nil
  have "(502,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion (data_list_nil_schema::(nat,nat,nat) factor_schema)))
      \<in>positive_meaning empty_payload_calls_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (auto simp: empty_payload_calls_clauses_def data_list_nil_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def empty_payload_calls_call)
  then show ?case by (simp add: data_list_nil_schema_def octets_formed_def)
next
  case (Cons z zs)
  show ?case
  proof
    assume holds: "(502,data_list_term (z#zs)) \<in> positive_meaning empty_payload_calls_system"
    have formed: "term_formed (data_list_term (z#zs))"
      using positive_meaning_formed[OF holds] by (simp add: empty_payload_calls_call)
    obtain k d x where z: "z = Pair_Term k (Pair_Term d x)" "(500,x) \<in> positive_meaning empty_payloads_system"
        "(502,data_list_term zs) \<in> positive_meaning empty_payload_calls_system"
      using empty_payload_calls_cases[OF holds] by auto
    then show "term_formed (data_list_term (z#zs)) \<and>
        (\<forall>z\<in>set (z#zs). \<exists>k d x. z = Pair_Term k (Pair_Term d x) \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
      using formed Cons.IH by auto
  next
    assume given: "term_formed (data_list_term (z#zs)) \<and>
      (\<forall>z\<in>set (z#zs). \<exists>k d x. z = Pair_Term k (Pair_Term d x) \<and> (500,x) \<in> positive_meaning empty_payloads_system)"
    then obtain k d x where z: "z = Pair_Term k (Pair_Term d x)" "(500,x) \<in> positive_meaning empty_payloads_system"
      by auto
    have parts: "term_formed k" "term_formed d" "term_formed x" "term_formed (data_list_term zs)"
      "(502,data_list_term zs) \<in> positive_meaning empty_payload_calls_system"
      using given Cons.IH by (auto simp: z)
    let ?h="\<lambda>n::nat. if n=0 then k else if n=1 then d else if n=2 then x else data_list_term zs"
    have "(502,evaluate_pattern ?h (schema_conclusion empty_payload_calls_schema))\<in>positive_meaning empty_payload_calls_system"
      by (rule ordinary_positive_formed_step[where c=1])
        (use parts z in \<open>auto simp: empty_payload_calls_clauses_def empty_payload_calls_schema_def
          schema_formed_def schema_variables_def single_valued_def rel_dom_def empty_payload_calls_call
          empty_payload_calls_empty\<close>)
    then show "(502,data_list_term (z#zs)) \<in> positive_meaning empty_payload_calls_system"
      by (simp add: z empty_payload_calls_schema_def)
  qed
qed

lemma whole_bag_consumer:
  assumes lists: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (e,data_list_term xs) \<in> M \<Longrightarrow> (e,data_list_term ys) \<in> M"
  shows "consumer_discharged M e whole_view bag_corresponds"
proof (rule whole_consumer)
  fix v v' assume "bag_corresponds v v'" "(e,v) \<in> M"
  then show "(e,v') \<in> M" unfolding bag_corresponds_def using lists by blast
next
  fix v v' assume "bag_corresponds v v'"
  then show "bag_corresponds v' v" unfolding bag_corresponds_def by (metis (no_types))
qed

lemma audit_consumers:
  "consumer_discharged (positive_meaning clause_payloads_system) 500 whole_view (=)"
  "consumer_discharged (positive_meaning clause_payloads_system) 502 whole_view bag_corresponds"
  "consumer_discharged (positive_meaning clause_payloads_system) 501 whole_view bag_corresponds"
proof -
  show "consumer_discharged (positive_meaning clause_payloads_system) 500 whole_view (=)"
    by (rule whole_consumer) blast+
  have calls: "consumer_discharged (positive_meaning empty_payload_calls_system) 502 whole_view bag_corresponds"
  proof (rule whole_bag_consumer)
    fix xs ys :: "factor_term list" assume m: "mset xs = mset ys"
      and h: "(502,data_list_term xs) \<in> positive_meaning empty_payload_calls_system"
    have s: "set ys = set xs" using mset_eq_setD[OF m] by (rule sym)
    show "(502,data_list_term ys) \<in> positive_meaning empty_payload_calls_system"
      using h by (simp only: empty_payload_calls_list stated_list_formed s)
  qed
  have rows: "consumer_discharged (positive_meaning empty_payload_rows_system) 501 whole_view bag_corresponds"
  proof (rule whole_bag_consumer)
    fix xs ys :: "factor_term list" assume m: "mset xs = mset ys"
      and h: "(501,data_list_term xs) \<in> positive_meaning empty_payload_rows_system"
    have s: "set ys = set xs" using mset_eq_setD[OF m] by (rule sym)
    show "(501,data_list_term ys) \<in> positive_meaning empty_payload_rows_system"
      using h by (simp only: empty_payload_rows_list stated_list_formed s)
  qed
  show "consumer_discharged (positive_meaning clause_payloads_system) 502 whole_view bag_corresponds"
    using calls by (simp only: consumer_discharged_site[OF clause_payloads_components(4)])
  show "consumer_discharged (positive_meaning clause_payloads_system) 501 whole_view bag_corresponds"
    using rows by (simp only: consumer_discharged_site[OF clause_payloads_components(3)])
qed

text \<open>
  65's producer declaration is the second part's (@{text schema_declarations}); this record holds the consumers the
  clause newly needs, each naming the hole it holds.
\<close>

definition clause_payloads_declarations :: "(nat,nat,nat) resolution_declarations" where
  "clause_payloads_declarations = \<lparr>declared_producers = {||},
    declared_consumers = {|(65,500,whole_view,0),(65,502,whole_view,1),(65,501,whole_view,2)|},
    declared_sockets = {||}\<rparr>"

theorem clause_payloads_declarations_discharged:
  "declarations_discharged (positive_meaning clause_payloads_system) clause_payloads_declarations
    schema_instantiation_correspondence"
  using audit_consumers
  by (simp add: declarations_discharged_def declarations_formed_def clause_payloads_declarations_def whole_view_formed
    schema_instantiation_correspondence_def)

section \<open>The stated clause (587) at its report view\<close>

text \<open>
  The stated clause reads a schema's source, use and root and gives its report: the ground field, the stated leaves
  of its conclusion, and its call and material rows keyed by their sockets in any order
  (@{thm [source] stated_clause_exact}). The ground field and the leaves are determined by the schema; the two row
  lists are bags of its call and material sockets.
\<close>

definition stated_view :: "nat resolution_view" where
  "stated_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Variable 2)) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 4)
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 4)
      (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))))"

definition stated_holes :: "nat finite_term_pattern list" where
  "stated_holes = [Finite_Variable 3,Finite_Variable 4,Finite_Variable 5,Finite_Variable 6]"

definition stated_correspondence :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "stated_correspondence d i = (if d = 587 \<and> i \<in> {0,1} then (=) else bag_corresponds)"

lemma stated_view_formed: "view_formed stated_view"
  by (auto simp: view_formed_def stated_view_def fset_eq_iff)

lemma stated_view_holes: "view_holes stated_view stated_holes"
  by (simp add: view_holes_def stated_view_def stated_holes_def)

lemma distinct_keyed_mset:
  assumes "distinct (map fst xs)" "distinct (map fst ys)" "set xs = set ys"
  shows "mset xs = mset ys"
  using assms by (simp add: set_eq_iff_mset_eq_distinct[symmetric] distinct_map)

lemma stated_answers:
  assumes one: "(587,Pair_Term (Pair_Term (Pair_Term e u) a) (Pair_Term g (Pair_Term l (Pair_Term q m))))
      \<in> positive_meaning stated_clause_system"
    and two: "(587,Pair_Term (Pair_Term (Pair_Term e u) a) (Pair_Term g' (Pair_Term l' (Pair_Term q' m'))))
      \<in> positive_meaning stated_clause_system"
  shows "g = g' \<and> l = l' \<and> bag_corresponds q q' \<and> bag_corresponds m m'"
proof -
  obtain E v r S where s1: "environment_value_presents E e" "u = use_data_term v" "a = Payload_Term r"
      "native_schema_at E v r S" "clause_stated_presents S (Pair_Term g (Pair_Term l (Pair_Term q m)))"
    using one by (auto simp: stated_clause_exact)
  obtain E' v' r' S' where s2: "environment_value_presents E' e" "u = use_data_term v'" "a = Payload_Term r'"
      "native_schema_at E' v' r' S'" "clause_stated_presents S' (Pair_Term g' (Pair_Term l' (Pair_Term q' m')))"
    using two by (auto simp: stated_clause_exact)
  have "E' = E" by (rule environment_value_presents_unique[OF s2(1) s1(1)])
  moreover have "v' = v" using s1(2) s2(2) use_data_term_injective by (metis injD)
  moreover have "r' = r" using s1(3) s2(3) by simp
  ultimately have "S' = S" using native_schema_unique[OF s2(4)] s1(4) by simp
  then have p2: "clause_stated_presents S (Pair_Term g' (Pair_Term l' (Pair_Term q' m')))" using s2(5) by simp
  obtain qs ms where r1: "distinct (map fst qs)" "set qs = clause_calls S" "distinct (map fst ms)"
      "set ms = clause_materials S" "g = data_list_term (clause_ground S)"
      "l = data_list_term (pattern_stated (schema_conclusion S))" "q = data_list_term (map place_term qs)"
      "m = data_list_term (map material_place_term ms)"
    using s1(5) by (auto simp: clause_stated_presents_def)
  obtain qs' ms' where r2: "distinct (map fst qs')" "set qs' = clause_calls S" "distinct (map fst ms')"
      "set ms' = clause_materials S" "g' = data_list_term (clause_ground S)"
      "l' = data_list_term (pattern_stated (schema_conclusion S))" "q' = data_list_term (map place_term qs')"
      "m' = data_list_term (map material_place_term ms')"
    using p2 by (auto simp: clause_stated_presents_def)
  have "mset qs = mset qs'" by (rule distinct_keyed_mset) (simp_all add: r1 r2)
  moreover have "mset ms = mset ms'" by (rule distinct_keyed_mset) (simp_all add: r1 r2)
  ultimately show ?thesis by (simp add: r1(5-8) r2(5-8) bag_corresponds_mapped)
qed

theorem stated_producer_discharged:
  "producer_discharged (positive_meaning stated_clause_system) 587 stated_view stated_holes (stated_correspondence 587)"
proof (rule producer_discharged_valuations[OF stated_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(587,evaluate_pattern g (decode_finite_pattern (fst stated_view))) \<in> positive_meaning stated_clause_system"
    and b: "(587,evaluate_pattern g' (decode_finite_pattern (fst stated_view))) \<in> positive_meaning stated_clause_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd stated_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd stated_view)))"
    and i: "i < length stated_holes"
  have a': "(587,Pair_Term (Pair_Term (Pair_Term (g 0) (g 1)) (g 2)) (Pair_Term (g 3) (Pair_Term (g 4)
      (Pair_Term (g 5) (g 6))))) \<in> positive_meaning stated_clause_system"
    using a by (simp add: stated_view_def)
  have b': "(587,Pair_Term (Pair_Term (Pair_Term (g 0) (g 1)) (g 2)) (Pair_Term (g' 3) (Pair_Term (g' 4)
      (Pair_Term (g' 5) (g' 6))))) \<in> positive_meaning stated_clause_system"
    using b same by (simp add: stated_view_def)
  have "g 3 = g' 3 \<and> g 4 = g' 4 \<and> bag_corresponds (g 5) (g' 5) \<and> bag_corresponds (g 6) (g' 6)"
    by (rule stated_answers[OF a' b'])
  then show "stated_correspondence 587 i (evaluate_pattern g (decode_finite_pattern (stated_holes ! i)))
      (evaluate_pattern g' (decode_finite_pattern (stated_holes ! i)))"
    using i by (auto simp: stated_holes_def stated_correspondence_def numeral_eq_Suc less_Suc_eq)
qed

section \<open>587.0/0: schema instantiation at the ground clause, a free socket, 580 carrying its term\<close>

text \<open>
  The ground clause calls schema instantiation with the empty table and empty call and material rows: those are
  input at @{text schema_conclusion_view}, the term alone out, determined by them
  (@{thm [source] schema_instantiation_result_unique}). The term is the report's ground field and is read by the
  stated leaves (580), a carrier of it into the leaves the head reports; nothing else holds it.
\<close>

definition schema_conclusion_view :: "nat resolution_view" where
  "schema_conclusion_view = (fst schema_view,
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3)
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)))),
    Finite_Variable 4)"

lemma schema_conclusion_view_formed: "view_formed schema_conclusion_view"
  by (auto simp: view_formed_def schema_conclusion_view_def schema_view_def fset_eq_iff)

theorem schema_conclusion_producer_discharged:
  "producer_discharged (positive_meaning schema_instantiation_system) 65 schema_conclusion_view
    [snd (snd schema_conclusion_view)] (\<lambda>_. (=))"
proof (rule producer_discharged_valuations[OF schema_conclusion_view_formed])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(65,evaluate_pattern g (decode_finite_pattern (fst schema_conclusion_view)))
      \<in> positive_meaning schema_instantiation_system"
    and b: "(65,evaluate_pattern g' (decode_finite_pattern (fst schema_conclusion_view)))
      \<in> positive_meaning schema_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd schema_conclusion_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd schema_conclusion_view)))"
    and i: "i < length [snd (snd schema_conclusion_view)]"
  have a': "(65,schema_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
      \<in> positive_meaning schema_instantiation_system"
    using a by (simp add: schema_conclusion_view_def schema_view_def)
  have b': "(65,schema_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g' 4) (g 5) (g 6))
      \<in> positive_meaning schema_instantiation_system"
    using b same by (simp add: schema_conclusion_view_def schema_view_def)
  have "g 4 = g' 4" using schema_answers[OF a' b'] by blast
  then show "evaluate_pattern g (decode_finite_pattern ([snd (snd schema_conclusion_view)] ! i)) =
      evaluate_pattern g' (decode_finite_pattern ([snd (snd schema_conclusion_view)] ! i))"
    using i by (simp add: schema_conclusion_view_def)
qed

definition stated_ground_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "stated_ground_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2))
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Payload []))
        (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])))),
    finite_schema_premises = {|(0,65,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
          (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])))))),
      (1,580,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 7)))|},
    finite_schema_materials = {||}\<rparr>"

lemma stated_ground_socket_decoded: "decode_finite_schema stated_ground_socket_schema = stated_clause_ground_schema"
  by (simp add: stated_ground_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def stated_clause_ground_schema_def)

lemma stated_ground_producer:
  "producer_discharged (positive_meaning stated_clause_system) 65 schema_conclusion_view
    [snd (snd schema_conclusion_view)] (\<lambda>_. (=))"
  using schema_conclusion_producer_discharged by (simp add: producer_discharged_site[OF stated_clause_components(1)])

lemma stated_leaves_term_carrier:
  "carrier_discharged (positive_meaning stated_clause_system) 580 join_view (=) (=)"
  by (auto simp: carrier_discharged_def)

definition stated_ground_carriers :: "nat clause_carrier list" where
  "stated_ground_carriers = [(1,join_view,(=),(=))]"

lemmas stated_ground_listed_simps = socket_listed_simps view_listed[OF schema_conclusion_view_def]
  view_listed[OF stated_view_def] schema_view_def stated_ground_carriers_def stated_ground_socket_schema_def

theorem stated_ground_socket_carried:
  "socket_carried (positive_meaning stated_clause_system) stated_ground_socket_schema 0 False schema_conclusion_view
    stated_view (=) stated_ground_carriers"
  by (rule socket_carried_listed[OF meaning_answers_formed schema_conclusion_view_formed stated_ground_producer,
      where \<sigma> = "\<lambda>v. v"])
    (simp add: stated_ground_listed_simps stated_leaves_term_carrier)

lemma stated_ground_carried_variables:
  "carried_variables stated_ground_socket_schema 0 schema_conclusion_view stated_ground_carriers = {4,7}"
  by (auto simp: stated_ground_listed_simps)

theorem stated_ground_socket_framed:
  "socket_framed (positive_meaning stated_clause_system) stated_ground_socket_schema 0 False schema_conclusion_view
    stated_view {4,7}"
  using socket_framed_carried[OF stated_ground_socket_carried] by (simp only: stated_ground_carried_variables)

theorem stated_ground_socket_discharged:
  "socket_discharged (positive_meaning stated_clause_system) stated_ground_socket_schema 0 False
    schema_conclusion_view stated_view"
  by (rule socket_discharged_carried[OF stated_ground_socket_carried])

section \<open>An element-wise traversal carries a bag of its list to a bag of its results\<close>

text \<open>
  A traversal relating a list element by element in a context (@{thm [source] related_list_profile.exact}) relates a
  permuted list to the results permuted alike: at @{const join_view}, the context and list in and the result list
  out, it is a carrier from a bag of the list to a bag of the results. Stated once for every such profile; 584 (the
  call rows' stated leaves) and 586 (the material rows') are its instances.
\<close>


context related_list_profile
begin

theorem bag_carrier:
  "carrier_discharged (positive_meaning P) list_site join_view (tuple_corresponds [(=),bag_corresponds])
    bag_corresponds"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix t x y x'
  assume holds: "(list_site,t) \<in> positive_meaning P" and vt: "resolution_view_term join_view t = Some (x,y)"
    and cx: "tuple_corresponds [(=),bag_corresponds] x x'"
  obtain a xs ys where t: "t = context_relation_argument a (data_list_term xs) (data_list_term ys)"
      and af: "term_formed a" and rel: "list_all2 (related a) xs ys"
    using sound[OF holds] by blast
  have x: "x = Pair_Term a (data_list_term xs)" and y: "y = data_list_term ys"
    using vt t by (simp_all add: join_view_term)
  obtain x2 where x': "x' = Pair_Term a x2" and b: "bag_corresponds (data_list_term xs) x2" using cx x by auto
  obtain xs' where xs': "x2 = data_list_term xs'" "mset xs' = mset xs" using b by (rule bag_corresponds_list)
  obtain ys' where ys': "list_all2 (related a) xs' ys'" "mset ys' = mset ys"
    using list_all2_reorder_left_invariance[OF rel xs'(2)] by blast
  have "(list_site,context_relation_argument a (data_list_term xs') (data_list_term ys')) \<in> positive_meaning P"
    by (rule complete[OF af ys'(1)])
  moreover have "resolution_view_term join_view (context_relation_argument a (data_list_term xs') (data_list_term ys'))
      = Some (x',data_list_term ys')"
    by (simp add: join_view_term x' xs'(1))
  moreover have "bag_corresponds y (data_list_term ys')" using ys'(2) by (simp add: y bag_corresponds_lists)
  ultimately show "\<exists>b y'. (list_site,b) \<in> positive_meaning P \<and> resolution_view_term join_view b = Some (x',y') \<and>
      bag_corresponds y y'" by blast
qed

end

lemma stated_clause_carriers:
  "carrier_discharged (positive_meaning stated_clause_system) 584 join_view (tuple_corresponds [(=),bag_corresponds])
    bag_corresponds"
  "carrier_discharged (positive_meaning stated_clause_system) 586 join_view (tuple_corresponds [(=),bag_corresponds])
    bag_corresponds"
  using stated_calls_profile.bag_carrier stated_materials_profile.bag_carrier
  by (simp_all add: carrier_discharged_site[OF stated_clause_components(4)]
    carrier_discharged_site[OF stated_clause_components(5)])

section \<open>105.0/2: scoped instantiation at its pattern, kept, 5 carrying its slots\<close>

text \<open>
  At 105.0/2 scoped instantiation reads the interface's source and root with its term free (a premise-only variable
  of the clause), so it is read at @{const application_view}, the first part's view of that shape: the source, use
  and root in; the table and term, interior and slots out. Every answer at one input reads the one scoped pattern at
  that root
  (@{thm [source] scoped_pattern_unique}), so its interior and slots are the pattern's, in any order; its table and
  term are one instance among all, which the clause reads nowhere. The slots go to 5, which selects the demanded slot
  and returns a remainder no other goal holds (@{thm [source] selection_carrier}).
\<close>


abbreviation pattern_correspondence :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "pattern_correspondence \<equiv> tuple_corresponds [\<lambda>_ _. True,bag_corresponds,term_bag_transport]"

lemma pattern_answers:
  assumes first: "(56,scoped_instantiation_argument e u r b t i k) \<in> positive_meaning scoped_instantiation_system"
    and second: "(56,scoped_instantiation_argument e u r b' t' i' k') \<in> positive_meaning scoped_instantiation_system"
  shows "bag_corresponds i i' \<and> term_bag_transport k k'"
proof -
  obtain E where source: "environment_value_presents E e" using first by (auto simp: scoped_instantiation_exact)
  obtain v a xs p Is Ks where one: "u = use_data_term v" "r = Payload_Term a"
      "i = data_list_term (map Payload_Term Is)" "k = data_list_term (map Payload_Term Ks)"
      "distinct Is" "distinct Ks" "scoped_pattern_at E v a p (set Is) (set Ks)"
    using first by (auto simp: scoped_instantiation_at_source[OF source])
  obtain v' a' ys p' Js Ls where two: "u = use_data_term v'" "r = Payload_Term a'"
      "i' = data_list_term (map Payload_Term Js)" "k' = data_list_term (map Payload_Term Ls)"
      "distinct Js" "distinct Ls" "scoped_pattern_at E v' a' p' (set Js) (set Ls)"
    using second by (auto simp: scoped_instantiation_at_source[OF source])
  have "v' = v" using one(1) two(1) use_data_term_injective by (metis injD)
  moreover have "a' = a" using one(2) two(2) by simp
  ultimately have "p = p' \<and> set Is = set Js \<and> set Ks = set Ls"
    using scoped_pattern_unique[OF one(7)] two(7) by simp
  then have "mset Is = mset Js" "mset Ks = mset Ls"
    using one(5,6) two(5,6) by (simp_all add: set_eq_iff_mset_eq_distinct)
  then show ?thesis by (simp add: one(3,4) two(3,4) bag_corresponds_mapped term_bag_transport_lists)
qed

theorem pattern_producer_discharged:
  "producer_discharged (positive_meaning scoped_instantiation_system) 56 application_view [snd (snd application_view)]
    (\<lambda>_. pattern_correspondence)"
proof (rule producer_discharged_valuations[OF instantiation_views_formed(5)])
  fix g g' :: "nat \<Rightarrow> factor_term" and i :: nat
  assume a: "(56,evaluate_pattern g (decode_finite_pattern (fst application_view))) \<in> positive_meaning scoped_instantiation_system"
    and b: "(56,evaluate_pattern g' (decode_finite_pattern (fst application_view))) \<in> positive_meaning scoped_instantiation_system"
    and same: "evaluate_pattern g (decode_finite_pattern (fst (snd application_view))) =
      evaluate_pattern g' (decode_finite_pattern (fst (snd application_view)))"
    and i: "i < length [snd (snd application_view)]"
  have a': "(56,scoped_instantiation_argument (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
      \<in> positive_meaning scoped_instantiation_system"
    using a by (simp add: application_view_def)
  have b': "(56,scoped_instantiation_argument (g 0) (g 1) (g 2) (g' 3) (g' 4) (g' 5) (g' 6))
      \<in> positive_meaning scoped_instantiation_system"
    using b same by (simp add: application_view_def)
  have "bag_corresponds (g 5) (g' 5) \<and> term_bag_transport (g 6) (g' 6)" by (rule pattern_answers[OF a' b'])
  then show "pattern_correspondence (evaluate_pattern g (decode_finite_pattern ([snd (snd application_view)] ! i)))
      (evaluate_pattern g' (decode_finite_pattern ([snd (snd application_view)] ! i)))"
    using i by (simp add: application_view_def)
qed

definition interface_slot_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "interface_slot_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 8))),
      (1,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 6))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 7)) (Finite_Pattern_Payload [])))),
      (2,56,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 10))
          (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12))))),
      (3,5,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 12) (Finite_Variable 13)))|},
    finite_schema_materials = {||}\<rparr>"

lemma interface_slot_socket_decoded:
  "decode_finite_schema interface_slot_socket_schema = definition_interface_slot_schema"
  by (simp add: interface_slot_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def definition_interface_slot_schema_def)

lemma interface_slot_producer:
  "producer_discharged (positive_meaning definition_slot_reading_system) 56 application_view [snd (snd application_view)]
    (\<lambda>_. pattern_correspondence)"
  using pattern_producer_discharged by (simp add: producer_discharged_site[OF definition_slot_reading_scoped])

theorem interface_slot_socket_carried:
  "socket_carried (positive_meaning definition_slot_reading_system) interface_slot_socket_schema 2 True application_view
    view_identity pattern_correspondence (selection_carriers 3)"
  by (rule socket_carried_listed[OF meaning_answers_formed instantiation_views_formed(5) interface_slot_producer,
      where \<sigma> = "\<lambda>v. if v = 9 then 3 else if v = 10 then 4 else if v = 11 then 5 else if v = 12 then 6 else v"])
    (simp add: row_selection_listed_simps view_listed[OF application_view_def] interface_slot_socket_schema_def
      selection_carrier_at[OF definition_slot_reading_components(4)])

lemma interface_slot_carried_variables:
  "carried_variables interface_slot_socket_schema 2 application_view (selection_carriers 3) = {9,10,11,12,13}"
  by (auto simp: row_selection_listed_simps view_listed[OF application_view_def] interface_slot_socket_schema_def)

theorem interface_slot_socket_framed:
  "socket_framed (positive_meaning definition_slot_reading_system) interface_slot_socket_schema 2 True application_view
    view_identity {9,10,11,12,13}"
  using socket_framed_carried[OF interface_slot_socket_carried] by (simp only: interface_slot_carried_variables)

theorem interface_slot_socket_discharged:
  "socket_discharged (positive_meaning definition_slot_reading_system) interface_slot_socket_schema 2 True
    application_view view_identity"
  by (rule socket_discharged_carried[OF interface_slot_socket_carried])

section \<open>The records at the notions' systems\<close>

definition stated_clause_declarations :: "(nat,nat,nat) resolution_declarations" where
  "stated_clause_declarations = \<lparr>declared_producers = {|(587,stated_view,stated_holes)|},
    declared_consumers = {||},
    declared_sockets = {|(587,stated_ground_socket_schema,0,False,schema_conclusion_view,stated_view)|}\<rparr>"

definition stated_clause_frames :: "(nat,nat,nat) resolution_frames" where
  "stated_clause_frames = {|(587,stated_ground_socket_schema,0,{|4,7|})|}"

theorem stated_clause_declarations_discharged:
  "declarations_discharged (positive_meaning stated_clause_system) stated_clause_declarations stated_correspondence"
  using stated_producer_discharged stated_ground_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def stated_clause_declarations_def stated_view_formed
    schema_conclusion_view_formed)

theorem stated_clause_frames_discharged:
  "frames_discharged (positive_meaning stated_clause_system) stated_clause_declarations stated_clause_frames"
  using stated_ground_socket_framed
  by (auto simp: frames_discharged_def stated_clause_declarations_def stated_clause_frames_def)

definition interface_slot_declarations :: "(nat,nat,nat) resolution_declarations" where
  "interface_slot_declarations = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(105,interface_slot_socket_schema,2,True,application_view,view_identity)|}\<rparr>"

definition interface_slot_frames :: "(nat,nat,nat) resolution_frames" where
  "interface_slot_frames = {|(105,interface_slot_socket_schema,2,{|9,10,11,12,13|})|}"

theorem interface_slot_declarations_discharged:
  "declarations_discharged (positive_meaning definition_slot_reading_system) interface_slot_declarations
    instantiation_correspondence"
  using interface_slot_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def interface_slot_declarations_def
    instantiation_views_formed(5) view_identity_formed)

theorem interface_slot_frames_discharged:
  "frames_discharged (positive_meaning definition_slot_reading_system) interface_slot_declarations
    interface_slot_frames"
  using interface_slot_socket_framed
  by (auto simp: frames_discharged_def interface_slot_declarations_def interface_slot_frames_def)

end
