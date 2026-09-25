theory Factor_Stated_Leaves
  imports Factor_Payload_Audit Factor_Related_Lists Factor_Executable_Material_Syntax Factor_Term_Sequence_Operations
begin

declare One_nat_def [simp del]

section \<open>What a definition states: its target leaves, its empty payloads and its ground clauses\<close>

text \<open>
  A place of a definition is its interface, a clause's conclusion, an ordinary premise's argument at its
  socket, or a material premise's operand at its socket and field. At each place the reader reports, in
  order, the target leaves the place states and each empty payload it states; for each clause it reports
  whether the clause is ground (an empty binder scope and no premise) and then the term it asserts. The
  reader computes and does not judge: which reported leaf a candidate may not state is the criticism's
  classification (DECISIONS.md, the entry of task 381, parts (e) and (h)).

  The method is the audit's, every clause at an instance, with one change the report needs: the table
  binds every variable to a value that states nothing (a payload other than the empty one), where the
  audit's blank table binds the empty payload. An instance then carries exactly the leaves its pattern
  states, since a stated leaf passes through unchanged and a bound value adds none; at the blank table a
  variable and a stated empty payload could not be told apart. The table is hidden and checked, value by
  value, to state nothing; no octet is stated to build it.
\<close>

fun term_stated :: "factor_term \<Rightarrow> factor_term list" where
  "term_stated (Target_Term x)=[Target_Term x]"
| "term_stated (Payload_Term v)=(if v=[] then [Payload_Term []] else [])"
| "term_stated (Pair_Term x y)=term_stated x @ term_stated y"

fun pattern_stated :: "'a term_pattern \<Rightarrow> factor_term list" where
  "pattern_stated (Pattern_Variable a)=[]"
| "pattern_stated (Pattern_Target x)=[Target_Term x]"
| "pattern_stated (Pattern_Payload v)=(if v=[] then [Payload_Term []] else [])"
| "pattern_stated (Pattern_Pair p q)=pattern_stated p @ pattern_stated q"

lemma pattern_stated_leaves:
  "set (pattern_stated p)={x\<in>pattern_leaves p. x=Payload_Term [] \<or> (\<exists>y. x=Target_Term y)}"
  by (induction p) auto

corollary pattern_stated_targets:
  "Target_Term x\<in>set (pattern_stated p) \<longleftrightarrow> Target_Term x\<in>pattern_leaves p"
  by (simp add: pattern_stated_leaves)

corollary pattern_stated_empty:
  "Payload_Term []\<in>set (pattern_stated p) \<longleftrightarrow> Payload_Term []\<in>pattern_leaves p"
  by (simp add: pattern_stated_leaves)

lemma pattern_instance_stated:
  assumes "pattern_instance V p t" "\<forall>a x. (a,x)\<in>V \<longrightarrow> term_stated x=[]"
  shows "term_stated t=pattern_stated p"
  using assms by (induction rule: pattern_instance.induct) auto

lemma term_stated_formed:
  assumes "term_formed t"
  shows "\<forall>x\<in>set (term_stated t). term_formed x"
  using assms
proof (induction t)
  case (Target_Term y)
  then show ?case by simp
next
  case (Payload_Term v)
  show ?case by (simp add: octets_formed_def)
next
  case (Pair_Term a b)
  have af: "term_formed a" and bf: "term_formed b" using Pair_Term.prems by simp_all
  have "\<forall>x\<in>set (term_stated a). term_formed x" "\<forall>x\<in>set (term_stated b). term_formed x"
    by (rule Pair_Term.IH(1)[OF af], rule Pair_Term.IH(2)[OF bf])
  then show ?case by auto
qed

definition stated_onto :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "stated_onto t y=foldr Pair_Term (term_stated t) y"

lemma foldr_pair_formed:
  "term_formed (foldr Pair_Term xs y) \<longleftrightarrow> (\<forall>x\<in>set xs. term_formed x) \<and> term_formed y"
  by (induction xs) auto


lemma data_list_term_empty:
  "data_list_term xs=Payload_Term [] \<longleftrightarrow> xs=[]" "Payload_Term []=data_list_term xs \<longleftrightarrow> xs=[]"
  by (cases xs; simp)+

lemma stated_list_formed: "term_formed (data_list_term xs) \<longleftrightarrow> (\<forall>x\<in>set xs. term_formed x)"
  by (induction xs) (auto simp: octets_formed_def)

lemma binding_rows_empty: "binding_rows_term xs=Payload_Term [] \<longleftrightarrow> xs=[]"
  by (cases xs) auto

lemma call_rows_empty: "call_instance_rows_term qs=Payload_Term [] \<longleftrightarrow> qs=[]"
  by (cases qs) auto

lemma binding_rows_formed:
  assumes "term_formed (binding_rows_term xs)"
  shows "\<forall>(a,x)\<in>set xs. octets_formed a \<and> term_formed x"
proof -
  have "\<forall>y\<in>set (map (\<lambda>(k,v). Pair_Term k v) (map (\<lambda>(a,t). (Payload_Term a,t)) xs)). term_formed y"
    using assms by (simp only: stated_list_formed)
  then show ?thesis by auto
qed

section \<open>Ground clauses\<close>

fun pattern_ground :: "'a term_pattern \<Rightarrow> factor_term option" where
  "pattern_ground (Pattern_Variable a)=None"
| "pattern_ground (Pattern_Target x)=Some (Target_Term x)"
| "pattern_ground (Pattern_Payload v)=Some (Payload_Term v)"
| "pattern_ground (Pattern_Pair p q)=(case (pattern_ground p,pattern_ground q) of
    (Some x,Some y) \<Rightarrow> Some (Pair_Term x y) | _ \<Rightarrow> None)"

lemma pattern_ground_none: "pattern_ground p=None \<longleftrightarrow> pattern_variables p\<noteq>{}"
  by (induction p) (auto split: option.splits)

lemma pattern_ground_instance:
  assumes "pattern_instance V p t" "pattern_ground p=Some g"
  shows "t=g"
  using assms by (induction arbitrary: g rule: pattern_instance.induct) (auto split: option.splits)

definition clause_ground :: "('a,'s,'d) factor_schema \<Rightarrow> factor_term list" where
  "clause_ground S=(if schema_premises S={} \<and> schema_material_premises S={}
    then (case pattern_ground (schema_conclusion S) of None \<Rightarrow> [] | Some g \<Rightarrow> [g]) else [])"

lemma clause_ground_ground:
  "clause_ground S\<noteq>[] \<longleftrightarrow> schema_variables S={} \<and> schema_premises S={} \<and> schema_material_premises S={}"
  using pattern_ground_none[of "schema_conclusion S"]
  by (auto simp: clause_ground_def schema_variables_def split: option.splits)

section \<open>The report of a definition\<close>

definition material_stated :: "'a material_pattern \<Rightarrow> factor_term list list" where
  "material_stated M=map pattern_stated (material_fields M)"

definition clause_calls :: "('a,'s,'d) factor_schema \<Rightarrow> ('s\<times>factor_term list) set" where
  "clause_calls S=(\<lambda>(s,d,p). (s,pattern_stated p)) ` schema_premises S"

definition clause_materials :: "('a,'s,'d) factor_schema \<Rightarrow> ('s\<times>factor_term list list) set" where
  "clause_materials S=(\<lambda>(s,M). (s,material_stated M)) ` schema_material_premises S"

definition place_term :: "octets\<times>factor_term list \<Rightarrow> factor_term" where
  "place_term z=Pair_Term (Payload_Term (fst z)) (data_list_term (snd z))"

definition stated_tuple :: "factor_term list list \<Rightarrow> factor_term" where
  "stated_tuple ls=material_tuple (data_list_term (ls!0)) (data_list_term (ls!1)) (data_list_term (ls!2))
    (data_list_term (ls!3)) (data_list_term (ls!4))"

definition material_place_term :: "octets\<times>factor_term list list \<Rightarrow> factor_term" where
  "material_place_term z=Pair_Term (Payload_Term (fst z)) (stated_tuple (snd z))"

text \<open>
  A clause's report is its ground field (the asserted term when the clause is ground, else nothing), the
  leaves its conclusion states, and one row per ordinary premise and per material premise keyed by its
  socket, in any order of the sockets. A definition's report is the leaves its interface states and one
  row per clause keyed by its clause socket, in any order.
\<close>

definition clause_stated_presents :: "(local_address,local_address,'d) factor_schema \<Rightarrow> factor_term \<Rightarrow> bool" where
  "clause_stated_presents S r \<longleftrightarrow> (\<exists>qs ms. distinct (map fst qs) \<and> set qs=clause_calls S \<and>
    distinct (map fst ms) \<and> set ms=clause_materials S \<and>
    r=Pair_Term (data_list_term (clause_ground S)) (Pair_Term (data_list_term (pattern_stated (schema_conclusion S)))
      (Pair_Term (data_list_term (map place_term qs)) (data_list_term (map material_place_term ms)))))"

definition definition_stated_presents ::
    "'a term_pattern \<Rightarrow> (local_address\<times>(local_address,local_address,'d) factor_schema) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "definition_stated_presents p C z \<longleftrightarrow> (\<exists>ks. distinct (map fst ks) \<and> fst ` set ks=rel_dom C \<and>
    (\<forall>c v. (c,v)\<in>set ks \<longrightarrow> (\<exists>S. (c,S)\<in>C \<and> clause_stated_presents S v)) \<and>
    z=Pair_Term (data_list_term (pattern_stated p)) (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks)))"

section \<open>Keyed lists\<close>

lemma stated_keyed_enumeration:
  assumes sv: "single_valued R" and keys: "distinct (map fst ks)" "fst ` set ks=rel_dom R"
  obtains rs where "map fst rs=map fst ks" "set rs=R" "distinct rs"
proof -
  let ?rs="map (\<lambda>k. (fst k,rel_value R (fst k))) ks"
  have member: "(fst k,rel_value R (fst k))\<in>R" if k: "k\<in>set ks" for k
  proof -
    obtain y where "(fst k,y)\<in>R" using k keys(2) by (force simp: rel_dom_def)
    then show ?thesis using rel_value_eq[OF sv] by simp
  qed
  have set: "set ?rs=R"
  proof
    show "set ?rs\<subseteq>R" using member by auto
    show "R\<subseteq>set ?rs"
    proof
      fix z assume z: "z\<in>R"
      obtain s y where zs: "z=(s,y)" by (cases z)
      have "s\<in>fst ` set ks" using z zs keys(2) by (auto simp: rel_dom_def)
      then obtain k where k: "k\<in>set ks" "fst k=s" by blast
      have "rel_value R s=y" using rel_value_eq[OF sv] z zs by simp
      then show "z\<in>set ?rs" using k zs by force
    qed
  qed
  have keyed: "map fst ?rs=map fst ks" by simp
  have "distinct (map fst ?rs)" by (simp only: keyed keys(1))
  then have "distinct ?rs" by (rule distinct_map[THEN iffD1, THEN conjunct1])
  then show ?thesis using that keyed set by blast
qed

lemma stated_keyed_map:
  assumes keys: "map fst rs=map fst ks"
    and agree: "\<And>r k. r\<in>set rs \<Longrightarrow> k\<in>set ks \<Longrightarrow> fst r=fst k \<Longrightarrow> f r=g k"
  shows "map f rs=map g ks"
proof (rule nth_equalityI)
  have len: "length rs=length ks" using arg_cong[OF keys, of length] by simp
  show "length (map f rs)=length (map g ks)" using len by simp
  fix i assume i: "i<length (map f rs)"
  have li: "i<length rs" "i<length ks" using i len by auto
  have "fst (rs!i)=fst (ks!i)" using arg_cong[OF keys, of "\<lambda>l. l!i"] li by simp
  then show "map f rs!i=map g ks!i" using agree[of "rs!i" "ks!i"] li by simp
qed

lemma stated_list_all2_function:
  assumes "\<forall>x\<in>set xs. \<forall>y. P x y \<longleftrightarrow> y=f x"
  shows "list_all2 P xs ys \<longleftrightarrow> ys=map f xs"
  using assms by (induction xs arbitrary: ys) (auto simp: list_all2_Cons1)

lemma stated_list_all2_cong:
  assumes "\<And>x y. x\<in>set xs \<Longrightarrow> P x y \<longleftrightarrow> Q x y"
  shows "list_all2 P xs ys \<longleftrightarrow> list_all2 Q xs ys"
  using assms by (induction xs arbitrary: ys) (auto simp: list_all2_Cons1)

lemma stated_list_all2_witnesses:
  assumes "list_all2 (\<lambda>x y. \<exists>z. y=f x z \<and> Q x z) xs ys"
  shows "\<exists>zs. ys=map2 f xs zs \<and> list_all2 Q xs zs"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  obtain z where z: "y=f x z" "Q x z" using Cons.hyps(1) by blast
  obtain zs where zs: "ys=map2 f xs zs" "list_all2 Q xs zs" using Cons.IH by blast
  show ?case by (rule exI[of _ "z#zs"]) (simp add: z zs)
qed

section \<open>The stated leaves of a term, in order (580)\<close>

text \<open>
  580 holds of a term, an accumulator and the accumulator extended in front by the term's stated leaves:
  the empty payload is stated, a target (read by the target projection) is stated, a payload other than
  the empty one (read by the distinct-payload program on the list of it and the empty payload) states
  nothing, and a pair states its left leaves before its right ones.
\<close>

definition stated_leaves_empty_schema :: "(nat,nat,nat) factor_schema" where
  "stated_leaves_empty_schema=data_rule
    (Pattern_Pair (Pattern_Payload []) (Pattern_Pair data_x (Pattern_Pair (Pattern_Payload []) data_x))) {}"

definition stated_leaves_target_schema :: "(nat,nat,nat) factor_schema" where
  "stated_leaves_target_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_x data_y)))
    {(0,45,Pattern_Pair data_x data_z)}"

definition stated_leaves_payload_schema :: "(nat,nat,nat) factor_schema" where
  "stated_leaves_payload_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_y))
    {(0,1,Pattern_Pair data_x (Pattern_Pair (Pattern_Payload []) (Pattern_Payload [])))}"

definition stated_leaves_pair_schema :: "(nat,nat,nat) factor_schema" where
  "stated_leaves_pair_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,580,Pattern_Pair data_y (Pattern_Pair data_z (Pattern_Variable 4))),
     (1,580,Pattern_Pair data_x (Pattern_Pair (Pattern_Variable 4) data_w))}"

definition stated_leaves_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "stated_leaves_clauses={(0,stated_leaves_empty_schema),(1,stated_leaves_target_schema),
    (2,stated_leaves_payload_schema),(3,stated_leaves_pair_schema)}"

definition stated_leaves_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_leaves_system=add_view_definition payload_audit_system 580 data_x stated_leaves_clauses"

lemmas stated_leaves_schema_defs=stated_leaves_empty_schema_def stated_leaves_target_schema_def
  stated_leaves_payload_schema_def stated_leaves_pair_schema_def

lemma stated_leaves_system_formed [simp]: "schema_system_formed stated_leaves_system"
  unfolding stated_leaves_system_def
  by (rule add_recursive_definition_formed[OF payload_audit_system_formed])
    (auto simp: stated_leaves_clauses_def stated_leaves_schema_defs schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_leaves_definitions [simp]:
  "system_definitions stated_leaves_system=insert 580 (system_definitions payload_audit_system)"
  by (simp add: stated_leaves_system_def)

lemma stated_leaves_call:
  "schema_call_formed stated_leaves_system d t \<longleftrightarrow> d\<in>system_definitions stated_leaves_system \<and> term_formed t"
  using added_variable_calls[OF payload_audit_system_formed
    stated_leaves_system_formed[unfolded stated_leaves_system_def] payload_audit_call]
  by (simp only: stated_leaves_system_def[symmetric])

lemma stated_leaves_old_meaning:
  assumes "d\<in>system_definitions payload_audit_system"
  shows "(d,t)\<in>positive_meaning stated_leaves_system \<longleftrightarrow> (d,t)\<in>positive_meaning payload_audit_system"
  using added_definition_preserves_old(2)[OF payload_audit_system_formed
    stated_leaves_system_formed[unfolded stated_leaves_system_def] _ assms]
  by (simp add: stated_leaves_system_def)

lemma stated_leaves_clause [simp]:
  "((580,c),S)\<in>system_clauses stated_leaves_system \<longleftrightarrow> (c,S)\<in>stated_leaves_clauses"
  unfolding stated_leaves_system_def by (rule audit_layer_clause) simp_all

lemma stated_leaves_components:
  "(45,t)\<in>positive_meaning stated_leaves_system \<longleftrightarrow> (45,t)\<in>positive_meaning target_projection_system"
  "(1,t)\<in>positive_meaning stated_leaves_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
  using stated_leaves_old_meaning[of 45 t] payload_audit_admission_meaning[of 45 t] audit_target_meaning[of t]
    stated_leaves_old_meaning[of 1 t] payload_audit_admission_meaning[of 1 t]
    definition_call_admission_instantiation_meaning[of 1 t] schema_instantiation_pattern_meaning[of 1 t]
    pattern_instantiation_quotation_meaning[of 1 t] quotation_admission_old_meaning[of 1 t]
    payload_disjoint_components(2)[of t] by simp_all

lemma stated_nonempty_payload:
  "(1,Pair_Term x (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning distinct_payloads_system
    \<longleftrightarrow> (\<exists>v. x=Payload_Term v \<and> octets_formed v \<and> v\<noteq>[])"
proof
  assume holds: "(1,Pair_Term x (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning distinct_payloads_system"
  have list: "Pair_Term x (Pair_Term (Payload_Term []) (Payload_Term []))=data_list_term [x,Payload_Term []]" by simp
  obtain A where A: "distinct A" "\<forall>a\<in>set A. octets_formed a" "data_list_term [x,Payload_Term []]=data_list_term (map Payload_Term A)"
    using holds by (simp only: list distinct_payloads_positive_exact) blast
  have "map Payload_Term A=[x,Payload_Term []]" using A(3) by (simp only: data_list_term_injective)
  then show "\<exists>v. x=Payload_Term v \<and> octets_formed v \<and> v\<noteq>[]" using A(1,2) by (auto simp: map_eq_Cons_conv)
next
  assume "\<exists>v. x=Payload_Term v \<and> octets_formed v \<and> v\<noteq>[]"
  then obtain v where v: "x=Payload_Term v" "octets_formed v" "v\<noteq>[]" by blast
  show "(1,Pair_Term x (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning distinct_payloads_system"
    using unequal_payloads_exact[of v "[]"] v by (simp add: octets_formed_def)
qed

lemma stated_leaves_cases:
  assumes holds: "(580,z)\<in>positive_meaning stated_leaves_system"
  shows "(\<exists>y. z=Pair_Term (Payload_Term []) (Pair_Term y (Pair_Term (Payload_Term []) y))) \<or>
    (\<exists>x y. z=Pair_Term (Target_Term x) (Pair_Term y (Pair_Term (Target_Term x) y))) \<or>
    (\<exists>v y. v\<noteq>[] \<and> z=Pair_Term (Payload_Term v) (Pair_Term y y)) \<or>
    (\<exists>a b y m w. z=Pair_Term (Pair_Term a b) (Pair_Term y w) \<and>
      (580,Pair_Term b (Pair_Term y m))\<in>positive_meaning stated_leaves_system \<and>
      (580,Pair_Term a (Pair_Term m w))\<in>positive_meaning stated_leaves_system)"
proof -
  obtain c S h where clause: "((580,c),S)\<in>system_clauses stated_leaves_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_leaves_system"
    using positive_meaning_valuationE[OF holds] by blast
  have "(c,S)\<in>stated_leaves_clauses" using clause by simp
  then consider "S=stated_leaves_empty_schema" | "S=stated_leaves_target_schema"
    | "S=stated_leaves_payload_schema" | "S=stated_leaves_pair_schema"
    by (auto simp: stated_leaves_clauses_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using conclusion by (simp add: stated_leaves_empty_schema_def)
  next
    case 2
    have "(45,Pair_Term (h 0) (h 2))\<in>positive_meaning target_projection_system"
      using support 2 by (auto simp: stated_leaves_target_schema_def stated_leaves_components)
    then show ?thesis using conclusion 2 by (auto simp: target_projection_exact stated_leaves_target_schema_def)
  next
    case 3
    have "(1,Pair_Term (h 0) (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning distinct_payloads_system"
      using support 3 by (auto simp: stated_leaves_payload_schema_def stated_leaves_components)
    then show ?thesis using conclusion 3 by (auto simp: stated_nonempty_payload stated_leaves_payload_schema_def)
  next
    case 4
    have "(580,Pair_Term (h 1) (Pair_Term (h 2) (h 4)))\<in>positive_meaning stated_leaves_system"
      "(580,Pair_Term (h 0) (Pair_Term (h 4) (h 3)))\<in>positive_meaning stated_leaves_system"
      using support 4 by (auto simp: stated_leaves_pair_schema_def)
    then show ?thesis using conclusion 4 by (simp add: stated_leaves_pair_schema_def) blast
  qed
qed

lemma stated_leaves_sound:
  assumes "(580,Pair_Term t (Pair_Term y w))\<in>positive_meaning stated_leaves_system"
  shows "w=stated_onto t y"
  using assms
proof (induction t arbitrary: y w)
  case (Target_Term x)
  then show ?case using stated_leaves_cases[OF Target_Term.prems] by (auto simp: stated_onto_def)
next
  case (Payload_Term v)
  then show ?case using stated_leaves_cases[OF Payload_Term.prems] by (auto simp: stated_onto_def)
next
  case (Pair_Term a b)
  obtain m where right: "(580,Pair_Term b (Pair_Term y m))\<in>positive_meaning stated_leaves_system"
    and left: "(580,Pair_Term a (Pair_Term m w))\<in>positive_meaning stated_leaves_system"
    using stated_leaves_cases[OF Pair_Term.prems] by auto
  have "m=stated_onto b y" by (rule Pair_Term.IH(2)[OF right])
  moreover have "w=stated_onto a m" by (rule Pair_Term.IH(1)[OF left])
  ultimately show ?case by (simp add: stated_onto_def)
qed

lemma stated_leaves_complete:
  assumes "term_formed t" "term_formed y"
  shows "(580,Pair_Term t (Pair_Term y (stated_onto t y)))\<in>positive_meaning stated_leaves_system"
  using assms
proof (induction t arbitrary: y)
  case (Target_Term x)
  have tf: "target_formed x" using Target_Term.prems by simp
  obtain a where presented: "target_value_presents x a" using target_value_presents_total[OF tf] by blast
  have af: "term_formed a" using target_value_presents_formed[OF presented] by blast
  have support: "(45,Pair_Term (Target_Term x) a)\<in>positive_meaning stated_leaves_system"
    by (simp only: stated_leaves_components target_projection_exact) (use presented in blast)
  let ?h="\<lambda>n::nat. if n=0 then Target_Term x else if n=1 then y else a"
  have "(580,evaluate_pattern ?h (schema_conclusion stated_leaves_target_schema))\<in>positive_meaning stated_leaves_system"
    by (rule ordinary_positive_formed_step[where c=1])
      (use Target_Term.prems af support in \<open>auto simp: stated_leaves_clauses_def stated_leaves_schema_defs
        schema_formed_def schema_variables_def single_valued_def rel_dom_def stated_leaves_call\<close>)
  then show ?case by (simp add: stated_leaves_target_schema_def stated_onto_def)
next
  case (Payload_Term v)
  show ?case
  proof (cases "v=[]")
    case True
    let ?h="\<lambda>n::nat. y"
    have "(580,evaluate_pattern ?h (schema_conclusion stated_leaves_empty_schema))\<in>positive_meaning stated_leaves_system"
      by (rule ordinary_positive_formed_step[where c=0])
        (use Payload_Term.prems in \<open>auto simp: stated_leaves_clauses_def stated_leaves_schema_defs
          schema_formed_def schema_variables_def single_valued_def rel_dom_def octets_formed_def stated_leaves_call\<close>)
    then show ?thesis using True by (simp add: stated_leaves_empty_schema_def stated_onto_def)
  next
    case False
    have support: "(1,Pair_Term (Payload_Term v) (Pair_Term (Payload_Term []) (Payload_Term [])))
        \<in>positive_meaning stated_leaves_system"
      using Payload_Term.prems False by (simp add: stated_leaves_components stated_nonempty_payload)
    let ?h="\<lambda>n::nat. if n=0 then Payload_Term v else y"
    have "(580,evaluate_pattern ?h (schema_conclusion stated_leaves_payload_schema))\<in>positive_meaning stated_leaves_system"
      by (rule ordinary_positive_formed_step[where c=2])
        (use Payload_Term.prems support in \<open>auto simp: stated_leaves_clauses_def stated_leaves_schema_defs
          schema_formed_def schema_variables_def single_valued_def rel_dom_def octets_formed_def stated_leaves_call\<close>)
    then show ?thesis using False by (simp add: stated_leaves_payload_schema_def stated_onto_def)
  qed
next
  case (Pair_Term a b)
  have af: "term_formed a" and bf: "term_formed b" using Pair_Term.prems by auto
  have right: "(580,Pair_Term b (Pair_Term y (stated_onto b y)))\<in>positive_meaning stated_leaves_system"
    by (rule Pair_Term.IH(2)[OF bf Pair_Term.prems(2)])
  have mf: "term_formed (stated_onto b y)"
    using term_stated_formed[OF bf] Pair_Term.prems(2) by (simp add: stated_onto_def foldr_pair_formed)
  have left: "(580,Pair_Term a (Pair_Term (stated_onto b y) (stated_onto a (stated_onto b y))))
      \<in>positive_meaning stated_leaves_system"
    by (rule Pair_Term.IH(1)[OF af mf])
  have of: "term_formed (stated_onto a (stated_onto b y))"
    using term_stated_formed[OF af] mf by (simp add: stated_onto_def foldr_pair_formed)
  let ?h="\<lambda>n::nat. if n=0 then a else if n=1 then b else if n=2 then y
    else if n=3 then stated_onto a (stated_onto b y) else stated_onto b y"
  have "(580,evaluate_pattern ?h (schema_conclusion stated_leaves_pair_schema))\<in>positive_meaning stated_leaves_system"
    by (rule ordinary_positive_formed_step[where c=3])
      (use af bf mf of Pair_Term.prems left right in \<open>auto simp: stated_leaves_clauses_def stated_leaves_schema_defs
        schema_formed_def schema_variables_def single_valued_def rel_dom_def stated_leaves_call\<close>)
  then show ?case by (simp add: stated_leaves_pair_schema_def stated_onto_def)
qed

abbreviation stated_leaves_result :: "factor_term \<Rightarrow> bool" where
  "stated_leaves_result z \<equiv> \<exists>t y. z=Pair_Term t (Pair_Term y (stated_onto t y)) \<and> term_formed t \<and> term_formed y"

theorem stated_leaves_exact:
  "(580,z)\<in>positive_meaning stated_leaves_system \<longleftrightarrow> stated_leaves_result z"
proof
  assume holds: "(580,z)\<in>positive_meaning stated_leaves_system"
  have formed: "term_formed z" using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by blast
  obtain t y w where z: "z=Pair_Term t (Pair_Term y w)" using stated_leaves_cases[OF holds] by blast
  show "stated_leaves_result z" using stated_leaves_sound[OF holds[unfolded z]] formed z by auto
next
  assume "stated_leaves_result z"
  then obtain t y where z: "z=Pair_Term t (Pair_Term y (stated_onto t y))" "term_formed t" "term_formed y" by blast
  show "(580,z)\<in>positive_meaning stated_leaves_system" using stated_leaves_complete[OF z(2,3)] z(1) by simp
qed

corollary stated_leaves_list:
  "(580,Pair_Term t (Pair_Term (Payload_Term []) l))\<in>positive_meaning stated_leaves_system \<longleftrightarrow>
    term_formed t \<and> l=data_list_term (term_stated t)"
  by (auto simp: stated_leaves_exact stated_onto_def term_sequence_pair_boundaries(1) octets_formed_def)

section \<open>A binding value states nothing (581), and every value of a table (582)\<close>

definition stated_value_schema :: "(nat,nat,nat) factor_schema" where
  "stated_value_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,580,Pattern_Pair data_y (Pattern_Pair (Pattern_Payload []) (Pattern_Payload [])))}"

definition stated_value_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_value_system=add_view_definition stated_leaves_system 581 data_x {(0,stated_value_schema)}"

lemma stated_value_system_formed [simp]: "schema_system_formed stated_value_system"
  unfolding stated_value_system_def
  by (rule add_recursive_definition_formed[OF stated_leaves_system_formed])
    (auto simp: stated_value_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma stated_value_definitions [simp]:
  "system_definitions stated_value_system=insert 581 (system_definitions stated_leaves_system)"
  by (simp add: stated_value_system_def)

lemma stated_value_call:
  "schema_call_formed stated_value_system d t \<longleftrightarrow> d\<in>system_definitions stated_value_system \<and> term_formed t"
  using added_variable_calls[OF stated_leaves_system_formed
    stated_value_system_formed[unfolded stated_value_system_def] stated_leaves_call]
  by (simp only: stated_value_system_def[symmetric])

lemma stated_value_old_meaning:
  assumes "d\<in>system_definitions stated_leaves_system"
  shows "(d,t)\<in>positive_meaning stated_value_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_leaves_system"
  using added_definition_preserves_old(2)[OF stated_leaves_system_formed
    stated_value_system_formed[unfolded stated_value_system_def] _ assms]
  by (simp add: stated_value_system_def)

lemma stated_value_clause [simp]:
  "((581,c),S)\<in>system_clauses stated_value_system \<longleftrightarrow> c=0 \<and> S=stated_value_schema"
  unfolding stated_value_system_def by (subst audit_layer_clause) simp_all

theorem stated_value_exact:
  "(581,z)\<in>positive_meaning stated_value_system \<longleftrightarrow>
    (\<exists>k v. z=Pair_Term k v \<and> term_formed k \<and> term_formed v \<and> term_stated v=[])"
proof
  assume holds: "(581,z)\<in>positive_meaning stated_value_system"
  obtain c S h where clause: "((581,c),S)\<in>system_clauses stated_value_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_value_system"
    by (rule positive_meaning_valuationE[OF holds])
  have schema: "S=stated_value_schema" using clause by simp
  have leaves: "(580,Pair_Term (h 1) (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning stated_leaves_system"
    using support by (simp add: schema stated_value_schema_def stated_value_old_meaning)
  have empty: "term_stated (h 1)=[]" using leaves by (simp add: stated_leaves_list data_list_term_empty)
  show "\<exists>k v. z=Pair_Term k v \<and> term_formed k \<and> term_formed v \<and> term_stated v=[]"
    using conclusion assignment empty by (auto simp: schema stated_value_schema_def schema_variables_def)
next
  assume "\<exists>k v. z=Pair_Term k v \<and> term_formed k \<and> term_formed v \<and> term_stated v=[]"
  then obtain k v where z: "z=Pair_Term k v" "term_formed k" "term_formed v" "term_stated v=[]" by blast
  have leaves: "(580,Pair_Term v (Pair_Term (Payload_Term []) (Payload_Term [])))\<in>positive_meaning stated_value_system"
    using z(3,4) by (simp add: stated_value_old_meaning stated_leaves_list)
  let ?h="\<lambda>n::nat. if n=0 then k else v"
  have "(581,evaluate_pattern ?h (schema_conclusion stated_value_schema))\<in>positive_meaning stated_value_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (use z leaves in \<open>auto simp: stated_value_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def stated_value_call\<close>)
  then show "(581,z)\<in>positive_meaning stated_value_system" by (simp add: stated_value_schema_def z(1))
qed

definition stated_values_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_values_system=add_view_definition stated_value_system 582 data_x (list_profile_clauses 581 582)"

lemma stated_values_system_formed [simp]: "schema_system_formed stated_values_system"
  unfolding stated_values_system_def
  by (rule add_recursive_definition_formed[OF stated_value_system_formed])
    (auto simp: list_profile_clauses_def list_step_schema_def data_list_nil_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_values_definitions [simp]:
  "system_definitions stated_values_system=insert 582 (system_definitions stated_value_system)"
  by (simp add: stated_values_system_def)

lemma stated_values_call:
  "schema_call_formed stated_values_system d t \<longleftrightarrow> d\<in>system_definitions stated_values_system \<and> term_formed t"
  using added_variable_calls[OF stated_value_system_formed
    stated_values_system_formed[unfolded stated_values_system_def] stated_value_call]
  by (simp only: stated_values_system_def[symmetric])

lemma stated_values_old_meaning:
  assumes "d\<in>system_definitions stated_value_system"
  shows "(d,t)\<in>positive_meaning stated_values_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_value_system"
  using added_definition_preserves_old(2)[OF stated_value_system_formed
    stated_values_system_formed[unfolded stated_values_system_def] _ assms]
  by (simp add: stated_values_system_def)

lemma stated_values_clause [simp]:
  "((582,c),S)\<in>system_clauses stated_values_system \<longleftrightarrow> (c,S)\<in>list_profile_clauses 581 582"
  unfolding stated_values_system_def by (rule audit_layer_clause) simp_all

interpretation stated_values_profile: list_profile stated_values_system 581 582
  by (rule list_profile.intro) (auto simp: stated_values_call)

lemma stated_values_rows:
  "(582,binding_rows_term ys)\<in>positive_meaning stated_values_system \<longleftrightarrow>
    (\<forall>(a,x)\<in>set ys. octets_formed a \<and> term_formed x \<and> term_stated x=[])"
proof -
  have element: "(581,t)\<in>positive_meaning stated_values_system \<longleftrightarrow> (581,t)\<in>positive_meaning stated_value_system" for t
    by (rule stated_values_old_meaning) simp
  show ?thesis
    by (simp only: stated_values_profile.exact element stated_value_exact data_list_term_injective) auto
qed

section \<open>An ordinary premise's argument at its socket (583, 584)\<close>

fun stated_call_row :: "factor_term \<Rightarrow> factor_term" where
  "stated_call_row (Pair_Term k (Pair_Term d t))=Pair_Term k (data_list_term (term_stated t))"
| "stated_call_row x=x"

definition stated_call_schema :: "(nat,nat,nat) factor_schema" where
  "stated_call_schema=data_rule
    (context_relation_pattern data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w))
      (Pattern_Pair data_y (Pattern_Variable 4)))
    {(0,580,Pattern_Pair data_w (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 4)))}"

definition stated_call_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_call_system=add_view_definition stated_values_system 583 data_x {(0,stated_call_schema)}"

lemma stated_call_system_formed [simp]: "schema_system_formed stated_call_system"
  unfolding stated_call_system_def
  by (rule add_recursive_definition_formed[OF stated_values_system_formed])
    (auto simp: stated_call_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma stated_call_definitions [simp]:
  "system_definitions stated_call_system=insert 583 (system_definitions stated_values_system)"
  by (simp add: stated_call_system_def)

lemma stated_call_call:
  "schema_call_formed stated_call_system d t \<longleftrightarrow> d\<in>system_definitions stated_call_system \<and> term_formed t"
  using added_variable_calls[OF stated_values_system_formed
    stated_call_system_formed[unfolded stated_call_system_def] stated_values_call]
  by (simp only: stated_call_system_def[symmetric])

lemma stated_call_old_meaning:
  assumes "d\<in>system_definitions stated_values_system"
  shows "(d,t)\<in>positive_meaning stated_call_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_values_system"
  using added_definition_preserves_old(2)[OF stated_values_system_formed
    stated_call_system_formed[unfolded stated_call_system_def] _ assms]
  by (simp add: stated_call_system_def)

lemma stated_call_clause [simp]:
  "((583,c),S)\<in>system_clauses stated_call_system \<longleftrightarrow> c=0 \<and> S=stated_call_schema"
  unfolding stated_call_system_def by (subst audit_layer_clause) simp_all

lemma stated_call_leaves:
  "(580,t)\<in>positive_meaning stated_call_system \<longleftrightarrow> (580,t)\<in>positive_meaning stated_leaves_system"
  by (simp add: stated_call_old_meaning stated_values_old_meaning stated_value_old_meaning)

lemma stated_call_conclusion:
  assumes "context_relation_argument c (Pair_Term k (Pair_Term d t)) y=evaluate_pattern h (schema_conclusion stated_call_schema)"
  shows "h 1=k \<and> h 3=t \<and> y=Pair_Term (h 1) (h 4)"
  using assms by (simp add: stated_call_schema_def)

lemma stated_call_support:
  assumes "\<forall>s e p. (s,e,p)\<in>schema_premises stated_call_schema \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_call_system"
  shows "(580,Pair_Term (h 3) (Pair_Term (Payload_Term []) (h 4)))\<in>positive_meaning stated_leaves_system"
proof -
  have "(580,evaluate_pattern h (Pattern_Pair data_w (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 4))))
      \<in>positive_meaning stated_call_system"
    using assms by (simp only: stated_call_schema_def factor_schema.select_convs) blast
  then show ?thesis by (simp only: stated_call_leaves evaluate_pattern.simps)
qed

lemma stated_call_on_row_sound:
  assumes holds: "(583,context_relation_argument c (Pair_Term k (Pair_Term d t)) y)\<in>positive_meaning stated_call_system"
  shows "y=Pair_Term k (data_list_term (term_stated t))"
proof -
  obtain c' S h where clause: "((583,c'),S)\<in>system_clauses stated_call_system"
    and conclusion: "context_relation_argument c (Pair_Term k (Pair_Term d t)) y=evaluate_pattern h (schema_conclusion S)"
    and "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_call_system"
    by (rule positive_meaning_valuationE[OF holds])
  have schema: "S=stated_call_schema" using clause by simp
  have fields: "h 1=k \<and> h 3=t \<and> y=Pair_Term (h 1) (h 4)" by (rule stated_call_conclusion[OF conclusion[unfolded schema]])
  have "(580,Pair_Term (h 3) (Pair_Term (Payload_Term []) (h 4)))\<in>positive_meaning stated_leaves_system"
    by (rule stated_call_support[OF support[unfolded schema]])
  then have "h 4=data_list_term (term_stated (h 3))" by (simp only: stated_leaves_list)
  then show ?thesis using fields by simp
qed

theorem stated_call_on_row:
  assumes formed: "term_formed c" "term_formed k" "term_formed d" "term_formed t"
  shows "(583,context_relation_argument c (Pair_Term k (Pair_Term d t)) y)\<in>positive_meaning stated_call_system
    \<longleftrightarrow> y=Pair_Term k (data_list_term (term_stated t))"
proof
  assume holds: "(583,context_relation_argument c (Pair_Term k (Pair_Term d t)) y)\<in>positive_meaning stated_call_system"
  then show "y=Pair_Term k (data_list_term (term_stated t))" by (rule stated_call_on_row_sound)
next
  assume y: "y=Pair_Term k (data_list_term (term_stated t))"
  have leaves: "(580,Pair_Term t (Pair_Term (Payload_Term []) (data_list_term (term_stated t))))
      \<in>positive_meaning stated_call_system"
    using formed(4) by (simp add: stated_call_leaves stated_leaves_list)
  have lf: "term_formed (data_list_term (term_stated t))" using term_stated_formed[OF formed(4)] by (simp add: stated_list_formed)
  let ?h="\<lambda>n::nat. if n=0 then c else if n=1 then k else if n=2 then d else if n=3 then t
    else data_list_term (term_stated t)"
  have "(583,evaluate_pattern ?h (schema_conclusion stated_call_schema))\<in>positive_meaning stated_call_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (use formed leaves lf in \<open>auto simp: stated_call_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def stated_call_call\<close>)
  then show "(583,context_relation_argument c (Pair_Term k (Pair_Term d t)) y)\<in>positive_meaning stated_call_system"
    by (simp add: stated_call_schema_def y)
qed

definition stated_calls_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_calls_system=add_view_definition stated_call_system 584 data_x (related_list_clauses 583 584)"

lemma stated_calls_system_formed [simp]: "schema_system_formed stated_calls_system"
  unfolding stated_calls_system_def
  by (rule add_recursive_definition_formed[OF stated_call_system_formed])
    (auto simp: related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_calls_definitions [simp]:
  "system_definitions stated_calls_system=insert 584 (system_definitions stated_call_system)"
  by (simp add: stated_calls_system_def)

lemma stated_calls_call:
  "schema_call_formed stated_calls_system d t \<longleftrightarrow> d\<in>system_definitions stated_calls_system \<and> term_formed t"
  using added_variable_calls[OF stated_call_system_formed
    stated_calls_system_formed[unfolded stated_calls_system_def] stated_call_call]
  by (simp only: stated_calls_system_def[symmetric])

lemma stated_calls_old_meaning:
  assumes "d\<in>system_definitions stated_call_system"
  shows "(d,t)\<in>positive_meaning stated_calls_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_call_system"
  using added_definition_preserves_old(2)[OF stated_call_system_formed
    stated_calls_system_formed[unfolded stated_calls_system_def] _ assms]
  by (simp add: stated_calls_system_def)

lemma stated_calls_clause [simp]:
  "((584,c),S)\<in>system_clauses stated_calls_system \<longleftrightarrow> (c,S)\<in>related_list_clauses 583 584"
  unfolding stated_calls_system_def by (rule audit_layer_clause) simp_all

interpretation stated_calls_profile: related_list_profile stated_calls_system 583 584
  by (rule related_list_profile.intro) (auto simp: stated_calls_call)

lemma stated_calls_rows:
  assumes formed: "term_formed (call_instance_rows_term qs)"
  shows "(584,context_relation_argument (Payload_Term []) (call_instance_rows_term qs) r)\<in>positive_meaning stated_calls_system
    \<longleftrightarrow> r=data_list_term (map (\<lambda>(s,d,x). Pair_Term (Payload_Term s) (data_list_term (term_stated x))) qs)"
proof -
  let ?rows="map (\<lambda>(s,d,x). Pair_Term (Payload_Term s) (call_instance_value d x)) qs"
  have rows: "call_instance_rows_term qs=data_list_term ?rows" by (induction qs) auto
  have rf: "\<forall>x\<in>set ?rows. term_formed x" using formed rows by (simp only: stated_list_formed)
  have element: "(583,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_calls_system
      \<longleftrightarrow> y=stated_call_row x" if x: "x\<in>set ?rows" for x y
  proof -
    obtain s d t where xq: "(s,d,t)\<in>set qs" and xs: "x=Pair_Term (Payload_Term s) (Pair_Term (site_data_term (fst d) (snd d)) t)"
      using x by (auto simp: call_instance_value_def)
    have xt: "term_formed x" using rf x by blast
    have xf: "term_formed (Payload_Term s)" "term_formed (site_data_term (fst d) (snd d))" "term_formed t"
      using xt xs by simp_all
    have old: "(583,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_calls_system \<longleftrightarrow>
        (583,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_call_system"
      by (rule stated_calls_old_meaning) simp
    show ?thesis
      using stated_call_on_row[of "Payload_Term []", OF _ xf, of y] old xs by (simp add: octets_formed_def)
  qed
  have "(584,context_relation_argument (Payload_Term []) (call_instance_rows_term qs) r)\<in>positive_meaning stated_calls_system
      \<longleftrightarrow> (\<exists>ys. r=data_list_term ys \<and> list_all2 (\<lambda>x y. (583,context_relation_argument (Payload_Term []) x y)
        \<in>positive_meaning stated_calls_system) ?rows ys)"
    by (simp only: stated_calls_profile.exact rows factor_term.inject data_list_term_injective) (auto simp: octets_formed_def)
  also have "\<dots> \<longleftrightarrow> r=data_list_term (map stated_call_row ?rows)"
  proof -
    have lifted: "list_all2 (\<lambda>x y. (583,context_relation_argument (Payload_Term []) x y)
        \<in>positive_meaning stated_calls_system) ?rows ys \<longleftrightarrow> ys=map stated_call_row ?rows" for ys
      by (rule stated_list_all2_function) (use element in blast)
    show ?thesis using lifted by auto
  qed
  also have "map stated_call_row ?rows=map (\<lambda>(s,d,x). Pair_Term (Payload_Term s) (data_list_term (term_stated x))) qs"
    by (auto simp: call_instance_value_def)
  finally show ?thesis .
qed

section \<open>A material premise's operand at its socket and field (585, 586)\<close>

fun tuple_stated :: "factor_term \<Rightarrow> factor_term list list" where
  "tuple_stated (Pair_Term a (Pair_Term b (Pair_Term c (Pair_Term d e))))=
    [term_stated a,term_stated b,term_stated c,term_stated d,term_stated e]"
| "tuple_stated x=[]"

fun stated_material_row :: "factor_term \<Rightarrow> factor_term" where
  "stated_material_row (Pair_Term k x)=Pair_Term k (stated_tuple (tuple_stated x))"
| "stated_material_row x=x"

lemma tuple_stated_material:
  "tuple_stated (material_tuple a b c d e)=[term_stated a,term_stated b,term_stated c,term_stated d,term_stated e]"
  by (simp add: material_tuple_def)

lemma material_instance_stated:
  assumes inst: "material_pattern_instance V M a b c d e" and blank: "\<forall>x y. (x,y)\<in>V \<longrightarrow> term_stated y=[]"
  shows "tuple_stated (material_tuple a b c d e)=material_stated M"
proof -
  have fields: "pattern_instance V (material_source M) a" "pattern_instance V (material_atoms M) b"
    "pattern_instance V (material_edges M) c" "pattern_instance V (material_counts M) d"
    "pattern_instance V (material_functions M) e"
    using inst by (simp_all add: material_pattern_instance_def)
  have "term_stated a=pattern_stated (material_source M)" "term_stated b=pattern_stated (material_atoms M)"
    "term_stated c=pattern_stated (material_edges M)" "term_stated d=pattern_stated (material_counts M)"
    "term_stated e=pattern_stated (material_functions M)"
    by (rule pattern_instance_stated[OF fields(1) blank], rule pattern_instance_stated[OF fields(2) blank],
      rule pattern_instance_stated[OF fields(3) blank], rule pattern_instance_stated[OF fields(4) blank],
      rule pattern_instance_stated[OF fields(5) blank])
  then show ?thesis by (simp add: tuple_stated_material material_stated_def material_fields_def)
qed

definition stated_material_schema :: "(nat,nat,nat) factor_schema" where
  "stated_material_schema=data_rule
    (context_relation_pattern data_x
      (Pattern_Pair data_y (Pattern_Pair data_z (Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 4)
        (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))))))
      (Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8)
        (Pattern_Pair (Pattern_Variable 9) (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)))))))
    {(0,580,Pattern_Pair data_z (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 7))),
     (1,580,Pattern_Pair data_w (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 8))),
     (2,580,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 9))),
     (3,580,Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 10))),
     (4,580,Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 11)))}"

definition stated_material_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_material_system=add_view_definition stated_calls_system 585 data_x {(0,stated_material_schema)}"

lemma stated_material_system_formed [simp]: "schema_system_formed stated_material_system"
  unfolding stated_material_system_def
  by (rule add_recursive_definition_formed[OF stated_calls_system_formed])
    (auto simp: stated_material_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma stated_material_definitions [simp]:
  "system_definitions stated_material_system=insert 585 (system_definitions stated_calls_system)"
  by (simp add: stated_material_system_def)

lemma stated_material_call:
  "schema_call_formed stated_material_system d t \<longleftrightarrow> d\<in>system_definitions stated_material_system \<and> term_formed t"
  using added_variable_calls[OF stated_calls_system_formed
    stated_material_system_formed[unfolded stated_material_system_def] stated_calls_call]
  by (simp only: stated_material_system_def[symmetric])

lemma stated_material_old_meaning:
  assumes "d\<in>system_definitions stated_calls_system"
  shows "(d,t)\<in>positive_meaning stated_material_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_calls_system"
  using added_definition_preserves_old(2)[OF stated_calls_system_formed
    stated_material_system_formed[unfolded stated_material_system_def] _ assms]
  by (simp add: stated_material_system_def)

lemma stated_material_clause [simp]:
  "((585,c),S)\<in>system_clauses stated_material_system \<longleftrightarrow> c=0 \<and> S=stated_material_schema"
  unfolding stated_material_system_def by (subst audit_layer_clause) simp_all

lemma stated_material_leaves:
  "(580,t)\<in>positive_meaning stated_material_system \<longleftrightarrow> (580,t)\<in>positive_meaning stated_leaves_system"
  by (simp add: stated_material_old_meaning stated_calls_old_meaning stated_call_old_meaning
    stated_values_old_meaning stated_value_old_meaning)

theorem stated_material_on_row:
  assumes formed: "term_formed c" "term_formed k" "term_formed a1" "term_formed a2" "term_formed a3"
    "term_formed a4" "term_formed a5"
  shows "(585,context_relation_argument c (Pair_Term k (material_tuple a1 a2 a3 a4 a5)) y)
      \<in>positive_meaning stated_material_system \<longleftrightarrow>
    y=Pair_Term k (stated_tuple (tuple_stated (material_tuple a1 a2 a3 a4 a5)))"
proof
  assume holds: "(585,context_relation_argument c (Pair_Term k (material_tuple a1 a2 a3 a4 a5)) y)
      \<in>positive_meaning stated_material_system"
  obtain c' S h where clause: "((585,c'),S)\<in>system_clauses stated_material_system"
    and conclusion: "context_relation_argument c (Pair_Term k (material_tuple a1 a2 a3 a4 a5)) y=
      evaluate_pattern h (schema_conclusion S)"
    and "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_material_system"
    by (rule positive_meaning_valuationE[OF holds])
  have schema: "S=stated_material_schema" using clause by simp
  have fields: "h 1=k" "h 2=a1" "h 3=a2" "h 4=a3" "h 5=a4" "h 6=a5"
    "y=Pair_Term k (Pair_Term (h 7) (Pair_Term (h 8) (Pair_Term (h 9) (Pair_Term (h 10) (h 11)))))"
    using conclusion by (simp_all add: schema stated_material_schema_def material_tuple_def)
  have "(580,Pair_Term (h 2) (Pair_Term (Payload_Term []) (h 7)))\<in>positive_meaning stated_leaves_system"
    "(580,Pair_Term (h 3) (Pair_Term (Payload_Term []) (h 8)))\<in>positive_meaning stated_leaves_system"
    "(580,Pair_Term (h 4) (Pair_Term (Payload_Term []) (h 9)))\<in>positive_meaning stated_leaves_system"
    "(580,Pair_Term (h 5) (Pair_Term (Payload_Term []) (h 10)))\<in>positive_meaning stated_leaves_system"
    "(580,Pair_Term (h 6) (Pair_Term (Payload_Term []) (h 11)))\<in>positive_meaning stated_leaves_system"
    using support by (simp_all add: schema stated_material_schema_def stated_material_leaves)
  then show "y=Pair_Term k (stated_tuple (tuple_stated (material_tuple a1 a2 a3 a4 a5)))"
    using fields by (simp add: stated_leaves_list tuple_stated_material stated_tuple_def material_tuple_def)
next
  assume y: "y=Pair_Term k (stated_tuple (tuple_stated (material_tuple a1 a2 a3 a4 a5)))"
  have leaves: "(580,Pair_Term a (Pair_Term (Payload_Term []) (data_list_term (term_stated a))))
      \<in>positive_meaning stated_material_system" if "term_formed a" for a
    using that by (simp add: stated_material_leaves stated_leaves_list)
  have lf: "term_formed (data_list_term (term_stated a))" if "term_formed a" for a
    using term_stated_formed[OF that] by (simp add: stated_list_formed)
  let ?h="\<lambda>n::nat. if n=0 then c else if n=1 then k else if n=2 then a1 else if n=3 then a2
    else if n=4 then a3 else if n=5 then a4 else if n=6 then a5
    else if n=7 then data_list_term (term_stated a1) else if n=8 then data_list_term (term_stated a2)
    else if n=9 then data_list_term (term_stated a3) else if n=10 then data_list_term (term_stated a4)
    else data_list_term (term_stated a5)"
  have "(585,evaluate_pattern ?h (schema_conclusion stated_material_schema))\<in>positive_meaning stated_material_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (use formed leaves lf in \<open>auto simp: stated_material_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def octets_formed_def stated_material_call\<close>)
  then show "(585,context_relation_argument c (Pair_Term k (material_tuple a1 a2 a3 a4 a5)) y)
      \<in>positive_meaning stated_material_system"
    by (simp add: stated_material_schema_def y tuple_stated_material stated_tuple_def material_tuple_def)
qed

definition stated_materials_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_materials_system=add_view_definition stated_material_system 586 data_x (related_list_clauses 585 586)"

lemma stated_materials_system_formed [simp]: "schema_system_formed stated_materials_system"
  unfolding stated_materials_system_def
  by (rule add_recursive_definition_formed[OF stated_material_system_formed])
    (auto simp: related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_materials_definitions [simp]:
  "system_definitions stated_materials_system=insert 586 (system_definitions stated_material_system)"
  by (simp add: stated_materials_system_def)

lemma stated_materials_call:
  "schema_call_formed stated_materials_system d t \<longleftrightarrow> d\<in>system_definitions stated_materials_system \<and> term_formed t"
  using added_variable_calls[OF stated_material_system_formed
    stated_materials_system_formed[unfolded stated_materials_system_def] stated_material_call]
  by (simp only: stated_materials_system_def[symmetric])

lemma stated_materials_old_meaning:
  assumes "d\<in>system_definitions stated_material_system"
  shows "(d,t)\<in>positive_meaning stated_materials_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_material_system"
  using added_definition_preserves_old(2)[OF stated_material_system_formed
    stated_materials_system_formed[unfolded stated_materials_system_def] _ assms]
  by (simp add: stated_materials_system_def)

lemma stated_materials_clause [simp]:
  "((586,c),S)\<in>system_clauses stated_materials_system \<longleftrightarrow> (c,S)\<in>related_list_clauses 585 586"
  unfolding stated_materials_system_def by (rule audit_layer_clause) simp_all

interpretation stated_materials_profile: related_list_profile stated_materials_system 585 586
  by (rule related_list_profile.intro) (auto simp: stated_materials_call)

lemma stated_materials_rows:
  assumes formed: "term_formed (binding_rows_term cs)"
    and tuples: "\<forall>(s,x)\<in>set cs. \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
  shows "(586,context_relation_argument (Payload_Term []) (binding_rows_term cs) r)\<in>positive_meaning stated_materials_system
    \<longleftrightarrow> r=data_list_term (map (\<lambda>(s,x). material_place_term (s,tuple_stated x)) cs)"
proof -
  let ?rows="map (\<lambda>(s,x). Pair_Term (Payload_Term s) x) cs"
  have rows: "binding_rows_term cs=data_list_term ?rows" by (induction cs) auto
  have rf: "\<forall>x\<in>set ?rows. term_formed x" using formed rows by (simp only: stated_list_formed)
  have element: "(585,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_materials_system
      \<longleftrightarrow> y=stated_material_row x" if x: "x\<in>set ?rows" for x y
  proof -
    obtain s x0 where sx: "(s,x0)\<in>set cs" and xx: "x=Pair_Term (Payload_Term s) x0" using x by auto
    have "case (s,x0) of (s,x) \<Rightarrow> \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
      by (rule bspec[OF tuples sx])
    then obtain a1 a2 a3 a4 a5 where "x0=material_tuple a1 a2 a3 a4 a5" by auto
    then have xs: "x=Pair_Term (Payload_Term s) (material_tuple a1 a2 a3 a4 a5)" using xx by simp
    have xt: "term_formed x" using rf x by blast
    have xf: "term_formed (Payload_Term s)" "term_formed a1" "term_formed a2" "term_formed a3" "term_formed a4"
      "term_formed a5" using xt xs by (simp_all add: material_tuple_def)
    have old: "(585,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_materials_system \<longleftrightarrow>
        (585,context_relation_argument (Payload_Term []) x y)\<in>positive_meaning stated_material_system"
      by (rule stated_materials_old_meaning) simp
    show ?thesis
      using stated_material_on_row[of "Payload_Term []", OF _ xf, of y] old xs by (simp add: octets_formed_def)
  qed
  have "(586,context_relation_argument (Payload_Term []) (binding_rows_term cs) r)\<in>positive_meaning stated_materials_system
      \<longleftrightarrow> (\<exists>ys. r=data_list_term ys \<and> list_all2 (\<lambda>x y. (585,context_relation_argument (Payload_Term []) x y)
        \<in>positive_meaning stated_materials_system) ?rows ys)"
    by (simp only: stated_materials_profile.exact rows factor_term.inject data_list_term_injective) (auto simp: octets_formed_def)
  also have "\<dots> \<longleftrightarrow> r=data_list_term (map stated_material_row ?rows)"
  proof -
    have lifted: "list_all2 (\<lambda>x y. (585,context_relation_argument (Payload_Term []) x y)
        \<in>positive_meaning stated_materials_system) ?rows ys \<longleftrightarrow> ys=map stated_material_row ?rows" for ys
      by (rule stated_list_all2_function) (use element in blast)
    show ?thesis using lifted by auto
  qed
  also have "map stated_material_row ?rows=map (\<lambda>(s,x). material_place_term (s,tuple_stated x)) cs"
    by (auto simp: material_place_term_def)
  finally show ?thesis .
qed

section \<open>The report of one clause (587)\<close>

text \<open>
  The clause is instantiated by 65 at a hidden table whose values state nothing (582). A ground clause
  has an empty table and no premise rows, and its report asserts its instance; any other clause has a
  nonempty table, call rows or material rows, and its ground field is empty.
\<close>

definition stated_clause_ground_schema :: "(nat,nat,nat) factor_schema" where
  "stated_clause_ground_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
      (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Payload []))
        (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Payload []) (Pattern_Payload [])))))
    {(0,65,schema_instantiation_pattern data_x data_y data_z (Pattern_Payload []) (Pattern_Variable 4)
       (Pattern_Payload []) (Pattern_Payload [])),
     (1,580,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 7)))}"

definition stated_clause_open_schema ::
    "nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> (nat,nat,nat) factor_schema" where
  "stated_clause_open_schema T Q M=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
      (Pattern_Pair (Pattern_Payload [])
        (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)))))
    {(0,65,schema_instantiation_pattern data_x data_y data_z T (Pattern_Variable 4) Q M),
     (1,582,T),
     (2,580,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 7))),
     (3,584,context_relation_pattern (Pattern_Payload []) Q (Pattern_Variable 8)),
     (4,586,context_relation_pattern (Pattern_Payload []) M (Pattern_Variable 9))}"

abbreviation stated_open :: "nat term_pattern" where
  "stated_open \<equiv> Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)"

definition stated_clause_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "stated_clause_clauses={(0,stated_clause_ground_schema),
    (1,stated_clause_open_schema stated_open (Pattern_Variable 5) (Pattern_Variable 6)),
    (2,stated_clause_open_schema data_w stated_open (Pattern_Variable 6)),
    (3,stated_clause_open_schema data_w (Pattern_Variable 5) stated_open)}"

definition stated_clause_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_clause_system=add_view_definition stated_materials_system 587 data_x stated_clause_clauses"

lemma stated_clause_system_formed [simp]: "schema_system_formed stated_clause_system"
  unfolding stated_clause_system_def
  by (rule add_recursive_definition_formed[OF stated_materials_system_formed])
    (auto simp: stated_clause_clauses_def stated_clause_ground_schema_def stated_clause_open_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_clause_definitions [simp]:
  "system_definitions stated_clause_system=insert 587 (system_definitions stated_materials_system)"
  by (simp add: stated_clause_system_def)

lemma stated_clause_call:
  "schema_call_formed stated_clause_system d t \<longleftrightarrow> d\<in>system_definitions stated_clause_system \<and> term_formed t"
  using added_variable_calls[OF stated_materials_system_formed
    stated_clause_system_formed[unfolded stated_clause_system_def] stated_materials_call]
  by (simp only: stated_clause_system_def[symmetric])

lemma stated_clause_old_meaning:
  assumes "d\<in>system_definitions stated_materials_system"
  shows "(d,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_materials_system"
  using added_definition_preserves_old(2)[OF stated_materials_system_formed
    stated_clause_system_formed[unfolded stated_clause_system_def] _ assms]
  by (simp add: stated_clause_system_def)

lemma stated_clause_clause [simp]:
  "((587,c),S)\<in>system_clauses stated_clause_system \<longleftrightarrow> (c,S)\<in>stated_clause_clauses"
  unfolding stated_clause_system_def by (rule audit_layer_clause) simp_all

lemmas stated_lower_meanings=stated_clause_old_meaning stated_materials_old_meaning stated_material_old_meaning
  stated_calls_old_meaning stated_call_old_meaning stated_values_old_meaning stated_value_old_meaning

lemma stated_clause_components:
  "(65,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (65,t)\<in>positive_meaning schema_instantiation_system"
  "(582,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (582,t)\<in>positive_meaning stated_values_system"
  "(580,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (580,t)\<in>positive_meaning stated_leaves_system"
  "(584,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (584,t)\<in>positive_meaning stated_calls_system"
  "(586,t)\<in>positive_meaning stated_clause_system \<longleftrightarrow> (586,t)\<in>positive_meaning stated_materials_system"
  using stated_leaves_old_meaning[of 65 t] payload_audit_admission_meaning[of 65 t]
    definition_call_admission_instantiation_meaning[of 65 t]
  by (simp_all add: stated_lower_meanings)

lemma stated_clause_core:
  assumes inst: "(65,schema_instantiation_argument e u a T t Q Cm)\<in>positive_meaning schema_instantiation_system"
    and table: "(582,T)\<in>positive_meaning stated_values_system"
    and head: "(580,Pair_Term t (Pair_Term (Payload_Term []) lt))\<in>positive_meaning stated_leaves_system"
    and calls: "(584,context_relation_argument (Payload_Term []) Q qr)\<in>positive_meaning stated_calls_system"
    and materials: "(586,context_relation_argument (Payload_Term []) Cm mr)\<in>positive_meaning stated_materials_system"
  obtains E v l S qs ms where "environment_value_presents E e" "u=use_data_term v" "a=Payload_Term l"
    "native_schema_at E v l S" "lt=data_list_term (pattern_stated (schema_conclusion S))"
    "distinct (map fst qs)" "set qs=clause_calls S" "distinct (map fst ms)" "set ms=clause_materials S"
    "qr=data_list_term (map place_term qs)" "mr=data_list_term (map material_place_term ms)"
    "T=Payload_Term [] \<longleftrightarrow> schema_variables S={}" "Q=Payload_Term [] \<longleftrightarrow> schema_premises S={}"
    "Cm=Payload_Term [] \<longleftrightarrow> schema_material_premises S={}"
    "\<And>g. pattern_ground (schema_conclusion S)=Some g \<Longrightarrow> t=g"
proof -
  obtain E v l xs S qs cs where parts: "environment_value_presents E e" "u=use_data_term v" "a=Payload_Term l"
    "T=binding_rows_term xs" "Q=call_instance_rows_term qs" "Cm=binding_rows_term cs"
    "distinct xs" "distinct qs" "distinct cs" "native_schema_at E v l S" "schema_instance S (set xs) t (set qs)"
    "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using inst by (simp only: schema_instantiation_exact factor_term.inject) blast
  have argf: "term_formed (schema_instantiation_argument e u a T t Q Cm)"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]] by blast
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) (set xs)"
    and conc: "pattern_instance (set xs) (schema_conclusion S) t" and body: "schema_premise_instance S (set xs) (set qs)"
    using parts(11) by (auto simp: schema_instance_def)
  have blank: "\<forall>b x. (b,x)\<in>set xs \<longrightarrow> term_stated x=[]" using table parts(4) stated_values_rows by fastforce
  have lt: "lt=data_list_term (pattern_stated (schema_conclusion S))"
    using head pattern_instance_stated[OF conc blank] by (simp add: stated_leaves_list)
  have qf: "term_formed (call_instance_rows_term qs)" using argf parts(5) by simp
  have qr: "qr=data_list_term (map (\<lambda>(s,d,x). Pair_Term (Payload_Term s) (data_list_term (term_stated x))) qs)"
    by (rule stated_calls_rows[OF qf, THEN iffD1, OF calls[unfolded parts(5)]])
  let ?qs="map (\<lambda>(s,d,x). (s,term_stated x)) qs"
  have origin: "\<exists>p. (s,d,p)\<in>schema_premises S \<and> pattern_instance (set xs) p x" if "(s,d,x)\<in>set qs" for s d x
    using schema_premise_instance_origin[OF body that] by blast
  have cover: "\<exists>x. (s,d,x)\<in>set qs \<and> pattern_instance (set xs) p x" if "(s,d,p)\<in>schema_premises S" for s d p
    using body that unfolding schema_premise_instance_def by blast
  have qset: "set ?qs=clause_calls S"
  proof
    show "set ?qs\<subseteq>clause_calls S"
    proof
      fix z assume "z\<in>set ?qs"
      then obtain s d x where z: "z=(s,term_stated x)" "(s,d,x)\<in>set qs" by auto
      obtain p where p: "(s,d,p)\<in>schema_premises S" "pattern_instance (set xs) p x" using origin z(2) by blast
      show "z\<in>clause_calls S" using z p pattern_instance_stated[OF p(2) blank] by (force simp: clause_calls_def)
    qed
    show "clause_calls S\<subseteq>set ?qs"
    proof
      fix z assume "z\<in>clause_calls S"
      then obtain s d p where z: "z=(s,pattern_stated p)" "(s,d,p)\<in>schema_premises S" by (auto simp: clause_calls_def)
      obtain x where x: "(s,d,x)\<in>set qs" "pattern_instance (set xs) p x" using cover z(2) by blast
      show "z\<in>set ?qs" using z x pattern_instance_stated[OF x(2) blank] by force
    qed
  qed
  have qkeys: "map fst ?qs=map fst qs" by (induction qs) auto
  have qd: "distinct (map fst qs)"
    using parts(8) body distinct_keys_iff[of qs] by (simp add: schema_premise_instance_def)
  have qdistinct: "distinct (map fst ?qs)" by (simp only: qkeys qd)
  have qplace: "qr=data_list_term (map place_term ?qs)" using qr by (simp add: place_term_def split_def comp_def)
  have cf: "term_formed (binding_rows_term cs)" using argf parts(6) by simp
  have tuples: "\<forall>(s,x)\<in>set cs. \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
  proof (intro ballI)
    fix z assume z: "z\<in>set cs"
    obtain q y where zq: "z=(q,y)" by (cases z)
    have "(q,y)\<in>material_instance_relation (set xs) (schema_material_premises S)" using z zq parts(12) by simp
    then show "case z of (s,x) \<Rightarrow> \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
      using zq unfolding material_instance_relation_def by blast
  qed
  have mr: "mr=data_list_term (map (\<lambda>(s,x). material_place_term (s,tuple_stated x)) cs)"
    by (rule stated_materials_rows[OF cf tuples, THEN iffD1, OF materials[unfolded parts(6)]])
  let ?ms="map (\<lambda>(s,x). (s,tuple_stated x)) cs"
  have mset: "set ?ms=clause_materials S"
  proof
    show "set ?ms\<subseteq>clause_materials S"
    proof
      fix z assume "z\<in>set ?ms"
      then obtain s x where z: "z=(s,tuple_stated x)" "(s,x)\<in>set cs" by auto
      obtain M a1 a2 a3 a4 a5 where m: "(s,M)\<in>schema_material_premises S" "x=material_tuple a1 a2 a3 a4 a5"
        "material_pattern_instance (set xs) M a1 a2 a3 a4 a5"
        using z(2) parts(12) by (auto simp: material_instance_relation_def)
      show "z\<in>clause_materials S"
        using z m material_instance_stated[OF m(3) blank] by (force simp: clause_materials_def)
    qed
    show "clause_materials S\<subseteq>set ?ms"
    proof
      fix z assume "z\<in>clause_materials S"
      then obtain s M where z: "z=(s,material_stated M)" "(s,M)\<in>schema_material_premises S"
        by (auto simp: clause_materials_def)
      have mf: "material_pattern_formed M" using sf z(2) by (auto simp: schema_formed_def)
      have scope: "material_variables M\<subseteq>rel_dom (set xs)"
        using bindings z(2) by (auto simp: term_bindings_formed_def schema_variables_def)
      obtain a1 a2 a3 a4 a5 where inst5: "material_pattern_instance (set xs) M a1 a2 a3 a4 a5"
        using material_pattern_instance_exists[OF mf scope] by blast
      have "(s,material_tuple a1 a2 a3 a4 a5)\<in>set cs"
        unfolding parts(12) material_instance_relation_def using z(2) inst5 by blast
      then show "z\<in>set ?ms" using z material_instance_stated[OF inst5 blank] by force
    qed
  qed
  have mkeys: "map fst ?ms=map fst cs" by (induction cs) auto
  have msv: "single_valued (set cs)"
    using native_schema_material_instance_boundary(2)[OF parts(10) bindings] parts(12) by simp
  have md: "distinct (map fst cs)" using parts(9) msv distinct_keys_iff[of cs] by simp
  have mdistinct: "distinct (map fst ?ms)" by (simp only: mkeys md)
  have mplace: "mr=data_list_term (map material_place_term ?ms)" using mr by (simp add: split_def comp_def)
  have tempty: "T=Payload_Term [] \<longleftrightarrow> schema_variables S={}"
  proof -
    have "T=Payload_Term [] \<longleftrightarrow> xs=[]" by (simp only: parts(4) binding_rows_empty)
    moreover have "rel_dom (set xs)=schema_variables S" using bindings by (simp add: term_bindings_formed_def)
    ultimately show ?thesis by auto
  qed
  have qempty: "Q=Payload_Term [] \<longleftrightarrow> schema_premises S={}"
  proof -
    have "Q=Payload_Term [] \<longleftrightarrow> set ?qs={}" unfolding parts(5) call_rows_empty by simp
    then show ?thesis using qset by (auto simp: clause_calls_def)
  qed
  have cempty: "Cm=Payload_Term [] \<longleftrightarrow> schema_material_premises S={}"
  proof -
    have "Cm=Payload_Term [] \<longleftrightarrow> set ?ms={}" unfolding parts(6) binding_rows_empty by simp
    then show ?thesis using mset by (auto simp: clause_materials_def)
  qed
  show ?thesis
    by (rule that[OF parts(1-3,10) lt qdistinct qset mdistinct mset qplace mplace tempty qempty cempty
      pattern_ground_instance[OF conc]])
qed

abbreviation stated_clause_result :: "factor_term \<Rightarrow> bool" where
  "stated_clause_result z \<equiv> \<exists>E e u a S r. z=Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r \<and>
    environment_value_presents E e \<and> native_schema_at E u a S \<and> clause_stated_presents S r"

lemma stated_empty_rows:
  "(582,Payload_Term [])\<in>positive_meaning stated_values_system"
  "(584,context_relation_argument (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning stated_calls_system"
  "(586,context_relation_argument (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning stated_materials_system"
  using stated_values_rows[of "[]"] stated_calls_profile.lists[of "Payload_Term []" "[]" "[]"]
    stated_materials_profile.lists[of "Payload_Term []" "[]" "[]"] by (simp_all add: octets_formed_def)

theorem stated_clause_sound:
  assumes holds: "(587,z)\<in>positive_meaning stated_clause_system"
  shows "stated_clause_result z"
proof -
  obtain c S h where clause: "((587,c),S)\<in>system_clauses stated_clause_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning stated_clause_system"
    using positive_meaning_valuationE[OF holds] by blast
  have "(c,S)\<in>stated_clause_clauses" using clause by simp
  then consider (ground) "S=stated_clause_ground_schema"
    | (vars) "S=stated_clause_open_schema stated_open (Pattern_Variable 5) (Pattern_Variable 6)"
    | (calls) "S=stated_clause_open_schema data_w stated_open (Pattern_Variable 6)"
    | (materials) "S=stated_clause_open_schema data_w (Pattern_Variable 5) stated_open"
    by (auto simp: stated_clause_clauses_def)
  then show ?thesis
  proof cases
    case ground
    have inst: "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (Payload_Term []) (h 4) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning schema_instantiation_system"
      and head: "(580,Pair_Term (h 4) (Pair_Term (Payload_Term []) (h 7)))\<in>positive_meaning stated_leaves_system"
      using support by (auto simp: ground stated_clause_ground_schema_def stated_clause_components)
    obtain E v l S' qs ms where core: "environment_value_presents E (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
      "native_schema_at E v l S'" "h 7=data_list_term (pattern_stated (schema_conclusion S'))"
      "distinct (map fst qs)" "set qs=clause_calls S'" "distinct (map fst ms)" "set ms=clause_materials S'"
      "Payload_Term []=data_list_term (map place_term qs)" "Payload_Term []=data_list_term (map material_place_term ms)"
      "Payload_Term []=Payload_Term [] \<longleftrightarrow> schema_variables S'={}"
      "Payload_Term []=Payload_Term [] \<longleftrightarrow> schema_premises S'={}"
      "Payload_Term []=Payload_Term [] \<longleftrightarrow> schema_material_premises S'={}"
      "\<And>g. pattern_ground (schema_conclusion S')=Some g \<Longrightarrow> h 4=g"
      using stated_clause_core[OF inst stated_empty_rows(1) head stated_empty_rows(2,3)] by blast
    have empties: "schema_variables S'={}" "schema_premises S'={}" "schema_material_premises S'={}"
      using core(12,13,14) by simp_all
    obtain g where g: "pattern_ground (schema_conclusion S')=Some g"
      using empties(1) pattern_ground_none[of "schema_conclusion S'"] by (cases "pattern_ground (schema_conclusion S')")
        (auto simp: schema_variables_def)
    have groundf: "clause_ground S'=[h 4]" using g empties(2,3) core(15)[OF g] by (simp add: clause_ground_def)
    have "clause_stated_presents S' (Pair_Term (Pair_Term (h 4) (Payload_Term []))
        (Pair_Term (h 7) (Pair_Term (Payload_Term []) (Payload_Term []))))"
      unfolding clause_stated_presents_def using core(6-11) groundf core(5) by (intro exI[of _ qs] exI[of _ ms]) simp
    then have "clause_stated_presents S' (Pair_Term (data_list_term [h 4])
        (Pair_Term (h 7) (Pair_Term (Payload_Term []) (Payload_Term []))))" by simp
    moreover have "z=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (Pair_Term (Pair_Term (h 4) (Payload_Term []))
        (Pair_Term (h 7) (Pair_Term (Payload_Term []) (Payload_Term []))))"
      using conclusion by (simp add: ground stated_clause_ground_schema_def)
    ultimately show ?thesis using core(1-4) by auto
  next
    case vars
    have inst: "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (Pair_Term (h 10) (h 11)) (h 4) (h 5) (h 6))
        \<in>positive_meaning schema_instantiation_system"
      and table: "(582,Pair_Term (h 10) (h 11))\<in>positive_meaning stated_values_system"
      and head: "(580,Pair_Term (h 4) (Pair_Term (Payload_Term []) (h 7)))\<in>positive_meaning stated_leaves_system"
      and calls: "(584,context_relation_argument (Payload_Term []) (h 5) (h 8))\<in>positive_meaning stated_calls_system"
      and mats: "(586,context_relation_argument (Payload_Term []) (h 6) (h 9))\<in>positive_meaning stated_materials_system"
      using support by (auto simp: vars stated_clause_open_schema_def stated_clause_components)
    obtain E v l S' qs ms where core: "environment_value_presents E (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
      "native_schema_at E v l S'" "h 7=data_list_term (pattern_stated (schema_conclusion S'))"
      "distinct (map fst qs)" "set qs=clause_calls S'" "distinct (map fst ms)" "set ms=clause_materials S'"
      "h 8=data_list_term (map place_term qs)" "h 9=data_list_term (map material_place_term ms)"
      "Pair_Term (h 10) (h 11)=Payload_Term [] \<longleftrightarrow> schema_variables S'={}"
      "h 5=Payload_Term [] \<longleftrightarrow> schema_premises S'={}" "h 6=Payload_Term [] \<longleftrightarrow> schema_material_premises S'={}"
      "\<And>g. pattern_ground (schema_conclusion S')=Some g \<Longrightarrow> h 4=g"
      using stated_clause_core[OF inst table head calls mats] by blast
    have groundf: "clause_ground S'=[]" using core(12) clause_ground_ground[of S'] by auto
    have "clause_stated_presents S' (Pair_Term (Payload_Term []) (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      unfolding clause_stated_presents_def using core(5-11) groundf by (intro exI[of _ qs] exI[of _ ms]) simp
    moreover have "z=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (Pair_Term (Payload_Term [])
        (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      using conclusion by (simp add: vars stated_clause_open_schema_def)
    ultimately show ?thesis using core(1-4) by auto
  next
    case calls
    have inst: "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (Pair_Term (h 10) (h 11)) (h 6))
        \<in>positive_meaning schema_instantiation_system"
      and table: "(582,h 3)\<in>positive_meaning stated_values_system"
      and head: "(580,Pair_Term (h 4) (Pair_Term (Payload_Term []) (h 7)))\<in>positive_meaning stated_leaves_system"
      and callrows: "(584,context_relation_argument (Payload_Term []) (Pair_Term (h 10) (h 11)) (h 8))\<in>positive_meaning stated_calls_system"
      and mats: "(586,context_relation_argument (Payload_Term []) (h 6) (h 9))\<in>positive_meaning stated_materials_system"
      using support by (auto simp: calls stated_clause_open_schema_def stated_clause_components)
    obtain E v l S' qs ms where core: "environment_value_presents E (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
      "native_schema_at E v l S'" "h 7=data_list_term (pattern_stated (schema_conclusion S'))"
      "distinct (map fst qs)" "set qs=clause_calls S'" "distinct (map fst ms)" "set ms=clause_materials S'"
      "h 8=data_list_term (map place_term qs)" "h 9=data_list_term (map material_place_term ms)"
      "h 3=Payload_Term [] \<longleftrightarrow> schema_variables S'={}"
      "Pair_Term (h 10) (h 11)=Payload_Term [] \<longleftrightarrow> schema_premises S'={}"
      "h 6=Payload_Term [] \<longleftrightarrow> schema_material_premises S'={}"
      "\<And>g. pattern_ground (schema_conclusion S')=Some g \<Longrightarrow> h 4=g"
      using stated_clause_core[OF inst table head callrows mats] by blast
    have groundf: "clause_ground S'=[]" using core(13) clause_ground_ground[of S'] by auto
    have "clause_stated_presents S' (Pair_Term (Payload_Term []) (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      unfolding clause_stated_presents_def using core(5-11) groundf by (intro exI[of _ qs] exI[of _ ms]) simp
    moreover have "z=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (Pair_Term (Payload_Term [])
        (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      using conclusion by (simp add: calls stated_clause_open_schema_def)
    ultimately show ?thesis using core(1-4) by auto
  next
    case materials
    have inst: "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (Pair_Term (h 10) (h 11)))
        \<in>positive_meaning schema_instantiation_system"
      and table: "(582,h 3)\<in>positive_meaning stated_values_system"
      and head: "(580,Pair_Term (h 4) (Pair_Term (Payload_Term []) (h 7)))\<in>positive_meaning stated_leaves_system"
      and callrows: "(584,context_relation_argument (Payload_Term []) (h 5) (h 8))\<in>positive_meaning stated_calls_system"
      and mats: "(586,context_relation_argument (Payload_Term []) (Pair_Term (h 10) (h 11)) (h 9))\<in>positive_meaning stated_materials_system"
      using support by (auto simp: materials stated_clause_open_schema_def stated_clause_components)
    obtain E v l S' qs ms where core: "environment_value_presents E (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
      "native_schema_at E v l S'" "h 7=data_list_term (pattern_stated (schema_conclusion S'))"
      "distinct (map fst qs)" "set qs=clause_calls S'" "distinct (map fst ms)" "set ms=clause_materials S'"
      "h 8=data_list_term (map place_term qs)" "h 9=data_list_term (map material_place_term ms)"
      "h 3=Payload_Term [] \<longleftrightarrow> schema_variables S'={}" "h 5=Payload_Term [] \<longleftrightarrow> schema_premises S'={}"
      "Pair_Term (h 10) (h 11)=Payload_Term [] \<longleftrightarrow> schema_material_premises S'={}"
      "\<And>g. pattern_ground (schema_conclusion S')=Some g \<Longrightarrow> h 4=g"
      using stated_clause_core[OF inst table head callrows mats] by blast
    have groundf: "clause_ground S'=[]" using core(14) clause_ground_ground[of S'] by auto
    have "clause_stated_presents S' (Pair_Term (Payload_Term []) (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      unfolding clause_stated_presents_def using core(5-11) groundf by (intro exI[of _ qs] exI[of _ ms]) simp
    moreover have "z=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (Pair_Term (Payload_Term [])
        (Pair_Term (h 7) (Pair_Term (h 8) (h 9))))"
      using conclusion by (simp add: materials stated_clause_open_schema_def)
    ultimately show ?thesis using core(1-4) by auto
  qed
qed

theorem stated_clause_complete:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u a S"
    and presents: "clause_stated_presents S r"
  shows "(587,Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)\<in>positive_meaning stated_clause_system"
proof -
  obtain qs' ms' where p: "distinct (map fst qs')" "set qs'=clause_calls S" "distinct (map fst ms')" "set ms'=clause_materials S"
    "r=Pair_Term (data_list_term (clause_ground S)) (Pair_Term (data_list_term (pattern_stated (schema_conclusion S)))
      (Pair_Term (data_list_term (map place_term qs')) (data_list_term (map material_place_term ms'))))"
    using presents by (auto simp: clause_stated_presents_def)
  have sf: "schema_formed S" by (rule native_schema_formed[OF raw])
  let ?V="(\<lambda>b. (b,Payload_Term [0])) ` schema_variables S"
  have vf: "finite ?V" using schema_variables_finite[OF sf] by simp
  obtain xs where xs: "set xs=?V" "distinct xs" using finite_distinct_list[OF vf] by blast
  have bindings: "term_bindings_formed (schema_variables S) (set xs)"
    using schema_variables_finite[OF sf]
    by (auto simp: xs(1) term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  have blank: "\<forall>b x. (b,x)\<in>set xs \<longrightarrow> term_stated x=[]" using xs(1) by auto
  obtain t qs0 cs0 where fact0: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a) (binding_rows_term xs) t
      (call_instance_rows_term qs0) (binding_rows_term cs0))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw bindings xs(2)] by blast
  have at0: "distinct qs0" "distinct cs0" "schema_instance S (set xs) t (set qs0)"
    "set cs0=material_instance_relation (set xs) (schema_material_premises S)"
    using fact0 schema_instantiation_at_schema[OF source raw] by blast+
  have conc: "pattern_instance (set xs) (schema_conclusion S) t" and body: "schema_premise_instance S (set xs) (set qs0)"
    using at0(3) by (auto simp: schema_instance_def)
  have qsv: "single_valued (set qs0)" using body by (simp add: schema_premise_instance_def)
  have qdom: "fst ` set qs'=rel_dom (set qs0)"
  proof -
    have "fst ` clause_calls S=rel_dom (schema_premises S)"
      by (simp add: clause_calls_def rel_dom_image image_image split_def)
    then show ?thesis using p(2) body by (simp add: schema_premise_instance_def)
  qed
  obtain qs where qs: "map fst qs=map fst qs'" "set qs=set qs0" "distinct qs"
    using stated_keyed_enumeration[OF qsv p(1) qdom] by blast
  have msv: "single_valued (set cs0)"
    using native_schema_material_instance_boundary(2)[OF raw bindings] at0(4) by simp
  have mdom: "fst ` set ms'=rel_dom (set cs0)"
  proof -
    have "rel_dom (set cs0)=rel_dom (schema_material_premises S)"
    proof
      show "rel_dom (set cs0)\<subseteq>rel_dom (schema_material_premises S)"
        using at0(4) by (auto simp: material_instance_relation_def rel_dom_def)
      show "rel_dom (schema_material_premises S)\<subseteq>rel_dom (set cs0)"
      proof
        fix s assume "s\<in>rel_dom (schema_material_premises S)"
        then obtain M where m: "(s,M)\<in>schema_material_premises S" by (auto simp: rel_dom_def)
        have mf: "material_pattern_formed M" using sf m by (auto simp: schema_formed_def)
        have scope: "material_variables M\<subseteq>rel_dom (set xs)"
          using bindings m by (auto simp: term_bindings_formed_def schema_variables_def)
        obtain a1 a2 a3 a4 a5 where inst5: "material_pattern_instance (set xs) M a1 a2 a3 a4 a5"
          using material_pattern_instance_exists[OF mf scope] by blast
        have "(s,material_tuple a1 a2 a3 a4 a5)\<in>set cs0"
          unfolding at0(4) material_instance_relation_def using m inst5 by blast
        then show "s\<in>rel_dom (set cs0)" by (rule rel_domI)
      qed
    qed
    moreover have "fst ` clause_materials S=rel_dom (schema_material_premises S)"
      by (simp add: clause_materials_def rel_dom_image image_image split_def)
    ultimately show ?thesis using p(4) by simp
  qed
  obtain cs where cs: "map fst cs=map fst ms'" "set cs=set cs0" "distinct cs"
    using stated_keyed_enumeration[OF msv p(3) mdom] by blast
  have fact: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_at_schema[OF source raw] xs(2) qs(2,3) cs(2,3) at0 by simp
  have argf: "term_formed (schema_instantiation_argument e (use_data_term u) (Payload_Term a) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))"
    using schema_call_formed_target[OF positive_meaning_formed[OF fact]] by blast
  have table: "(582,binding_rows_term xs)\<in>positive_meaning stated_values_system"
    by (subst stated_values_rows) (use binding_rows_formed[of xs] argf blank in auto)
  have tf: "term_formed t" using argf by simp
  have stated_t: "term_stated t=pattern_stated (schema_conclusion S)" by (rule pattern_instance_stated[OF conc blank])
  have head: "(580,Pair_Term t (Pair_Term (Payload_Term []) (data_list_term (pattern_stated (schema_conclusion S)))))
      \<in>positive_meaning stated_leaves_system"
    using tf stated_t by (simp add: stated_leaves_list)
  have qagree: "(\<lambda>(s,d,x). Pair_Term (Payload_Term s) (data_list_term (term_stated x))) q=place_term k"
    if q: "q\<in>set qs" "k\<in>set qs'" "fst q=fst k" for q k
  proof -
    obtain s d x where qe: "q=(s,d,x)" by (cases q) auto
    obtain p0 where p0: "(s,d,p0)\<in>schema_premises S" "pattern_instance (set xs) p0 x"
      using schema_premise_instance_origin[OF body] q(1) qe qs(2) by blast
    obtain s' d' p1 where k: "k=(s',pattern_stated p1)" "(s',d',p1)\<in>schema_premises S"
      using q(2) p(2) by (auto simp: clause_calls_def)
    have "s'=s" using q(3) qe k by simp
    have sv: "single_valued (schema_premises S)" using sf by (simp add: schema_formed_def)
    have "(d',p1)=(d,p0)" using single_valued_outputs[OF sv k(2)[unfolded \<open>s'=s\<close>] p0(1)] .
    then show ?thesis using qe k \<open>s'=s\<close> pattern_instance_stated[OF p0(2) blank] by (simp add: place_term_def)
  qed
  have qrows: "map (\<lambda>(s,d,x). Pair_Term (Payload_Term s) (data_list_term (term_stated x))) qs=map place_term qs'"
    by (rule stated_keyed_map[OF qs(1)]) (use qagree in blast)
  have callrows: "(584,context_relation_argument (Payload_Term []) (call_instance_rows_term qs)
      (data_list_term (map place_term qs')))\<in>positive_meaning stated_calls_system"
    using stated_calls_rows[of qs] argf qrows by simp
  have tuples: "\<forall>(s,x)\<in>set cs. \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
  proof (intro ballI)
    fix z assume z: "z\<in>set cs"
    obtain q y where zq: "z=(q,y)" by (cases z)
    have "(q,y)\<in>material_instance_relation (set xs) (schema_material_premises S)" using z zq cs(2) at0(4) by simp
    then show "case z of (s,x) \<Rightarrow> \<exists>a1 a2 a3 a4 a5. x=material_tuple a1 a2 a3 a4 a5"
      using zq unfolding material_instance_relation_def by blast
  qed
  have magree: "(\<lambda>(s,x). material_place_term (s,tuple_stated x)) q=material_place_term k"
    if q: "q\<in>set cs" "k\<in>set ms'" "fst q=fst k" for q k
  proof -
    obtain s x where qe: "q=(s,x)" by (cases q) auto
    obtain M a1 a2 a3 a4 a5 where m: "(s,M)\<in>schema_material_premises S" "x=material_tuple a1 a2 a3 a4 a5"
      "material_pattern_instance (set xs) M a1 a2 a3 a4 a5"
      using q(1) qe cs(2) at0(4) by (auto simp: material_instance_relation_def)
    obtain s' M' where k: "k=(s',material_stated M')" "(s',M')\<in>schema_material_premises S"
      using q(2) p(4) by (auto simp: clause_materials_def)
    have "s'=s" using q(3) qe k by simp
    have sv: "single_valued (schema_material_premises S)" using sf by (simp add: schema_formed_def)
    have "M'=M" using single_valued_outputs[OF sv k(2)[unfolded \<open>s'=s\<close>] m(1)] .
    then show ?thesis using qe k m \<open>s'=s\<close> material_instance_stated[OF m(3) blank] by simp
  qed
  have mrows: "map (\<lambda>(s,x). material_place_term (s,tuple_stated x)) cs=map material_place_term ms'"
    by (rule stated_keyed_map[OF cs(1)]) (use magree in blast)
  have matrows: "(586,context_relation_argument (Payload_Term []) (binding_rows_term cs)
      (data_list_term (map material_place_term ms')))\<in>positive_meaning stated_materials_system"
    using stated_materials_rows[of cs] argf tuples mrows by simp
  have lf: "term_formed (data_list_term (pattern_stated (schema_conclusion S)))"
    using term_stated_formed[OF tf] stated_t by (simp add: stated_list_formed)
  have qrf: "term_formed (data_list_term (map place_term qs'))"
    using schema_call_formed_target[OF positive_meaning_formed[OF callrows]] by simp
  have mrf: "term_formed (data_list_term (map material_place_term ms'))"
    using schema_call_formed_target[OF positive_meaning_formed[OF matrows]] by simp
  have ef: "term_formed e" "term_formed (use_data_term u)" "octets_formed a" using argf by simp_all
  show ?thesis
  proof (cases "clause_ground S=[]")
    case False
    then have empty: "schema_variables S={}" "schema_premises S={}" "schema_material_premises S={}"
      using clause_ground_ground[of S] by auto
    obtain g where g: "pattern_ground (schema_conclusion S)=Some g"
      using empty(1) pattern_ground_none[of "schema_conclusion S"]
      by (cases "pattern_ground (schema_conclusion S)") (auto simp: schema_variables_def)
    have tg: "t=g" using pattern_ground_instance[OF conc g] .
    have groundf: "clause_ground S=[t]" using g empty tg by (simp add: clause_ground_def)
    have xnil: "xs=[]" using xs(1) empty(1) by simp
    have qnil: "qs=[]" using qs(2) body empty(2) by (auto simp: schema_premise_instance_def)
    have cnil: "cs=[]" using cs(2) at0(4) empty(3) by (auto simp: material_instance_relation_def)
    have qnil': "qs'=[]" using p(2) empty(2) by (simp add: clause_calls_def)
    have mnil': "ms'=[]" using p(4) empty(3) by (simp add: clause_materials_def)
    let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then use_data_term u else if n=2 then Payload_Term a
      else if n=4 then t else data_list_term (pattern_stated (schema_conclusion S))"
    have "(587,evaluate_pattern ?h (schema_conclusion stated_clause_ground_schema))\<in>positive_meaning stated_clause_system"
      by (rule ordinary_positive_formed_step[where c=0])
        (use fact head tf lf ef xnil qnil cnil in \<open>auto simp: stated_clause_clauses_def stated_clause_ground_schema_def
          schema_formed_def schema_variables_def single_valued_def rel_dom_def octets_formed_def
          stated_clause_call stated_clause_components\<close>)
    then show ?thesis using p(5) groundf qnil' mnil' by (simp add: stated_clause_ground_schema_def)
  next
    case True
    have open_rows: "xs\<noteq>[] \<or> qs\<noteq>[] \<or> cs\<noteq>[]"
    proof (rule ccontr)
      assume "\<not>(xs\<noteq>[] \<or> qs\<noteq>[] \<or> cs\<noteq>[])"
      then have nil: "xs=[]" "qs=[]" "cs=[]" by auto
      have "schema_variables S={}" using nil(1) bindings by (simp add: term_bindings_formed_def)
      moreover have "schema_premises S={}" using nil(2) qs(2) body by (auto simp: schema_premise_instance_def)
      moreover have "schema_material_premises S={}"
        using nil(3) cs(2) mdom p(4) by (auto simp: clause_materials_def)
      ultimately show False using True clause_ground_ground[of S] by simp
    qed
    have rf: "term_formed (binding_rows_term xs)" "term_formed (call_instance_rows_term qs)"
      "term_formed (binding_rows_term cs)" using argf by simp_all
    let ?base="\<lambda>n::nat. if n=0 then e else if n=1 then use_data_term u else if n=2 then Payload_Term a
      else if n=3 then binding_rows_term xs else if n=4 then t else if n=5 then call_instance_rows_term qs
      else if n=6 then binding_rows_term cs else if n=7 then data_list_term (pattern_stated (schema_conclusion S))
      else if n=8 then data_list_term (map place_term qs') else data_list_term (map material_place_term ms')"
    have target: "Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r=
      Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) (Pair_Term (Payload_Term [])
        (Pair_Term (data_list_term (pattern_stated (schema_conclusion S)))
          (Pair_Term (data_list_term (map place_term qs')) (data_list_term (map material_place_term ms')))))"
      using p(5) True by simp
    consider (vars) b y xs' where "xs=(b,y)#xs'" | (calls) s d x qs'' where "xs=[]" "qs=(s,d,x)#qs''"
      | (mats) s x cs' where "xs=[]" "qs=[]" "cs=(s,x)#cs'"
    proof (cases xs)
      case (Cons xy xs')
      then show ?thesis using that(1) by (cases xy) blast
    next
      case Nil
      show ?thesis
      proof (cases qs)
        case (Cons q qs'')
        then show ?thesis using that(2) Nil by (cases q rule: prod_cases3) blast
      next
        case Nil2: Nil
        show ?thesis
        proof (cases cs)
          case (Cons z cs')
          then show ?thesis using that(3) Nil Nil2 by (cases z) blast
        next
          case Nil3: Nil
          then show ?thesis using open_rows Nil Nil2 by simp
        qed
      qed
    qed
    then show ?thesis
    proof cases
      case vars
      let ?h="\<lambda>n::nat. if n=10 then Pair_Term (Payload_Term b) y else if n=11 then binding_rows_term xs' else ?base n"
      have "(587,evaluate_pattern ?h (schema_conclusion (stated_clause_open_schema stated_open (Pattern_Variable 5)
          (Pattern_Variable 6))))\<in>positive_meaning stated_clause_system"
        by (rule ordinary_positive_formed_step[where c=1])
          (use fact table head callrows matrows tf lf qrf mrf ef rf vars in \<open>auto simp: stated_clause_clauses_def
            stated_clause_open_schema_def schema_formed_def schema_variables_def single_valued_def rel_dom_def
            octets_formed_def stated_clause_call stated_clause_components\<close>)
      then show ?thesis using target by (simp add: stated_clause_open_schema_def)
    next
      case calls
      let ?h="\<lambda>n::nat. if n=10 then Pair_Term (Payload_Term s) (call_instance_value d x)
        else if n=11 then call_instance_rows_term qs'' else ?base n"
      have "(587,evaluate_pattern ?h (schema_conclusion (stated_clause_open_schema data_w stated_open
          (Pattern_Variable 6))))\<in>positive_meaning stated_clause_system"
        by (rule ordinary_positive_formed_step[where c=2])
          (use fact table head callrows matrows tf lf qrf mrf ef rf calls in \<open>auto simp: stated_clause_clauses_def
            stated_clause_open_schema_def schema_formed_def schema_variables_def single_valued_def rel_dom_def
            octets_formed_def stated_clause_call stated_clause_components\<close>)
      then show ?thesis using target by (simp add: stated_clause_open_schema_def)
    next
      case mats
      let ?h="\<lambda>n::nat. if n=10 then Pair_Term (Payload_Term s) x else if n=11 then binding_rows_term cs' else ?base n"
      have "(587,evaluate_pattern ?h (schema_conclusion (stated_clause_open_schema data_w (Pattern_Variable 5)
          stated_open)))\<in>positive_meaning stated_clause_system"
        by (rule ordinary_positive_formed_step[where c=3])
          (use fact table head callrows matrows tf lf qrf mrf ef rf mats in \<open>auto simp: stated_clause_clauses_def
            stated_clause_open_schema_def schema_formed_def schema_variables_def single_valued_def rel_dom_def
            octets_formed_def stated_clause_call stated_clause_components\<close>)
      then show ?thesis using target by (simp add: stated_clause_open_schema_def)
    qed
  qed
qed

theorem stated_clause_exact:
  "(587,z)\<in>positive_meaning stated_clause_system \<longleftrightarrow> stated_clause_result z"
  using stated_clause_sound stated_clause_complete by blast

corollary stated_clause_on_values:
  assumes source: "environment_value_presents E e"
  shows "(587,Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)\<in>positive_meaning stated_clause_system
    \<longleftrightarrow> (\<exists>S. native_schema_at E u a S \<and> clause_stated_presents S r)"
proof
  assume "(587,Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)\<in>positive_meaning stated_clause_system"
  then have "stated_clause_result (Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)"
    by (rule stated_clause_sound)
  then obtain F e' u' a' S r' where parts: "Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r=
      Pair_Term (Pair_Term (Pair_Term e' (use_data_term u')) (Payload_Term a')) r'"
    "environment_value_presents F e'" "native_schema_at F u' a' S" "clause_stated_presents S r'"
    by (elim exE conjE) (rule that; assumption)
  have same: "e'=e" "u'=u" "a'=a" "r'=r" using parts(1) injD[OF use_data_term_injective] by auto
  have "F=E" using parts(2) source same(1) environment_value_presents_unique by blast
  then show "\<exists>S. native_schema_at E u a S \<and> clause_stated_presents S r" using parts(3,4) same by auto
next
  assume "\<exists>S. native_schema_at E u a S \<and> clause_stated_presents S r"
  then show "(587,Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)\<in>positive_meaning stated_clause_system"
    using stated_clause_complete[OF source] by blast
qed

section \<open>Every clause of the family, keyed by its socket (588, 589)\<close>

definition stated_row_schema :: "(nat,nat,nat) factor_schema" where
  "stated_row_schema=data_rule
    (context_relation_pattern data_x (Pattern_Pair data_y data_z) (Pattern_Pair data_y data_w))
    {(0,587,Pattern_Pair (Pattern_Pair data_x data_z) data_w)}"

definition stated_row_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_row_system=add_view_definition stated_clause_system 588 data_x {(0,stated_row_schema)}"

lemma stated_row_system_formed [simp]: "schema_system_formed stated_row_system"
  unfolding stated_row_system_def
  by (rule add_recursive_definition_formed[OF stated_clause_system_formed])
    (auto simp: stated_row_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma stated_row_definitions [simp]:
  "system_definitions stated_row_system=insert 588 (system_definitions stated_clause_system)"
  by (simp add: stated_row_system_def)

lemma stated_row_call:
  "schema_call_formed stated_row_system d t \<longleftrightarrow> d\<in>system_definitions stated_row_system \<and> term_formed t"
  using added_variable_calls[OF stated_clause_system_formed
    stated_row_system_formed[unfolded stated_row_system_def] stated_clause_call]
  by (simp only: stated_row_system_def[symmetric])

lemma stated_row_old_meaning:
  assumes "d\<in>system_definitions stated_clause_system"
  shows "(d,t)\<in>positive_meaning stated_row_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_clause_system"
  using added_definition_preserves_old(2)[OF stated_clause_system_formed
    stated_row_system_formed[unfolded stated_row_system_def] _ assms]
  by (simp add: stated_row_system_def)

lemma stated_row_clause [simp]:
  "((588,c),S)\<in>system_clauses stated_row_system \<longleftrightarrow> c=0 \<and> S=stated_row_schema"
  unfolding stated_row_system_def by (subst audit_layer_clause) simp_all

theorem stated_row_exact:
  "(588,z)\<in>positive_meaning stated_row_system \<longleftrightarrow> (\<exists>c k x w. z=context_relation_argument c (Pair_Term k x) (Pair_Term k w) \<and>
    term_formed c \<and> term_formed k \<and> (587,Pair_Term (Pair_Term c x) w)\<in>positive_meaning stated_clause_system)"
proof
  assume holds: "(588,z)\<in>positive_meaning stated_row_system"
  obtain c S h where clause: "((588,c),S)\<in>system_clauses stated_row_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern h p)\<in>positive_meaning stated_row_system"
    by (rule positive_meaning_valuationE[OF holds])
  have schema: "S=stated_row_schema" using clause by simp
  have "(587,Pair_Term (Pair_Term (h 0) (h 2)) (h 3))\<in>positive_meaning stated_clause_system"
    using support by (simp add: schema stated_row_schema_def stated_row_old_meaning)
  then show "\<exists>c k x w. z=context_relation_argument c (Pair_Term k x) (Pair_Term k w) \<and>
      term_formed c \<and> term_formed k \<and> (587,Pair_Term (Pair_Term c x) w)\<in>positive_meaning stated_clause_system"
    using conclusion assignment by (auto simp: schema stated_row_schema_def schema_variables_def)
next
  assume "\<exists>c k x w. z=context_relation_argument c (Pair_Term k x) (Pair_Term k w) \<and>
    term_formed c \<and> term_formed k \<and> (587,Pair_Term (Pair_Term c x) w)\<in>positive_meaning stated_clause_system"
  then obtain c k x w where z: "z=context_relation_argument c (Pair_Term k x) (Pair_Term k w)"
    "term_formed c" "term_formed k" "(587,Pair_Term (Pair_Term c x) w)\<in>positive_meaning stated_clause_system" by blast
  have fw: "term_formed x" "term_formed w" using schema_call_formed_target[OF positive_meaning_formed[OF z(4)]] by simp_all
  have support: "(587,Pair_Term (Pair_Term c x) w)\<in>positive_meaning stated_row_system"
    using z(4) by (simp add: stated_row_old_meaning)
  let ?h="\<lambda>n::nat. if n=0 then c else if n=1 then k else if n=2 then x else w"
  have "(588,evaluate_pattern ?h (schema_conclusion stated_row_schema))\<in>positive_meaning stated_row_system"
    by (rule ordinary_positive_formed_step[where c=0])
      (use z fw support in \<open>auto simp: stated_row_schema_def schema_formed_def schema_variables_def
        single_valued_def rel_dom_def stated_row_call\<close>)
  then show "(588,z)\<in>positive_meaning stated_row_system" by (simp add: stated_row_schema_def z(1))
qed

definition stated_rows_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_rows_system=add_view_definition stated_row_system 589 data_x (related_list_clauses 588 589)"

lemma stated_rows_system_formed [simp]: "schema_system_formed stated_rows_system"
  unfolding stated_rows_system_def
  by (rule add_recursive_definition_formed[OF stated_row_system_formed])
    (auto simp: related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stated_rows_definitions [simp]:
  "system_definitions stated_rows_system=insert 589 (system_definitions stated_row_system)"
  by (simp add: stated_rows_system_def)

lemma stated_rows_call:
  "schema_call_formed stated_rows_system d t \<longleftrightarrow> d\<in>system_definitions stated_rows_system \<and> term_formed t"
  using added_variable_calls[OF stated_row_system_formed
    stated_rows_system_formed[unfolded stated_rows_system_def] stated_row_call]
  by (simp only: stated_rows_system_def[symmetric])

lemma stated_rows_old_meaning:
  assumes "d\<in>system_definitions stated_row_system"
  shows "(d,t)\<in>positive_meaning stated_rows_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_row_system"
  using added_definition_preserves_old(2)[OF stated_row_system_formed
    stated_rows_system_formed[unfolded stated_rows_system_def] _ assms]
  by (simp add: stated_rows_system_def)

lemma stated_rows_clause [simp]:
  "((589,c),S)\<in>system_clauses stated_rows_system \<longleftrightarrow> (c,S)\<in>related_list_clauses 588 589"
  unfolding stated_rows_system_def by (rule audit_layer_clause) simp_all

interpretation stated_rows_profile: related_list_profile stated_rows_system 588 589
  by (rule related_list_profile.intro) (auto simp: stated_rows_call)

lemma stated_rows_on_values:
  assumes source: "environment_value_presents E e" and cf: "term_formed (Pair_Term e (use_data_term u))"
    and rf: "term_formed (data_list_term (map address_pair_data xs))"
  shows "(589,context_relation_argument (Pair_Term e (use_data_term u)) (data_list_term (map address_pair_data xs))
      (data_list_term ys))\<in>positive_meaning stated_rows_system \<longleftrightarrow>
    list_all2 (\<lambda>z y. \<exists>r. y=Pair_Term (Payload_Term (fst z)) r \<and>
      (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S r)) xs ys"
proof -
  have zf: "octets_formed (fst z)" if "z\<in>set xs" for z
    using rf that by (auto simp: stated_list_formed address_pair_data_def)
  have element: "(588,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data z) y)
      \<in>positive_meaning stated_rows_system \<longleftrightarrow>
    (\<exists>r. y=Pair_Term (Payload_Term (fst z)) r \<and> (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S r))"
    if z: "z\<in>set xs" for z y
  proof -
    obtain s a where zs: "z=(s,a)" by (cases z)
    have sf: "octets_formed s" using zf[OF z] zs by simp
    have "(588,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data z) y)\<in>positive_meaning stated_rows_system
        \<longleftrightarrow> (588,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data z) y)\<in>positive_meaning stated_row_system"
      by (rule stated_rows_old_meaning) simp
    also have "\<dots> \<longleftrightarrow> (\<exists>r. y=Pair_Term (Payload_Term s) r \<and>
        (587,Pair_Term (Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term a)) r)\<in>positive_meaning stated_clause_system)"
      by (simp only: stated_row_exact zs address_pair_data_def fst_conv snd_conv) (use cf sf in auto)
    also have "\<dots> \<longleftrightarrow> (\<exists>r. y=Pair_Term (Payload_Term (fst z)) r \<and> (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S r))"
      using stated_clause_on_values[OF source] zs by simp
    finally show ?thesis .
  qed
  have "(589,context_relation_argument (Pair_Term e (use_data_term u)) (data_list_term (map address_pair_data xs))
      (data_list_term ys))\<in>positive_meaning stated_rows_system \<longleftrightarrow>
    list_all2 (\<lambda>x y. (588,context_relation_argument (Pair_Term e (use_data_term u)) x y)\<in>positive_meaning stated_rows_system)
      (map address_pair_data xs) ys"
    using stated_rows_profile.lists[of "Pair_Term e (use_data_term u)" "map address_pair_data xs" ys] cf by simp
  also have "\<dots> \<longleftrightarrow> list_all2 (\<lambda>z y. (588,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data z) y)
      \<in>positive_meaning stated_rows_system) xs ys"
    by (simp add: list_all2_map1)
  also have "\<dots> \<longleftrightarrow> list_all2 (\<lambda>z y. \<exists>r. y=Pair_Term (Payload_Term (fst z)) r \<and>
      (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S r)) xs ys"
    by (rule stated_list_all2_cong) (use element in blast)
  finally show ?thesis .
qed

section \<open>The reader's entry (590)\<close>

text \<open>
  The entry reads the definition at a site of an environment presented as data, as the audit does: 72
  admits it at the interface's instance, 37 and 34 read its artifact and record, 32 its clause family's
  rows. 56 instantiates the actual interface at a hidden table whose values state nothing (582), and 589
  reports every clause through 587. Its report is the leaves the interface states beside the clause rows.
\<close>

definition stated_report_schema :: "(nat,nat,nat) factor_schema" where
  "stated_report_schema=data_rule
    (Pattern_Pair (source_root_pattern data_x data_y data_z) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14)))
    {(0,72,citation_observation_pattern data_x data_y data_z data_w),
     (1,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (2,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6),
         Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)])),
     (3,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8)) (Pattern_Variable 9)),
     (4,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 6) (Pattern_Variable 10) data_w
       (Pattern_Variable 11) (Pattern_Variable 12)),
     (5,582,Pattern_Variable 10),
     (6,580,Pattern_Pair data_w (Pattern_Pair (Pattern_Payload []) (Pattern_Variable 13))),
     (7,589,context_relation_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 9) (Pattern_Variable 14))}"

definition stated_report_system :: "(nat,nat,nat,nat) schema_system" where
  "stated_report_system=add_view_definition stated_rows_system 590 data_x {(0,stated_report_schema)}"

lemma stated_report_schema_formed: "schema_formed stated_report_schema"
  by (auto simp: stated_report_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

lemma stated_report_system_formed [simp]: "schema_system_formed stated_report_system"
  unfolding stated_report_system_def
  by (rule add_recursive_definition_formed[OF stated_rows_system_formed])
    (auto simp: stated_report_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma stated_report_definitions [simp]:
  "system_definitions stated_report_system=insert 590 (system_definitions stated_rows_system)"
  by (simp add: stated_report_system_def)

lemma stated_report_call:
  "schema_call_formed stated_report_system d t \<longleftrightarrow> d\<in>system_definitions stated_report_system \<and> term_formed t"
  using added_variable_calls[OF stated_rows_system_formed
    stated_report_system_formed[unfolded stated_report_system_def] stated_rows_call]
  by (simp only: stated_report_system_def[symmetric])

lemma stated_report_old_meaning:
  assumes "d\<in>system_definitions stated_rows_system"
  shows "(d,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (d,t)\<in>positive_meaning stated_rows_system"
  using added_definition_preserves_old(2)[OF stated_rows_system_formed
    stated_report_system_formed[unfolded stated_report_system_def] _ assms]
  by (simp add: stated_report_system_def)

lemma stated_report_clause [simp]:
  "((590,c),S)\<in>system_clauses stated_report_system \<longleftrightarrow> c=0 \<and> S=stated_report_schema"
  unfolding stated_report_system_def by (subst audit_layer_clause) simp_all

lemmas stated_upper_meanings=stated_report_old_meaning stated_rows_old_meaning stated_row_old_meaning
  stated_lower_meanings

lemma stated_report_components:
  "(72,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (72,t)\<in>positive_meaning definition_call_admission_system"
  "(37,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(56,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (56,t)\<in>positive_meaning scoped_instantiation_system"
  "(582,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (582,t)\<in>positive_meaning stated_values_system"
  "(580,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (580,t)\<in>positive_meaning stated_leaves_system"
  "(589,t)\<in>positive_meaning stated_report_system \<longleftrightarrow> (589,t)\<in>positive_meaning stated_rows_system"
  using stated_leaves_old_meaning[of 72 t] stated_leaves_old_meaning[of 37 t] stated_leaves_old_meaning[of 34 t]
    stated_leaves_old_meaning[of 32 t] stated_leaves_old_meaning[of 56 t]
    payload_audit_components(1-5)[of t] payload_audit_admission_meaning[of 56 t]
    definition_call_admission_scoped_meaning[of t]
  by (simp_all add: stated_upper_meanings)

abbreviation stated_report_result :: "factor_term \<Rightarrow> bool" where
  "stated_report_result z \<equiv> \<exists>E e u r p C y. z=Pair_Term (source_root_argument e (use_data_term u) (Payload_Term r)) y \<and>
    environment_value_presents E e \<and> native_definition_at E u r p C \<and> definition_stated_presents p C y"

theorem stated_report_sound:
  assumes holds: "(590,z)\<in>positive_meaning stated_report_system"
  shows "stated_report_result z"
proof -
  obtain c S h where clause: "((590,c),S)\<in>system_clauses stated_report_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning stated_report_system"
    using positive_meaning_valuationE[OF holds] by blast
  have schema: "S=stated_report_schema" using clause by simp
  have calls: "(72,citation_observation_argument (h 0) (h 1) (h 2) (h 3))\<in>positive_meaning definition_call_admission_system"
    "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 4) (h 2) (data_list_term [Pair_Term (h 5) (h 6),Pair_Term (h 7) (h 8)]))
      \<in>positive_meaning record_admission_system"
    "(32,rooted_rows_argument (h 4) (h 8) (h 9))\<in>positive_meaning family_admission_system"
    "(56,scoped_instantiation_argument (h 0) (h 1) (h 6) (h 10) (h 3) (h 11) (h 12))\<in>positive_meaning scoped_instantiation_system"
    "(582,h 10)\<in>positive_meaning stated_values_system"
    "(580,Pair_Term (h 3) (Pair_Term (Payload_Term []) (h 13)))\<in>positive_meaning stated_leaves_system"
    "(589,context_relation_argument (Pair_Term (h 0) (h 1)) (h 9) (h 14))\<in>positive_meaning stated_rows_system"
    using support by (auto simp: schema stated_report_schema_def stated_report_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 4)"
    using calls(2) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r a i b m where rec: "h 2=Payload_Term r" "h 5=Payload_Term a" "h 6=Payload_Term i"
    "h 7=Payload_Term b" "h 8=Payload_Term m" "record_at R r [a,b] [i,m]"
    using calls(3) by (simp only: record_admission_pair_fields[OF source(4)]) blast
  obtain xs where fam: "h 9=data_list_term (map address_pair_data xs)" "distinct xs" "family_at R m (set xs)"
    using calls(4) by (simp only: rec(5) family_admission_at_source[OF source(4)] factor_term.inject) blast
  obtain F v l p C where defined: "environment_value_presents F (h 0)" "h 1=use_data_term v" "h 2=Payload_Term l"
    "native_definition_at F v l p C" "pattern_accepts p (h 3)"
    using calls(1) by (simp only: definition_call_admission_exact factor_term.inject) blast
  have same: "F=E" "v=u" "l=r"
    using environment_value_presents_unique[OF defined(1) source(1)] defined(2,3) source(2) rec(1)
      injD[OF use_data_term_injective] by auto
  have raw: "native_definition_at E u r p C" using defined(4) same by simp
  have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  obtain R' ps i' m' I K where parts: "artifact_at E u R'" "record_at R' r ps [i',m']"
    "scoped_pattern_at E u i' p I K" "native_schema_family_at E u m' C"
    using raw by (auto simp: native_definition_at_def)
  have "R'=R" by (rule environment_artifact_unique[OF ef parts(1) source(3)])
  then have "record_at R r ps [i',m']" using parts(2) by simp
  then have ends: "i'=i" "m'=m" using record_at_unique[OF _ rec(6)] by fastforce+
  obtain R'' M where family: "artifact_at E u R''" "family_at R'' m M" "single_valued C"
    "rel_dom C=rel_dom M" "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using parts(4) ends(2) by (auto simp: native_schema_family_at_def)
  have "R''=R" by (rule environment_artifact_unique[OF ef family(1) source(3)])
  then have "family_at R m M" using family(2) by simp
  then have rows: "M=set xs" by (rule family_at_unique[OF _ fam(3)])
  have msv: "single_valued (set xs)" using fam(3) by (simp add: family_at_def)
  obtain v' a' ys p' Is Ks where inst: "h 1=use_data_term v'" "h 6=Payload_Term a'" "h 10=binding_rows_term ys"
    "scoped_pattern_at E v' a' p' (set Is) (set Ks)" "pattern_instance (set ys) p' (h 3)"
    using calls(5) by (simp only: scoped_instantiation_at_source[OF source(1)]) blast
  have v'u: "v'=u" "a'=i" using inst(1,2) source(2) rec(3) injD[OF use_data_term_injective] by auto
  have "p'=p" using scoped_pattern_unique[OF inst(4)[unfolded v'u] parts(3)[unfolded ends(1)]] by blast
  then have instp: "pattern_instance (set ys) p (h 3)" using inst(5) by simp
  have blank: "\<forall>b x. (b,x)\<in>set ys \<longrightarrow> term_stated x=[]" using calls(6) inst(3) stated_values_rows by fastforce
  have interface: "h 13=data_list_term (pattern_stated p)"
    using calls(7) pattern_instance_stated[OF instp blank] by (simp add: stated_leaves_list)
  have argf: "term_formed (context_relation_argument (Pair_Term (h 0) (h 1)) (h 9) (h 14))"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(8)]] by blast
  have "\<exists>a xs ys. context_relation_argument (Pair_Term (h 0) (h 1)) (h 9) (h 14)=
      context_relation_argument a (data_list_term xs) (data_list_term ys) \<and> term_formed a \<and>
      list_all2 (\<lambda>x y. (588,context_relation_argument a x y)\<in>positive_meaning stated_rows_system) xs ys"
    using calls(8) by (simp only: stated_rows_profile.exact)
  then obtain ys' where ys': "h 14=data_list_term ys'" by auto
  have listed: "list_all2 (\<lambda>z y. \<exists>rr. y=Pair_Term (Payload_Term (fst z)) rr \<and>
      (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S rr)) xs ys'"
    using calls(8) stated_rows_on_values[OF source(1), of u xs ys'] argf fam(1) ys' source(2) by simp
  obtain rs where rs: "ys'=map2 (\<lambda>z rr. Pair_Term (Payload_Term (fst z)) rr) xs rs"
    "list_all2 (\<lambda>z rr. \<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S rr) xs rs"
    using stated_list_all2_witnesses[OF listed] by blast
  have len: "length rs=length xs" using list_all2_lengthD[OF rs(2)] by simp
  let ?ks="zip (map fst xs) rs"
  have kfst: "map fst ?ks=map fst xs" using len by simp
  have kdistinct: "distinct (map fst ?ks)" using kfst fam(2) msv distinct_keys_iff[of xs] by simp
  have kdom: "fst ` set ?ks=rel_dom C"
  proof -
    have "fst ` set ?ks=set (map fst ?ks)" by (simp only: list.set_map)
    also have "\<dots>=set (map fst xs)" by (simp only: kfst)
    also have "\<dots>=rel_dom (set xs)" by (simp only: list.set_map rel_dom_image)
    finally show ?thesis using family(4) rows by simp
  qed
  have kclauses: "\<exists>S. (c,S)\<in>C \<and> clause_stated_presents S w" if k: "(c,w)\<in>set ?ks" for c w
  proof -
    obtain n where n: "n<length xs" "fst (xs!n)=c" "rs!n=w" using k len by (auto simp: in_set_zip)
    obtain S where S: "native_schema_at E u (snd (xs!n)) S" "clause_stated_presents S w"
      using list_all2_nthD[OF rs(2) n(1)] n(3) by blast
    have "xs!n\<in>set xs" using n(1) by (rule nth_mem)
    then have "(fst (xs!n),snd (xs!n))\<in>M" using rows by simp
    then obtain S' where S': "(c,S')\<in>C" "native_schema_at E u (snd (xs!n)) S'" using family(5) n(2) by blast
    have "S'=S" by (rule native_schema_unique[OF S'(2) S(1)])
    then show ?thesis using S'(1) S(2) by blast
  qed
  have report: "h 14=data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ?ks)"
    using ys' rs(1) by (simp add: zip_map1 split_def comp_def)
  have "definition_stated_presents p C (Pair_Term (h 13) (h 14))"
    unfolding definition_stated_presents_def using kdistinct kdom kclauses interface report by blast
  moreover have "z=Pair_Term (source_root_argument (h 0) (use_data_term u) (Payload_Term r)) (Pair_Term (h 13) (h 14))"
    using conclusion source(2) rec(1) by (simp add: schema stated_report_schema_def)
  ultimately show ?thesis using source(1) raw by blast
qed

theorem stated_report_complete:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
    and presents: "definition_stated_presents p C z"
  shows "(590,Pair_Term (source_root_argument e (use_data_term u) (Payload_Term r)) z)\<in>positive_meaning stated_report_system"
proof -
  obtain ks where ks: "distinct (map fst ks)" "fst ` set ks=rel_dom C"
    "\<forall>c v. (c,v)\<in>set ks \<longrightarrow> (\<exists>S. (c,S)\<in>C \<and> clause_stated_presents S v)"
    "z=Pair_Term (data_list_term (pattern_stated p)) (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks))"
    using presents by (auto simp: definition_stated_presents_def)
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    using raw by (auto simp: native_definition_at_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain material where presented: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  obtain a b where ports: "ps=[a,b]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  have scoped: "pattern_formed p" "finite I" "finite K" using scoped_pattern_formed[OF parts(3)] by blast+
  let ?W="(\<lambda>b. (b,Payload_Term [0])) ` pattern_variables p"
  have wf: "finite ?W" by simp
  obtain ys where ys: "set ys=?W" "distinct ys" using finite_distinct_list[OF wf] by blast
  have wb: "term_bindings_formed (pattern_variables p) (set ys)"
    by (auto simp: ys(1) term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  have blank: "\<forall>b x. (b,x)\<in>set ys \<longrightarrow> term_stated x=[]" using ys(1) by auto
  obtain Is where Is: "set Is=I" "distinct Is" using finite_distinct_list[OF scoped(2)] by blast
  obtain Ks where Ks: "set Ks=K" "distinct Ks" using finite_distinct_list[OF scoped(3)] by blast
  obtain w where scopedfact: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i) (binding_rows_term ys) w
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    using scoped_instantiation_total[OF parts(3) source wb ys(2) Is(2) Ks(2) Is(1) Ks(1)] by blast
  obtain p' where p': "scoped_pattern_at E u i p' (set Is) (set Ks)" "pattern_instance (set ys) p' w"
    using scopedfact by (simp only: scoped_instantiation_on_values[OF source]) blast
  have "p'=p" using scoped_pattern_unique[OF p'(1) parts(3)] by blast
  then have instw: "pattern_instance (set ys) p w" using p'(2) by simp
  have sargf: "term_formed (scoped_instantiation_argument e (use_data_term u) (Payload_Term i) (binding_rows_term ys) w
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))"
    using schema_call_formed_target[OF positive_meaning_formed[OF scopedfact]] by blast
  have wformed: "term_formed w" using sargf by simp
  have accepts: "pattern_accepts p w" using wb instw wformed by (auto simp: pattern_accepts_def)
  have admitted: "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) w)
      \<in>positive_meaning definition_call_admission_system"
    by (rule definition_call_admission_complete[OF source raw accepts])
  have table: "(582,binding_rows_term ys)\<in>positive_meaning stated_values_system"
    by (subst stated_values_rows) (use binding_rows_formed[of ys] sargf blank in auto)
  have stated_w: "term_stated w=pattern_stated p" by (rule pattern_instance_stated[OF instw blank])
  have head: "(580,Pair_Term w (Pair_Term (Payload_Term []) (data_list_term (pattern_stated p))))
      \<in>positive_meaning stated_leaves_system"
    using wformed stated_w by (simp add: stated_leaves_list)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term a) (Payload_Term i),Pair_Term (Payload_Term b) (Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF presented]) (use parts(2) in \<open>auto simp: ports\<close>)
  obtain R'' M where family: "artifact_at E u R''" "family_at R'' m M" "single_valued C" "rel_dom C=rel_dom M"
    "\<forall>s a. (s,a)\<in>M \<longrightarrow> (\<exists>S. (s,S)\<in>C \<and> native_schema_at E u a S)"
    using parts(4) by (auto simp: native_schema_family_at_def)
  have "R''=R" by (rule environment_artifact_unique[OF ef family(1) parts(1)])
  then have fr: "family_at R m M" using family(2) by simp
  have msv: "single_valued M" using fr by (simp add: family_at_def)
  have kdom: "fst ` set ks=rel_dom M" using ks(2) family(4) by simp
  obtain xs where xs: "map fst xs=map fst ks" "set xs=M" "distinct xs"
    using stated_keyed_enumeration[OF msv ks(1) kdom] by blast
  let ?rows="data_list_term (map address_pair_data xs)"
  have rows: "(32,rooted_rows_argument material (Payload_Term m) ?rows)\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_rows[OF presented]) (use fr xs in auto)
  have formed: "term_formed ?rows" "term_formed e" "term_formed material" "term_formed (use_data_term u)"
    using schema_call_formed_target[OF positive_meaning_formed[OF rows]]
      schema_call_formed_target[OF positive_meaning_formed[OF lookup]] by auto
  have len: "length xs=length ks" using arg_cong[OF xs(1), of length] by simp
  have listed: "list_all2 (\<lambda>z y. \<exists>rr. y=Pair_Term (Payload_Term (fst z)) rr \<and>
      (\<exists>S. native_schema_at E u (snd z) S \<and> clause_stated_presents S rr)) xs
      (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks)"
  proof (rule list_all2_all_nthI)
    show "length xs=length (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks)" using len by simp
    fix n assume n: "n<length xs"
    have key: "fst (xs!n)=fst (ks!n)" using arg_cong[OF xs(1), of "\<lambda>l. l!n"] n len by simp
    obtain c v where kn: "ks!n=(c,v)" by (cases "ks!n")
    have kin: "(c,v)\<in>set ks" using kn n len by (metis nth_mem)
    obtain S where S: "(c,S)\<in>C" "clause_stated_presents S v" using ks(3) kin by blast
    have "xs!n\<in>set xs" using n by (rule nth_mem)
    then have "(fst (xs!n),snd (xs!n))\<in>M" using xs(2) by simp
    then obtain S' where S': "(fst (xs!n),S')\<in>C" "native_schema_at E u (snd (xs!n)) S'" using family(5) by blast
    have "S'=S" using family(3) S(1) S'(1) key kn by (auto simp: single_valued_def)
    then show "\<exists>rr. map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks!n=Pair_Term (Payload_Term (fst (xs!n))) rr \<and>
        (\<exists>S. native_schema_at E u (snd (xs!n)) S \<and> clause_stated_presents S rr)"
      using S S' key kn n len by auto
  qed
  have cf: "term_formed (Pair_Term e (use_data_term u))" using formed by simp
  have family_rows: "(589,context_relation_argument (Pair_Term e (use_data_term u)) ?rows
      (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks)))\<in>positive_meaning stated_rows_system"
    using stated_rows_on_values[OF source cf formed(1)] listed by simp
  have operands: "term_formed (Payload_Term r)" "term_formed (Payload_Term a)" "term_formed (Payload_Term i)"
    "term_formed (Payload_Term b)" "term_formed (Payload_Term m)"
    using schema_call_formed_target[OF positive_meaning_formed[OF rec]] by auto
  have more: "term_formed (binding_rows_term ys)" "term_formed (data_list_term (map Payload_Term Is))"
    "term_formed (data_list_term (map Payload_Term Ks))" using sargf by simp_all
  have lf: "term_formed (data_list_term (pattern_stated p))"
    using term_stated_formed[OF wformed] stated_w by (simp add: stated_list_formed)
  have kf: "term_formed (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF family_rows]] by simp
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then use_data_term u else if n=2 then Payload_Term r
    else if n=3 then w else if n=4 then material else if n=5 then Payload_Term a else if n=6 then Payload_Term i
    else if n=7 then Payload_Term b else if n=8 then Payload_Term m else if n=9 then ?rows
    else if n=10 then binding_rows_term ys else if n=11 then data_list_term (map Payload_Term Is)
    else if n=12 then data_list_term (map Payload_Term Ks) else if n=13 then data_list_term (pattern_stated p)
    else data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks)"
  have "(590,evaluate_pattern ?h (schema_conclusion stated_report_schema))\<in>positive_meaning stated_report_system"
    by (rule ordinary_positive_formed_step[where c=0, OF _ _ stated_report_schema_formed])
      (use formed operands more wformed lf kf admitted lookup rec rows scopedfact table head family_rows in
        \<open>simp_all add: stated_report_schema_def schema_variables_def stated_report_call stated_report_components\<close>)
  then show ?thesis by (simp add: stated_report_schema_def ks(4))
qed

theorem stated_report_exact:
  "(590,z)\<in>positive_meaning stated_report_system \<longleftrightarrow> stated_report_result z"
  using stated_report_sound stated_report_complete by blast

corollary stated_report_at_source:
  assumes source: "environment_value_presents E e"
  shows "(590,Pair_Term (source_root_argument e u r) y)\<in>positive_meaning stated_report_system \<longleftrightarrow>
    (\<exists>v a p C. u=use_data_term v \<and> r=Payload_Term a \<and> native_definition_at E v a p C \<and> definition_stated_presents p C y)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: stated_report_exact factor_term.inject) (use source unique in blast)
qed

corollary stated_report_on_values:
  assumes source: "environment_value_presents E e"
  shows "(590,Pair_Term (source_root_argument e (use_data_term u) (Payload_Term r)) y)\<in>positive_meaning stated_report_system
    \<longleftrightarrow> (\<exists>p C. native_definition_at E u r p C \<and> definition_stated_presents p C y)"
  by (simp only: stated_report_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary stated_report_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(590,Pair_Term (source_root_argument e u r) y)\<in>positive_meaning stated_report_system \<longleftrightarrow>
    (590,Pair_Term (source_root_argument f u r) y)\<in>positive_meaning stated_report_system"
  by (simp only: stated_report_at_source[OF assms(1)] stated_report_at_source[OF assms(2)])

section \<open>The reader's own stated payloads\<close>

text \<open>
  By the audit's criterion the reader's eleven definitions state the empty payload alone (as the leaf it
  reports, as the accumulator's and every data list's end, and as the empty table and rows of a ground
  clause), no target, and no material premise. Every other octet it meets is compared by the readers it
  calls under their contracts, as the audit's are.
\<close>

lemma stated_leaves_own_payloads:
  assumes "(c,S)\<in>stated_leaves_clauses \<union> {(0,stated_value_schema)} \<union> list_profile_clauses 581 582 \<union>
    {(0,stated_call_schema)} \<union> related_list_clauses 583 584 \<union> {(0,stated_material_schema)} \<union>
    related_list_clauses 585 586 \<union> stated_clause_clauses \<union> {(0,stated_row_schema)} \<union>
    related_list_clauses 588 589 \<union> {(0,stated_report_schema)}"
  shows "schema_payloads S\<subseteq>{[]} \<and> (\<forall>x. Target_Term x\<notin>schema_leaves S) \<and> schema_material_premises S={}"
  using assms
  by (auto simp: stated_leaves_clauses_def stated_leaves_schema_defs stated_value_schema_def list_profile_clauses_def
    list_step_schema_def data_list_nil_schema_def stated_call_schema_def related_list_clauses_def
    related_list_nil_schema_def related_list_step_schema_def stated_material_schema_def stated_clause_clauses_def
    stated_clause_ground_schema_def stated_clause_open_schema_def stated_row_schema_def stated_report_schema_def
    schema_payloads_def schema_leaves_def)

section \<open>The finite computation of a definition's report\<close>

definition clause_stated :: "('a,'s,'d) factor_schema \<Rightarrow>
    factor_term list\<times>factor_term list\<times>('s\<times>factor_term list) set\<times>('s\<times>factor_term list list) set" where
  "clause_stated S=(clause_ground S,pattern_stated (schema_conclusion S),clause_calls S,clause_materials S)"

definition definition_stated :: "'a term_pattern \<Rightarrow> ('c\<times>('a,'s,'d) factor_schema) set \<Rightarrow>
    factor_term list\<times>('c\<times>(factor_term list\<times>factor_term list\<times>('s\<times>factor_term list) set\<times>('s\<times>factor_term list list) set)) set" where
  "definition_stated p C=(pattern_stated p,(\<lambda>(c,S). (c,clause_stated S)) ` C)"

fun finite_pattern_stated :: "'a finite_term_pattern \<Rightarrow> finite_factor_term list" where
  "finite_pattern_stated (Finite_Variable a)=[]"
| "finite_pattern_stated (Finite_Pattern_Target x)=[Finite_Target x]"
| "finite_pattern_stated (Finite_Pattern_Payload v)=(if v=[] then [Finite_Payload []] else [])"
| "finite_pattern_stated (Finite_Pattern_Pair p q)=finite_pattern_stated p @ finite_pattern_stated q"

lemma finite_pattern_stated_exact:
  "map decode_finite_term (finite_pattern_stated p)=pattern_stated (decode_finite_pattern p)"
  by (induction p) auto

fun finite_pattern_ground :: "'a finite_term_pattern \<Rightarrow> finite_factor_term option" where
  "finite_pattern_ground (Finite_Variable a)=None"
| "finite_pattern_ground (Finite_Pattern_Target x)=Some (Finite_Target x)"
| "finite_pattern_ground (Finite_Pattern_Payload v)=Some (Finite_Payload v)"
| "finite_pattern_ground (Finite_Pattern_Pair p q)=(case (finite_pattern_ground p,finite_pattern_ground q) of
    (Some x,Some y) \<Rightarrow> Some (Finite_Pair x y) | _ \<Rightarrow> None)"

lemma finite_pattern_ground_exact:
  "map_option decode_finite_term (finite_pattern_ground p)=pattern_ground (decode_finite_pattern p)"
proof (induction p)
  case (Finite_Pattern_Pair p q)
  show ?case using Finite_Pattern_Pair.IH[symmetric]
    by (cases "finite_pattern_ground p"; cases "finite_pattern_ground q") simp_all
qed simp_all

definition finite_clause_stated :: "('a,'s,'d) finite_factor_schema \<Rightarrow>
    finite_factor_term list\<times>finite_factor_term list\<times>('s\<times>finite_factor_term list) fset\<times>
      ('s\<times>finite_factor_term list list) fset" where
  "finite_clause_stated S=((if finite_schema_premises S={||} \<and> finite_schema_materials S={||}
      then (case finite_pattern_ground (finite_schema_conclusion S) of None \<Rightarrow> [] | Some g \<Rightarrow> [g]) else []),
    finite_pattern_stated (finite_schema_conclusion S),
    fimage (\<lambda>(s,q). (s,finite_pattern_stated (snd q))) (finite_schema_premises S),
    fimage (\<lambda>(s,M). (s,map finite_pattern_stated (finite_material_fields M))) (finite_schema_materials S))"

definition decode_clause_stated ::
    "finite_factor_term list\<times>finite_factor_term list\<times>('s\<times>finite_factor_term list) fset\<times>('s\<times>finite_factor_term list list) fset \<Rightarrow>
      factor_term list\<times>factor_term list\<times>('s\<times>factor_term list) set\<times>('s\<times>factor_term list list) set" where
  "decode_clause_stated z=(case z of (g,l,Q,M) \<Rightarrow> (map decode_finite_term g,map decode_finite_term l,
    (\<lambda>(s,x). (s,map decode_finite_term x)) ` fset Q,(\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ` fset M))"

lemma decode_finite_call_pattern_snd:
  "snd (decode_finite_call_pattern q)=decode_finite_pattern (snd q)"
  by (cases q) (simp add: decode_finite_call_pattern_def)

theorem finite_clause_stated_exact:
  "decode_clause_stated (finite_clause_stated S)=clause_stated (decode_finite_schema S)"
proof -
  have fields: "schema_premises (decode_finite_schema S)=map_relation_values decode_finite_call_pattern (fset (finite_schema_premises S))"
    "schema_material_premises (decode_finite_schema S)=map_relation_values decode_finite_material (fset (finite_schema_materials S))"
    "schema_conclusion (decode_finite_schema S)=decode_finite_pattern (finite_schema_conclusion S)"
    by (simp_all add: decode_finite_schema_def)
  have ground: "map decode_finite_term (if finite_schema_premises S={||} \<and> finite_schema_materials S={||}
      then (case finite_pattern_ground (finite_schema_conclusion S) of None \<Rightarrow> [] | Some g \<Rightarrow> [g]) else [])=
    clause_ground (decode_finite_schema S)"
    using finite_pattern_ground_exact[of "finite_schema_conclusion S"]
    by (auto simp: clause_ground_def fields map_relation_values_def split: option.splits)
  have calls: "(\<lambda>(s,x). (s,map decode_finite_term x)) ` fset (fimage (\<lambda>(s,q). (s,finite_pattern_stated (snd q)))
      (finite_schema_premises S))=clause_calls (decode_finite_schema S)"
    by (simp add: clause_calls_def fields map_relation_values_def fimage.rep_eq image_image split_def
      finite_pattern_stated_exact decode_finite_call_pattern_snd)
  have materials: "(\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ` fset (fimage (\<lambda>(s,M). (s,map finite_pattern_stated
      (finite_material_fields M))) (finite_schema_materials S))=clause_materials (decode_finite_schema S)"
    by (simp add: clause_materials_def material_stated_def fields map_relation_values_def fimage.rep_eq image_image
      split_def finite_material_fields_correct[symmetric] map_map comp_def finite_pattern_stated_exact)
  show ?thesis
    using ground calls materials finite_pattern_stated_exact[of "finite_schema_conclusion S"]
    by (simp add: decode_clause_stated_def finite_clause_stated_def clause_stated_def fields)
qed

definition finite_definition_stated where
  "finite_definition_stated p C=(finite_pattern_stated p,fimage (\<lambda>(c,S). (c,finite_clause_stated S)) C)"

theorem finite_definition_stated_exact:
  "(map decode_finite_term (fst (finite_definition_stated p C)),
      (\<lambda>(c,z). (c,decode_clause_stated z)) ` fset (snd (finite_definition_stated p C)))=
    definition_stated (decode_finite_pattern p) ((\<lambda>(c,S). (c,decode_finite_schema S)) ` fset C)"
proof -
  have "(\<lambda>(c,z). (c,decode_clause_stated z)) ` fset (fimage (\<lambda>(c,S). (c,finite_clause_stated S)) C)=
      (\<lambda>(c,S). (c,clause_stated S)) ` ((\<lambda>(c,S). (c,decode_finite_schema S)) ` fset C)"
    by (simp add: fimage.rep_eq image_image split_def finite_clause_stated_exact)
  then show ?thesis by (simp add: finite_definition_stated_def definition_stated_def finite_pattern_stated_exact)
qed

section \<open>Controls, and why the native evaluator does not run the reader\<close>

text \<open>
  The one native evaluator of a finite program, finite_program_evaluation, is ready only on a
  demand whose program is head-covered: every premise variable of a clause is bound by its head. This
  reader is not, as the audit is not: 580's target clause leaves its projection (variable 2) and its pair
  clause the intermediate accumulator (4) to the premises; 587's three clauses that are not ground leave
  the instance (4), the table (3, or 10 and 11), the call rows (5) and the material rows (6), while its
  ground clause is head-covered; 590 leaves the interface's
  instance (3), the artifact's data (4), the record's ports and endpoints (5 to 8), the family's rows (9),
  the table (10) and the quotation's interior and slots (11, 12). The readers they call (72, 65, 56, 37, 34,
  32, 45 and the distinct-payload program) hold clauses of the same kind. The controls are therefore
  evaluated through the finite computation, exact against the leaves and so against the native contract,
  beside the audit's HOL counterpart at the same definitions.
\<close>

definition stated_control_target :: "nat finite_term_pattern" where
  "stated_control_target=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)"

definition stated_leaves_controls :: "(nat finite_term_pattern\<times>(nat\<times>(nat,nat,nat) finite_factor_schema) fset) list" where
  "stated_leaves_controls=[
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Pattern_Payload [1]) stated_control_target,
      finite_schema_premises={||},finite_schema_materials={||}\<rparr>)|}),
    (Finite_Pattern_Pair (Finite_Variable 0) stated_control_target,
     {|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) stated_control_target,
      finite_schema_premises={|(1,(5,Finite_Pattern_Pair stated_control_target (Finite_Variable 0)))|},
      finite_schema_materials={|(2,\<lparr>finite_material_source=stated_control_target,finite_material_atoms=Finite_Variable 1,
        finite_material_edges=Finite_Variable 2,finite_material_counts=Finite_Variable 3,
        finite_material_functions=Finite_Variable 4\<rparr>)|}\<rparr>)|}),
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Payload []),
      finite_schema_premises={|(1,(5,Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 0)))|},
      finite_schema_materials={||}\<rparr>)|}),
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Variable 0,
      finite_schema_premises={|(1,(5,Finite_Variable 0))|},finite_schema_materials={||}\<rparr>)|})]"

definition stated_leaves_control_reports where
  "stated_leaves_control_reports=map (\<lambda>(p,C). (finite_definition_stated p C,finite_definition_payloads p C))
    stated_leaves_controls"

ML \<open>
  val stated_leaves_control_context = @{context};
  val (stated_leaves_control_time, stated_leaves_control_value) =
    Timing.timing (Code_Evaluation.dynamic_value_strict stated_leaves_control_context)
      @{term "stated_leaves_control_reports"};
  val _ = writeln ("STATED_LEAVES_CONTROLS " ^ Timing.message stated_leaves_control_time);
  val _ = writeln (Syntax.string_of_term stated_leaves_control_context stated_leaves_control_value);
\<close>

declare One_nat_def [simp]

end
