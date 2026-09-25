theory Factor_Least_Collections
  imports Factor_Resolution_Completeness Factor_System_Alpha Finite_Presented_Collections Finite_Singleton_Selection
    Finite_Functional_Enumeration
begin

section \<open>The program a query searches, its variables apart from the query's\<close>

text \<open>
  A least witness is collected from the answers of queries to the program's own sites (W2 of DECISIONS.md "A
  checker does not produce"). A query is a goal pattern at a site over variables of its own; R3's search renames
  a clause at a derivation position with both flags of that position, so a variable of the program's own type
  can meet a renamed clause variable at any position. The query's search therefore runs over the program with its
  variables lifted by @{const Inl}, the query's variables being @{const Inr}: no renaming of a clause reaches them.
  The lifted program is the original one with its variables renamed, so it is formed and means what the original
  means (@{text finite_query_program_formed}, @{text finite_query_program_meaning}).
\<close>

definition system_variable_renaming :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'s,'d,'c) schema_system" where
  "system_variable_renaming f Q=\<lparr>system_interfaces=map_relation_values (rename_pattern f) (system_interfaces Q),
    system_clauses=map_relation_values (rename_schema f id id) (system_clauses Q)\<rparr>"

lemma system_variable_renaming_fields [simp]:
  "system_interfaces (system_variable_renaming f Q)=map_relation_values (rename_pattern f) (system_interfaces Q)"
  "system_clauses (system_variable_renaming f Q)=map_relation_values (rename_schema f id id) (system_clauses Q)"
  by (simp_all add: system_variable_renaming_def)

lemma system_variable_renaming_definitions [simp]:
  "system_definitions (system_variable_renaming f Q)=system_definitions Q"
  by (simp add: system_definitions_def)

lemma system_variable_renaming_formed:
  assumes formed: "schema_system_formed Q"
  shows "schema_system_formed (system_variable_renaming f Q)"
proof -
  have sv: "single_valued (map_relation_values g R)" if "single_valued R" for g :: "'x \<Rightarrow> 'y" and R :: "('k\<times>'x) set"
    using that by (auto simp: single_valued_def)
  have clauses: "d \<in> system_definitions Q \<and> schema_formed (rename_schema f id id S) \<and>
      schema_dependencies (rename_schema f id id S) \<subseteq> system_definitions Q"
    if "((d,c),S) \<in> system_clauses Q" for d c S
    using formed that renamed_schema_formed[where S=S and h=id and f=f and g=id]
    by (auto simp: schema_system_formed_def renamed_schema_dependencies)
  have "single_valued (system_interfaces Q)" "single_valued (system_clauses Q)"
    using formed by (simp_all add: schema_system_formed_def)
  then show ?thesis
    using formed clauses sv[of "system_interfaces Q" "rename_pattern f"] sv[of "system_clauses Q" "rename_schema f id id"]
    unfolding schema_system_formed_def system_variable_renaming_definitions
    by (auto simp: rename_pattern_formed)
qed

lemma system_variable_renaming_alpha:
  assumes formed: "schema_system_formed Q" and injective: "inj f"
  shows "system_alpha_variant Q (system_variable_renaming f Q)"
proof -
  let ?R="system_variable_renaming f Q"
  have rformed: "schema_system_formed ?R" by (rule system_variable_renaming_formed[OF formed])
  have family: "(c,T) \<in> system_clause_family ?R d \<longleftrightarrow> (\<exists>S. (c,S) \<in> system_clause_family Q d \<and> T=rename_schema f id id S)"
    for c T d by auto
  have fields: "\<exists>g h. inj_on g (pattern_variables (system_interface Q d)) \<and>
      system_interface ?R d=rename_pattern g (system_interface Q d) \<and>
      schema_family_variant h (system_clause_family Q d) (system_clause_family ?R d)"
    if member: "d \<in> system_definitions Q" for d
  proof (intro exI conjI)
    show "inj_on f (pattern_variables (system_interface Q d))" by (rule inj_on_subset[OF injective subset_UNIV])
    have "(d,rename_pattern f (system_interface Q d)) \<in> system_interfaces ?R"
      using system_interface_member[OF formed member] by auto
    then show "system_interface ?R d=rename_pattern f (system_interface Q d)" by (rule system_interface_unique[OF rformed])
    show "schema_family_variant id (system_clause_family Q d) (system_clause_family ?R d)"
      unfolding schema_family_variant_def
    proof (intro conjI allI impI)
      show "inj_on id (rel_dom (system_clause_family Q d))" by simp
      show "finite (system_clause_family ?R d)" by (rule system_clause_family_finite[OF rformed])
      show "single_valued (system_clause_family ?R d)" by (rule system_clause_family_functional[OF rformed])
      show "rel_dom (system_clause_family ?R d)=id ` rel_dom (system_clause_family Q d)"
        by (auto simp: rel_dom_def family)
      fix c S assume source: "(c,S) \<in> system_clause_family Q d"
      show "\<exists>T. (id c,T) \<in> system_clause_family ?R d \<and> schema_alpha_variant S T"
      proof (intro exI conjI)
        show "(id c,rename_schema f id id S) \<in> system_clause_family ?R d" using source family by auto
        show "schema_alpha_variant S (rename_schema f id id S)" unfolding schema_alpha_variant_def
          by (rule exI[of _ f], rule exI[of _ id]) (simp add: inj_on_subset[OF injective subset_UNIV])
      qed
    qed
  qed
  show ?thesis using formed rformed fields by (simp add: system_alpha_variant_def)
qed

definition finite_query_program ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a+'v,'s,'d,'c) finite_schema_system" where
  "finite_query_program P=\<lparr>finite_system_interfaces=fimage (\<lambda>(d,p). (d,map_finite_term_pattern Inl p))
      (finite_system_interfaces P),
    finite_system_clauses=fimage (\<lambda>(k,S). (k,finite_rename_schema Inl id id S)) (finite_system_clauses P)\<rparr>"

lemma decode_finite_query_program:
  "decode_finite_system (finite_query_program P)=system_variable_renaming Inl (decode_finite_system P)"
  by (simp add: finite_query_program_def decode_finite_system_def system_variable_renaming_def
      map_relation_values_def image_image split_def decode_finite_pattern_map finite_rename_schema_correct fimage.rep_eq)

theorem finite_query_program_formed:
  assumes "finite_system_formed P"
  shows "finite_system_formed (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system)"
  using system_variable_renaming_formed assms by (simp add: finite_system_formed_correct decode_finite_query_program)

theorem finite_query_program_meaning:
  assumes formed: "finite_system_formed P"
  shows "positive_meaning (decode_finite_system (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system))=
    positive_meaning (decode_finite_system P)"
proof -
  have "positive_meaning (decode_finite_system P)=
      positive_meaning (system_variable_renaming (Inl::'a \<Rightarrow> 'a+'v) (decode_finite_system P))"
    by (rule system_alpha_positive_meaning[OF system_variable_renaming_alpha])
      (use formed in \<open>simp_all add: finite_system_formed_correct\<close>)
  then show ?thesis by (simp add: decode_finite_query_program)
qed

section \<open>The value of a pattern under a valuation\<close>

lemma resolution_value_constructors [simp]:
  "resolution_value \<theta> (Finite_Variable x)=\<theta> x"
  "resolution_value \<theta> (Finite_Pattern_Target y)=Finite_Target y"
  "resolution_value \<theta> (Finite_Pattern_Payload v)=Finite_Payload v"
  "resolution_value \<theta> (Finite_Pattern_Pair p q)=Finite_Pair (resolution_value \<theta> p) (resolution_value \<theta> q)"
  by (simp_all add: resolution_value_def)

lemma resolution_value_rename:
  "resolution_value \<theta> (map_finite_term_pattern f p)=resolution_value (\<theta> \<circ> f) p"
  by (induction p) simp_all

lemma resolution_value_ground_pattern:
  "finite_pattern_variables p={||} \<Longrightarrow> resolution_value \<theta> p=finite_residual_term p"
  by (induction p) auto

lemma resolution_value_variable_formed:
  "finite_term_formed (resolution_value \<theta> p) \<Longrightarrow> x |\<in>| finite_pattern_variables p \<Longrightarrow> finite_term_formed (\<theta> x)"
  by (induction p) auto

lemma finite_instance_value:
  assumes "finite_pattern_instance V p t"
    and "\<And>x u. x |\<in>| finite_pattern_variables p \<Longrightarrow> (x,u) |\<in>| V \<Longrightarrow> \<theta> x=u"
  shows "resolution_value \<theta> p=t"
  using assms by (induction p arbitrary: t) (auto split: finite_factor_term.splits)


text \<open>An instance depends only on the bindings of the pattern's own variables.\<close>

lemma finite_pattern_instance_variables:
  "finite_pattern_instance V p t \<Longrightarrow> (\<And>x u. x |\<in>| finite_pattern_variables p \<Longrightarrow> (x,u) |\<in>| V \<Longrightarrow> (x,u) |\<in>| W) \<Longrightarrow>
    finite_pattern_instance W p t"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_substitute_formed_on:
  "finite_pattern_formed p \<Longrightarrow> (\<And>x. x |\<in>| finite_pattern_variables p \<Longrightarrow> finite_pattern_formed (\<sigma> x)) \<Longrightarrow>
    finite_pattern_formed (finite_pattern_substitute \<sigma> p)"
  by (induction p) auto

lemma finite_substitute_variables_member:
  "x |\<in>| finite_pattern_variables p \<Longrightarrow>
    finite_pattern_variables (\<sigma> x) |\<subseteq>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)"
  by (induction p) auto

lemma finite_certificate_true:
  assumes "finite_checks_schema_proof P p d t"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  using assms by (simp only: finite_checks_schema_proof_exact) (rule schema_proof_sound)

lemma finite_true_call_formed:
  assumes "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  shows "finite_system_formed P" "finite_term_formed t"
  using positive_meaning_has_formed_system[OF assms] positive_meaning_formed[OF assms]
  by (auto simp: finite_system_formed_correct schema_call_formed_def pattern_accepts_def finite_term_formed_correct)

section \<open>A binding table read as a valuation\<close>

definition finite_binding_valuation :: "('x\<times>finite_factor_term) fset \<Rightarrow> 'x \<Rightarrow> finite_factor_term" where
  "finite_binding_valuation V x=(case finite_relation_option V x of Some t \<Rightarrow> t | None \<Rightarrow> Finite_Payload [])"

lemma finite_binding_valuation_member:
  assumes "finite_relation_functional V" and "(x,t) |\<in>| V"
  shows "finite_binding_valuation V x=t"
proof -
  have "finite_relation_option V x=Some t" using assms by (simp add: finite_relation_option_correct)
  then show ?thesis by (simp add: finite_binding_valuation_def)
qed

lemma finite_ground_bindings_functional: "finite_relation_functional (finite_ground_bindings \<theta> X)"
  unfolding finite_relation_functional_correct single_valued_def by auto

lemma finite_functional_subset:
  assumes "finite_relation_functional V" and "W |\<subseteq>| V"
  shows "finite_relation_functional W"
proof -
  have "single_valued (fset V)" using assms(1) by (simp only: finite_relation_functional_correct)
  then have "single_valued (fset W)" using assms(2) unfolding single_valued_def by (auto simp: less_eq_fset.rep_eq)
  then show ?thesis by (simp only: finite_relation_functional_correct)
qed

section \<open>Equations matched against patterns\<close>

lemma ffunion_list_member: "z |\<in>| ffUnion (fset_of_list (map f xs)) \<longleftrightarrow> (\<exists>x\<in>set xs. z |\<in>| f x)"
  by (induction xs) auto

text \<open>
  Equations pair a ground term with a pattern. They are matched by matching each pattern against its term
  (@{const finite_matching_bindings}) and joining the bindings: accepted when the join is functional and every
  pattern is an instance under it, and then the join is the one binding of the equations' variables that
  satisfies them (@{text finite_inputs_matching_complete}).
\<close>

definition finite_inputs_matching ::
    "(finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow> ('v\<times>finite_factor_term) fset option" where
  "finite_inputs_matching ts=(let W=ffUnion (fset_of_list (map (\<lambda>(t,p). finite_matching_bindings p t) ts)) in
    if finite_relation_functional W \<and> list_all (\<lambda>(t,p). finite_pattern_instance W p t) ts then Some W else None)"

lemma finite_inputs_matching_some:
  assumes "finite_inputs_matching ts=Some W"
  shows "finite_relation_functional W" "\<And>t p. (t,p) \<in> set ts \<Longrightarrow> finite_pattern_instance W p t"
  using assms by (auto simp: finite_inputs_matching_def Let_def list_all_iff split: if_splits)

lemma finite_inputs_matching_complete:
  assumes evaluated: "\<And>t p. (t,p) \<in> set ts \<Longrightarrow> finite_pattern_formed p \<and> resolution_value \<theta> p=t"
  obtains W where "finite_inputs_matching ts=Some W" "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
proof -
  define X where "X=ffUnion (fset_of_list (map (\<lambda>(t,p). finite_pattern_variables p) ts))"
  define V where "V=finite_ground_bindings \<theta> X"
  have functional: "finite_relation_functional V" unfolding V_def by (rule finite_ground_bindings_functional)
  have inst: "finite_pattern_instance V p t" if member: "(t,p) \<in> set ts" for t p
  proof -
    have scope: "finite_pattern_variables p |\<subseteq>| X"
      using member unfolding X_def by (force simp: less_eq_fset.rep_eq ffUnion.rep_eq fset_of_list.rep_eq)
    have eq: "finite_pattern_substitute (resolution_substitution \<theta>) p=finite_exact_term_pattern t"
      using evaluated[OF member] resolution_value_exact[of \<theta> p] by simp
    show ?thesis unfolding V_def by (rule resolution_ground_instance[OF _ scope eq]) (use evaluated[OF member] in simp)
  qed
  define W where "W=ffUnion (fset_of_list (map (\<lambda>(t,p). finite_matching_bindings p t) ts))"
  have parts: "finite_matching_bindings p t=ffilter (\<lambda>z. fst z |\<in>| finite_pattern_variables p) V"
    if "(t,p) \<in> set ts" for t p
    by (rule finite_matching_bindings_instance[OF functional inst[OF that]])
  have inside: "z |\<in>| V" if zW: "z |\<in>| W" for z
  proof -
    obtain y where y: "y \<in> set ts" "z |\<in>| (\<lambda>(t,p). finite_matching_bindings p t) y"
      using zW unfolding W_def ffunion_list_member by blast
    obtain t p where yt: "y=(t,p)" by (cases y)
    have member: "(t,p) \<in> set ts" and z: "z |\<in>| finite_matching_bindings p t" using y yt by simp_all
    show ?thesis using z parts[OF member] by simp
  qed
  have functional_W: "finite_relation_functional W"
    by (rule finite_functional_subset[OF functional]) (use inside in \<open>auto simp: less_eq_fset.rep_eq\<close>)
  have inst_W: "finite_pattern_instance W p t" if member: "(t,p) \<in> set ts" for t p
  proof -
    have "finite_pattern_instance (finite_matching_bindings p t) p t"
      using finite_pattern_instance_restrict[of p "finite_pattern_variables p" V] inst[OF member] parts[OF member]
      by simp
    moreover have "finite_matching_bindings p t |\<subseteq>| W"
    proof (rule fsubsetI)
      fix z assume z: "z |\<in>| finite_matching_bindings p t"
      have "\<exists>x\<in>set ts. z |\<in>| (\<lambda>(t,p). finite_matching_bindings p t) x" using member z by force
      then show "z |\<in>| W" unfolding W_def ffunion_list_member .
    qed
    ultimately show ?thesis using finite_pattern_instance_variables[of "finite_matching_bindings p t" p t W] fsubsetD
      by blast
  qed
  have "finite_inputs_matching ts=Some W"
    using functional_W inst_W unfolding finite_inputs_matching_def W_def[symmetric] Let_def list_all_iff by auto
  moreover have "\<theta> x=u" if "(x,u) |\<in>| W" for x u using inside[OF that] unfolding V_def by simp
  ultimately show ?thesis by (rule that)
qed

section \<open>A query and its answers\<close>

text \<open>
  A query is posed at a clause's ground bindings: its equations match the values of clause variables against
  patterns over the query's variables, and its goal is a call at a site of the same program whose pattern is over
  those variables; its element variable is the one whose instances it answers. A step query is posed with one more
  equation, the element the step is taken at matched against its source pattern. The query holds at an element
  when some valuation of its variables satisfies its equations, gives the element and makes the goal a true call
  of the program (@{text finite_query_holds}).
\<close>

record ('a,'d,'v) collection_query =
  query_equations :: "('a\<times>'v finite_term_pattern) list"
  query_site :: 'd
  query_goal :: "'v finite_term_pattern"
  query_element :: 'v

definition finite_query_inputs :: "('a,'d,'v) collection_query \<Rightarrow> ('a\<times>finite_factor_term) fset \<Rightarrow>
    (finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow> (finite_factor_term\<times>'v finite_term_pattern) list option" where
  "finite_query_inputs q B E=map_option (\<lambda>ts. ts@E)
    (those (map (\<lambda>(a,p). map_option (\<lambda>t. (t,p)) (finite_relation_option B a)) (query_equations q)))"

definition finite_query_holds :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_query \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_query_holds P q B E e \<longleftrightarrow> (\<exists>ts \<theta>. finite_query_inputs q B E=Some ts \<and> \<theta> (query_element q)=e \<and>
    (\<forall>(t,p)\<in>set ts. resolution_value \<theta> p=t) \<and>
    (query_site q,decode_finite_term (resolution_value \<theta> (query_goal q))) \<in> positive_meaning (decode_finite_system P))"

definition finite_query_formed :: "('a,'d,'v) collection_query \<Rightarrow> (finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow> bool" where
  "finite_query_formed q ts \<longleftrightarrow> finite_pattern_formed (query_goal q) \<and>
    query_element q |\<in>| finite_pattern_variables (query_goal q) \<and> list_all (\<lambda>(t,p). finite_pattern_formed p) ts"

definition finite_query_substitution :: "('v\<times>finite_factor_term) fset \<Rightarrow> 'v \<Rightarrow> 'v finite_term_pattern" where
  "finite_query_substitution W v=(case finite_relation_option W v of Some t \<Rightarrow> finite_exact_term_pattern t
    | None \<Rightarrow> Finite_Variable v)"

definition finite_query_pattern :: "('a,'d,'v) collection_query \<Rightarrow> ('v\<times>finite_factor_term) fset \<Rightarrow> 'v finite_term_pattern" where
  "finite_query_pattern q W=finite_pattern_substitute (finite_query_substitution W) (query_goal q)"

definition finite_query_valuation ::
    "('v\<times>finite_factor_term) fset \<Rightarrow> ('v\<times>finite_factor_term) fset \<Rightarrow> 'v \<Rightarrow> finite_factor_term" where
  "finite_query_valuation W M v=(case finite_relation_option W v of Some t \<Rightarrow> t | None \<Rightarrow> finite_binding_valuation M v)"

text \<open>The element a ground instance of the query's goal gives, read by matching that instance.\<close>

definition finite_query_element ::
    "('a,'d,'v) collection_query \<Rightarrow> ('v\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term option" where
  "finite_query_element q W t=(let g=finite_query_pattern q W; M=finite_matching_bindings g t in
    if finite_relation_functional M \<and> finite_pattern_instance M g t
    then Some (finite_query_valuation W M (query_element q)) else None)"

lemma finite_query_substitution_value:
  "resolution_value (finite_binding_valuation M) (finite_query_substitution W v)=finite_query_valuation W M v"
  by (cases "finite_relation_option W v")
    (simp_all add: finite_query_substitution_def finite_query_valuation_def resolution_value_ground)

lemma finite_query_pattern_value:
  assumes agree: "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
  shows "resolution_value \<theta> (finite_query_pattern q W)=resolution_value \<theta> (query_goal q)"
proof -
  have "resolution_value \<theta> (finite_query_substitution W x)=\<theta> x" for x
  proof (cases "finite_relation_option W x")
    case (Some u)
    then show ?thesis using agree[OF finite_relation_option_member[OF Some]]
      by (simp add: finite_query_substitution_def resolution_value_ground)
  qed (simp add: finite_query_substitution_def)
  then show ?thesis by (simp add: finite_query_pattern_def resolution_value_instance)
qed

lemma finite_query_pattern_formed:
  assumes agree: "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u" and formed: "finite_pattern_formed (query_goal q)"
    and valued: "finite_term_formed (resolution_value \<theta> (query_goal q))"
  shows "finite_pattern_formed (finite_query_pattern q W)"
  unfolding finite_query_pattern_def
proof (rule finite_substitute_formed_on[OF formed])
  fix x assume x: "x |\<in>| finite_pattern_variables (query_goal q)"
  show "finite_pattern_formed (finite_query_substitution W x)"
  proof (cases "finite_relation_option W x")
    case (Some u)
    have "finite_term_formed u"
      using resolution_value_variable_formed[OF valued x] agree[OF finite_relation_option_member[OF Some]] by simp
    then show ?thesis using Some by (simp add: finite_query_substitution_def)
  qed (simp add: finite_query_substitution_def)
qed

lemma finite_query_element_sound:
  assumes functional: "finite_relation_functional W" and element: "finite_query_element q W t=Some e"
  obtains M where "finite_query_valuation W M (query_element q)=e"
    "resolution_value (finite_query_valuation W M) (query_goal q)=t"
    "\<forall>p u. finite_pattern_instance W p u \<longrightarrow> resolution_value (finite_query_valuation W M) p=u"
proof -
  define M where "M=finite_matching_bindings (finite_query_pattern q W) t"
  have M: "finite_relation_functional M" "finite_pattern_instance M (finite_query_pattern q W) t"
    and e: "e=finite_query_valuation W M (query_element q)"
    using element by (auto simp: finite_query_element_def M_def Let_def split: if_splits)
  have "resolution_value (finite_binding_valuation M) (finite_query_pattern q W)=t"
    by (rule finite_instance_value[OF M(2)]) (simp add: finite_binding_valuation_member[OF M(1)])
  then have goal: "resolution_value (finite_query_valuation W M) (query_goal q)=t"
    by (simp add: finite_query_pattern_def resolution_value_instance finite_query_substitution_value)
  have inputs: "resolution_value (finite_query_valuation W M) p=u" if "finite_pattern_instance W p u" for p u
  proof (rule finite_instance_value[OF that])
    fix x v assume "(x,v) |\<in>| W"
    then have "finite_relation_option W x=Some v" by (simp add: finite_relation_option_correct[OF functional])
    then show "finite_query_valuation W M x=v" by (simp add: finite_query_valuation_def)
  qed
  show ?thesis using that[OF e[symmetric] goal] inputs by blast
qed

lemma finite_query_element_complete:
  assumes agree: "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
    and formed: "finite_pattern_formed (query_goal q)" and element: "query_element q |\<in>| finite_pattern_variables (query_goal q)"
    and evaluation: "resolution_value \<theta> (query_goal q)=t" and tformed: "finite_term_formed t"
  shows "finite_query_element q W t=Some (\<theta> (query_element q))"
proof -
  let ?g="finite_query_pattern q W"
  have gvalue: "resolution_value \<theta> ?g=t" using finite_query_pattern_value[of W \<theta> q, OF agree] evaluation by simp
  have valued: "finite_term_formed (resolution_value \<theta> (query_goal q))" by (subst evaluation) (rule tformed)
  have gformed: "finite_pattern_formed ?g" by (rule finite_query_pattern_formed[of W \<theta> q, OF agree formed valued])
  define V where "V=finite_ground_bindings \<theta> (finite_pattern_variables ?g)"
  have functional: "finite_relation_functional V" unfolding V_def by (rule finite_ground_bindings_functional)
  have eq: "finite_pattern_substitute (resolution_substitution \<theta>) ?g=finite_exact_term_pattern t"
    using gvalue resolution_value_exact[of \<theta> ?g] by simp
  have scope: "finite_pattern_variables ?g |\<subseteq>| finite_pattern_variables ?g" by (rule order.refl)
  have inst: "finite_pattern_instance V ?g t" unfolding V_def by (rule resolution_ground_instance[OF gformed scope eq])
  have keep: "ffilter (\<lambda>x. fst x |\<in>| finite_pattern_variables ?g) V=V"
    unfolding fset_eq_iff split_paired_All by (simp add: V_def finite_ground_bindings_member)
  have M: "finite_matching_bindings ?g t=V"
    using finite_matching_bindings_instance[OF functional inst] keep by simp
  have valuation: "finite_query_valuation W V (query_element q)=\<theta> (query_element q)"
  proof (cases "finite_relation_option W (query_element q)")
    case (Some u)
    then show ?thesis using agree[OF finite_relation_option_member[OF Some]] by (simp add: finite_query_valuation_def)
  next
    case None
    have "finite_pattern_variables (finite_query_substitution W (query_element q)) |\<subseteq>| finite_pattern_variables ?g"
      unfolding finite_query_pattern_def by (rule finite_substitute_variables_member[OF element])
    then have "query_element q |\<in>| finite_pattern_variables ?g" using None by (simp add: finite_query_substitution_def)
    then have "(query_element q,\<theta> (query_element q)) |\<in>| V" by (simp add: V_def)
    then show ?thesis using None by (simp add: finite_query_valuation_def finite_binding_valuation_member[OF functional])
  qed
  show ?thesis using functional inst valuation by (simp add: finite_query_element_def M Let_def)
qed

section \<open>A query's answers: the instances its search finds, each resolved as a ground call\<close>

text \<open>
  The query's search starts at its goal, the equations' values substituted and the rest of its variables the
  query's own (@{text finite_query_variable}), over the lifted program. Every root call a successful branch
  ends with must be ground; each is resolved again as a ground call of the program by R3's
  @{const finite_program_resolution}, so the certificate an answer carries is one the finite proof checker
  accepted at that call in the program itself. An instance refuted is no answer; one unresolved, a diagnosis of the
  search, or a root call left open makes the query incomplete, and no answers are returned.
\<close>

definition finite_query_variable :: "'v \<Rightarrow> ('s,'a+'v) resolution_variable" where
  "finite_query_variable v=(([],True),Inr v)"

definition finite_query_search :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 'd \<Rightarrow>
    ('s,'a+'v) resolution_variable finite_term_pattern \<Rightarrow> ('a+'v,'s,'d,'c) resolution_outcome" where
  "finite_query_search P n d p=
    finite_resolution_search no_witness_construction (finite_query_program P) n (finite_pattern_state d p)"

definition finite_root_calls :: "('a,'s,'d,'c) resolution_outcome \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern fset" where
  "finite_root_calls R=ffUnion (fimage (\<lambda>st. fimage resolution_node_call
    (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))) (resolution_found R))"

definition finite_query_instances :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'d,'v) collection_query \<Rightarrow> ('v\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term list option" where
  "finite_query_instances P n q W=(let R=finite_query_search P n (query_site q)
      (map_finite_term_pattern finite_query_variable (finite_query_pattern q W)); C=finite_root_calls R in
    if resolution_diagnoses R={||} \<and> fBall C (\<lambda>c. finite_pattern_variables c={||})
    then Some (map unordered_factor_term (sorted_list_of_fset (fimage (Ordered_Factor_Term \<circ> finite_residual_term) C)))
    else None)"

fun finite_resolution_unresolved :: "('a,'s,'d,'c) finite_resolution_result \<Rightarrow> bool" where
  "finite_resolution_unresolved (Finite_Unresolved D)=True"
| "finite_resolution_unresolved r=False"

type_synonym ('a,'s,'c) query_answer = "finite_factor_term\<times>finite_factor_term\<times>('a,'s,'c) finite_schema_proof fset"

definition finite_query_answer :: "('a,'d,'v) collection_query \<Rightarrow> ('v\<times>finite_factor_term) fset \<Rightarrow>
    finite_factor_term\<times>('a,'s,'d,'c) finite_resolution_result \<Rightarrow> ('a,'s,'c) query_answer list" where
  "finite_query_answer q W z=(case snd z of Finite_Resolved Cs \<Rightarrow>
      (case finite_query_element q W (fst z) of Some e \<Rightarrow> [(e,fst z,Cs)] | None \<Rightarrow> [])
    | _ \<Rightarrow> [])"

definition finite_query_answers :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'d,'v) collection_query \<Rightarrow> ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow>
    ('a,'s,'c) query_answer list option" where
  "finite_query_answers P n q B E=(case finite_query_inputs q B E of None \<Rightarrow> None | Some ts \<Rightarrow>
    if \<not> finite_query_formed q ts then None else (case finite_inputs_matching ts of None \<Rightarrow> Some [] | Some W \<Rightarrow>
      (case finite_query_instances P n q W of None \<Rightarrow> None | Some Ts \<Rightarrow>
        let rs=map (\<lambda>t. (t,finite_program_resolution no_witness_construction P (query_site q) t n)) Ts in
        if list_ex (\<lambda>z. finite_resolution_unresolved (snd z)) rs then None
        else Some (concat (map (finite_query_answer q W) rs)))))"

lemma finite_query_answer_member:
  "x \<in> set (finite_query_answer q W (t,r)) \<longleftrightarrow>
    (\<exists>e Cs. x=(e,t,Cs) \<and> r=Finite_Resolved Cs \<and> finite_query_element q W t=Some e)"
  by (cases r) (auto simp: finite_query_answer_def split: option.splits)

lemma finite_query_answers_member:
  assumes answers: "finite_query_answers P n q B E=Some A" and member: "(e,t,Cs) \<in> set A"
  obtains ts W where "finite_query_inputs q B E=Some ts" "finite_query_formed q ts" "finite_inputs_matching ts=Some W"
    "finite_query_element q W t=Some e"
    "finite_program_resolution no_witness_construction P (query_site q) t n=Finite_Resolved Cs"
proof -
  obtain ts where inputs: "finite_query_inputs q B E=Some ts"
    using answers by (cases "finite_query_inputs q B E") (simp_all add: finite_query_answers_def)
  have formed: "finite_query_formed q ts" using answers inputs by (auto simp: finite_query_answers_def split: if_splits)
  obtain W where matching: "finite_inputs_matching ts=Some W"
    using answers inputs formed member by (cases "finite_inputs_matching ts") (auto simp: finite_query_answers_def split: if_splits)
  obtain Ts where instances: "finite_query_instances P n q W=Some Ts"
    using answers inputs formed matching
    by (cases "finite_query_instances P n q W") (auto simp: finite_query_answers_def split: if_splits)
  have "A=concat (map (finite_query_answer q W)
      (map (\<lambda>t. (t,finite_program_resolution no_witness_construction P (query_site q) t n)) Ts))"
    using answers inputs formed matching instances by (auto simp: finite_query_answers_def Let_def split: if_splits)
  then obtain t' where "t' \<in> set Ts" and "(e,t,Cs) \<in> set (finite_query_answer q W
      (t',finite_program_resolution no_witness_construction P (query_site q) t' n))"
    using member by auto
  then have "finite_query_element q W t=Some e"
    "finite_program_resolution no_witness_construction P (query_site q) t n=Finite_Resolved Cs"
    by (auto simp: finite_query_answer_member)
  then show ?thesis using that inputs formed matching by blast
qed

lemma finite_query_checked_holds:
  assumes inputs: "finite_query_inputs q B E=Some ts" and formed: "finite_query_formed q ts"
    and matching: "finite_inputs_matching ts=Some W" and element: "finite_query_element q W t=Some e"
    and true: "(query_site q,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  shows "finite_query_holds P q B E e" "finite_term_formed e"
proof -
  have functional: "finite_relation_functional W" by (rule finite_inputs_matching_some(1)[OF matching])
  obtain M where e: "finite_query_valuation W M (query_element q)=e"
    and goal: "resolution_value (finite_query_valuation W M) (query_goal q)=t"
    and inst: "\<forall>p u. finite_pattern_instance W p u \<longrightarrow> resolution_value (finite_query_valuation W M) p=u"
    by (rule finite_query_element_sound[OF functional element])
  have evaluated: "\<forall>(u,p)\<in>set ts. resolution_value (finite_query_valuation W M) p=u"
    using inst finite_inputs_matching_some(2)[OF matching] by blast
  show "finite_query_holds P q B E e"
    unfolding finite_query_holds_def using inputs e evaluated goal true by blast
  have "finite_term_formed t" by (rule finite_true_call_formed(2)[OF true])
  moreover have "query_element q |\<in>| finite_pattern_variables (query_goal q)"
    using formed by (simp add: finite_query_formed_def)
  ultimately show "finite_term_formed e"
    using resolution_value_variable_formed[of "finite_query_valuation W M" "query_goal q"] goal e by blast
qed

text \<open>(1), soundness: every answer's certificates are accepted at its instance and its element is one the query holds at.\<close>

theorem finite_query_answers_sound:
  assumes answers: "finite_query_answers P n q B E=Some A" and member: "(e,t,Cs) \<in> set A"
  shows "Cs\<noteq>{||}" "fBall Cs (\<lambda>p. finite_checks_schema_proof P p (query_site q) t)"
    "finite_query_holds P q B E e" "finite_term_formed e"
proof -
  obtain ts W where inputs: "finite_query_inputs q B E=Some ts" and formed: "finite_query_formed q ts"
    and matching: "finite_inputs_matching ts=Some W" and element: "finite_query_element q W t=Some e"
    and resolved: "finite_program_resolution no_witness_construction P (query_site q) t n=Finite_Resolved Cs"
    by (rule finite_query_answers_member[OF answers member])
  show "Cs\<noteq>{||}" by (rule finite_program_resolution_sound(1)[OF resolved])
  show "fBall Cs (\<lambda>p. finite_checks_schema_proof P p (query_site q) t)"
    using finite_program_resolution_accepted[OF resolved] by blast
  have true: "(query_site q,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    by (rule finite_program_resolution_sound(2)[OF resolved])
  show "finite_query_holds P q B E e" "finite_term_formed e"
    by (rule finite_query_checked_holds[OF inputs formed matching element true])+
qed

section \<open>The lifting a query's completeness rests on\<close>

text \<open>
  A query is complete when its search keeps the branch of every true instance of its goal. R4's lifting at a
  pattern root (@{text finite_resolution_pattern_lifting}) gives it at the lifted program, whose variables are all
  @{const Inl} while the query's are @{const Inr}, for every program.
\<close>

lemma finite_query_program_variables:
  assumes x: "x |\<in>| finite_program_variables (finite_query_program P)"
  shows "\<exists>a. x=Inl a"
proof -
  have pattern: "\<exists>a. y=Inl a" if "y |\<in>| finite_pattern_variables (map_finite_term_pattern Inl p)" for y p
    using that by (auto simp: finite_pattern_variables_map)
  have schema: "\<exists>a. y=Inl a" if "y |\<in>| finite_schema_variables (finite_rename_schema Inl id id S)" for y S
    using that by (auto simp: finite_schema_variables_correct finite_rename_schema_correct renamed_schema_variables)
  show ?thesis using x unfolding finite_program_variables_def finite_query_program_def
    by (auto simp: resolution_fset_simps dest!: pattern schema)
qed

theorem finite_query_search_lifting:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and p :: "('s,'a+'v) resolution_variable finite_term_pattern"
  assumes formed: "finite_pattern_formed p" and own: "\<And>z. z |\<in>| finite_pattern_variables p \<Longrightarrow> \<exists>v. snd z=Inr v"
    and holds: "(d,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
  shows "resolution_diagnoses (finite_query_search P n d p)\<noteq>{||} \<or>
    (\<exists>c \<theta>'. c |\<in>| finite_root_calls (finite_query_search P n d p) \<and> resolution_value \<theta>' c=resolution_value \<theta> p)"
proof -
  have Pf: "finite_system_formed P" by (rule finite_true_call_formed(1)[OF holds])
  have Qf: "finite_system_formed (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system)"
    by (rule finite_query_program_formed[OF Pf])
  have Qholds: "(d,decode_finite_term (resolution_value \<theta> p)) \<in>
      positive_meaning (decode_finite_system (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system))"
    by (subst finite_query_program_meaning[OF Pf]) (rule holds)
  have foreign: "\<And>z. z |\<in>| finite_pattern_variables p \<Longrightarrow>
      snd z |\<notin>| finite_program_variables (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system)"
    using own finite_query_program_variables by fastforce
  let ?R="finite_resolution_search no_witness_construction
    (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) n (finite_pattern_state d p)"
  have lift: "resolution_diagnoses ?R\<noteq>{||} \<or> (\<exists>st nd \<theta>' \<rho>. st |\<in>| resolution_found ?R \<and>
      nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[] \<and> resolution_node_site nd=d \<and>
      resolution_node_call nd=finite_pattern_substitute \<rho> p \<and>
      resolution_value \<theta>' (resolution_node_call nd)=resolution_value \<theta> p)"
    using finite_resolution_pattern_lifting[OF Qf formed foreign Qholds, of n] by simp
  from lift show ?thesis
  proof (elim disjE exE conjE)
    assume "resolution_diagnoses (finite_resolution_search no_witness_construction (finite_query_program P) n
      (finite_pattern_state d p))\<noteq>{||}"
    then show ?thesis by (simp add: finite_query_search_def)
  next
    fix st nd \<theta>' \<rho>
    assume st: "st |\<in>| resolution_found (finite_resolution_search no_witness_construction (finite_query_program P) n
        (finite_pattern_state d p))"
      and nd: "nd |\<in>| resolution_nodes st" and pos: "resolution_node_position nd=[]"
      and site: "resolution_node_site nd=d" and call: "resolution_node_call nd=finite_pattern_substitute \<rho> p"
      and valued: "resolution_value \<theta>' (resolution_node_call nd)=resolution_value \<theta> p"
    have "resolution_node_call nd |\<in>| finite_root_calls (finite_query_search P n d p)"
      unfolding finite_query_search_def finite_root_calls_def using st nd pos by (force simp: resolution_fset_simps)
    then show ?thesis using valued by blast
  qed
qed

text \<open>(1), completeness: a complete query answers every element it holds at.\<close>

theorem finite_query_answers_complete:
  fixes q :: "('a,'d,'v) collection_query" and P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes answers: "finite_query_answers P n q B E=Some A" and holds: "finite_query_holds P q B E e"
  shows "\<exists>t Cs. (e,t,Cs) \<in> set A"
proof -
  obtain ts \<theta> where inputs: "finite_query_inputs q B E=Some ts" and elem: "\<theta> (query_element q)=e"
    and evaluated: "\<forall>(t,p)\<in>set ts. resolution_value \<theta> p=t"
    and true: "(query_site q,decode_finite_term (resolution_value \<theta> (query_goal q))) \<in> positive_meaning (decode_finite_system P)"
    using holds unfolding finite_query_holds_def by blast
  have formed: "finite_query_formed q ts" using answers inputs by (auto simp: finite_query_answers_def split: if_splits)
  obtain W where matching: "finite_inputs_matching ts=Some W" and agree: "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
    by (rule finite_inputs_matching_complete[of ts \<theta>]) (use evaluated formed in \<open>auto simp: finite_query_formed_def list_all_iff\<close>)
  define t0 where "t0=resolution_value \<theta> (query_goal q)"
  have tf: "finite_term_formed t0" unfolding t0_def by (rule finite_true_call_formed(2)[OF true])
  have gformed: "finite_pattern_formed (query_goal q)" and gelem: "query_element q |\<in>| finite_pattern_variables (query_goal q)"
    using formed by (simp_all add: finite_query_formed_def)
  have element: "finite_query_element q W t0=Some e"
    using finite_query_element_complete[of W \<theta> q t0, OF agree gformed gelem t0_def[symmetric] tf] elem by simp
  let ?g="finite_query_pattern q W"
  let ?gs="map_finite_term_pattern finite_query_variable ?g :: ('s,'a+'v) resolution_variable finite_term_pattern"
  define \<theta>s where "\<theta>s=(\<lambda>z::('s,'a+'v) resolution_variable. case snd z of Inr v \<Rightarrow> \<theta> v | Inl a \<Rightarrow> Finite_Payload [])"
  have comp: "\<theta>s \<circ> finite_query_variable=\<theta>" by (rule ext) (simp add: \<theta>s_def finite_query_variable_def)
  have gsvalue: "resolution_value \<theta>s ?gs=t0"
    using finite_query_pattern_value[of W \<theta> q, OF agree] by (simp add: resolution_value_rename comp t0_def)
  have gsformed: "finite_pattern_formed ?gs"
    using finite_query_pattern_formed[of W \<theta> q, OF agree gformed] tf by (simp add: t0_def)
  have gsvars: "\<And>z. z |\<in>| finite_pattern_variables ?gs \<Longrightarrow> \<exists>v. snd z=Inr v"
    by (auto simp: finite_pattern_variables_map finite_query_variable_def)
  have Ptrue: "(query_site q,decode_finite_term (resolution_value \<theta>s ?gs)) \<in> positive_meaning (decode_finite_system P)"
    using true by (simp add: gsvalue t0_def)
  have lifted: "resolution_diagnoses (finite_query_search P n (query_site q) ?gs)\<noteq>{||} \<or>
      (\<exists>c \<theta>'. c |\<in>| finite_root_calls (finite_query_search P n (query_site q) ?gs) \<and> resolution_value \<theta>' c=t0)"
    using finite_query_search_lifting[OF gsformed gsvars Ptrue, of n] by (simp only: gsvalue)
  obtain Ts where instances: "finite_query_instances P n q W=Some Ts"
    using answers inputs formed matching
    by (cases "finite_query_instances P n q W") (auto simp: finite_query_answers_def split: if_splits)
  have clean: "resolution_diagnoses (finite_query_search P n (query_site q) ?gs)={||}"
    and ground: "fBall (finite_root_calls (finite_query_search P n (query_site q) ?gs)) (\<lambda>c. finite_pattern_variables c={||})"
    and Ts: "Ts=map unordered_factor_term (sorted_list_of_fset (fimage (Ordered_Factor_Term \<circ> finite_residual_term)
      (finite_root_calls (finite_query_search P n (query_site q) ?gs))))"
    using instances by (simp_all add: finite_query_instances_def Let_def split: if_splits)
  obtain c \<theta>' where c: "c |\<in>| finite_root_calls (finite_query_search P n (query_site q) ?gs)"
    and cvalue: "resolution_value \<theta>' c=t0"
    using lifted clean by blast
  have "finite_residual_term c=t0" using resolution_value_ground_pattern[of c \<theta>'] ground c cvalue by auto
  then have t0mem: "t0 \<in> set Ts" unfolding Ts using c by (force simp: fimage_iff)
  define r where "r=finite_program_resolution no_witness_construction P (query_site q) t0 n"
  have A: "A=concat (map (finite_query_answer q W)
      (map (\<lambda>t. (t,finite_program_resolution no_witness_construction P (query_site q) t n)) Ts))"
    and settled: "\<not> list_ex (\<lambda>z. finite_resolution_unresolved (snd z))
      (map (\<lambda>t. (t,finite_program_resolution no_witness_construction P (query_site q) t n)) Ts)"
    using answers inputs formed matching instances by (auto simp: finite_query_answers_def Let_def split: if_splits)
  show ?thesis
  proof (cases r)
    case (Finite_Resolved Cs)
    have "(e,t0,Cs) \<in> set (finite_query_answer q W (t0,r))" using Finite_Resolved element
      by (simp add: finite_query_answer_member)
    then show ?thesis using t0mem unfolding A r_def by force
  next
    case Finite_Refuted
    then show ?thesis using finite_program_resolution_refutation_exact[of P "query_site q" t0 n] true
      by (simp add: r_def t0_def)
  next
    case (Finite_Unresolved D)
    then show ?thesis using settled t0mem by (force simp: list_ex_iff r_def)
  qed
qed


section \<open>The iteration of a collection\<close>

text \<open>
  A collection is iterated over answers given as lists: the base answers, then, round after round, the step
  answers at each element the last round added, until a round adds none. An answer whose key no element has is
  added; one whose key an element has is dropped when it equals the first such element or the identity check
  identifies them, and is added with the pair recorded as a conflict when the check refutes their identity; an
  unresolved identity check, a missing answer list or a round left over at the bound gives nothing. Each element
  keeps the element its step was taken at (a base answer none) and the data of the answer that brought it. Each
  round's answers are listed by an order of their elements, a presentation no check reads. This part of the
  iteration is stated for any answers, keys and identity checks.
\<close>

definition finite_collect_covered :: "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow> ('e\<times>'x) list \<Rightarrow> 'e \<Rightarrow> bool" where
  "finite_collect_covered key ident es e \<longleftrightarrow>
    (\<exists>x\<in>set es. key (fst x)=key e \<and> (fst x=e \<or> ident (fst x) e=Some True))"

lemma finite_collect_covered_append:
  "finite_collect_covered key ident es e \<Longrightarrow> finite_collect_covered key ident (es@ad) e"
  by (auto simp: finite_collect_covered_def)

definition finite_collect_conflicts ::
    "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow> ('e\<times>'x) list \<Rightarrow> ('e\<times>'e) list \<Rightarrow> bool" where
  "finite_collect_conflicts key ident es cs \<longleftrightarrow> (\<forall>z\<in>set cs. fst z \<in> fst ` set es \<and> snd z \<in> fst ` set es \<and>
    key (fst z)=key (snd z) \<and> fst z\<noteq>snd z \<and> ident (fst z) (snd z)=Some False)"

lemma finite_collect_conflicts_append:
  "finite_collect_conflicts key ident es cs \<Longrightarrow> finite_collect_conflicts key ident (es@ad) cs"
  unfolding finite_collect_conflicts_def by auto

lemma finite_collect_covered_added: "finite_collect_covered key ident (es@[a]) (fst a)"
  unfolding finite_collect_covered_def by simp

definition finite_collect_place :: "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow>
    ('e\<times>'x) list\<times>('e\<times>'e) list \<Rightarrow> 'e\<times>'x \<Rightarrow> (('e\<times>'x) list\<times>('e\<times>'e) list) option" where
  "finite_collect_place key ident s a=(case find (\<lambda>x. key (fst x)=key (fst a)) (fst s) of
      None \<Rightarrow> Some (fst s@[a],snd s)
    | Some x \<Rightarrow> if fst x=fst a then Some s else (case ident (fst x) (fst a) of
        None \<Rightarrow> None
      | Some b \<Rightarrow> if b then Some s else Some (fst s@[a],snd s@[(fst x,fst a)])))"

lemma finite_collect_place_some:
  assumes insert: "finite_collect_place key ident (es,cs) a=Some (es',cs')"
    and conflicts: "finite_collect_conflicts key ident es cs"
  shows "(\<exists>ad. es'=es@ad \<and> set ad \<subseteq> {a}) \<and> finite_collect_covered key ident es' (fst a) \<and>
    finite_collect_conflicts key ident es' cs'"
proof (cases "find (\<lambda>x. key (fst x)=key (fst a)) es")
  case None
  then have eq: "es'=es@[a]" "cs'=cs" using insert by (simp_all add: finite_collect_place_def)
  show ?thesis unfolding eq using finite_collect_covered_added finite_collect_conflicts_append[OF conflicts]
    by (intro conjI exI[of _ "[a]"]) simp_all
next
  case (Some x)
  note found=Some
  have x: "x \<in> set es" "key (fst x)=key (fst a)" using found by (auto simp: find_Some_iff)
  show ?thesis
  proof (cases "fst x=fst a")
    case True
    then have eq: "es'=es" "cs'=cs" using insert found by (simp_all add: finite_collect_place_def)
    have cov: "finite_collect_covered key ident es (fst a)" unfolding finite_collect_covered_def using x True by blast
    show ?thesis unfolding eq using cov conflicts by (intro conjI exI[of _ "[]"]) simp_all
  next
    case different: False
    show ?thesis
    proof (cases "ident (fst x) (fst a)")
      case None
      then show ?thesis using insert found different by (simp add: finite_collect_place_def)
    next
      case (Some b)
      note checked=Some
      show ?thesis
      proof (cases b)
        case True
        then have eq: "es'=es" "cs'=cs" using insert found different checked by (simp_all add: finite_collect_place_def)
        have same: "ident (fst x) (fst a)=Some True" using checked True by simp
        have cov: "finite_collect_covered key ident es (fst a)"
          unfolding finite_collect_covered_def using x same by blast
        show ?thesis unfolding eq using cov conflicts by (intro conjI exI[of _ "[]"]) simp_all
      next
        case False
        then have eq: "es'=es@[a]" "cs'=cs@[(fst x,fst a)]"
          using insert found different checked by (simp_all add: finite_collect_place_def)
        have fx: "fst x \<in> fst ` set (es@[a])" by (rule rev_image_eqI[of x]) (use x(1) in simp_all)
        have fa: "fst a \<in> fst ` set (es@[a])" by (rule rev_image_eqI[of a]) simp_all
        have new: "finite_collect_conflicts key ident (es@[a]) [(fst x,fst a)]"
          unfolding finite_collect_conflicts_def using fx fa x(2) different checked False by simp
        have conf: "finite_collect_conflicts key ident (es@[a]) (cs@[(fst x,fst a)])"
          using new finite_collect_conflicts_append[OF conflicts, of "[a]"]
          unfolding finite_collect_conflicts_def by (simp only: set_append ball_Un)
        show ?thesis unfolding eq using finite_collect_covered_added conf
          by (intro conjI exI[of _ "[a]"]) simp_all
      qed
    qed
  qed
qed

text \<open>An answer whose element is already an element is dropped; any other is placed by its key.\<close>

definition finite_collect_insert :: "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow>
    ('e\<times>'x) list\<times>('e\<times>'e) list \<Rightarrow> 'e\<times>'x \<Rightarrow> (('e\<times>'x) list\<times>('e\<times>'e) list) option" where
  "finite_collect_insert key ident s a=(if fst a \<in> set (map fst (fst s)) then Some s else finite_collect_place key ident s a)"

lemma finite_collect_insert_some:
  assumes insert: "finite_collect_insert key ident (es,cs) a=Some (es',cs')"
    and conflicts: "finite_collect_conflicts key ident es cs"
  shows "(\<exists>ad. es'=es@ad \<and> set ad \<subseteq> {a}) \<and> finite_collect_covered key ident es' (fst a) \<and>
    finite_collect_conflicts key ident es' cs'"
proof (cases "fst a \<in> set (map fst es)")
  case True
  then have eq: "es'=es" "cs'=cs" using insert by (simp_all add: finite_collect_insert_def)
  obtain x where x: "x \<in> set es" "fst x=fst a" using True by (auto simp: image_iff)
  have cov: "finite_collect_covered key ident es (fst a)"
    unfolding finite_collect_covered_def by (rule bexI[of _ x]) (simp_all add: x)
  show ?thesis unfolding eq using cov conflicts by (intro conjI exI[of _ "[]"]) simp_all
next
  case False
  then have "finite_collect_place key ident (es,cs) a=Some (es',cs')" using insert by (simp add: finite_collect_insert_def)
  then show ?thesis by (rule finite_collect_place_some[OF _ conflicts])
qed

definition finite_collect_round :: "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow>
    ('e\<times>'x) list\<times>('e\<times>'e) list \<Rightarrow> ('e\<times>'x) list \<Rightarrow> (('e\<times>'x) list\<times>('e\<times>'e) list) option" where
  "finite_collect_round key ident s A=fold (\<lambda>a r. Option.bind r (\<lambda>s. finite_collect_insert key ident s a)) A (Some s)"

lemma finite_collect_fold_none:
  "fold (\<lambda>a r. Option.bind r (\<lambda>s. finite_collect_insert key ident s a)) A None=None"
  by (induction A) simp_all

lemma finite_collect_round_some:
  "finite_collect_round key ident (es,cs) A=Some (es',cs') \<Longrightarrow> finite_collect_conflicts key ident es cs \<Longrightarrow>
    (\<exists>ad. es'=es@ad \<and> set ad \<subseteq> set A) \<and> (\<forall>a\<in>set A. finite_collect_covered key ident es' (fst a)) \<and>
    finite_collect_conflicts key ident es' cs'"
proof (induction A arbitrary: es cs)
  case Nil
  then show ?case by (simp add: finite_collect_round_def)
next
  case (Cons a A)
  show ?case
  proof (cases "finite_collect_insert key ident (es,cs) a")
    case None
    then show ?thesis using Cons.prems(1) by (simp add: finite_collect_round_def finite_collect_fold_none)
  next
    case (Some s1)
    obtain es1 cs1 where s1: "s1=(es1,cs1)" by (cases s1)
    have first: "(\<exists>ad. es1=es@ad \<and> set ad \<subseteq> {a}) \<and> finite_collect_covered key ident es1 (fst a) \<and>
        finite_collect_conflicts key ident es1 cs1"
      by (rule finite_collect_insert_some[OF Some[unfolded s1] Cons.prems(2)])
    have rest: "finite_collect_round key ident (es1,cs1) A=Some (es',cs')"
      using Cons.prems(1) Some s1 by (simp add: finite_collect_round_def)
    have later: "(\<exists>ad. es'=es1@ad \<and> set ad \<subseteq> set A) \<and> (\<forall>a\<in>set A. finite_collect_covered key ident es' (fst a)) \<and>
        finite_collect_conflicts key ident es' cs'"
      using Cons.IH[OF rest] first by blast
    obtain ad1 ad2 where ad: "es1=es@ad1" "set ad1 \<subseteq> {a}" "es'=es1@ad2" "set ad2 \<subseteq> set A"
      using first later by blast
    have "finite_collect_covered key ident es' (fst a)"
      using first ad(3) finite_collect_covered_append[of key ident es1 "fst a" ad2] by simp
    then show ?thesis using later ad by auto
  qed
qed

lemma those_map_some:
  "those (map g F)=Some As \<Longrightarrow> (\<forall>f\<in>set F. \<exists>L\<in>set As. g f=Some L) \<and> (\<forall>L\<in>set As. \<exists>f\<in>set F. g f=Some L)"
proof (induction F arbitrary: As)
  case Nil
  then show ?case by simp
next
  case (Cons f F)
  obtain L As' where "g f=Some L" "those (map g F)=Some As'" "As=L#As'"
    using Cons.prems by (auto split: option.splits)
  then show ?case using Cons.IH by auto
qed

fun finite_collect_steps :: "('e \<Rightarrow> 'o::linorder) \<Rightarrow> ('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow>
    ('e \<Rightarrow> ('e\<times>'j) list option) \<Rightarrow> nat \<Rightarrow> ('e\<times>'e option\<times>'j) list\<times>('e\<times>'e) list \<Rightarrow> 'e list \<Rightarrow>
    (('e\<times>'e option\<times>'j) list\<times>('e\<times>'e) list) option" where
  "finite_collect_steps ord key ident step 0 s F=(if F=[] then Some s else None)"
| "finite_collect_steps ord key ident step (Suc n) s F=(if F=[] then Some s else
    (case those (map (\<lambda>f. map_option (map (\<lambda>(e,j). (e,Some f,j))) (step f)) F) of None \<Rightarrow> None
    | Some As \<Rightarrow> (case finite_collect_round key ident s (sort_key (ord \<circ> fst) (concat As)) of None \<Rightarrow> None
      | Some s' \<Rightarrow> finite_collect_steps ord key ident step n s' (map fst (drop (length (fst s)) (fst s'))))))"

definition finite_collect :: "('e \<Rightarrow> 'o::linorder) \<Rightarrow> ('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow>
    ('e\<times>'j) list option \<Rightarrow> ('e \<Rightarrow> ('e\<times>'j) list option) \<Rightarrow> nat \<Rightarrow> (('e\<times>'e option\<times>'j) list\<times>('e\<times>'e) list) option" where
  "finite_collect ord key ident base step n=(case base of None \<Rightarrow> None | Some A \<Rightarrow>
    (case finite_collect_round key ident ([],[]) (sort_key (ord \<circ> fst) (map (\<lambda>(e,j). (e,None,j)) A)) of None \<Rightarrow> None
    | Some s \<Rightarrow> finite_collect_steps ord key ident step n s (map fst (fst s))))"

definition finite_collect_origin :: "('e\<times>'j) list \<Rightarrow> ('e \<Rightarrow> ('e\<times>'j) list option) \<Rightarrow> 'e\<times>'e option\<times>'j \<Rightarrow> bool" where
  "finite_collect_origin A step x \<longleftrightarrow> (case fst (snd x) of None \<Rightarrow> (fst x,snd (snd x)) \<in> set A
    | Some f \<Rightarrow> (\<exists>L. step f=Some L \<and> (fst x,snd (snd x)) \<in> set L))"

definition finite_collect_invariant :: "('e \<Rightarrow> 'k) \<Rightarrow> ('e \<Rightarrow> 'e \<Rightarrow> bool option) \<Rightarrow> ('e\<times>'j) list \<Rightarrow>
    ('e \<Rightarrow> ('e\<times>'j) list option) \<Rightarrow> ('e\<times>'e option\<times>'j) list \<Rightarrow> ('e\<times>'e) list \<Rightarrow> 'e list \<Rightarrow> bool" where
  "finite_collect_invariant key ident A step es cs F \<longleftrightarrow>
    (\<forall>x\<in>set es. finite_collect_origin A step x) \<and>
    (\<forall>k<length es. \<forall>f. fst (snd (es!k))=Some f \<longrightarrow> f \<in> fst ` set (take k es)) \<and>
    set F \<subseteq> fst ` set es \<and>
    (\<forall>a\<in>set A. finite_collect_covered key ident es (fst a)) \<and>
    (\<forall>x\<in>set es. fst x \<notin> set F \<longrightarrow>
      (\<exists>L. step (fst x)=Some L \<and> (\<forall>a\<in>set L. finite_collect_covered key ident es (fst a)))) \<and>
    finite_collect_conflicts key ident es cs"

lemma finite_collect_steps_invariant:
  "finite_collect_invariant key ident A step es cs F \<Longrightarrow>
    finite_collect_steps ord key ident step n (es,cs) F=Some (es',cs') \<Longrightarrow>
    finite_collect_invariant key ident A step es' cs' []"
proof (induction n arbitrary: es cs F)
  case 0
  then show ?case by (simp split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "F=[]")
    case True
    then show ?thesis using Suc.prems by simp
  next
    case False
    let ?tag="\<lambda>f. map (\<lambda>(e,j). (e,Some f,j))"
    obtain As where As: "those (map (\<lambda>f. map_option (?tag f) (step f)) F)=Some As"
      using Suc.prems(2) False by (auto split: option.splits)
    define R where "R=sort_key (ord \<circ> fst) (concat As)"
    obtain es1 cs1 where round: "finite_collect_round key ident (es,cs) R=Some (es1,cs1)"
      using Suc.prems(2) False As by (auto simp: R_def split: option.splits)
    have rest: "finite_collect_steps ord key ident step n (es1,cs1) (map fst (drop (length es) es1))=Some (es',cs')"
      using Suc.prems(2) False As round by (simp add: R_def)
    have inv: "\<forall>x\<in>set es. finite_collect_origin A step x"
      "\<forall>k<length es. \<forall>f. fst (snd (es!k))=Some f \<longrightarrow> f \<in> fst ` set (take k es)"
      "set F \<subseteq> fst ` set es" "\<forall>a\<in>set A. finite_collect_covered key ident es (fst a)"
      "\<forall>x\<in>set es. fst x \<notin> set F \<longrightarrow> (\<exists>L. step (fst x)=Some L \<and> (\<forall>a\<in>set L. finite_collect_covered key ident es (fst a)))"
      "finite_collect_conflicts key ident es cs"
      using Suc.prems(1) unfolding finite_collect_invariant_def by blast+
    obtain ad where es1: "es1=es@ad" and adR: "set ad \<subseteq> set R"
      and cov: "\<forall>a\<in>set R. finite_collect_covered key ident es1 (fst a)"
      and conf: "finite_collect_conflicts key ident es1 cs1"
      using finite_collect_round_some[OF round inv(6)] by blast
    have setR: "set R=set (concat As)" by (simp add: R_def)
    have parts: "\<forall>f\<in>set F. \<exists>L\<in>set As. map_option (?tag f) (step f)=Some L"
      "\<forall>L\<in>set As. \<exists>f\<in>set F. map_option (?tag f) (step f)=Some L"
      using those_map_some[OF As] by blast+
    have tagged: "\<exists>f\<in>set F. \<exists>L. step f=Some L \<and> fst (snd a)=Some f \<and> (fst a,snd (snd a)) \<in> set L"
      if aR: "a \<in> set R" for a
    proof -
      obtain L' where L': "L' \<in> set As" "a \<in> set L'" using aR setR by auto
      obtain f L where f: "f \<in> set F" "step f=Some L" "L'=?tag f L" using parts(2) L'(1) by fastforce
      show ?thesis using f L'(2) by (intro bexI[of _ f] exI[of _ L]) auto
    qed
    have stepped: "\<exists>L. step f=Some L \<and> (\<forall>a\<in>set L. finite_collect_covered key ident es1 (fst a))"
      if fF: "f \<in> set F" for f
    proof -
      obtain L' where L': "L' \<in> set As" "map_option (?tag f) (step f)=Some L'" using parts(1) fF by blast
      obtain L where L: "step f=Some L" "L'=?tag f L" using L'(2) by auto
      have "finite_collect_covered key ident es1 (fst a)" if "a \<in> set L" for a
      proof -
        have "(fst a,Some f,snd a) \<in> set R" using that L L'(1) setR by force
        then show ?thesis using cov by force
      qed
      then show ?thesis using L(1) by blast
    qed
    have drop: "drop (length es) es1=ad" by (simp add: es1)
    have "finite_collect_invariant key ident A step es1 cs1 (map fst ad)"
      unfolding finite_collect_invariant_def
    proof (intro conjI ballI allI impI)
      fix x assume "x \<in> set es1"
      then show "finite_collect_origin A step x"
      proof (cases "x \<in> set es")
        case True
        then show ?thesis using inv(1) by blast
      next
        case False
        then have "x \<in> set R" using \<open>x \<in> set es1\<close> es1 adR by auto
        then show ?thesis using tagged[of x] by (auto simp: finite_collect_origin_def)
      qed
    next
      fix k f assume k: "k<length es1" and src: "fst (snd (es1!k))=Some f"
      show "f \<in> fst ` set (take k es1)"
      proof (cases "k<length es")
        case True
        then show ?thesis using inv(2) src by (simp add: es1 nth_append)
      next
        case False
        then have "es1!k \<in> set ad" using k by (simp add: es1 nth_append)
        then have "es1!k \<in> set R" using adR by blast
        then obtain g where "g \<in> set F" "fst (snd (es1!k))=Some g" using tagged by blast
        then have "f \<in> fst ` set es" using src inv(3) by auto
        moreover have "set es \<subseteq> set (take k es1)" using False by (simp add: es1)
        ultimately show ?thesis by blast
      qed
    next
      show "set (map fst ad) \<subseteq> fst ` set es1" by (auto simp: es1)
    next
      fix a assume aA: "a \<in> set A"
      show "finite_collect_covered key ident es1 (fst a)"
        unfolding es1 by (rule finite_collect_covered_append) (use inv(4) aA in blast)
    next
      fix x assume x: "x \<in> set es1" and pending: "fst x \<notin> set (map fst ad)"
      have old: "x \<in> set es" using x pending es1 by auto
      show "\<exists>L. step (fst x)=Some L \<and> (\<forall>a\<in>set L. finite_collect_covered key ident es1 (fst a))"
      proof (cases "fst x \<in> set F")
        case True
        then show ?thesis using stepped by blast
      next
        case False
        then obtain L where L: "step (fst x)=Some L" "\<forall>a\<in>set L. finite_collect_covered key ident es (fst a)"
          using inv(5) old by blast
        have "\<forall>a\<in>set L. finite_collect_covered key ident es1 (fst a)"
          unfolding es1 using L(2) finite_collect_covered_append[of key ident es _ ad] by blast
        then show ?thesis using L(1) by (intro exI[of _ L] conjI)
      qed
    next
      show "finite_collect_conflicts key ident es1 cs1" by (rule conf)
    qed
    then show ?thesis using Suc.IH rest drop by simp
  qed
qed

theorem finite_collect_invariant_result:
  fixes A :: "('e\<times>'j) list"
  assumes collect: "finite_collect ord key ident (Some A) step n=Some (es,cs)"
  shows "finite_collect_invariant key ident A step es cs []"
proof -
  define R where "R=sort_key (ord \<circ> fst) (map (\<lambda>(e,j). (e,None::'e option,j)) A)"
  obtain s0 where round0: "finite_collect_round key ident ([],[]) R=Some s0"
  proof (cases "finite_collect_round key ident ([],[]) R")
    case None
    then show ?thesis using collect by (simp add: finite_collect_def R_def split: option.splits)
  next
    case (Some s)
    then show ?thesis by (rule that)
  qed
  obtain es0 cs0 where s0: "s0=(es0,cs0)" by (cases s0)
  have round: "finite_collect_round key ident ([],[]) R=Some (es0,cs0)" using round0 s0 by simp
  have steps: "finite_collect_steps ord key ident step n (es0,cs0) (map fst es0)=Some (es,cs)"
    using collect round by (simp add: finite_collect_def R_def)
  have empty: "finite_collect_conflicts key ident [] []" by (simp add: finite_collect_conflicts_def)
  obtain ad where es0: "es0=ad" "set ad \<subseteq> set R" and cov: "\<forall>a\<in>set R. finite_collect_covered key ident es0 (fst a)"
    and conf: "finite_collect_conflicts key ident es0 cs0"
    using finite_collect_round_some[OF round empty] by auto
  have setR: "set R=(\<lambda>(e,j). (e,None,j)) ` set A" by (simp add: R_def)
  have "finite_collect_invariant key ident A step es0 cs0 (map fst es0)"
    unfolding finite_collect_invariant_def
  proof (intro conjI ballI allI impI)
    fix x assume "x \<in> set es0"
    then show "finite_collect_origin A step x" using es0 setR by (auto simp: finite_collect_origin_def)
  next
    fix k f assume k: "k<length es0" and src: "fst (snd (es0!k))=Some f"
    have "es0!k \<in> (\<lambda>(e,j). (e,None,j)) ` set A" using es0 setR nth_mem[OF k] by blast
    then show "f \<in> fst ` set (take k es0)" using src by auto
  next
    show "set (map fst es0) \<subseteq> fst ` set es0" by auto
  next
    fix a assume "a \<in> set A"
    then have "(fst a,None,snd a) \<in> set R" using setR by force
    then show "finite_collect_covered key ident es0 (fst a)" using cov by force
  next
    fix x assume "x \<in> set es0" "fst x \<notin> set (map fst es0)"
    then show "\<exists>L. step (fst x)=Some L \<and> (\<forall>a\<in>set L. finite_collect_covered key ident es0 (fst a))" by auto
  qed (rule conf)
  then show ?thesis by (rule finite_collect_steps_invariant[OF _ steps])
qed

text \<open>Entries whose sources are earlier entries and whose answers are sound lie in the least closure.\<close>

lemma finite_sources_closure:
  assumes earlier: "\<And>k f. k<length es \<Longrightarrow> fst (snd (es!k))=Some f \<Longrightarrow> f \<in> fst ` set (take k es)"
    and based: "\<And>x. x \<in> set es \<Longrightarrow> fst (snd x)=None \<Longrightarrow> fst x \<in> Bs"
    and stepped: "\<And>x f. x \<in> set es \<Longrightarrow> fst (snd x)=Some f \<Longrightarrow> (f,fst x) \<in> Ss"
  shows "fst ` set es \<subseteq> Ss\<^sup>* `` Bs"
proof -
  have "fst (es!k) \<in> Ss\<^sup>* `` Bs" if "k<length es" for k
    using that
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases "fst (snd (es!k))")
      case None
      then show ?thesis using based[OF nth_mem[OF less.prems]] by blast
    next
      case (Some f)
      obtain y where y: "y \<in> set (take k es)" "f=fst y" using earlier[OF less.prems Some] by blast
      obtain i where i: "i<length (take k es)" "take k es!i=y" using y(1) by (auto simp: in_set_conv_nth)
      have ik: "i<k" "i<length es" "es!i=y" using i less.prems by auto
      have "f \<in> Ss\<^sup>* `` Bs" using less.IH[OF ik(1) ik(2)] ik(3) y(2) by simp
      moreover have "(f,fst (es!k)) \<in> Ss" by (rule stepped[OF nth_mem[OF less.prems] Some])
      ultimately show ?thesis by (auto intro: rtrancl_into_rtrancl)
    qed
  qed
  then have all: "\<And>k. k<length es \<Longrightarrow> fst (es!k) \<in> Ss\<^sup>* `` Bs" by blast
  show ?thesis
  proof
    fix y assume "y \<in> fst ` set es"
    then obtain x where x: "x \<in> set es" "y=fst x" by blast
    obtain k where k: "k<length es" "es!k=x" using x(1) by (auto simp: in_set_conv_nth)
    show "y \<in> Ss\<^sup>* `` Bs" using all[OF k(1)] k(2) x(2) by simp
  qed
qed

section \<open>The distinct keys of a collection with no conflict\<close>

text \<open>An element is added only under a new key or at a conflict, so a collection with no conflict has distinct keys.\<close>

lemma finite_collect_place_keys:
  assumes insert: "finite_collect_place key ident (es,cs) a=Some (es',cs')"
    and keys: "cs=[] \<longrightarrow> distinct (map (key\<circ>fst) es)"
  shows "cs'=[] \<longrightarrow> distinct (map (key\<circ>fst) es')"
proof (cases "find (\<lambda>x. key (fst x)=key (fst a)) es")
  case None
  then have eq: "es'=es@[a]" "cs'=cs" using insert by (simp_all add: finite_collect_place_def)
  have "key (fst a) \<notin> set (map (key\<circ>fst) es)" using None by (auto simp: find_None_iff)
  then show ?thesis using keys unfolding eq by simp
next
  case (Some x)
  note found=Some
  show ?thesis
  proof (cases "fst x=fst a")
    case True
    then have "es'=es" "cs'=cs" using insert found by (simp_all add: finite_collect_place_def)
    then show ?thesis using keys by simp
  next
    case different: False
    show ?thesis
    proof (cases "ident (fst x) (fst a)")
      case None
      then show ?thesis using insert found different by (simp add: finite_collect_place_def)
    next
      case (Some b)
      note checked=Some
      show ?thesis
      proof (cases b)
        case True
        then have "es'=es" "cs'=cs" using insert found different checked by (simp_all add: finite_collect_place_def)
        then show ?thesis using keys by simp
      next
        case False
        then have "cs'=cs@[(fst x,fst a)]" using insert found different checked by (simp add: finite_collect_place_def)
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma finite_collect_insert_keys:
  assumes insert: "finite_collect_insert key ident (es,cs) a=Some (es',cs')"
    and keys: "cs=[] \<longrightarrow> distinct (map (key\<circ>fst) es)"
  shows "cs'=[] \<longrightarrow> distinct (map (key\<circ>fst) es')"
proof (cases "fst a \<in> set (map fst es)")
  case True
  then have "es'=es" "cs'=cs" using insert by (simp_all add: finite_collect_insert_def)
  then show ?thesis using keys by simp
next
  case False
  then have "finite_collect_place key ident (es,cs) a=Some (es',cs')" using insert by (simp add: finite_collect_insert_def)
  then show ?thesis by (rule finite_collect_place_keys[OF _ keys])
qed

lemma finite_collect_round_keys:
  "finite_collect_round key ident (es,cs) A=Some (es',cs') \<Longrightarrow> (cs=[] \<longrightarrow> distinct (map (key\<circ>fst) es)) \<Longrightarrow>
    cs'=[] \<longrightarrow> distinct (map (key\<circ>fst) es')"
proof (induction A arbitrary: es cs)
  case Nil
  then show ?case by (simp add: finite_collect_round_def)
next
  case (Cons a A)
  show ?case
  proof (cases "finite_collect_insert key ident (es,cs) a")
    case None
    then show ?thesis using Cons.prems(1) by (simp add: finite_collect_round_def finite_collect_fold_none)
  next
    case (Some s1)
    obtain es1 cs1 where s1: "s1=(es1,cs1)" by (cases s1)
    have "cs1=[] \<longrightarrow> distinct (map (key\<circ>fst) es1)"
      by (rule finite_collect_insert_keys[OF Some[unfolded s1] Cons.prems(2)])
    moreover have "finite_collect_round key ident (es1,cs1) A=Some (es',cs')"
      using Cons.prems(1) Some s1 by (simp add: finite_collect_round_def)
    ultimately show ?thesis using Cons.IH by blast
  qed
qed

lemma finite_collect_steps_keys:
  "finite_collect_steps ord key ident step n (es,cs) F=Some (es',cs') \<Longrightarrow>
    (cs=[] \<longrightarrow> distinct (map (key\<circ>fst) es)) \<Longrightarrow> cs'=[] \<longrightarrow> distinct (map (key\<circ>fst) es')"
proof (induction n arbitrary: es cs F)
  case 0
  then show ?case by (simp split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "F=[]")
    case True
    then show ?thesis using Suc.prems by simp
  next
    case False
    let ?tag="\<lambda>f. map (\<lambda>(e,j). (e,Some f,j))"
    obtain As where As: "those (map (\<lambda>f. map_option (?tag f) (step f)) F)=Some As"
      using Suc.prems(1) False by (auto split: option.splits)
    obtain es1 cs1 where round: "finite_collect_round key ident (es,cs) (sort_key (ord \<circ> fst) (concat As))=Some (es1,cs1)"
      using Suc.prems(1) False As by (auto split: option.splits)
    have rest: "finite_collect_steps ord key ident step n (es1,cs1) (map fst (drop (length es) es1))=Some (es',cs')"
      using Suc.prems(1) False As round by simp
    have "cs1=[] \<longrightarrow> distinct (map (key\<circ>fst) es1)" by (rule finite_collect_round_keys[OF round Suc.prems(2)])
    then show ?thesis by (rule Suc.IH[OF rest])
  qed
qed

lemma finite_collect_keys:
  fixes A :: "('e\<times>'j) list"
  assumes collect: "finite_collect ord key ident (Some A) step n=Some (es,[])"
  shows "distinct (map (key\<circ>fst) es)"
proof -
  define R where "R=sort_key (ord \<circ> fst) (map (\<lambda>(e,j). (e,None::'e option,j)) A)"
  obtain s0 where round0: "finite_collect_round key ident ([],[]) R=Some s0"
  proof (cases "finite_collect_round key ident ([],[]) R")
    case None
    then show ?thesis using collect by (simp add: finite_collect_def R_def split: option.splits)
  next
    case (Some s)
    then show ?thesis by (rule that)
  qed
  obtain es0 cs0 where s0: "s0=(es0,cs0)" by (cases s0)
  have round: "finite_collect_round key ident ([],[]) R=Some (es0,cs0)" using round0 s0 by simp
  have steps: "finite_collect_steps ord key ident step n (es0,cs0) (map fst es0)=Some (es,[])"
    using collect round by (simp add: finite_collect_def R_def)
  have "cs0=[] \<longrightarrow> distinct (map (key\<circ>fst) es0)" by (rule finite_collect_round_keys[OF round]) simp
  then show ?thesis using finite_collect_steps_keys[OF steps] by simp
qed

section \<open>The identity of two elements and its check\<close>

text \<open>
  An identity query matches two elements against two patterns and asks a goal at a site of the same program
  whose variables those patterns bind. Its check is the ground call's resolution by R3: resolved, the two are
  identified; refuted, which R4 makes exact, or not matched, they are not; unresolved, or a goal the two
  elements do not ground, it gives nothing (@{text finite_identity_check_exact}).
\<close>

record ('d,'v) collection_identity =
  identity_left :: "'v finite_term_pattern"
  identity_right :: "'v finite_term_pattern"
  identity_site :: 'd
  identity_goal :: "'v finite_term_pattern"

definition finite_identity_holds :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d,'v) collection_identity \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_identity_holds P I x y \<longleftrightarrow> (\<exists>\<theta>. resolution_value \<theta> (identity_left I)=x \<and>
    resolution_value \<theta> (identity_right I)=y \<and>
    (identity_site I,decode_finite_term (resolution_value \<theta> (identity_goal I))) \<in> positive_meaning (decode_finite_system P))"

definition finite_identity_check :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('d,'v) collection_identity \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "finite_identity_check P n I x y=(if finite_pattern_formed (identity_left I) \<and> finite_pattern_formed (identity_right I)
    then (case finite_inputs_matching [(x,identity_left I),(y,identity_right I)] of None \<Rightarrow> Some False
      | Some W \<Rightarrow> if finite_pattern_variables (identity_goal I) |\<subseteq>| fimage fst W
        then (case finite_program_resolution no_witness_construction P (identity_site I)
            (resolution_value (finite_binding_valuation W) (identity_goal I)) n of
          Finite_Resolved Cs \<Rightarrow> Some True | Finite_Refuted \<Rightarrow> Some False | Finite_Unresolved D \<Rightarrow> None)
        else None)
    else None)"

lemma finite_inputs_matching_value:
  assumes "finite_inputs_matching ts=Some W" and "(t,p) \<in> set ts"
  shows "resolution_value (finite_binding_valuation W) p=t"
  by (rule finite_instance_value[OF finite_inputs_matching_some(2)[OF assms]])
    (simp add: finite_binding_valuation_member[OF finite_inputs_matching_some(1)[OF assms(1)]])


lemma finite_binding_valuation_agree:
  assumes functional: "finite_relation_functional W" and agree: "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
    and scope: "finite_pattern_variables p |\<subseteq>| fimage fst W"
  shows "resolution_value \<theta> p=resolution_value (finite_binding_valuation W) p"
proof (rule resolution_value_cong)
  fix x assume x: "x |\<in>| finite_pattern_variables p"
  have "x |\<in>| fimage fst W" by (rule fsubsetD[OF scope x])
  then obtain z where z: "x=fst z" "z |\<in>| W" by (rule fimageE)
  have xz: "(x,snd z) |\<in>| W" using z by simp
  show "\<theta> x=finite_binding_valuation W x" using agree[OF xz] finite_binding_valuation_member[OF functional xz] by simp
qed

theorem finite_identity_check_exact:
  assumes check: "finite_identity_check P n I x y=Some b"
  shows "b \<longleftrightarrow> finite_identity_holds P I x y"
proof -
  let ?ts="[(x,identity_left I),(y,identity_right I)]"
  have formed: "finite_pattern_formed (identity_left I)" "finite_pattern_formed (identity_right I)"
    using check by (auto simp: finite_identity_check_def split: if_splits)
  show ?thesis
  proof (cases "finite_inputs_matching ?ts")
    case None
    have notb: "\<not> b" using check formed None by (simp add: finite_identity_check_def)
    have "\<not> finite_identity_holds P I x y"
    proof
      assume "finite_identity_holds P I x y"
      then obtain \<theta> where l: "resolution_value \<theta> (identity_left I)=x" and r: "resolution_value \<theta> (identity_right I)=y"
        unfolding finite_identity_holds_def by blast
      obtain W where "finite_inputs_matching ?ts=Some W"
        by (rule finite_inputs_matching_complete[of ?ts \<theta>]) (use l r formed in auto)
      then show False using None by simp
    qed
    then show ?thesis using notb by blast
  next
    case (Some W)
    have functional: "finite_relation_functional W" by (rule finite_inputs_matching_some(1)[OF Some])
    have scope: "finite_pattern_variables (identity_goal I) |\<subseteq>| fimage fst W"
      using check formed Some by (auto simp: finite_identity_check_def split: if_splits)
    define t where "t=resolution_value (finite_binding_valuation W) (identity_goal I)"
    have l: "resolution_value (finite_binding_valuation W) (identity_left I)=x" by (rule finite_inputs_matching_value[OF Some]) simp
    have r: "resolution_value (finite_binding_valuation W) (identity_right I)=y" by (rule finite_inputs_matching_value[OF Some]) simp
    have res: "(case finite_program_resolution no_witness_construction P (identity_site I) t n of
        Finite_Resolved Cs \<Rightarrow> Some True | Finite_Refuted \<Rightarrow> Some False | Finite_Unresolved D \<Rightarrow> None)=Some b"
      using check formed Some scope by (simp add: finite_identity_check_def t_def)
    show ?thesis
    proof (cases "finite_program_resolution no_witness_construction P (identity_site I) t n")
      case (Finite_Resolved Cs)
      have "(identity_site I,decode_finite_term (resolution_value (finite_binding_valuation W) (identity_goal I))) \<in>
          positive_meaning (decode_finite_system P)"
        using finite_program_resolution_sound(2)[OF Finite_Resolved] by (simp add: t_def)
      then have "finite_identity_holds P I x y" unfolding finite_identity_holds_def using l r by blast
      then show ?thesis using res Finite_Resolved by simp
    next
      case Finite_Refuted
      have "\<not> finite_identity_holds P I x y"
      proof
        assume "finite_identity_holds P I x y"
        then obtain \<theta> where l': "resolution_value \<theta> (identity_left I)=x" and r': "resolution_value \<theta> (identity_right I)=y"
          and true: "(identity_site I,decode_finite_term (resolution_value \<theta> (identity_goal I))) \<in>
            positive_meaning (decode_finite_system P)"
          unfolding finite_identity_holds_def by blast
        obtain W' where W': "finite_inputs_matching ?ts=Some W'" and agree: "\<And>x u. (x,u) |\<in>| W' \<Longrightarrow> \<theta> x=u"
          by (rule finite_inputs_matching_complete[of ?ts \<theta>]) (use l' r' formed in auto)
        have "W'=W" using W' Some by simp
        note agreeW=agree[unfolded this]
        have "resolution_value \<theta> (identity_goal I)=t"
          unfolding t_def by (rule finite_binding_valuation_agree[OF functional agreeW scope])
        then show False using true finite_program_resolution_refutation_exact[OF Finite_Refuted] by simp
      qed
      then show ?thesis using res Finite_Refuted by simp
    next
      case (Finite_Unresolved D)
      then show ?thesis using res by simp
    qed
  qed
qed

section \<open>A family: its queries, key and identity\<close>

text \<open>
  A family names its base queries, an optional step query with the pattern its source element is matched against,
  a key (a pattern over the element and the variable its key part is), and an optional identity query; with none,
  elements are identified by equality of ground terms. Its answers at a clause's bindings are those of its
  queries (@{text finite_family_base}, @{text finite_family_step}), each tagged with the query it answers and
  the ground instance and certificates that brought it, and its collection is the iteration over them. The two
  answer relations the contract is stated with are read at the program's positive meaning.
\<close>

record ('a,'d,'v) collection_family =
  family_base :: "('a,'d,'v) collection_query list"
  family_step :: "(('a,'d,'v) collection_query\<times>'v finite_term_pattern) option"
  family_key :: "'v finite_term_pattern\<times>'v"
  family_identity :: "('d,'v) collection_identity option"

definition finite_family_key :: "('a,'d,'v) collection_family \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term option" where
  "finite_family_key F e=(case finite_inputs_matching [(e,fst (family_key F))] of None \<Rightarrow> None
    | Some W \<Rightarrow> finite_relation_option W (snd (family_key F)))"

definition finite_family_identity :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'d,'v) collection_family \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "finite_family_identity P n F x y=(case family_identity F of None \<Rightarrow> Some (x=y)
    | Some I \<Rightarrow> finite_identity_check P n I x y)"

definition finite_family_identified :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_family_identified P F x y \<longleftrightarrow> (case family_identity F of None \<Rightarrow> x=y
    | Some I \<Rightarrow> finite_identity_holds P I x y)"

lemma finite_family_identity_exact:
  assumes "finite_family_identity P n F x y=Some b"
  shows "b \<longleftrightarrow> finite_family_identified P F x y"
proof (cases "family_identity F")
  case None
  then show ?thesis using assms by (auto simp: finite_family_identity_def finite_family_identified_def)
next
  case (Some I)
  then show ?thesis using assms finite_identity_check_exact[of P n I x y b]
    by (simp add: finite_family_identity_def finite_family_identified_def)
qed

type_synonym ('a,'s,'c) collection_data = "nat\<times>finite_factor_term\<times>('a,'s,'c) finite_schema_proof fset"

definition finite_tag_answers ::
    "nat \<Rightarrow> ('a,'s,'c) query_answer list \<Rightarrow> (finite_factor_term\<times>('a,'s,'c) collection_data) list" where
  "finite_tag_answers i=map (\<lambda>(e,t,Cs). (e,(i,t,Cs)))"

definition finite_family_base :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>('a,'s,'c) collection_data) list option" where
  "finite_family_base P n F B=map_option concat (those (map (\<lambda>i. map_option (finite_tag_answers i)
    (finite_query_answers P n (family_base F!i) B [])) [0..<length (family_base F)]))"

definition finite_family_step :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term \<Rightarrow> (finite_factor_term\<times>('a,'s,'c) collection_data) list option" where
  "finite_family_step P n F B f=(case family_step F of None \<Rightarrow> Some []
    | Some qp \<Rightarrow> map_option (finite_tag_answers 0) (finite_query_answers P n (fst qp) B [(f,snd qp)]))"

definition finite_family_collection :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> ((finite_factor_term\<times>finite_factor_term option\<times>('a,'s,'c) collection_data) list\<times>
      (finite_factor_term\<times>finite_factor_term) list) option" where
  "finite_family_collection P n F B=finite_collect Ordered_Factor_Term (finite_family_key F) (finite_family_identity P n F)
    (finite_family_base P n F B) (finite_family_step P n F B) n"

definition finite_family_value :: "(finite_factor_term\<times>'x) list \<Rightarrow> finite_factor_term" where
  "finite_family_value es=finite_data_list (map fst es)"

definition finite_family_base_answers :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term set" where
  "finite_family_base_answers P F B={e. \<exists>q\<in>set (family_base F). finite_query_holds P q B [] e}"

definition finite_family_step_answers :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>finite_factor_term) set" where
  "finite_family_step_answers P F B={(f,e). \<exists>q p. family_step F=Some (q,p) \<and> finite_query_holds P q B [(f,p)] e}"

definition finite_family_covers :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    finite_factor_term set \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_family_covers P F E e \<longleftrightarrow> (\<exists>x\<in>E. finite_family_key F x=finite_family_key F e \<and>
    (x=e \<or> finite_family_identified P F x e))"

lemma finite_family_covered:
  assumes "finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es e"
  shows "finite_family_covers P F (fst ` set es) e"
proof -
  obtain x where x: "x \<in> set es" "finite_family_key F (fst x)=finite_family_key F e"
    and same: "fst x=e \<or> finite_family_identity P n F (fst x) e=Some True"
    using assms unfolding finite_collect_covered_def by blast
  have "fst x=e \<or> finite_family_identified P F (fst x) e"
    using same finite_family_identity_exact[of P n F "fst x" e True] by blast
  then show ?thesis unfolding finite_family_covers_def using x by (intro bexI[of _ "fst x"]) auto
qed

lemma finite_family_base_origin:
  assumes base: "finite_family_base P n F B=Some A" and member: "(e,i,t,Cs) \<in> set A"
  obtains Ai where "i<length (family_base F)" "finite_query_answers P n (family_base F!i) B []=Some Ai" "(e,t,Cs) \<in> set Ai"
proof -
  let ?g="\<lambda>i. map_option (finite_tag_answers i) (finite_query_answers P n (family_base F!i) B [])"
  obtain As where As: "those (map ?g [0..<length (family_base F)])=Some As" and A: "A=concat As"
    using base by (auto simp: finite_family_base_def)
  obtain L where L: "L \<in> set As" "(e,i,t,Cs) \<in> set L" using member A by auto
  obtain j where j: "j \<in> set [0..<length (family_base F)]" "?g j=Some L" using those_map_some[OF As] L(1) by blast
  obtain Aj where Aj: "finite_query_answers P n (family_base F!j) B []=Some Aj" "L=finite_tag_answers j Aj"
    using j(2) by auto
  have "i=j \<and> (e,t,Cs) \<in> set Aj" using L(2) Aj(2) by (auto simp: finite_tag_answers_def)
  then show ?thesis using that j(1) Aj(1) by auto
qed

lemma finite_family_base_listed:
  assumes base: "finite_family_base P n F B=Some A" and i: "i<length (family_base F)"
  obtains Ai where "finite_query_answers P n (family_base F!i) B []=Some Ai"
    "\<forall>e t Cs. (e,t,Cs) \<in> set Ai \<longrightarrow> (e,i,t,Cs) \<in> set A"
proof -
  let ?g="\<lambda>i. map_option (finite_tag_answers i) (finite_query_answers P n (family_base F!i) B [])"
  obtain As where As: "those (map ?g [0..<length (family_base F)])=Some As" and A: "A=concat As"
    using base by (auto simp: finite_family_base_def)
  obtain L where L: "L \<in> set As" "?g i=Some L" using those_map_some[OF As] i by fastforce
  obtain Ai where Ai: "finite_query_answers P n (family_base F!i) B []=Some Ai" "L=finite_tag_answers i Ai"
    using L(2) by auto
  have "\<forall>e t Cs. (e,t,Cs) \<in> set Ai \<longrightarrow> (e,i,t,Cs) \<in> set A"
  proof (intro allI impI)
    fix e t Cs assume "(e,t,Cs) \<in> set Ai"
    then have "(e,i,t,Cs) \<in> set L" using Ai(2) by (force simp: finite_tag_answers_def)
    then show "(e,i,t,Cs) \<in> set A" using L(1) A by auto
  qed
  then show ?thesis by (rule that[OF Ai(1)])
qed

lemma finite_family_step_origin:
  assumes step: "finite_family_step P n F B f=Some L" and member: "(e,i,t,Cs) \<in> set L"
  obtains q p Af where "family_step F=Some (q,p)" "finite_query_answers P n q B [(f,p)]=Some Af" "(e,t,Cs) \<in> set Af"
proof (cases "family_step F")
  case None
  then show ?thesis using step member by (simp add: finite_family_step_def)
next
  case (Some qp)
  obtain q p where qp: "qp=(q,p)" by (cases qp)
  obtain Af where Af: "finite_query_answers P n q B [(f,p)]=Some Af" "L=finite_tag_answers 0 Af"
    using step Some qp by (auto simp: finite_family_step_def)
  have "(e,t,Cs) \<in> set Af" using member Af(2) by (auto simp: finite_tag_answers_def)
  then show ?thesis using that[of q p Af] Some qp Af(1) by simp
qed

lemma finite_family_step_listed:
  assumes step: "finite_family_step P n F B f=Some L" and fam: "family_step F=Some (q,p)"
  obtains Af where "finite_query_answers P n q B [(f,p)]=Some Af" "\<forall>e t Cs. (e,t,Cs) \<in> set Af \<longrightarrow> (e,0,t,Cs) \<in> set L"
proof -
  obtain Af where Af: "finite_query_answers P n q B [(f,p)]=Some Af" "L=finite_tag_answers 0 Af"
    using step fam by (auto simp: finite_family_step_def)
  have "\<forall>e t Cs. (e,t,Cs) \<in> set Af \<longrightarrow> (e,0,t,Cs) \<in> set L"
  proof (intro allI impI)
    fix e t Cs assume "(e,t,Cs) \<in> set Af"
    then show "(e,0,t,Cs) \<in> set L" using Af(2) by (force simp: finite_tag_answers_def)
  qed
  then show ?thesis by (rule that[OF Af(1)])
qed

lemma finite_family_collection_invariant:
  assumes collect: "finite_family_collection P n F B=Some (es,cs)"
  obtains A where "finite_family_base P n F B=Some A"
    "finite_collect_invariant (finite_family_key F) (finite_family_identity P n F) A (finite_family_step P n F B) es cs []"
proof -
  obtain A where base: "finite_family_base P n F B=Some A"
    using collect by (cases "finite_family_base P n F B") (simp_all add: finite_family_collection_def finite_collect_def)
  have collect': "finite_collect Ordered_Factor_Term (finite_family_key F) (finite_family_identity P n F) (Some A)
      (finite_family_step P n F B) n=Some (es,cs)"
    using collect base by (simp add: finite_family_collection_def)
  show ?thesis by (rule that[OF base finite_collect_invariant_result[OF collect']])
qed

section \<open>The justification of a collection and its check\<close>

text \<open>
  Each element carries the certificates of the answer that brought it, the query and ground instance they are
  certificates of, and the element its step was taken at. The check re-reads every element: its certificates
  accepted by the finite proof checker at its query's ground instance (a base query's, or the step query's at its
  source element), the element read from that instance, and every step taken at an earlier element. It reads the
  program only through the checker and the query's own patterns; it produces nothing.
\<close>

definition finite_query_checked :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_query \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>'v finite_term_pattern) list \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'c) finite_schema_proof fset \<Rightarrow> bool" where
  "finite_query_checked P q B E e t Cs \<longleftrightarrow> Cs\<noteq>{||} \<and> fBall Cs (\<lambda>p. finite_checks_schema_proof P p (query_site q) t) \<and>
    (case finite_query_inputs q B E of None \<Rightarrow> False | Some ts \<Rightarrow> finite_query_formed q ts \<and>
      (case finite_inputs_matching ts of None \<Rightarrow> False | Some W \<Rightarrow> finite_query_element q W t=Some e))"

lemma finite_query_checked_sound:
  assumes checked: "finite_query_checked P q B E e t Cs"
  shows "finite_query_holds P q B E e" "finite_term_formed e"
proof -
  have "Cs\<noteq>{||}" using checked by (simp add: finite_query_checked_def)
  then obtain p where p: "p |\<in>| Cs" by (metis all_not_fin_conv)
  have "finite_checks_schema_proof P p (query_site q) t" using checked p by (simp add: finite_query_checked_def)
  then have true: "(query_site q,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    by (rule finite_certificate_true)
  obtain ts where inputs: "finite_query_inputs q B E=Some ts"
    using checked by (cases "finite_query_inputs q B E") (simp_all add: finite_query_checked_def)
  have formed: "finite_query_formed q ts" using checked inputs by (simp add: finite_query_checked_def)
  obtain W where matching: "finite_inputs_matching ts=Some W"
    using checked inputs by (cases "finite_inputs_matching ts") (simp_all add: finite_query_checked_def)
  have element: "finite_query_element q W t=Some e" using checked inputs matching by (simp add: finite_query_checked_def)
  show "finite_query_holds P q B E e" "finite_term_formed e"
    by (rule finite_query_checked_holds[OF inputs formed matching element true])+
qed

lemma finite_query_answers_checked:
  assumes answers: "finite_query_answers P n q B E=Some A" and member: "(e,t,Cs) \<in> set A"
  shows "finite_query_checked P q B E e t Cs"
proof -
  obtain ts W where inputs: "finite_query_inputs q B E=Some ts" and formed: "finite_query_formed q ts"
    and matching: "finite_inputs_matching ts=Some W" and element: "finite_query_element q W t=Some e"
    and resolved: "finite_program_resolution no_witness_construction P (query_site q) t n=Finite_Resolved Cs"
    by (rule finite_query_answers_member[OF answers member])
  show ?thesis unfolding finite_query_checked_def
    using inputs formed matching element finite_program_resolution_sound(1)[OF resolved]
      finite_program_resolution_accepted[OF resolved] by simp
qed

definition finite_justification_query :: "('a,'d,'v) collection_family \<Rightarrow> finite_factor_term option \<Rightarrow> nat \<Rightarrow>
    (('a,'d,'v) collection_query\<times>(finite_factor_term\<times>'v finite_term_pattern) list) option" where
  "finite_justification_query F src i=(case src of
      None \<Rightarrow> if i<length (family_base F) then Some (family_base F!i,[]) else None
    | Some f \<Rightarrow> map_option (\<lambda>qp. (fst qp,[(f,snd qp)])) (family_step F))"

definition finite_justification_entry :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term list \<Rightarrow>
    finite_factor_term\<times>finite_factor_term option\<times>('a,'s,'c) collection_data \<Rightarrow> bool" where
  "finite_justification_entry P F B prior x \<longleftrightarrow>
    (case fst (snd x) of None \<Rightarrow> True | Some f \<Rightarrow> f \<in> set prior) \<and>
    (case finite_justification_query F (fst (snd x)) (fst (snd (snd x))) of None \<Rightarrow> False
     | Some qE \<Rightarrow> finite_query_checked P (fst qE) B (snd qE) (fst x) (fst (snd (snd (snd x)))) (snd (snd (snd (snd x)))))"

definition finite_justification_check :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow>
    ('a\<times>finite_factor_term) fset \<Rightarrow> (finite_factor_term\<times>finite_factor_term option\<times>('a,'s,'c) collection_data) list \<Rightarrow> bool" where
  "finite_justification_check P F B es \<longleftrightarrow>
    list_all (\<lambda>k. finite_justification_entry P F B (map fst (take k es)) (es!k)) [0..<length es]"

lemma finite_justification_query_answers:
  assumes query: "finite_justification_query F src i=Some qE" and holds: "finite_query_holds P (fst qE) B (snd qE) e"
  shows "(src=None \<longrightarrow> e \<in> finite_family_base_answers P F B) \<and>
    (\<forall>f. src=Some f \<longrightarrow> (f,e) \<in> finite_family_step_answers P F B)"
proof (cases src)
  case None
  then have i: "i<length (family_base F)" and qE: "qE=(family_base F!i,[])"
    using query by (auto simp: finite_justification_query_def split: if_splits)
  show ?thesis using None holds nth_mem[OF i] unfolding qE finite_family_base_answers_def by auto
next
  case (Some f)
  then obtain q p where fam: "family_step F=Some (q,p)" and qE: "qE=(q,[(f,p)])"
    using query by (auto simp: finite_justification_query_def)
  show ?thesis using Some holds fam unfolding qE finite_family_step_answers_def by auto
qed

text \<open>(3), the check is sound: a justified list's elements lie in the least set and are formed.\<close>

theorem finite_justification_sound:
  assumes check: "finite_justification_check P F B es"
  shows "fst ` set es \<subseteq> (finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
    and "\<forall>x\<in>set es. finite_term_formed (fst x)"
proof -
  have entry: "finite_justification_entry P F B (map fst (take k es)) (es!k)" if "k<length es" for k
    using check that by (auto simp: finite_justification_check_def list_all_iff)
  have member: "(fst (snd x)=None \<longrightarrow> fst x \<in> finite_family_base_answers P F B) \<and>
      (\<forall>f. fst (snd x)=Some f \<longrightarrow> (f,fst x) \<in> finite_family_step_answers P F B) \<and> finite_term_formed (fst x)"
    if xin: "x \<in> set es" for x
  proof -
    obtain k where k: "k<length es" "es!k=x" using xin by (auto simp: in_set_conv_nth)
    obtain qE where qE: "finite_justification_query F (fst (snd x)) (fst (snd (snd x)))=Some qE"
      and checked: "finite_query_checked P (fst qE) B (snd qE) (fst x) (fst (snd (snd (snd x)))) (snd (snd (snd (snd x))))"
      using entry[OF k(1)] unfolding k(2) by (auto simp: finite_justification_entry_def split: option.splits)
    have holds: "finite_query_holds P (fst qE) B (snd qE) (fst x)" and formed: "finite_term_formed (fst x)"
      by (rule finite_query_checked_sound[OF checked])+
    show ?thesis using finite_justification_query_answers[OF qE holds] formed by blast
  qed
  show "fst ` set es \<subseteq> (finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
  proof (rule finite_sources_closure)
    fix k f assume k: "k<length es" and src: "fst (snd (es!k))=Some f"
    show "f \<in> fst ` set (take k es)" using entry[OF k] src by (auto simp: finite_justification_entry_def)
  next
    fix x assume "x \<in> set es" "fst (snd x)=None"
    then show "fst x \<in> finite_family_base_answers P F B" using member by blast
  next
    fix x f assume "x \<in> set es" "fst (snd x)=Some f"
    then show "(f,fst x) \<in> finite_family_step_answers P F B" using member by blast
  qed
  show "\<forall>x\<in>set es. finite_term_formed (fst x)" using member by blast
qed

text \<open>(3), the justification a collection returns is accepted by the check.\<close>

theorem finite_family_collection_justified:
  assumes collect: "finite_family_collection P n F B=Some (es,cs)"
  shows "finite_justification_check P F B es"
proof -
  obtain A where base: "finite_family_base P n F B=Some A"
    and inv: "finite_collect_invariant (finite_family_key F) (finite_family_identity P n F) A (finite_family_step P n F B) es cs []"
    by (rule finite_family_collection_invariant[OF collect])
  have origin: "\<forall>x\<in>set es. finite_collect_origin A (finite_family_step P n F B) x"
    using inv unfolding finite_collect_invariant_def by blast
  have earlier: "\<forall>k<length es. \<forall>f. fst (snd (es!k))=Some f \<longrightarrow> f \<in> fst ` set (take k es)"
    using inv unfolding finite_collect_invariant_def by blast
  have entry: "finite_justification_entry P F B (map fst (take k es)) (es!k)" if k: "k<length es" for k
  proof -
    obtain e src i t Cs where x: "es!k=(e,src,i,t,Cs)" by (rule prod_cases5)
    have xin: "(e,src,i,t,Cs) \<in> set es" using nth_mem[OF k] x by simp
    have orig: "finite_collect_origin A (finite_family_step P n F B) (e,src,i,t,Cs)" using origin xin by blast
    show ?thesis
    proof (cases src)
      case None
      then have "(e,i,t,Cs) \<in> set A" using orig by (simp add: finite_collect_origin_def)
      then obtain Ai where i: "i<length (family_base F)"
        and Ai: "finite_query_answers P n (family_base F!i) B []=Some Ai" "(e,t,Cs) \<in> set Ai"
        by (rule finite_family_base_origin[OF base])
      have "finite_query_checked P (family_base F!i) B [] e t Cs" by (rule finite_query_answers_checked[OF Ai])
      then show ?thesis using None i x by (simp add: finite_justification_entry_def finite_justification_query_def)
    next
      case (Some f)
      then obtain L where L: "finite_family_step P n F B f=Some L" "(e,i,t,Cs) \<in> set L"
        using orig by (auto simp: finite_collect_origin_def)
      obtain q p Af where fam: "family_step F=Some (q,p)"
        and Af: "finite_query_answers P n q B [(f,p)]=Some Af" "(e,t,Cs) \<in> set Af"
        by (rule finite_family_step_origin[OF L])
      have "finite_query_checked P q B [(f,p)] e t Cs" by (rule finite_query_answers_checked[OF Af])
      moreover have "f \<in> set (map fst (take k es))" using earlier k x Some by force
      ultimately show ?thesis using Some fam x by (simp add: finite_justification_entry_def finite_justification_query_def)
    qed
  qed
  then show ?thesis by (auto simp: finite_justification_check_def list_all_iff)
qed

section \<open>The contract of a family's collection\<close>

text \<open>(2), soundness: every element lies in the image of the base answers under the step answers' closure.\<close>

theorem finite_family_collection_sound:
  assumes "finite_family_collection P n F B=Some (es,cs)"
  shows "fst ` set es \<subseteq> (finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
    and "\<forall>x\<in>set es. finite_term_formed (fst x)"
  by (rule finite_justification_sound[OF finite_family_collection_justified[OF assms]])+

text \<open>
  (2), completeness: a collection is returned only when every query of its iteration was complete; its elements then cover every base answer and every step answer at an element, up to the key and the
  identity query.
\<close>

theorem finite_family_collection_complete:
  fixes F :: "('a,'d,'v) collection_family" and P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes collect: "finite_family_collection P n F B=Some (es,cs)"
  shows "\<forall>e\<in>finite_family_base_answers P F B. finite_family_covers P F (fst ` set es) e"
    and "\<forall>f\<in>fst ` set es. \<forall>e. (f,e) \<in> finite_family_step_answers P F B \<longrightarrow> finite_family_covers P F (fst ` set es) e"
proof -
  obtain A where base: "finite_family_base P n F B=Some A"
    and inv: "finite_collect_invariant (finite_family_key F) (finite_family_identity P n F) A (finite_family_step P n F B) es cs []"
    by (rule finite_family_collection_invariant[OF collect])
  have covA: "\<forall>a\<in>set A. finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es (fst a)"
    using inv unfolding finite_collect_invariant_def by blast
  have stepped: "\<forall>x\<in>set es. fst x \<notin> set [] \<longrightarrow> (\<exists>L. finite_family_step P n F B (fst x)=Some L \<and>
      (\<forall>a\<in>set L. finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es (fst a)))"
    using inv unfolding finite_collect_invariant_def by blast
  show "\<forall>e\<in>finite_family_base_answers P F B. finite_family_covers P F (fst ` set es) e"
  proof
    fix e assume "e \<in> finite_family_base_answers P F B"
    then obtain q where q: "q \<in> set (family_base F)" and holds: "finite_query_holds P q B [] e"
      unfolding finite_family_base_answers_def by blast
    obtain i where i: "i<length (family_base F)" "family_base F!i=q" using q by (auto simp: in_set_conv_nth)
    obtain Ai where Ai: "finite_query_answers P n (family_base F!i) B []=Some Ai"
      and listed: "\<forall>e t Cs. (e,t,Cs) \<in> set Ai \<longrightarrow> (e,i,t,Cs) \<in> set A"
      by (rule finite_family_base_listed[OF base i(1)])
    have holdsi: "finite_query_holds P (family_base F!i) B [] e" using holds i(2) by simp
    obtain t Cs where "(e,t,Cs) \<in> set Ai" using finite_query_answers_complete[OF Ai holdsi] by blast
    then have "(e,i,t,Cs) \<in> set A" using listed by blast
    then have "finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es e"
      using bspec[OF covA] by fastforce
    then show "finite_family_covers P F (fst ` set es) e" by (rule finite_family_covered)
  qed
  show "\<forall>f\<in>fst ` set es. \<forall>e. (f,e) \<in> finite_family_step_answers P F B \<longrightarrow> finite_family_covers P F (fst ` set es) e"
  proof (intro ballI allI impI)
    fix f e assume f: "f \<in> fst ` set es" and fe: "(f,e) \<in> finite_family_step_answers P F B"
    obtain q p where fam: "family_step F=Some (q,p)" and holds: "finite_query_holds P q B [(f,p)] e"
      using fe unfolding finite_family_step_answers_def by blast
    obtain x where x: "x \<in> set es" "f=fst x" using f by blast
    have "\<exists>L. finite_family_step P n F B f=Some L \<and>
        (\<forall>a\<in>set L. finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es (fst a))"
      using bspec[OF stepped x(1)] x(2) by simp
    then obtain L where L: "finite_family_step P n F B f=Some L"
      and covL: "\<forall>a\<in>set L. finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es (fst a)"
      by blast
    obtain Af where Af: "finite_query_answers P n q B [(f,p)]=Some Af"
      and listed: "\<forall>e t Cs. (e,t,Cs) \<in> set Af \<longrightarrow> (e,0,t,Cs) \<in> set L"
      by (rule finite_family_step_listed[OF L fam])
    obtain t Cs where "(e,t,Cs) \<in> set Af" using finite_query_answers_complete[OF Af holds] by blast
    then have "(e,0,t,Cs) \<in> set L" using listed by blast
    then have "finite_collect_covered (finite_family_key F) (finite_family_identity P n F) es e"
      using bspec[OF covL] by fastforce
    then show "finite_family_covers P F (fst ` set es) e" by (rule finite_family_covered)
  qed
qed

text \<open>(2), exactness where the family has no identity query: the elements are exactly the least set.\<close>

theorem finite_family_collection_exact:
  fixes F :: "('a,'d,'v) collection_family" and P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes collect: "finite_family_collection P n F B=Some (es,cs)"
    and none: "family_identity F=None"
  shows "fst ` set es=(finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
proof
  show "fst ` set es \<subseteq> (finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
    by (rule finite_family_collection_sound(1)[OF collect])
  have element: "e \<in> fst ` set es" if "finite_family_covers P F (fst ` set es) e" for e
    using that none by (auto simp: finite_family_covers_def finite_family_identified_def)
  note complete=finite_family_collection_complete[OF collect]
  show "(finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B \<subseteq> fst ` set es"
  proof
    fix e assume "e \<in> (finite_family_step_answers P F B)\<^sup>* `` finite_family_base_answers P F B"
    then obtain b where b: "b \<in> finite_family_base_answers P F B" and path: "(b,e) \<in> (finite_family_step_answers P F B)\<^sup>*"
      by blast
    from path show "e \<in> fst ` set es"
    proof (induction rule: rtrancl_induct)
      case base
      then show ?case using complete(1) b element by blast
    next
      case (step y z)
      then show ?case using complete(2) element by blast
    qed
  qed
qed

text \<open>A conflict presents two answers of one key whose identity the identity query refutes.\<close>

theorem finite_family_collection_conflicts:
  assumes collect: "finite_family_collection P n F B=Some (es,cs)" and conflict: "(x,y) \<in> set cs"
  shows "x \<in> fst ` set es" "y \<in> fst ` set es" "finite_family_key F x=finite_family_key F y" "x\<noteq>y"
    "\<not> finite_family_identified P F x y"
proof -
  obtain A where inv: "finite_collect_invariant (finite_family_key F) (finite_family_identity P n F) A
      (finite_family_step P n F B) es cs []"
    by (rule finite_family_collection_invariant[OF collect])
  have conf: "finite_collect_conflicts (finite_family_key F) (finite_family_identity P n F) es cs"
    using inv unfolding finite_collect_invariant_def by blast
  have c: "x \<in> fst ` set es \<and> y \<in> fst ` set es \<and> finite_family_key F x=finite_family_key F y \<and> x\<noteq>y \<and>
      finite_family_identity P n F x y=Some False"
    using bspec[OF conf[unfolded finite_collect_conflicts_def] conflict] by simp
  then show "x \<in> fst ` set es" "y \<in> fst ` set es" "finite_family_key F x=finite_family_key F y" "x\<noteq>y" by simp_all
  show "\<not> finite_family_identified P F x y" using c finite_family_identity_exact[of P n F x y False] by simp
qed

text \<open>With no conflict the elements are distinct, and the value is the data list of them in the order found.\<close>

theorem finite_family_collection_distinct:
  assumes collect: "finite_family_collection P n F B=Some (es,[])"
  shows "distinct (map fst es)"
proof -
  obtain A where base: "finite_family_base P n F B=Some A"
    using collect by (cases "finite_family_base P n F B") (simp_all add: finite_family_collection_def finite_collect_def)
  have "finite_collect Ordered_Factor_Term (finite_family_key F) (finite_family_identity P n F) (Some A)
      (finite_family_step P n F B) n=Some (es,[])"
    using collect base by (simp add: finite_family_collection_def)
  then have "distinct (map (finite_family_key F\<circ>fst) es)" by (rule finite_collect_keys)
  then have "distinct (map (finite_family_key F) (map fst es))" by (simp only: map_map)
  then show ?thesis using distinct_map[of "finite_family_key F" "map fst es"] by blast
qed


theorem finite_family_value_presents:
  "decode_finite_term (finite_family_value es)=data_list_term (map (decode_finite_term \<circ> fst) es)"
  by (simp add: finite_family_value_def)

theorem finite_family_collection_presents:
  assumes collect: "finite_family_collection P n F B=Some (es,[])"
  shows "data_collection_presents (\<lambda>x t. t=decode_finite_term x) (fst ` set es) (decode_finite_term (finite_family_value es))"
  unfolding data_collection_presents_def
  by (rule exI[of _ "map fst es"], rule exI[of _ "map decode_finite_term (map fst es)"])
    (simp add: finite_family_collection_distinct[OF collect] finite_family_value_def list_all2_conv_all_nth)

section \<open>Registrations and the construction from them\<close>

text \<open>
  A registration names a clause by its site and schema, compared as values, and one variable of it; it holds one
  family, or two whose values it presents as a pair. The construction from a list of registrations registers
  exactly their variables at their clauses, and its value at a registered variable, at the clause's ground
  bindings, is the registration's collection value: nothing where a query was incomplete or the bound was reached,
  and otherwise the data list of every element found, conflicting ones kept. Every value it returns is formed
  (@{text finite_collection_construction_formed}), from the formedness of an accepted justification's elements.
  Registrations are read by the construction alone; no checker reads them.
\<close>

datatype ('a,'d,'v) registration_families =
  Single_Family "('a,'d,'v) collection_family"
| Paired_Families "('a,'d,'v) collection_family" "('a,'d,'v) collection_family"

record ('a,'s,'d,'v) collection_registration =
  registration_site :: 'd
  registration_schema :: "('a,'s,'d) finite_factor_schema"
  registration_variable :: 'a
  registration_families :: "('a,'d,'v) registration_families"

definition finite_family_collected :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'d,'v) collection_family \<Rightarrow> ('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term option" where
  "finite_family_collected P n F B=map_option (\<lambda>c. finite_family_value (fst c)) (finite_family_collection P n F B)"

lemma finite_family_collected_some:
  "finite_family_collected P n F B=Some v \<longleftrightarrow>
    (\<exists>es cs. finite_family_collection P n F B=Some (es,cs) \<and> v=finite_family_value es)"
  by (auto simp: finite_family_collected_def)

lemma finite_family_collected_formed:
  assumes collected: "finite_family_collected P n F B=Some v"
  shows "finite_term_formed v"
proof -
  obtain c where c: "finite_family_collection P n F B=Some c" and v: "v=finite_family_value (fst c)"
    using collected by (auto simp: finite_family_collected_def)
  obtain es cs where es: "c=(es,cs)" by (cases c)
  have "\<forall>x\<in>set es. finite_term_formed (fst x)" by (rule finite_family_collection_sound(2)[OF c[unfolded es]])
  then show ?thesis unfolding v es finite_family_value_def by (simp add: finite_data_list_formed list_all_iff)
qed

definition finite_registration_value :: "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'s,'d,'v) collection_registration \<Rightarrow> ('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term option" where
  "finite_registration_value P n R B=(case registration_families R of
      Single_Family F \<Rightarrow> finite_family_collected P n F B
    | Paired_Families F G \<Rightarrow> (case finite_family_collected P n F B of None \<Rightarrow> None
        | Some x \<Rightarrow> map_option (Finite_Pair x) (finite_family_collected P n G B)))"

lemma finite_registration_value_formed:
  assumes "finite_registration_value P n R B=Some v"
  shows "finite_term_formed v"
proof (cases "registration_families R")
  case (Single_Family F)
  then show ?thesis using assms finite_family_collected_formed by (simp add: finite_registration_value_def)
next
  case (Paired_Families F G)
  then show ?thesis using assms finite_family_collected_formed
    by (auto simp: finite_registration_value_def split: option.splits)
qed

definition finite_registration_matches ::
    "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow> bool" where
  "finite_registration_matches d S R \<longleftrightarrow> registration_site R=d \<and> registration_schema R=S"

definition finite_registered_variables ::
    "('a,'s,'d,'v) collection_registration list \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a fset" where
  "finite_registered_variables Rs d S=fset_of_list (map registration_variable (filter (finite_registration_matches d S) Rs))"

lemma finite_registered_variables_member:
  "a |\<in>| finite_registered_variables Rs d S \<longleftrightarrow>
    (\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R=a)"
  by (auto simp: finite_registered_variables_def fset_of_list_elem)

definition finite_collection_construction ::
    "('a,'s,'d,'v) collection_registration list \<Rightarrow> nat \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction" where
  "finite_collection_construction Rs n=\<lparr>witness_registered=finite_registered_variables Rs,
    witness_value=(\<lambda>P d S B a. case find (\<lambda>R. finite_registration_matches d S R \<and> registration_variable R=a) Rs of
      None \<Rightarrow> None | Some R \<Rightarrow> finite_registration_value P n R B)\<rparr>"

text \<open>(4): the construction registers exactly the registrations' variables, and each value it returns is formed.\<close>

theorem finite_collection_construction_registered:
  "a |\<in>| witness_registered (finite_collection_construction Rs n) d S \<longleftrightarrow>
    (\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R=a)"
  by (simp add: finite_collection_construction_def finite_registered_variables_member)

theorem finite_collection_construction_value:
  assumes "witness_value (finite_collection_construction Rs n) P d S B a=Some v"
  shows "\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R=a \<and>
    finite_registration_value P n R B=Some v"
proof -
  obtain R where R: "find (\<lambda>R. finite_registration_matches d S R \<and> registration_variable R=a) Rs=Some R"
    and v: "finite_registration_value P n R B=Some v"
    using assms by (auto simp: finite_collection_construction_def split: option.splits)
  have "finite_registration_matches d S R \<and> registration_variable R=a \<and> R \<in> set Rs"
    using R by (auto simp: find_Some_iff)
  then show ?thesis using v by blast
qed

theorem finite_collection_construction_formed:
  "finite_witness_construction_formed (finite_collection_construction Rs n)"
  unfolding finite_witness_construction_formed_def
proof (intro allI impI)
  fix P d S B a v assume "witness_value (finite_collection_construction Rs n) P d S B a=Some v"
  then have "\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R=a \<and>
      finite_registration_value P n R B=Some v"
    by (rule finite_collection_construction_value)
  then show "finite_term_formed v" using finite_registration_value_formed by blast
qed

section \<open>A proposer's hand-ins and the resolution with them\<close>

text \<open>
  A proposer may hand in witnesses, rows of a registration, the ground bindings of its clause's other variables and
  a value, and whole certificates of the call. The hand-in construction registers the variables of the
  registrations and of the rows' registrations, so a clause no registration names can be handed a witness; at each
  point it returns the formed handed-in value of a row that matches, and otherwise the construction's own
  production. The resolution with hand-ins checks the handed-in
  certificates with the finite proof checker as they are; failing those, it is the resolution with the hand-in
  construction where that resolves, and otherwise the resolution with the construction's own production, the first
  run's diagnoses kept in an unresolved result. It resolves only with certificates the checker accepts
  (@{text finite_handin_resolution_accepted}) and refutes only where the resolution with the construction's own
  production refutes (@{text finite_handin_resolution_refuted}): a handed-in witness never refutes.
\<close>

type_synonym ('a,'s,'d,'v) handin_table =
  "(('a,'s,'d,'v) collection_registration\<times>('a\<times>finite_factor_term) fset\<times>finite_factor_term) list"

definition finite_handin_row :: "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a\<times>finite_factor_term) fset \<Rightarrow> 'a \<Rightarrow>
    ('a,'s,'d,'v) collection_registration\<times>('a\<times>finite_factor_term) fset\<times>finite_factor_term \<Rightarrow> bool" where
  "finite_handin_row d S B a h \<longleftrightarrow> finite_registration_matches d S (fst h) \<and> registration_variable (fst h)=a \<and>
    fst (snd h)=B \<and> finite_term_formed (snd (snd h))"

definition finite_handin_construction :: "('a,'s,'d,'v) collection_registration list \<Rightarrow> ('a,'s,'d,'v) handin_table \<Rightarrow>
    nat \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction" where
  "finite_handin_construction Rs H n=\<lparr>witness_registered=finite_registered_variables (Rs@map fst H),
    witness_value=(\<lambda>P d S B a. case find (finite_handin_row d S B a) H of
      Some h \<Rightarrow> Some (snd (snd h))
    | None \<Rightarrow> witness_value (finite_collection_construction Rs n) P d S B a)\<rparr>"

theorem finite_handin_construction_registered:
  "a |\<in>| witness_registered (finite_handin_construction Rs H n) d S \<longleftrightarrow>
    (\<exists>R\<in>set Rs \<union> fst ` set H. finite_registration_matches d S R \<and> registration_variable R=a)"
  by (auto simp: finite_handin_construction_def finite_registered_variables_member)

theorem finite_handin_construction_formed:
  "finite_witness_construction_formed (finite_handin_construction Rs H n)"
  unfolding finite_witness_construction_formed_def
proof (intro allI impI)
  fix P d S B a v assume v: "witness_value (finite_handin_construction Rs H n) P d S B a=Some v"
  show "finite_term_formed v"
  proof (cases "find (finite_handin_row d S B a) H")
    case None
    then have "witness_value (finite_collection_construction Rs n) P d S B a=Some v"
      using v by (simp add: finite_handin_construction_def)
    then have "\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R=a \<and>
        finite_registration_value P n R B=Some v"
      by (rule finite_collection_construction_value)
    then show ?thesis using finite_registration_value_formed by blast
  next
    case (Some h)
    then have vh: "v=snd (snd h)" using v by (simp add: finite_handin_construction_def)
    have "finite_handin_row d S B a h" using Some by (auto simp: find_Some_iff)
    then show ?thesis using vh by (simp add: finite_handin_row_def)
  qed
qed

definition finite_handin_resolution :: "('a,'s,'d,'v) collection_registration list \<Rightarrow> ('a,'s,'d,'v) handin_table \<Rightarrow>
    ('a,'s,'c) finite_schema_proof fset \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
    nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_handin_resolution Rs H Cs P d t n=(let A=ffilter (\<lambda>p. finite_checks_schema_proof P p d t) Cs in
    if A\<noteq>{||} then Finite_Resolved A else
    (case finite_program_resolution (finite_handin_construction Rs H n) P d t n of
      Finite_Resolved C \<Rightarrow> Finite_Resolved C
    | Finite_Refuted \<Rightarrow> finite_program_resolution (finite_collection_construction Rs n) P d t n
    | Finite_Unresolved D \<Rightarrow> (case finite_program_resolution (finite_collection_construction Rs n) P d t n of
        Finite_Resolved C \<Rightarrow> Finite_Resolved C
      | Finite_Refuted \<Rightarrow> Finite_Refuted
      | Finite_Unresolved D' \<Rightarrow> Finite_Unresolved (D' |\<union>| D))))"

text \<open>(5): resolved only with certificates the checker accepts, so the call holds.\<close>

theorem finite_handin_resolution_accepted:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes resolved: "finite_handin_resolution Rs H Cs P d t n=Finite_Resolved C"
  shows "C\<noteq>{||}" "fBall C (\<lambda>p. finite_checks_schema_proof P p d t)"
    "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  have run: "C\<noteq>{||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p d t)"
    if "finite_program_resolution \<kappa> P d t n=Finite_Resolved C" for \<kappa> :: "('a,'s,'d,'c) finite_witness_construction"
    using finite_program_resolution_sound(1)[OF that] finite_program_resolution_accepted[OF that] by blast
  have both: "C\<noteq>{||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p d t)"
  proof (cases "ffilter (\<lambda>p. finite_checks_schema_proof P p d t) Cs\<noteq>{||}")
    case True
    then show ?thesis using resolved by (auto simp: finite_handin_resolution_def Let_def)
  next
    case False
    show ?thesis
    proof (cases "finite_program_resolution (finite_handin_construction Rs H n) P d t n")
      case (Finite_Resolved C1)
      then have "finite_program_resolution (finite_handin_construction Rs H n) P d t n=Finite_Resolved C"
        using resolved False by (simp add: finite_handin_resolution_def Let_def)
      then show ?thesis by (rule run)
    next
      case Finite_Refuted
      then have "finite_program_resolution (finite_collection_construction Rs n) P d t n=Finite_Resolved C"
        using resolved False by (simp add: finite_handin_resolution_def Let_def)
      then show ?thesis by (rule run)
    next
      case (Finite_Unresolved D)
      then have "finite_program_resolution (finite_collection_construction Rs n) P d t n=Finite_Resolved C"
        using resolved False by (simp add: finite_handin_resolution_def Let_def split: finite_resolution_result.splits)
      then show ?thesis by (rule run)
    qed
  qed
  then show "C\<noteq>{||}" "fBall C (\<lambda>p. finite_checks_schema_proof P p d t)" by blast+
  obtain p where p: "p |\<in>| C" using both by (metis all_not_fin_conv)
  have "finite_checks_schema_proof P p d t" using both p by blast
  then show "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)" by (rule finite_certificate_true)
qed

text \<open>(5): refuted only where the resolution with the construction's own production refutes.\<close>

theorem finite_handin_resolution_refuted:
  assumes "finite_handin_resolution Rs H Cs P d t n=Finite_Refuted"
  shows "finite_program_resolution (finite_collection_construction Rs n) P d t n=Finite_Refuted"
  using assms by (auto simp: finite_handin_resolution_def Let_def split: if_splits finite_resolution_result.splits)

export_code finite_family_collection finite_justification_check finite_collection_construction
  finite_handin_construction finite_handin_resolution checking SML

end
