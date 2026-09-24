theory Factor_Package_Additions
  imports Factor_Scope_Reading_Base Factor_Row_Value_Agreement Factor_Component_Agreement
    Factor_Positive_Parametricity
begin

section \<open>The members a package adds to another, each satisfying a callee's predicate\<close>

text \<open>
  The argument is a pair of two site values (@{const site_value_presents}): the first the given's,
  the second the candidate's. The entry holds exactly when the candidate's package exists and every
  one of its members is a member of the given's package or satisfies a callee's predicate at the pair
  of the first site value and the member's site. The members are read through a finite bound of the
  candidate's package: a list of definition sites that contains the package's actual roots
  (@{const root_family_reading_system}, @{const data_subset_system}) and every callee of each of its
  definitions (@{const definition_callee_list_system}), so it contains the least closure of the roots,
  which is the package. Each bound member is checked; the check is membership of the given's package
  (@{const package_membership_system}) or the callee. The callee is a parameter: the contract is proved
  once for every callee meaning.
\<close>

abbreviation package_additions_result :: "(factor_term \<Rightarrow> bool) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "package_additions_result holds z \<equiv> \<exists>E u r t F v s w R.
    z=Pair_Term t w \<and> site_value_presents E u r t \<and> site_value_presents F v s w \<and>
    native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      holds (Pair_Term (Pair_Term t w) (definition_site_value d)))"

definition addition_member_schema :: "(nat,nat,nat) factor_schema" where
  "addition_member_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Variable 4)) data_w)
    {(0,83,package_subject_pattern data_x data_y data_z data_w)}"

definition addition_callee_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "addition_callee_schema callee=data_rule (Pattern_Pair data_x data_y) {(0,callee,Pattern_Pair data_x data_y)}"

definition addition_element_clauses :: "nat \<Rightarrow> (nat \<times> (nat,nat,nat) factor_schema) set" where
  "addition_element_clauses callee={(0,addition_member_schema),(1,addition_callee_schema callee)}"

definition package_additions_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "package_additions_schema list_site=data_rule
    (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w)))
    {(0,156,data_x),(1,156,Pattern_Pair data_y (Pattern_Pair data_z data_w)),
     (2,79,Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4))),
     (3,47,Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)),
     (4,76,Pattern_Pair (Pattern_Pair data_y (Pattern_Variable 5)) (Pattern_Variable 5)),
     (5,list_site,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w)))
       (Pattern_Variable 5))}"

locale package_additions_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and element_site list_site entry_site callee_site :: nat
  assumes system_formed: "schema_system_formed P"
    and element_family: "\<And>c S. ((element_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>addition_element_clauses callee_site"
    and list_family: "\<And>c S. ((list_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>context_list_clauses element_site list_site"
    and entry_family: "\<And>c S. ((entry_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=package_additions_schema list_site"
    and element_call: "\<And>t. schema_call_formed P element_site t \<longleftrightarrow> term_formed t"
    and list_call: "\<And>t. schema_call_formed P list_site t \<longleftrightarrow> term_formed t"
    and entry_call: "\<And>t. schema_call_formed P entry_site t \<longleftrightarrow> term_formed t"
    and site_meaning: "\<And>t. (156,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>E u r. site_value_presents E u r t)"
    and membership_meaning: "\<And>t. (83,t)\<in>positive_meaning P \<longleftrightarrow> package_membership_result t"
    and roots_meaning: "\<And>t. (79,t)\<in>positive_meaning P \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
    and subset_meaning: "\<And>t. (47,t)\<in>positive_meaning P \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound_meaning: "\<And>t. (76,t)\<in>positive_meaning P \<longleftrightarrow>
      (76,t)\<in>positive_meaning definition_callee_list_system"
begin

sublocale listing: context_list_profile P element_site list_site
  by (rule context_list_profile.intro[OF system_formed list_family list_call])

lemma element_member:
  assumes holds: "(83,package_subject_argument e u r m)\<in>positive_meaning P" and other: "term_formed c"
  shows "(element_site,Pair_Term (Pair_Term (Pair_Term e (Pair_Term u r)) c) m)\<in>positive_meaning P"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed m"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then m else c"
  have result: "(element_site,evaluate_pattern ?h (schema_conclusion addition_member_schema))\<in>positive_meaning P"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed other holds in \<open>auto simp: element_family addition_element_clauses_def addition_member_schema_def
        schema_variables_def element_call\<close>)
  show ?thesis using result by (simp add: addition_member_schema_def)
qed

lemma element_callee:
  assumes holds: "(callee_site,Pair_Term a m)\<in>positive_meaning P"
  shows "(element_site,Pair_Term a m)\<in>positive_meaning P"
proof -
  have formed: "term_formed a" "term_formed m"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by auto
  let ?h="\<lambda>n::nat. if n=0 then a else m"
  have result: "(element_site,evaluate_pattern ?h (schema_conclusion (addition_callee_schema callee_site)))
      \<in>positive_meaning P"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed holds in \<open>auto simp: element_family addition_element_clauses_def addition_callee_schema_def
        schema_variables_def element_call\<close>)
  show ?thesis using result by (simp add: addition_callee_schema_def)
qed

lemma element_sound:
  assumes holds: "(element_site,t)\<in>positive_meaning P"
  shows "\<exists>a m. t=Pair_Term a m \<and> ((\<exists>e u r c. a=Pair_Term (Pair_Term e (Pair_Term u r)) c \<and>
    (83,package_subject_argument e u r m)\<in>positive_meaning P) \<or> (callee_site,Pair_Term a m)\<in>positive_meaning P)"
proof -
  have consequence: "(element_site,t)\<in>schema_consequences P (positive_meaning P)"
    using holds positive_meaning_unfold[of P] by blast
  obtain n S h where clause: "((element_site,n),S)\<in>system_clauses P"
    and conclusion: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning P"
    using schema_consequences_valuationD[OF consequence] by blast
  have "S=addition_member_schema \<or> S=addition_callee_schema callee_site"
    using clause by (auto simp: element_family addition_element_clauses_def)
  then show ?thesis
  proof
    assume schema: "S=addition_member_schema"
    have "(83,package_subject_argument (h 0) (h 1) (h 2) (h 3))\<in>positive_meaning P"
      using support by (auto simp: schema addition_member_schema_def)
    then show ?thesis using conclusion by (auto simp: schema addition_member_schema_def)
  next
    assume schema: "S=addition_callee_schema callee_site"
    have "(callee_site,Pair_Term (h 0) (h 1))\<in>positive_meaning P"
      using support by (auto simp: schema addition_callee_schema_def)
    then show ?thesis using conclusion by (auto simp: schema addition_callee_schema_def)
  qed
qed

lemma element_at_site:
  assumes first: "site_value_presents E u r t" and other: "term_formed c"
  shows "(element_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
    (callee_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P"
proof -
  obtain e where source: "environment_value_presents E e"
    "t=Pair_Term e (Pair_Term (use_data_term u) (Payload_Term r))"
    using first by (auto simp: site_value_presents_def site_data_term_def)
  have member: "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning P \<longleftrightarrow> (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q)"
    using package_membership_on_values[OF source(1), of u r d]
    by (simp only: membership_meaning package_membership_exact)
  show ?thesis
  proof
    assume "(element_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P"
    then show "(\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P"
      using element_sound member by (auto simp: source(2))
  next
    assume "(\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P"
    then show "(element_site,Pair_Term (Pair_Term t c) (definition_site_value d))\<in>positive_meaning P"
      using element_member[of e "use_data_term u" "Payload_Term r" "definition_site_value d" c]
        element_callee member other by (auto simp: source(2))
  qed
qed

theorem sound:
  assumes holds: "(entry_site,z)\<in>positive_meaning P"
  shows "package_additions_result (\<lambda>t. (callee_site,t)\<in>positive_meaning P) z"
proof -
  have consequence: "(entry_site,z)\<in>schema_consequences P (positive_meaning P)"
    using holds positive_meaning_unfold[of P] by blast
  obtain n S h where clause: "((entry_site,n),S)\<in>system_clauses P"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning P"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=package_additions_schema list_site" using clause by (simp add: entry_family)
  have calls: "\<exists>E u r. site_value_presents E u r (h 0)"
    "\<exists>E u r. site_value_presents E u r (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
    "(79,citation_observation_argument (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning root_family_reading_system"
    "(47,Pair_Term (h 4) (h 5))\<in>positive_meaning data_subset_system"
    "(76,Pair_Term (Pair_Term (h 1) (h 5)) (h 5))\<in>positive_meaning definition_callee_list_system"
    "(list_site,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))) (h 5))\<in>positive_meaning P"
    using support by (auto simp: schema package_additions_schema_def site_meaning roots_meaning
      subset_meaning bound_meaning)
  obtain E u r where first: "site_value_presents E u r (h 0)" using calls(1) by blast
  obtain F v s where second: "site_value_presents F v s (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
    using calls(2) by blast
  have second_formed: "term_formed (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
    using site_value_presents_formed[OF second] by blast
  have source: "environment_value_presents F (h 1)" "h 2=use_data_term v" "h 3=Payload_Term s"
    using second by (auto simp: site_value_presents_def site_data_term_def)
  obtain rs where roots_value: "h 4=data_list_term (map (\<lambda>d. definition_site_value d) rs)"
    using calls(3) by (simp only: source(2,3) root_family_reading_at_source[OF source(1)]
      inj_eq[OF use_data_term_injective] factor_term.inject) blast
  have roots: "(79,citation_observation_argument (h 1) (use_data_term v) (Payload_Term s)
      (data_list_term (map (\<lambda>d. definition_site_value d) rs)))\<in>positive_meaning root_family_reading_system"
    using calls(3) by (simp only: source(2,3) roots_value)
  obtain Q where raw: "native_root_family_at F v s Q" "rel_ran Q=set rs"
    using root_family_reading_recovers[OF source(1) roots] by blast
  obtain xs ys where bounds: "h 4=data_list_term xs" "h 5=data_list_term ys"
    "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
    using calls(4) by (auto simp: data_subset_exact)
  have entries: "\<forall>x\<in>set ys. \<exists>w q p C. x=site_data_term w q \<and> native_definition_at F w q p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
    using calls(5) by (simp only: bounds(2) definition_callee_list_on_values[OF source(1) bounds(4)])
  let ?D="\<lambda>d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  have checked: "\<forall>x\<in>set ys. \<exists>d. x=definition_site_value d \<and> ?D d"
  proof (intro ballI)
    fix x assume member: "x\<in>set ys"
    obtain w q p C where parts: "x=site_data_term w q" "native_definition_at F w q p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      using entries member by blast
    show "\<exists>d. x=definition_site_value d \<and> ?D d" by (rule exI[of _ "(w,q)"]) (use parts in auto)
  qed
  obtain ds where definitions: "ys=map (\<lambda>d. definition_site_value d) ds" "\<forall>d\<in>set ds. ?D d"
    using iffD1[OF list_range_restricted_witnesses checked] by blast
  have closed: "\<forall>d\<in>set ds. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>set ds)"
    using definitions(2) by (simp add: definitions(1))
  have root_list: "xs=map (\<lambda>d. definition_site_value d) rs"
    using roots_value bounds(1) by (simp add: data_list_term_injective)
  have roots_inside: "set rs\<subseteq>set ds" using bounds(5) root_list definitions(1) by auto
  have ef: "environment_formed F" using environment_value_presents_formed[OF source(1)] by blast
  have formed: "native_package_formed F (rel_ran Q)"
    by (simp only: raw(2) native_package_finite_closed_bound)
      (use ef roots_inside closed in \<open>auto intro!: exI[of _ "set ds"]\<close>)
  have package: "native_package_at F v s (native_program F (rel_ran Q))"
    using raw(1) formed by (auto simp: native_package_at_def)
  have reached: "native_definition_sites F (rel_ran Q)\<subseteq>set ds"
    using native_closed_bound_contains_sites[OF _ closed] roots_inside raw(2) by simp
  have members: "system_definitions (native_program F (rel_ran Q))\<subseteq>set ds"
    using reached native_package_complete_roots[OF package raw(1)] by simp
  have elements: "\<forall>x\<in>set ys.
      (element_site,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))) x)\<in>positive_meaning P"
    using listing.sound[OF calls(6)] by (auto simp: bounds(2) data_list_term_injective)
  have covered: "\<forall>d\<in>system_definitions (native_program F (rel_ran Q)).
      (\<exists>Q'. native_package_at E u r Q' \<and> d\<in>system_definitions Q') \<or>
      (callee_site,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
        (definition_site_value d))\<in>positive_meaning P"
  proof
    fix d assume inside: "d\<in>system_definitions (native_program F (rel_ran Q))"
    have "definition_site_value d\<in>set ys" using members inside definitions(1) by auto
    then have "(element_site,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
        (definition_site_value d))\<in>positive_meaning P"
      using elements by blast
    then show "(\<exists>Q'. native_package_at E u r Q' \<and> d\<in>system_definitions Q') \<or>
      (callee_site,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
        (definition_site_value d))\<in>positive_meaning P"
      by (simp only: element_at_site[OF first second_formed])
  qed
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ u], rule exI[of _ r], rule exI[of _ "h 0"],
      rule exI[of _ F], rule exI[of _ v], rule exI[of _ s],
      rule exI[of _ "Pair_Term (h 1) (Pair_Term (h 2) (h 3))"], rule exI[of _ "native_program F (rel_ran Q)"])
      (use conclusion first second package covered in \<open>simp add: schema package_additions_schema_def\<close>)
qed

theorem complete:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
    and package: "native_package_at F v s R"
    and covered: "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P"
  shows "(entry_site,Pair_Term t w)\<in>positive_meaning P"
proof -
  obtain f where target: "environment_value_presents F f"
    "w=Pair_Term f (Pair_Term (use_data_term v) (Payload_Term s))"
    using second by (auto simp: site_value_presents_def site_data_term_def)
  obtain Q where raw: "native_root_family_at F v s Q" "native_package_formed F (rel_ran Q)"
    using package by (auto simp: native_package_at_def)
  have sites: "system_definitions R=native_definition_sites F (rel_ran Q)"
    by (rule native_package_complete_roots[OF package raw(1)])
  obtain rs where reading: "(79,citation_observation_argument f (use_data_term v) (Payload_Term s)
      (data_list_term (map (\<lambda>d. definition_site_value d) rs)))\<in>positive_meaning root_family_reading_system"
    and range: "rel_ran Q=set rs" using root_family_reading_total[OF target(1) raw(1)] by blast
  have finite: "finite (system_definitions R)" using native_package_sites(2)[OF raw(2)] sites by simp
  obtain ds where rows: "set ds=system_definitions R" using finite_distinct_list[OF finite] by blast
  have defined: "\<forall>d\<in>system_definitions R. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>system_definitions R)"
    unfolding sites by (rule native_package_sites_closed_bound[OF raw(2)])
  have site_formed: "term_formed (definition_site_value d)" if "d\<in>system_definitions R" for d
    using defined that native_definition_site_data_formed by blast
  let ?rs="map (\<lambda>d. definition_site_value d) rs" and ?ys="map (\<lambda>d. definition_site_value d) ds"
  have root_inside: "set rs\<subseteq>system_definitions R"
    using range sites native_definition_roots[of "rel_ran Q" F] by auto
  have site_address: "octets_formed b" if "(a,b)\<in>system_definitions R" for a b
    using site_formed[OF that] by (simp add: site_data_term_def)
  have data: "data_elements ?ys" "data_elements ?rs" using rows root_inside site_address by auto
  have subset: "(47,Pair_Term (data_list_term ?rs) (data_list_term ?ys))\<in>positive_meaning data_subset_system"
    by (simp only: data_subset_lists) (use data rows root_inside in auto)
  have bound: "(76,Pair_Term (Pair_Term f (data_list_term ?ys)) (data_list_term ?ys))
      \<in>positive_meaning definition_callee_list_system"
  proof (simp only: definition_callee_list_on_values[OF target(1) data(1)], intro ballI)
    fix x assume "x\<in>set ?ys"
    then obtain d where d: "x=definition_site_value d" "d\<in>system_definitions R" using rows by auto
    obtain p C where own: "native_definition_at F (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>system_definitions R" using defined d(2) by blast
    have image: "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys" if "(c,S)\<in>C" for c S
      using own(2) that rows by auto
    show "\<exists>w q p C. x=site_data_term w q \<and> native_definition_at F w q p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys)"
      using d(1) own(1) image by blast
  qed
  have pair_formed: "term_formed (Pair_Term t w)" "term_formed w"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] by simp_all
  have elements: "(list_site,Pair_Term (Pair_Term t w) (data_list_term ?ys))\<in>positive_meaning P"
  proof (rule listing.complete[OF pair_formed(1)], intro ballI)
    fix x assume "x\<in>set ?ys"
    then obtain d where d: "x=definition_site_value d" "d\<in>system_definitions R" using rows by auto
    show "(element_site,Pair_Term (Pair_Term t w) x)\<in>positive_meaning P"
      using covered d(2) by (simp only: d(1) element_at_site[OF first pair_formed(2)])
  qed
  have calls: "(156,t)\<in>positive_meaning P"
    "(156,Pair_Term f (Pair_Term (use_data_term v) (Payload_Term s)))\<in>positive_meaning P"
    "(79,citation_observation_argument f (use_data_term v) (Payload_Term s) (data_list_term ?rs))
      \<in>positive_meaning P"
    "(47,Pair_Term (data_list_term ?rs) (data_list_term ?ys))\<in>positive_meaning P"
    "(76,Pair_Term (Pair_Term f (data_list_term ?ys)) (data_list_term ?ys))\<in>positive_meaning P"
    using first second target(2) reading subset bound
    by (auto simp: site_meaning roots_meaning subset_meaning bound_meaning)
  have formed: "term_formed t" "term_formed f" "term_formed (Payload_Term s)"
    "term_formed (data_list_term ?rs)" "term_formed (data_list_term ?ys)"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] target(2) data
    by (auto simp: data_list_term_formed)
  let ?h="\<lambda>n::nat. if n=0 then t else if n=1 then f else if n=2 then use_data_term v
    else if n=3 then Payload_Term s else if n=4 then data_list_term ?rs else data_list_term ?ys"
  have result: "(entry_site,evaluate_pattern ?h (schema_conclusion (package_additions_schema list_site)))
      \<in>positive_meaning P"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed calls elements target(2) in \<open>auto simp: entry_family package_additions_schema_def
        schema_variables_def entry_call\<close>)
  show ?thesis using result target(2) by (simp add: package_additions_schema_def)
qed

theorem exact:
  "(entry_site,z)\<in>positive_meaning P \<longleftrightarrow> package_additions_result (\<lambda>t. (callee_site,t)\<in>positive_meaning P) z"
proof
  assume "(entry_site,z)\<in>positive_meaning P"
  then show "package_additions_result (\<lambda>t. (callee_site,t)\<in>positive_meaning P) z" by (rule sound)
next
  assume "package_additions_result (\<lambda>t. (callee_site,t)\<in>positive_meaning P) z"
  then obtain E u r t F v s w R where parts: "z=Pair_Term t w" "site_value_presents E u r t"
    "site_value_presents F v s w" "native_package_at F v s R"
    "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P" by blast
  show "(entry_site,z)\<in>positive_meaning P" using complete[OF parts(2-5)] parts(1) by simp
qed

corollary on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(entry_site,Pair_Term t w)\<in>positive_meaning P \<longleftrightarrow> (\<exists>R. native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P))"
proof
  assume "(entry_site,Pair_Term t w)\<in>positive_meaning P"
  then have "package_additions_result (\<lambda>t. (callee_site,t)\<in>positive_meaning P) (Pair_Term t w)" by (rule sound)
  then obtain E' u' r' F' v' s' R where parts: "site_value_presents E' u' r' t" "site_value_presents F' v' s' w"
    "native_package_at F' v' s' R"
    "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E' u' r' Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P"
    by (simp only: factor_term.inject) blast
  have "E'=E \<and> u'=u \<and> r'=r" by (rule site_value_presents_unique[OF parts(1) first])
  moreover have "F'=F \<and> v'=v \<and> s'=s" by (rule site_value_presents_unique[OF parts(2) second])
  ultimately show "\<exists>R. native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P)" using parts(3,4) by blast
next
  assume "\<exists>R. native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P)"
  then obtain R where "native_package_at F v s R" "\<forall>d\<in>system_definitions R.
    (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (callee_site,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning P" by blast
  then show "(entry_site,Pair_Term t w)\<in>positive_meaning P" by (rule complete[OF first second])
qed

corollary presentation_invariance:
  assumes "site_value_presents E u r t" "site_value_presents E u r t'"
    "site_value_presents F v s w" "site_value_presents F v s w'"
    and callee_invariance: "\<And>m. (callee_site,Pair_Term (Pair_Term t w) m)\<in>positive_meaning P \<longleftrightarrow>
      (callee_site,Pair_Term (Pair_Term t' w') m)\<in>positive_meaning P"
  shows "(entry_site,Pair_Term t w)\<in>positive_meaning P \<longleftrightarrow> (entry_site,Pair_Term t' w')\<in>positive_meaning P"
  by (simp only: on_values[OF assms(1,3)] on_values[OF assms(2,4)] callee_invariance)

end

section \<open>The callee boundary: every added member stands at a use the given's environment does not hold\<close>

text \<open>
  The instance's callee reads the member's use and the given environment's artifact table, the first
  of the environment value's two tables, and holds when no row of that table has the use as its key
  (@{const keyed_list_system}, key absence at 20). Uses are compared only by the inequality of their
  self-contained data. The programs join the scope-reading components, which hold the site context
  (156) beside package membership, the root reading, the closure bound, data inclusion and key absence,
  each agreeing with the program it was proved in.
\<close>


lemma membership_complete_data_agreement:
  "systems_agree_on package_membership_system complete_data_admission_system
    (system_definitions package_membership_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def)

lemma closure_complete_data_agreement:
  "systems_agree_on package_closure_admission_system complete_data_admission_system
    (system_definitions package_closure_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def root_family_reading_system_def
    located_list_system_def)

lemma row_values_complete_data_agreement:
  "systems_agree_on row_values_system complete_data_admission_system (system_definitions row_values_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def root_family_reading_system_def
    located_list_system_def package_closure_admission_system_def definition_callee_list_system_def
    definition_callee_inclusion_system_def schema_callee_list_system_def schema_callee_inclusion_system_def
    definition_call_admission_system_def schema_family_admission_system_def schema_root_list_system_def
    schema_admission_system_def schema_material_checking_system_def material_rows_checking_system_def
    material_checking_system_def schema_instantiation_system_def premise_family_instantiation_system_def
    premise_rows_system_def material_instantiation_system_def record_instantiation_system_def
    vector_instantiation_system_def)

lemma complete_data_addition_components:
  "(83,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> package_membership_result t"
  "(79,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (79,t)\<in>positive_meaning root_family_reading_system"
  "(47,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
  "(20,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
  "{20,47,76,79,83}\<subseteq>system_definitions complete_data_admission_system"
proof -
  have keyed_agreement: "systems_agree_on keyed_list_system complete_data_admission_system
      (system_definitions keyed_list_system)"
    by (rule whole_agreement_transitive[OF row_values_keyed_agreement row_values_complete_data_agreement])
  have membership: "(d,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning package_membership_system" if "d\<in>system_definitions package_membership_system" for d
    using whole_system_agreement_meaning[OF package_membership_system_formed complete_data_admission_system_formed
      membership_complete_data_agreement that] by simp
  have closure: "(d,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning package_closure_admission_system"
    if "d\<in>system_definitions package_closure_admission_system" for d
    using whole_system_agreement_meaning[OF package_closure_admission_system_formed complete_data_admission_system_formed
      closure_complete_data_agreement that] by simp
  have keyed: "(d,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning keyed_list_system" if "d\<in>system_definitions keyed_list_system" for d
    using whole_system_agreement_meaning[OF keyed_list_system_formed complete_data_admission_system_formed
      keyed_agreement that] by simp
  show "(83,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> package_membership_result t"
    using membership[of 83] package_membership_exact[of t] by simp
  show "(79,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (79,t)\<in>positive_meaning root_family_reading_system"
    using membership[of 79] package_membership_components(2)[of t] by simp
  show "(47,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    using closure[of 47] package_closure_admission_components(2)[of t] by simp
  show "(76,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
    using closure[of 76] package_closure_admission_components(3)[of t] by simp
  show "(20,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
    using keyed[of 20] by simp
  show "{20,47,76,79,83}\<subseteq>system_definitions complete_data_admission_system"
    using whole_agreement_definitions[OF membership_complete_data_agreement]
      whole_agreement_definitions[OF closure_complete_data_agreement]
      whole_agreement_definitions[OF keyed_agreement] by auto
qed

lemma context_base_fresh:
  assumes "d\<in>{390,391,392,393}"
  shows "d\<notin>system_definitions context_base_system"
  using assms subsetD[OF context_base_subdomain, of d] by auto

definition use_absence_schema :: "(nat,nat,nat) factor_schema" where
  "use_absence_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) (Pattern_Variable 5))
      (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,20,Pattern_Pair data_w data_x)}"

definition use_absence_system :: "(nat,nat,nat,nat) schema_system" where
  "use_absence_system=add_view_definition scope_reading_components_system 393 data_x {(0,use_absence_schema)}"

definition addition_element_system :: "(nat,nat,nat,nat) schema_system" where
  "addition_element_system=add_view_definition use_absence_system 390 data_x (addition_element_clauses 393)"

definition addition_list_system :: "(nat,nat,nat,nat) schema_system" where
  "addition_list_system=add_view_definition addition_element_system 391 data_x (context_list_clauses 390 391)"

definition use_additions_system :: "(nat,nat,nat,nat) schema_system" where
  "use_additions_system=add_view_definition addition_list_system 392 data_x {(0,package_additions_schema 391)}"

lemma use_absence_system_formed [simp]: "schema_system_formed use_absence_system"
  unfolding use_absence_system_def
  using complete_data_addition_components(6)
  by (intro add_recursive_definition_formed[OF scope_reading_components_formed])
    (auto simp: use_absence_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def context_base_fresh)

lemma use_absence_definitions [simp]:
  "system_definitions use_absence_system=insert 393 (system_definitions scope_reading_components_system)"
  by (simp add: use_absence_system_def)

lemma addition_element_system_formed [simp]: "schema_system_formed addition_element_system"
  unfolding addition_element_system_def
  using complete_data_addition_components(6)
  by (intro add_recursive_definition_formed[OF use_absence_system_formed])
    (auto simp: addition_element_clauses_def addition_member_schema_def addition_callee_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      context_base_fresh)

lemma addition_element_definitions [simp]:
  "system_definitions addition_element_system=insert 390 (system_definitions use_absence_system)"
  by (simp add: addition_element_system_def)

lemma addition_list_system_formed [simp]: "schema_system_formed addition_list_system"
  unfolding addition_list_system_def
  by (rule add_recursive_definition_formed[OF addition_element_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      context_base_fresh)

lemma addition_list_definitions [simp]:
  "system_definitions addition_list_system=insert 391 (system_definitions addition_element_system)"
  by (simp add: addition_list_system_def)

lemma use_additions_system_formed [simp]: "schema_system_formed use_additions_system"
  unfolding use_additions_system_def
  using complete_data_addition_components(6)
  by (intro add_recursive_definition_formed[OF addition_list_system_formed])
    (auto simp: package_additions_schema_def context_admission_definitions
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      context_base_fresh)

lemma use_additions_definitions [simp]:
  "system_definitions use_additions_system=insert 392 (system_definitions addition_list_system)"
  by (simp add: use_additions_system_def)

lemma use_additions_call:
  "schema_call_formed use_additions_system d t \<longleftrightarrow> d\<in>system_definitions use_additions_system \<and> term_formed t"
proof -
  have absence: "schema_call_formed use_absence_system d t \<longleftrightarrow>
      d\<in>system_definitions use_absence_system \<and> term_formed t" for d t
    using added_variable_calls[OF scope_reading_components_formed
      use_absence_system_formed[unfolded use_absence_system_def] scope_reading_components_call]
    by (simp only: use_absence_system_def[symmetric])
  have element: "schema_call_formed addition_element_system d t \<longleftrightarrow>
      d\<in>system_definitions addition_element_system \<and> term_formed t" for d t
    using added_variable_calls[OF use_absence_system_formed
      addition_element_system_formed[unfolded addition_element_system_def] absence]
    by (simp only: addition_element_system_def[symmetric])
  have listing: "schema_call_formed addition_list_system d t \<longleftrightarrow>
      d\<in>system_definitions addition_list_system \<and> term_formed t" for d t
    using added_variable_calls[OF addition_element_system_formed
      addition_list_system_formed[unfolded addition_list_system_def] element]
    by (simp only: addition_list_system_def[symmetric])
  show ?thesis
    using added_variable_calls[OF addition_list_system_formed
      use_additions_system_formed[unfolded use_additions_system_def] listing]
    by (simp only: use_additions_system_def[symmetric])
qed

lemma use_additions_old_meaning:
  assumes member: "d\<in>system_definitions scope_reading_components_system"
  shows "(d,t)\<in>positive_meaning use_additions_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning scope_reading_components_system"
proof -
  have absence: "(d,t)\<in>positive_meaning use_absence_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning scope_reading_components_system"
    using added_definition_preserves_old(2)[OF scope_reading_components_formed
      use_absence_system_formed[unfolded use_absence_system_def], of d t] member
    by (auto simp: use_absence_system_def context_base_fresh)
  have element: "(d,t)\<in>positive_meaning addition_element_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning use_absence_system"
    using added_definition_preserves_old(2)[OF use_absence_system_formed
      addition_element_system_formed[unfolded addition_element_system_def], of d t] member
    by (auto simp: addition_element_system_def context_base_fresh)
  have listing: "(d,t)\<in>positive_meaning addition_list_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning addition_element_system"
    using added_definition_preserves_old(2)[OF addition_element_system_formed
      addition_list_system_formed[unfolded addition_list_system_def], of d t] member
    by (auto simp: addition_list_system_def context_base_fresh)
  have additions: "(d,t)\<in>positive_meaning use_additions_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning addition_list_system"
    using added_definition_preserves_old(2)[OF addition_list_system_formed
      use_additions_system_formed[unfolded use_additions_system_def], of d t] member
    by (auto simp: use_additions_system_def context_base_fresh)
  show ?thesis using absence element listing additions by simp
qed

lemma use_additions_components:
  "(156,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (\<exists>E u r. site_value_presents E u r t)"
  "(83,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> package_membership_result t"
  "(79,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(47,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning use_additions_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
  "(20,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
proof -
  have lower: "(d,t)\<in>positive_meaning use_additions_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning complete_data_admission_system" if "d\<in>{20,47,76,79,83}" for d
  proof -
    have inside: "d\<in>system_definitions complete_data_admission_system"
      using that complete_data_addition_components(6) by blast
    have scope: "d\<in>system_definitions scope_reading_components_system"
      using inside unfolding scope_reading_components_definitions by blast
    show ?thesis
      by (rule trans[OF use_additions_old_meaning[OF scope] scope_reading_complete_locality(2)[OF inside]])
  qed
  have context_member: "156\<in>system_definitions context_admission_system"
    unfolding context_admission_definitions by blast
  have scope: "156\<in>system_definitions scope_reading_components_system"
    using context_member unfolding scope_reading_components_definitions by blast
  show "(156,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (\<exists>E u r. site_value_presents E u r t)"
    by (rule trans[OF trans[OF use_additions_old_meaning[OF scope]
      scope_reading_context_locality(2)[OF context_member]] site_context_exact])
  show "(83,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> package_membership_result t"
    using lower[of 83] complete_data_addition_components(1)[of t] by simp
  show "(79,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
    using lower[of 79] complete_data_addition_components(2)[of t] by simp
  show "(47,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    using lower[of 47] complete_data_addition_components(3)[of t] by simp
  show "(76,t)\<in>positive_meaning use_additions_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
    using lower[of 76] complete_data_addition_components(4)[of t] by simp
  show "(20,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
    using lower[of 20] complete_data_addition_components(5)[of t] by simp
qed

lemma use_additions_families:
  "((390,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 393"
  "((391,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 390 391"
  "((392,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> c=0 \<and> S=package_additions_schema 391"
  "((393,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> c=0 \<and> S=use_absence_schema"
proof -
  have owned: "((d,c),S)\<in>system_clauses scope_reading_components_system \<Longrightarrow>
    d\<in>system_definitions scope_reading_components_system" for d c S
    using scope_reading_components_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses scope_reading_components_system" if "d\<in>{390,391,392,393}" for d c S
    using that by (auto dest: owned simp: context_admission_definitions context_base_fresh)
  show "((390,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 393"
    "((391,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 390 391"
    "((392,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> c=0 \<and> S=package_additions_schema 391"
    "((393,c),S)\<in>system_clauses use_additions_system \<longleftrightarrow> c=0 \<and> S=use_absence_schema"
    using absent by (auto simp: use_additions_system_def addition_list_system_def addition_element_system_def
      use_absence_system_def)
qed

interpretation use_additions: package_additions_profile use_additions_system 390 391 392 393
  by unfold_locales (simp_all add: use_additions_families use_additions_call use_additions_components)

section \<open>The callee reads the absence of the member's use from the given environment's artifact table\<close>

theorem use_absence_exact:
  "(393,t)\<in>positive_meaning use_additions_system \<longleftrightarrow> (\<exists>xs b c y k q.
    t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (pair_list_term xs) b) c) y) (Pair_Term k q) \<and>
    term_formed b \<and> term_formed c \<and> term_formed y \<and> term_formed q \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs))"
proof
  assume holds: "(393,t)\<in>positive_meaning use_additions_system"
  have consequence: "(393,t)\<in>schema_consequences use_additions_system (positive_meaning use_additions_system)"
    using holds positive_meaning_unfold[of use_additions_system] by blast
  obtain n S h where clause: "((393,n),S)\<in>system_clauses use_additions_system"
    and conclusion: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning use_additions_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=use_absence_schema" using clause by (simp add: use_additions_families)
  have absent: "(20,Pair_Term (h 3) (h 0))\<in>positive_meaning keyed_list_system"
    using support by (auto simp: schema use_absence_schema_def use_additions_components)
  have formed: "term_formed (h 1)" "term_formed (h 2)" "term_formed (h 4)" "term_formed (h 5)"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] conclusion
    by (simp_all add: schema use_absence_schema_def)
  show "\<exists>xs b c y k q. t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (pair_list_term xs) b) c) y) (Pair_Term k q) \<and>
    term_formed b \<and> term_formed c \<and> term_formed y \<and> term_formed q \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs)"
    using absent formed conclusion by (auto simp: keyed_list_absence schema use_absence_schema_def)
next
  assume "\<exists>xs b c y k q. t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (pair_list_term xs) b) c) y) (Pair_Term k q) \<and>
    term_formed b \<and> term_formed c \<and> term_formed y \<and> term_formed q \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs)"
  then obtain xs b c y k q where parts:
    "t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (pair_list_term xs) b) c) y) (Pair_Term k q)"
    "term_formed b" "term_formed c" "term_formed q" "term_formed k" "self_contained_term k"
    "formed_key_rows xs" "k\<notin>set (map fst xs)" "term_formed y" by blast
  have absent: "(20,Pair_Term k (pair_list_term xs))\<in>positive_meaning use_additions_system"
    using parts by (auto simp: use_additions_components keyed_list_absence)
  have rows: "term_formed (pair_list_term xs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF absent]] by simp
  let ?h="\<lambda>n::nat. if n=0 then pair_list_term xs else if n=1 then b else if n=2 then c else if n=3 then k
    else if n=4 then q else y"
  have result: "(393,evaluate_pattern ?h (schema_conclusion use_absence_schema))\<in>positive_meaning use_additions_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use parts rows absent in \<open>auto simp: use_additions_families use_absence_schema_def schema_variables_def
        use_additions_call\<close>)
  show "(393,t)\<in>positive_meaning use_additions_system" using result parts(1) by (simp add: use_absence_schema_def)
qed


lemma environment_value_uses:
  assumes source: "environment_value_presents E e"
  obtains ps b where "e=Pair_Term (pair_list_term ps) b" "term_formed b" "formed_key_rows ps"
    "\<And>w. use_data_term w\<in>set (map fst ps) \<longleftrightarrow> w\<in>environment_uses E"
proof -
  obtain a b where parts: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    "e=Pair_Term a b" using source unfolding environment_value_presents_def by blast
  obtain zs ts where rows: "set zs=environment_artifacts E"
    "list_all2 environment_artifact_entry_presents zs ts" "a=data_list_term ts"
    using parts(1) unfolding data_collection_presents_def by blast
  have shape: "\<exists>v. x=Pair_Term (use_data_term (fst z)) v" if "environment_artifact_entry_presents z x" for z x
    using that by (auto simp: environment_artifact_entry_presents_def)
  obtain ps where entries: "ts=map (\<lambda>(k,v). Pair_Term k v) ps" "map fst ps=map (\<lambda>z. use_data_term (fst z)) zs"
    using list_all2_pair_entries[where key="\<lambda>z. use_data_term (fst z)", OF rows(2) shape] by blast
  have data: "data_elements ts" by (rule environment_artifact_list_data[OF rows(2)])
  have keys: "ts=map (\<lambda>(k,v). Pair_Term k v) ps" "formed_key_rows ps"
    "map fst ps=map (\<lambda>z. use_data_term (fst z)) zs" using data entries by auto
  have formed: "term_formed b" using environment_value_presents_formed[OF source] parts(2) by simp
  have table: "set (map fst ps)=(\<lambda>z. use_data_term (fst z)) ` environment_artifacts E"
    using arg_cong[OF keys(3), of set] rows(1) by simp
  have uses: "use_data_term w\<in>set (map fst ps) \<longleftrightarrow> w\<in>environment_uses E" for w
    by (simp only: table) (force simp: environment_uses_def rel_dom_def inj_eq[OF use_data_term_injective])
  show ?thesis by (rule that[of ps b]) (use parts(2) rows(3) keys(1,2) formed uses in auto)
qed

lemma use_absence_at_site:
  assumes first: "site_value_presents E u r t" and other: "term_formed w" and address: "octets_formed (snd d)"
  shows "(393,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning use_additions_system \<longleftrightarrow>
    fst d\<notin>environment_uses E"
proof -
  obtain e where source: "environment_value_presents E e"
    "t=Pair_Term e (Pair_Term (use_data_term u) (Payload_Term r))"
    using first by (auto simp: site_value_presents_def site_data_term_def)
  obtain ps b where table: "e=Pair_Term (pair_list_term ps) b" "term_formed b" "formed_key_rows ps"
    "\<And>w. use_data_term w\<in>set (map fst ps) \<longleftrightarrow> w\<in>environment_uses E"
    using environment_value_uses[OF source(1)] by blast
  have site: "term_formed (Payload_Term r)" using site_value_presents_formed[OF first] source(2) by simp
  show ?thesis
    by (simp only: use_absence_exact source(2) table(1) site_data_term_def factor_term.inject
      pair_list_term_injective) (use table site address other in \<open>auto simp: octets_formed_def\<close>)
qed

theorem use_additions_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(392,Pair_Term t w)\<in>positive_meaning use_additions_system \<longleftrightarrow> (\<exists>R. native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      fst d\<notin>environment_uses E))"
proof -
  have address: "octets_formed (snd d)" if package: "native_package_at F v s R" and member: "d\<in>system_definitions R"
    for R d
  proof -
    obtain Q where raw: "native_root_family_at F v s Q" "native_package_formed F (rel_ran Q)"
      using package by (auto simp: native_package_at_def)
    have "d\<in>native_definition_sites F (rel_ran Q)" using member native_package_complete_roots[OF package raw(1)] by simp
    then obtain p C where "native_definition_at F (fst d) (snd d) p C" using raw(2) by (auto simp: native_package_formed_def)
    then show ?thesis using native_definition_site_data_formed by (fastforce simp: site_data_term_def)
  qed
  have other: "term_formed w" using site_value_presents_formed[OF second] by blast
  have same: "(\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      (393,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning use_additions_system) \<longleftrightarrow>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      fst d\<notin>environment_uses E)" if package: "native_package_at F v s R" for R
    using use_absence_at_site[OF first other address[OF package]] by simp
  show ?thesis by (simp only: use_additions.on_values[OF first second]) (use same in blast)
qed

corollary use_additions_presentation_invariance:
  assumes "site_value_presents E u r t" "site_value_presents E u r t'"
    "site_value_presents F v s w" "site_value_presents F v s w'"
  shows "(392,Pair_Term t w)\<in>positive_meaning use_additions_system \<longleftrightarrow>
    (392,Pair_Term t' w')\<in>positive_meaning use_additions_system"
  by (simp only: use_additions_on_values[OF assms(1,3)] use_additions_on_values[OF assms(2,4)])

section \<open>The new programs state the empty payload alone\<close>

lemma package_additions_leaves:
  "schema_leaves addition_member_schema={}"
  "schema_leaves (addition_callee_schema callee)={}"
  "schema_leaves (package_additions_schema list_site)={}"
  "schema_leaves use_absence_schema={}"
  "schema_leaves context_list_nil_schema={Payload_Term []}"
  "schema_leaves (context_list_step_schema element_site list_site)={}"
  by (simp_all add: schema_leaves_def material_leaves_def addition_member_schema_def addition_callee_schema_def
    package_additions_schema_def use_absence_schema_def context_list_nil_schema_def context_list_step_schema_def)

text \<open>
  The notion is stated once over any system holding its three sites and a callee, and its contract is
  proved for every callee meaning. The list carries the whole pair as its context, so the callee receives
  both site values with the member's site and may read either environment. The callee boundary is its instance at the absence of the member's
  use from the given environment's artifact table: every definition of the candidate's package is a
  definition of the given's package or stands at a use of no artifact of the given environment. Both
  contracts are invariant over the presentations of the two site values. The four new definitions, and
  the context-list traversal their list site uses, state no payload leaf but the empty one.
\<close>

end
