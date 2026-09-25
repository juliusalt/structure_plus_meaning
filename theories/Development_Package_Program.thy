theory Development_Package_Program
  imports Development_Native_Readiness Development_Native_Verdict Development_Verdict_Witnesses
    Development_Native_Request Development_Native_Decomposition Factor_System_Relocation
    Factor_Finite_System_Fields Factor_Finite_Payload_Literals
begin

text \<open>
  The relocation of a definition list, its formation and its payloads are the rule programs' own
  (\<open>Native_Collection_Programs\<close>): this theory relocates the six notions and joins them.
\<close>

section \<open>The coordinates of the relocations\<close>

text \<open>
  The six notions hold their sites at one-component addresses of the use @{term "Some []"}, and they collide:
  readiness, the reach, request construction and the decomposition each hold a different family at
  @{term "(Some [],[1])"} (and on to @{term "(Some [],[4])"}), readiness and request construction differ again
  up to @{term "(Some [],[7])"}, request construction and the decomposition's rows at @{term "(Some [],[8])"} and
  @{term "(Some [],[9])"}, and request construction and the verdict's rows and mentions from
  @{term "(Some [],[11])"} to @{term "(Some [],[26])"}. The verdict, which holds the reach, the rows and the
  mentions, stays where it is, and so do the witnesses; readiness and request construction move whole under
  the address prefix @{term 1} and @{term 2}, the decomposition's own four sites under @{term 3}, so that its
  rows and mentions stay the verdict's.
\<close>

definition relocate_site :: "nat \<Rightarrow> 'u definition_site \<Rightarrow> 'u definition_site" where
  "relocate_site k d=(fst d,k#snd d)"

lemma relocate_site_inj: "inj (relocate_site k)"
  by (auto simp: inj_on_def relocate_site_def prod_eq_iff)

definition decomposition_relocation :: "local_address option definition_site \<Rightarrow> local_address option definition_site" where
  "decomposition_relocation d=(if d\<in>{decomposition_applies,decomposition_every,decomposition_defined,decomposition_declared}
    then relocate_site 3 d else d)"

text \<open>
  The relocation is injective on the decomposition's sites: its images of them are distinct, which is computed
  from the sites themselves. The injectivity rests on no length of an address: a site the relocation fixes is not
  the image of a site it moves, among the sites the decomposition holds.
\<close>

lemma decomposition_relocation_inj_on: "inj_on decomposition_relocation (fst ` set decomposition_definitions)"
proof -
  have "distinct (map decomposition_relocation (map fst decomposition_definitions))" by code_simp
  then have "inj_on decomposition_relocation (set (map fst decomposition_definitions))"
    by (rule conjunct2[OF iffD1[OF distinct_map]])
  then show ?thesis by (simp only: set_map)
qed

section \<open>The development package's program\<close>

text \<open>
  The program of the development's native package holds the six notions' definitions, relocated where they
  collide. A family two notions hold at one site is held once: the verdict holds the reach's four definitions, and
  the relocation of the decomposition fixes its rows and mentions, which are the verdict's
  (@{text decomposition_relocated}), so only its first six definitions are added. The package holds exactly the
  six (relocated) notions' definitions (@{text package_members}), at distinct sites, so every notion's meaning is
  carried to it by the join law (@{thm finite_rule_program_join}).
\<close>

lemma decomposition_relocated:
  "relocated_definitions decomposition_relocation decomposition_definitions=
    relocated_definitions decomposition_relocation (take 6 decomposition_definitions)@
      verdict_rows_definitions@drop 1 verdict_mentions_definitions"
proof -
  have drop: "drop 6 decomposition_definitions=verdict_rows_definitions@drop 1 verdict_mentions_definitions"
    by (simp add: decomposition_definitions_def development_row_definitions_def)
  have rows: "relocated_definitions decomposition_relocation verdict_rows_definitions=verdict_rows_definitions"
    by (rule relocated_fixed[OF verdict_rows_formed[unfolded verdict_rows_system_def finite_verdict_rows_def]])
      (auto simp: decomposition_relocation_def verdict_rows_definitions_def)
  have mentions: "relocated_definitions decomposition_relocation verdict_mentions_definitions=verdict_mentions_definitions"
    by (rule relocated_fixed[OF verdict_mentions_formed[unfolded verdict_mentions_system_def finite_verdict_mentions_def]])
      (auto simp: decomposition_relocation_def verdict_mentions_definitions_def)
  have "relocated_definitions decomposition_relocation decomposition_definitions=
      relocated_definitions decomposition_relocation (take 6 decomposition_definitions@drop 6 decomposition_definitions)"
    by simp
  also have "\<dots>=relocated_definitions decomposition_relocation (take 6 decomposition_definitions)@
      relocated_definitions decomposition_relocation verdict_rows_definitions@
      drop 1 (relocated_definitions decomposition_relocation verdict_mentions_definitions)"
    by (simp only: relocated_append drop relocated_drop)
  also have "\<dots>=relocated_definitions decomposition_relocation (take 6 decomposition_definitions)@
      verdict_rows_definitions@drop 1 verdict_mentions_definitions"
    by (simp only: rows mentions)
  finally show ?thesis .
qed

definition package_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "package_definitions=native_verdict_definitions@verdict_witness_definitions@
    relocated_definitions (relocate_site 1) readiness_definitions@
    relocated_definitions (relocate_site 2) native_request_definitions@
    relocated_definitions decomposition_relocation (take 6 decomposition_definitions)"

lemma package_members:
  "set package_definitions=set native_verdict_definitions\<union>set reach_definitions\<union>set verdict_witness_definitions\<union>
    set (relocated_definitions (relocate_site 1) readiness_definitions)\<union>
    set (relocated_definitions (relocate_site 2) native_request_definitions)\<union>
    set (relocated_definitions decomposition_relocation decomposition_definitions)"
proof -
  have reach: "set reach_definitions\<subseteq>set native_verdict_definitions"
    using native_verdict_whole(3) by (auto simp: verdict_unreached_definitions_def)
  have rows: "set verdict_rows_definitions\<subseteq>set native_verdict_definitions" by (rule native_verdict_whole(1))
  have mentions: "set (drop 1 verdict_mentions_definitions)\<subseteq>set native_verdict_definitions"
    by (auto simp: native_verdict_definitions_def)
  show ?thesis using reach rows mentions by (auto simp: package_definitions_def decomposition_relocated)
qed

definition finite_package_program :: "local_address option finite_native_system" where
  "finite_package_program=finite_rule_program package_definitions"

definition package_program :: "local_address option native_system" where
  "package_program=decode_finite_system finite_package_program"

lemma package_distinct: "distinct (map fst package_definitions)"
  unfolding package_definitions_def map_append relocated_sites by code_simp

lemma package_parts_formed:
  "schema_system_formed (decode_finite_system (finite_rule_program native_verdict_definitions))"
  "schema_system_formed (decode_finite_system (finite_rule_program reach_definitions))"
  "schema_system_formed (decode_finite_system (finite_rule_program verdict_witness_definitions))"
  "schema_system_formed (decode_finite_system (finite_rule_program
    (relocated_definitions (relocate_site 1) readiness_definitions)))"
  "schema_system_formed (decode_finite_system (finite_rule_program
    (relocated_definitions (relocate_site 2) native_request_definitions)))"
  "schema_system_formed (decode_finite_system (finite_rule_program
    (relocated_definitions decomposition_relocation decomposition_definitions)))"
  by (rule native_verdict_formed[unfolded native_verdict_system_def finite_native_verdict_def]
      native_reach_formed[unfolded native_reach_system_def finite_native_reach_def]
      verdict_witness_formed[unfolded verdict_witness_system_def finite_verdict_witnesses_def]
      relocated_formed[OF native_readiness_formed[unfolded native_readiness_system_def finite_native_readiness_def]
        inj_on_subset[OF relocate_site_inj subset_UNIV]]
      relocated_formed[OF native_request_formed[unfolded native_request_system_def finite_native_request_def]
        inj_on_subset[OF relocate_site_inj subset_UNIV]]
      relocated_formed[OF native_decomposition_formed[unfolded native_decomposition_system_def
        finite_native_decomposition_def] decomposition_relocation_inj_on])+

lemma package_program_formed: "schema_system_formed package_program"
  unfolding package_program_def finite_package_program_def
proof (rule finite_rule_program_formed_parts[OF package_distinct])
  fix d rs assume m: "(d,rs)\<in>set package_definitions"
  have witness: "\<exists>ds. (d,rs)\<in>set ds \<and> set ds\<subseteq>set package_definitions \<and>
      schema_system_formed (decode_finite_system (finite_rule_program ds))"
    if "(d,rs)\<in>set ds" "set ds\<subseteq>set package_definitions"
      "schema_system_formed (decode_finite_system (finite_rule_program ds))" for ds
    using that by blast
  have subs: "set native_verdict_definitions\<subseteq>set package_definitions"
    "set reach_definitions\<subseteq>set package_definitions"
    "set verdict_witness_definitions\<subseteq>set package_definitions"
    "set (relocated_definitions (relocate_site 1) readiness_definitions)\<subseteq>set package_definitions"
    "set (relocated_definitions (relocate_site 2) native_request_definitions)\<subseteq>set package_definitions"
    "set (relocated_definitions decomposition_relocation decomposition_definitions)\<subseteq>set package_definitions"
    by (auto simp: package_members)
  from m[unfolded package_members] consider "(d,rs)\<in>set native_verdict_definitions" | "(d,rs)\<in>set reach_definitions"
    | "(d,rs)\<in>set verdict_witness_definitions"
    | "(d,rs)\<in>set (relocated_definitions (relocate_site 1) readiness_definitions)"
    | "(d,rs)\<in>set (relocated_definitions (relocate_site 2) native_request_definitions)"
    | "(d,rs)\<in>set (relocated_definitions decomposition_relocation decomposition_definitions)"
    by blast
  then show "\<exists>ds. (d,rs)\<in>set ds \<and> set ds\<subseteq>set package_definitions \<and>
      schema_system_formed (decode_finite_system (finite_rule_program ds))"
  proof cases
    case 1 then show ?thesis by (rule witness[OF _ subs(1) package_parts_formed(1)])
  next
    case 2 then show ?thesis by (rule witness[OF _ subs(2) package_parts_formed(2)])
  next
    case 3 then show ?thesis by (rule witness[OF _ subs(3) package_parts_formed(3)])
  next
    case 4 then show ?thesis by (rule witness[OF _ subs(4) package_parts_formed(4)])
  next
    case 5 then show ?thesis by (rule witness[OF _ subs(5) package_parts_formed(5)])
  next
    case 6 then show ?thesis by (rule witness[OF _ subs(6) package_parts_formed(6)])
  qed
qed

section \<open>Every notion keeps its meaning in the package\<close>

lemma package_join:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and whole: "set ds\<subseteq>set package_definitions" and site: "d\<in>fst ` set ds"
  shows "(d,t)\<in>positive_meaning package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning (decode_finite_system (finite_rule_program ds))"
  unfolding package_program_def finite_package_program_def
  by (rule finite_rule_program_join[OF package_program_formed[unfolded package_program_def finite_package_program_def]
    package_distinct formed whole site])

lemma package_relocated:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and injective: "inj_on g (fst ` set ds)"
    and whole: "set (relocated_definitions g ds)\<subseteq>set package_definitions" and site: "d\<in>fst ` set ds"
  shows "(g d,t)\<in>positive_meaning package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning (decode_finite_system (finite_rule_program ds))"
proof -
  let ?P="decode_finite_system (finite_rule_program ds)"
  have renamed: "decode_finite_system (finite_rule_program (relocated_definitions g ds))=rename_system g ?P"
    by (simp only: relocated_rule_program finite_rename_system_correct)
  have defs: "system_definitions ?P=fst ` set ds" by (rule finite_rule_program_definitions)
  have inj: "inj_on g (system_definitions ?P)" using injective by (simp only: defs)
  have rformed: "schema_system_formed (decode_finite_system (finite_rule_program (relocated_definitions g ds)))"
    by (rule relocated_formed[OF formed injective])
  have member: "d\<in>system_definitions ?P" using site by (simp only: defs)
  have rsite: "g d\<in>fst ` set (relocated_definitions g ds)"
    using site by (simp add: relocated_definitions_sites)
  have "(g d,t)\<in>positive_meaning package_program \<longleftrightarrow>
      (g d,t)\<in>positive_meaning (decode_finite_system (finite_rule_program (relocated_definitions g ds)))"
    by (rule package_join[OF rformed whole rsite])
  also have "\<dots> \<longleftrightarrow> (d,t)\<in>positive_meaning ?P"
    unfolding renamed by (rule renamed_system_meaning_at[OF formed inj member])
  finally show ?thesis .
qed

text \<open>One transport per notion: at each of its sites, its meaning in the package is its meaning in its own program.\<close>

theorem package_verdict:
  assumes "d\<in>fst ` set native_verdict_definitions"
  shows "(d,t)\<in>positive_meaning package_program \<longleftrightarrow> (d,t)\<in>positive_meaning native_verdict_system"
  unfolding native_verdict_system_def finite_native_verdict_def
  by (rule package_join[OF package_parts_formed(1) _ assms]) (auto simp: package_members)

theorem package_reach:
  assumes "d\<in>fst ` set reach_definitions"
  shows "(d,t)\<in>positive_meaning package_program \<longleftrightarrow> (d,t)\<in>positive_meaning native_reach_system"
  unfolding native_reach_system_def finite_native_reach_def
  by (rule package_join[OF package_parts_formed(2) _ assms]) (auto simp: package_members)

theorem package_witnesses:
  assumes "d\<in>fst ` set verdict_witness_definitions"
  shows "(d,t)\<in>positive_meaning package_program \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_witness_system"
  unfolding verdict_witness_system_def finite_verdict_witnesses_def
  by (rule package_join[OF package_parts_formed(3) _ assms]) (auto simp: package_members)

theorem package_readiness:
  assumes "d\<in>fst ` set readiness_definitions"
  shows "(relocate_site 1 d,t)\<in>positive_meaning package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_readiness_system"
  unfolding native_readiness_system_def finite_native_readiness_def
  by (rule package_relocated[OF native_readiness_formed[unfolded native_readiness_system_def finite_native_readiness_def]
    inj_on_subset[OF relocate_site_inj subset_UNIV] _ assms]) (auto simp: package_members)

theorem package_request:
  assumes "d\<in>fst ` set native_request_definitions"
  shows "(relocate_site 2 d,t)\<in>positive_meaning package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_request_system"
  unfolding native_request_system_def finite_native_request_def
  by (rule package_relocated[OF native_request_formed[unfolded native_request_system_def finite_native_request_def]
    inj_on_subset[OF relocate_site_inj subset_UNIV] _ assms]) (auto simp: package_members)

theorem package_decomposition:
  assumes "d\<in>fst ` set decomposition_definitions"
  shows "(decomposition_relocation d,t)\<in>positive_meaning package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_decomposition_system"
  unfolding native_decomposition_system_def finite_native_decomposition_def
  by (rule package_relocated[OF native_decomposition_formed[unfolded native_decomposition_system_def
    finite_native_decomposition_def] decomposition_relocation_inj_on
    _ assms]) (auto simp: package_members)

section \<open>The package reads no octet as structure\<close>

text \<open>
  By the criterion of \<open>Factor_Positive_Parametricity\<close>, the payloads a program states are the octets it reads as
  structure. The package's are those of the notions it joins, which a relocation does not change: the empty payload
  alone.
\<close>

lemma finite_native_readiness_payloads: "finite_system_payloads finite_native_readiness |\<subseteq>| {|[]|}"
  by code_simp

lemma finite_native_reach_payloads: "finite_system_payloads finite_native_reach |\<subseteq>| {|[]|}"
  by code_simp

lemma finite_verdict_witnesses_payloads: "finite_system_payloads finite_verdict_witnesses |\<subseteq>| {|[]|}"
  by code_simp

lemma finite_package_payloads: "finite_system_payloads finite_package_program={|[]|}"
proof -
  have joined: "finite_package_program=finite_rule_program (native_verdict_definitions@reach_definitions@
      verdict_witness_definitions@relocated_definitions (relocate_site 1) readiness_definitions@
      relocated_definitions (relocate_site 2) native_request_definitions@
      relocated_definitions decomposition_relocation decomposition_definitions)"
    unfolding finite_package_program_def by (rule finite_rule_program_set) (simp add: package_members Un_assoc)
  have parts: "finite_system_payloads finite_package_program=finite_system_payloads finite_native_verdict |\<union>|
      (finite_system_payloads finite_native_reach |\<union>| (finite_system_payloads finite_verdict_witnesses |\<union>|
      (finite_system_payloads finite_native_readiness |\<union>| (finite_system_payloads finite_native_request |\<union>|
      finite_system_payloads finite_native_decomposition))))"
    unfolding joined finite_rule_program_append_payloads relocated_payloads finite_native_verdict_def
      finite_native_reach_def finite_verdict_witnesses_def finite_native_readiness_def finite_native_request_def
      finite_native_decomposition_def
    by (rule refl)
  have rest: "finite_system_payloads finite_native_reach |\<union>| (finite_system_payloads finite_verdict_witnesses |\<union>|
      (finite_system_payloads finite_native_readiness |\<union>| (finite_system_payloads finite_native_request |\<union>|
      {|[]|}))) |\<subseteq>| {|[]|}"
    by (intro le_supI order.refl finite_native_reach_payloads finite_verdict_witnesses_payloads
      finite_native_readiness_payloads finite_native_request_payloads)
  show ?thesis
    unfolding parts finite_native_verdict_payloads finite_native_decomposition_payloads by (rule sup.absorb1[OF rest])
qed

theorem package_payloads: "system_payloads package_program={[]}"
  using finite_system_payloads_exact[of finite_package_program]
  by (simp add: package_program_def finite_package_payloads)

end
