theory Development_Package_Program
  imports Development_Native_Readiness Development_Native_Verdict Development_Verdict_Witnesses
    Development_Native_Request Development_Native_Decomposition Factor_System_Relocation
    Factor_Finite_System_Fields Factor_Finite_Payload_Literals
begin

section \<open>A rule program relocated\<close>

text \<open>
  A relocation moves every site of a definition list, and every callee its rules name, by a map of
  sites; binders and premise sockets stay. The relocated list's program is the program renamed by that
  map (@{text finite_rename_system}), so an injective relocation keeps each site's meaning at the moved
  site (@{thm renamed_system_positive_meaning}). A site is an occurrence coordinate, compared only for
  equality: a relocation chooses coordinates and changes no meaning.
\<close>

definition relocated_definitions :: "('u definition_site \<Rightarrow> 'u definition_site) \<Rightarrow>
    ('u definition_site\<times>(local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list) list \<Rightarrow>
    ('u definition_site\<times>(local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list) list" where
  "relocated_definitions g ds=map (\<lambda>(d,rs). (g d,map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs)) ds"

lemma relocated_rule_program:
  "finite_rule_program (relocated_definitions g ds)=finite_rename_system g (finite_rule_program ds)"
proof -
  have interfaces: "map (\<lambda>(d,rs). (d,native_var 0)) (relocated_definitions g ds)=
      map (map_prod g id) (map (\<lambda>(d,rs). (d,native_var 0)) ds)"
    by (induction ds) (auto simp: relocated_definitions_def)
  have clauses: "concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) (relocated_definitions g ds))=
      map (map_prod (map_prod g id) (finite_rename_schema id id g))
        (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds))"
    by (induction ds) (auto simp: relocated_definitions_def case_prod_beta id_def)
  show ?thesis
    unfolding finite_rule_program_def finite_rename_system_def interfaces clauses by simp
qed

lemma relocated_definitions_sites: "fst ` set (relocated_definitions g ds)=g ` fst ` set ds"
  by (force simp: relocated_definitions_def)

lemma relocated_sites: "map fst (relocated_definitions g ds)=map g (map fst ds)"
  by (induction ds) (auto simp: relocated_definitions_def)

lemma relocated_append: "relocated_definitions g (xs@ys)=relocated_definitions g xs@relocated_definitions g ys"
  by (simp add: relocated_definitions_def)

lemma relocated_drop: "relocated_definitions g (drop n xs)=drop n (relocated_definitions g xs)"
  by (simp add: relocated_definitions_def drop_map)

lemma relocated_formed:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and injective: "inj_on g (fst ` set ds)"
  shows "schema_system_formed (decode_finite_system (finite_rule_program (relocated_definitions g ds)))"
proof -
  have "inj_on g (system_definitions (decode_finite_system (finite_rule_program ds)))"
    using injective by (simp only: finite_rule_program_definitions)
  then show ?thesis
    by (simp only: relocated_rule_program finite_rename_system_correct renamed_system_formed[OF formed])
qed

text \<open>A relocation that fixes every site of a formed rule program fixes the program: its callees are its sites.\<close>


lemma finite_rename_schema_fixed:
  assumes fixed: "\<And>e. e\<in>fset (finite_schema_dependencies F) \<Longrightarrow> g e=e"
  shows "finite_rename_schema id id g F=F"
proof -
  have "decode_finite_schema (finite_rename_schema id id g F)=rename_schema id id g (decode_finite_schema F)"
    by (rule finite_rename_schema_correct)
  also have "\<dots>=rename_schema id id id (decode_finite_schema F)"
    by (rule rename_schema_agreement) (simp_all add: fixed finite_schema_dependencies_correct[symmetric])
  also have "\<dots>=decode_finite_schema F" by (rule rename_schema_identity)
  finally show ?thesis by (simp only: decode_finite_schema_injective)
qed

lemma relocated_fixed:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and fixed: "\<And>d. d\<in>fst ` set ds \<Longrightarrow> g d=d"
  shows "relocated_definitions g ds=ds"
  unfolding relocated_definitions_def
proof (rule map_idI)
  fix x assume x: "x\<in>set ds"
  obtain d rs where xd: "x=(d,rs)" by (cases x)
  have "d\<in>fst ` set ds" using x xd by force
  then have site: "g d=d" by (rule fixed)
  have "finite_rename_schema id id g F=F" if cF: "(c,F)\<in>set rs" for c F
  proof (rule finite_rename_schema_fixed)
    fix e assume e: "e\<in>fset (finite_schema_dependencies F)"
    have "((d,c),decode_finite_schema F)\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
      unfolding finite_rule_program_clause using x xd cF by blast
    then have deps: "schema_dependencies (decode_finite_schema F)\<subseteq>fst ` set ds"
      using formed unfolding schema_system_formed_def finite_rule_program_definitions by blast
    have "e\<in>fst ` set ds" using e deps by (simp only: finite_schema_dependencies_correct) blast
    then show "g e=e" by (rule fixed)
  qed
  then have "map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs=rs" by (auto intro: map_idI)
  then show "(\<lambda>(d,rs). (g d,map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs)) x=x"
    using xd site by simp
qed

section \<open>A rule program whose definitions each belong to a formed part is formed\<close>

text \<open>
  A list of definitions with distinct sites, each of which lies in a formed rule program whose definitions the list
  holds, has a formed program: every clause is a clause of such a part, and every callee a site of it.
\<close>

lemma finite_rule_program_formed_parts:
  assumes distinct: "distinct (map fst ws)"
    and parts: "\<And>d rs. (d,rs)\<in>set ws \<Longrightarrow> \<exists>ds. (d,rs)\<in>set ds \<and> set ds\<subseteq>set ws \<and>
      schema_system_formed (decode_finite_system (finite_rule_program ds))"
  shows "schema_system_formed (decode_finite_system (finite_rule_program ws))"
proof -
  let ?W="decode_finite_system (finite_rule_program ws)"
  have interfaces: "system_interfaces ?W\<subseteq>fst ` set ws\<times>{Pattern_Variable [0]}"
    by (rule subrelI) (unfold finite_rule_program_interface, simp)
  have clauses: "system_clauses ?W=map_relation_values decode_finite_schema
      (set (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ws)))"
    by (simp only: decode_finite_system_fields finite_rule_program_def finite_schema_system.select_convs
      fset_of_list.rep_eq)
  have part: "\<exists>ds. set ds\<subseteq>set ws \<and> schema_system_formed (decode_finite_system (finite_rule_program ds)) \<and>
      ((d,c),S)\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
    if s: "((d,c),S)\<in>system_clauses ?W" for d c S
  proof -
    obtain rs F where m: "(d,rs)\<in>set ws" "(c,F)\<in>set rs" "S=decode_finite_schema F"
      using s unfolding finite_rule_program_clause by blast
    obtain ds where ds: "(d,rs)\<in>set ds" "set ds\<subseteq>set ws"
        "schema_system_formed (decode_finite_system (finite_rule_program ds))"
      using parts[OF m(1)] by blast
    show ?thesis unfolding finite_rule_program_clause using ds m by blast
  qed
  show ?thesis unfolding schema_system_formed_def
  proof (intro conjI allI impI)
    show "finite (system_interfaces ?W)" by (rule finite_subset[OF interfaces]) simp
    show "single_valued (system_interfaces ?W)"
      unfolding single_valued_def finite_rule_program_interface by simp
    show "pattern_formed p" if "(d,p)\<in>system_interfaces ?W" for d p
      using that unfolding finite_rule_program_interface by simp
    show "finite (system_clauses ?W)" unfolding clauses by (rule map_relation_values_finite, rule finite_set)
    show "single_valued (system_clauses ?W)"
      unfolding single_valued_def
    proof (intro allI impI)
      fix x S S' assume s: "(x,S)\<in>system_clauses ?W" and s': "(x,S')\<in>system_clauses ?W"
      obtain d c where x: "x=(d,c)" by (cases x)
      obtain rs F where m: "(d,rs)\<in>set ws" "(c,F)\<in>set rs" "S=decode_finite_schema F"
        using s[unfolded x] unfolding finite_rule_program_clause by blast
      obtain rs' F' where m': "(d,rs')\<in>set ws" "(c,F')\<in>set rs'" "S'=decode_finite_schema F'"
        using s'[unfolded x] unfolding finite_rule_program_clause by blast
      have same: "rs'=rs" by (rule eq_key_imp_eq_value[OF distinct m'(1) m(1)])
      obtain ds where ds: "(d,rs)\<in>set ds" "schema_system_formed (decode_finite_system (finite_rule_program ds))"
        using parts[OF m(1)] by blast
      have "((d,c),S)\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
          "((d,c),S')\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
        unfolding finite_rule_program_clause using ds(1) m m' same by blast+
      then show "S=S'" using ds(2) x unfolding schema_system_formed_def single_valued_def by blast
    qed
    fix d c S assume s: "((d,c),S)\<in>system_clauses ?W"
    then obtain ds where ds: "set ds\<subseteq>set ws" "schema_system_formed (decode_finite_system (finite_rule_program ds))"
        "((d,c),S)\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
      using part by blast
    have sub: "system_definitions (decode_finite_system (finite_rule_program ds))\<subseteq>system_definitions ?W"
      using ds(1) by (auto simp: finite_rule_program_definitions)
    show "d\<in>system_definitions ?W" "schema_formed S" "schema_dependencies S\<subseteq>system_definitions ?W"
      using ds(2,3) sub unfolding schema_system_formed_def by blast+
  qed
qed

text \<open>A rule program depends on the members of its list alone, and a list's two parts state its payloads.\<close>

lemma finite_rule_program_set:
  assumes same: "set ds=set ds'"
  shows "finite_rule_program ds=finite_rule_program ds'"
proof -
  have lifted: "fset_of_list xs=fset_of_list ys" if "set xs=set ys" for xs ys :: "'b list"
    using that by (metis fset_of_list.rep_eq fset_inject)
  have interfaces: "fset_of_list (map (\<lambda>(d,rs). (d,native_var 0)) ds)=
      fset_of_list (map (\<lambda>(d,rs). (d,native_var 0)) ds')"
    by (rule lifted) (simp only: set_map same)
  have clauses: "fset_of_list (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds))=
      fset_of_list (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds'))"
    by (rule lifted) (simp only: set_concat set_map same)
  show ?thesis unfolding finite_rule_program_def interfaces clauses ..
qed

lemma finite_rule_program_append_payloads:
  "finite_system_payloads (finite_rule_program (xs@ys))=
    finite_system_payloads (finite_rule_program xs) |\<union>| finite_system_payloads (finite_rule_program ys)"
  by (simp add: finite_system_payloads_def finite_rule_program_def fimage_funion sup_aci)

lemma finite_rename_schema_payloads:
  "finite_schema_payloads (finite_rename_schema id id g S)=finite_schema_payloads S"
  by (simp add: finite_schema_payloads_def finite_rename_schema_def finite_material_payloads_def
    finite_rename_material_def finite_term_pattern.map_id fset.map_comp comp_def case_prod_unfold)

lemma finite_rename_system_payloads:
  "finite_system_payloads (finite_rename_system g P)=finite_system_payloads P"
  by (simp add: finite_system_payloads_def finite_rename_system_def fset.map_comp comp_def case_prod_unfold
    finite_rename_schema_payloads map_prod_def)

lemma relocated_payloads:
  "finite_system_payloads (finite_rule_program (relocated_definitions g ds))=
    finite_system_payloads (finite_rule_program ds)"
  unfolding relocated_rule_program by (rule finite_rename_system_payloads)

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

lemma decomposition_relocation_inj: "inj_on decomposition_relocation {d. length (snd d)=1}"
  by (auto simp: inj_on_def decomposition_relocation_def relocate_site_def split: if_splits)

lemma decomposition_sites_single: "fst ` set decomposition_definitions\<subseteq>{d. length (snd d)=1}"
proof -
  have "list_all (\<lambda>(d,rs). length (snd d)=1) decomposition_definitions" by code_simp
  then show ?thesis by (auto simp: list_all_iff)
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
        finite_native_decomposition_def] inj_on_subset[OF decomposition_relocation_inj decomposition_sites_single]])+

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
    finite_native_decomposition_def] inj_on_subset[OF decomposition_relocation_inj decomposition_sites_single]
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
