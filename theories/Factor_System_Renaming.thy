theory Factor_System_Renaming
  imports Factor_System_Clauses
begin

section \<open>Relocating definition identities and every callee occurrence together\<close>

definition rename_system ::
  "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'e,'c) schema_system" where
  "rename_system g P =
    \<lparr>system_interfaces = map_prod g id ` system_interfaces P,
      system_clauses = map_prod (map_prod g id) (rename_schema id id g) ` system_clauses P\<rparr>"

lemma renamed_system_interface:
  "(e,p) \<in> system_interfaces (rename_system g P) \<longleftrightarrow>
    (\<exists>d. (d,p) \<in> system_interfaces P \<and> e=g d)"
  by (auto simp: rename_system_def map_prod_def intro: rev_image_eqI)

lemma renamed_system_clause:
  "((e,c),S) \<in> system_clauses (rename_system g P) \<longleftrightarrow>
    (\<exists>d T. ((d,c),T) \<in> system_clauses P \<and> e=g d \<and> S=rename_schema id id g T)"
  by (auto simp: rename_system_def map_prod_def intro: rev_image_eqI)

lemma renamed_system_definitions:
  "system_definitions (rename_system g P) = g ` system_definitions P"
  by (simp add: system_definitions_def rename_system_def pair_image_domain map_prod_def)

lemma system_clause_owner:
  assumes formed: "schema_system_formed P" and key: "dc \<in> rel_dom (system_clauses P)"
  shows "fst dc \<in> system_definitions P"
proof -
  obtain S where entry: "(dc,S) \<in> system_clauses P" using key by (auto simp: rel_dom_def)
  show ?thesis using formed entry by (cases dc) (auto simp: schema_system_formed_def)
qed

lemma renamed_system_agreeing_coordinates:
  assumes formed: "schema_system_formed P"
    and agree: "\<forall>d\<in>system_definitions P. g d=h d"
  shows "rename_system g P=rename_system h P"
proof -
  have clauses: "rename_schema id id g S=rename_schema id id h S"
    if "((d,c),S)\<in>system_clauses P" for d c S
  proof -
    have dependencies: "schema_dependencies S\<subseteq>system_definitions P"
      using formed that unfolding schema_system_formed_def by blast
    have callees: "\<forall>e\<in>schema_dependencies S. g e=h e" using dependencies agree by blast
    show ?thesis by (rule rename_schema_agreement[OF _ _ callees]) simp_all
  qed
  show ?thesis by (rule schema_system.equality)
    (use clauses formed agree in \<open>auto simp: rename_system_def map_prod_def
      system_definitions_def rel_dom_def schema_system_formed_def intro!: image_cong\<close>)
qed

theorem renamed_system_formed:
  fixes P :: "('a,'s,'d,'c) schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
  shows "schema_system_formed (rename_system g P)"
proof -
  let ?Q = "rename_system g P"
  have finite: "finite (system_interfaces ?Q)" "finite (system_clauses ?Q)"
    using formed by (auto simp: rename_system_def schema_system_formed_def)
  have isv: "single_valued (system_interfaces P)" and csv: "single_valued (system_clauses P)"
    using formed by (auto simp: schema_system_formed_def)
  have iinj: "inj_on g (rel_dom (system_interfaces P))" using injective by (simp add: system_definitions_def)
  have target_isv: "single_valued (system_interfaces ?Q)"
    using single_valued_pair_image[OF isv iinj, where g=id] by (simp add: rename_system_def map_prod_def)
  have cinj: "inj_on (map_prod g id) (rel_dom (system_clauses P))"
  proof (rule inj_onI)
    fix x y :: "'d \<times> 'c"
    assume xm: "x \<in> rel_dom (system_clauses P)" and ym: "y \<in> rel_dom (system_clauses P)"
      and same: "map_prod g id x = map_prod g id y"
    have xd: "fst x \<in> system_definitions P" by (rule system_clause_owner[OF formed xm])
    have yd: "fst y \<in> system_definitions P" by (rule system_clause_owner[OF formed ym])
    have first: "g (fst x) = g (fst y)" using same by (metis fst_map_prod)
    have second: "snd x = snd y" using same by (metis snd_map_prod id_apply)
    have original: "fst x = fst y" by (rule inj_onD[OF injective first xd yd])
    show "x=y" by (rule prod_eqI[OF original second])
  qed
  have target_csv: "single_valued (system_clauses ?Q)"
    using single_valued_pair_image[OF csv cinj, where g="rename_schema id id g"]
    by (simp add: rename_system_def map_prod_def)
  have interfaces: "\<forall>d p. (d,p) \<in> system_interfaces ?Q \<longrightarrow> pattern_formed p"
    using formed by (auto simp: renamed_system_interface schema_system_formed_def)
  have clauses: "\<forall>d c S. ((d,c),S) \<in> system_clauses ?Q \<longrightarrow>
    d \<in> system_definitions ?Q \<and> schema_formed S \<and> schema_dependencies S \<subseteq> system_definitions ?Q"
  proof (intro allI impI)
    fix d c S assume entry: "((d,c),S) \<in> system_clauses ?Q"
    obtain e T where original: "((e,c),T) \<in> system_clauses P" "d=g e" "S=rename_schema id id g T"
      using entry by (auto simp: renamed_system_clause)
    have source: "e \<in> system_definitions P" "schema_formed T" "schema_dependencies T \<subseteq> system_definitions P"
      using formed original(1) by (auto simp: schema_system_formed_def)
    have schema: "schema_formed S" using renamed_schema_formed[OF source(2), of id id g] original(3) by simp
    have deps: "schema_dependencies S \<subseteq> system_definitions ?Q"
      using image_mono[OF source(3), of g] original(3)
      by (simp only: renamed_schema_dependencies renamed_system_definitions)
    have owner: "d \<in> system_definitions ?Q" using imageI[OF source(1), of g] original(2) by (simp add: renamed_system_definitions)
    show "d \<in> system_definitions ?Q \<and> schema_formed S \<and> schema_dependencies S \<subseteq> system_definitions ?Q"
      using owner schema deps by blast
  qed
  show ?thesis using finite target_isv target_csv interfaces clauses by (simp add: schema_system_formed_def)
qed

lemma renamed_system_interface_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "d \<in> system_definitions P"
  shows "(g d,p) \<in> system_interfaces (rename_system g P) \<longleftrightarrow> (d,p) \<in> system_interfaces P"
proof
  assume "(g d,p) \<in> system_interfaces (rename_system g P)"
  then obtain e where entry: "(e,p) \<in> system_interfaces P" "g d=g e" by (auto simp: renamed_system_interface)
  have inside: "e \<in> system_definitions P" using entry(1) by (auto simp: system_definitions_def rel_dom_def)
  have same: "d=e" by (rule inj_onD[OF injective entry(2) member inside])
  show "(d,p) \<in> system_interfaces P" using entry(1) same by simp
next
  assume "(d,p) \<in> system_interfaces P"
  then show "(g d,p) \<in> system_interfaces (rename_system g P)" by (auto simp: renamed_system_interface)
qed

lemma renamed_system_clause_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "d \<in> system_definitions P"
  shows "(c,T) \<in> system_clause_family (rename_system g P) (g d) \<longleftrightarrow>
    (\<exists>S. (c,S) \<in> system_clause_family P d \<and> T=rename_schema id id g S)"
proof
  assume "(c,T) \<in> system_clause_family (rename_system g P) (g d)"
  then obtain e S where entry: "((e,c),S) \<in> system_clauses P" "g d=g e" "T=rename_schema id id g S"
    by (auto simp: renamed_system_clause)
  have key: "(e,c) \<in> rel_dom (system_clauses P)" by (rule rel_domI[OF entry(1)])
  have inside: "e \<in> system_definitions P" using system_clause_owner[OF formed key] by simp
  have same: "d=e" by (rule inj_onD[OF injective entry(2) member inside])
  show "\<exists>S. (c,S) \<in> system_clause_family P d \<and> T=rename_schema id id g S" using entry same by auto
next
  assume "\<exists>S. (c,S) \<in> system_clause_family P d \<and> T=rename_schema id id g S"
  then show "(c,T) \<in> system_clause_family (rename_system g P) (g d)"
    by (auto simp: renamed_system_clause)
qed

lemma renamed_system_call:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "d \<in> system_definitions P"
  shows "schema_call_formed (rename_system g P) (g d) t \<longleftrightarrow> schema_call_formed P d t"
  using formed renamed_system_formed[OF formed injective]
  by (simp only: schema_call_formed_def renamed_system_interface_at[OF formed injective member])

text \<open>
  The same injective map moves definition owners, interface keys, clause keys,
  and every callee occurrence. Interface patterns, private binders, premise
  sockets, literal targets, and material operands retain their source values.
  Injectivity is required only on the complete source definition set.
\<close>

end
