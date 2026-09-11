theory Factor_Program_Positions
  imports Factor_System_Alpha Factor_Packages
begin

section \<open>Program-local coordinates become exact semantic-use sites\<close>

definition positioned_program ::
  "(local_address,local_address,'u definition_site,local_address) schema_system \<Rightarrow>
    ('u definition_site,'u definition_site,'u definition_site,'u definition_site) schema_system" where
  "positioned_program P =
    \<lparr>system_interfaces = (\<lambda>(d,p). (d,rename_pattern (Pair (fst d)) p)) ` system_interfaces P,
     system_clauses = (\<lambda>((d,c),S). ((d,(fst d,c)),
       rename_schema (Pair (fst d)) (Pair (fst d)) id S)) ` system_clauses P\<rparr>"

lemma positioned_interface_entry:
  "(d,q) \<in> system_interfaces (positioned_program P) \<longleftrightarrow>
    (\<exists>p. (d,p) \<in> system_interfaces P \<and> q=rename_pattern (Pair (fst d)) p)"
  by (auto simp: positioned_program_def intro: rev_image_eqI)

lemma positioned_clause_entry:
  "((d,k),T) \<in> system_clauses (positioned_program P) \<longleftrightarrow>
    (\<exists>c S. ((d,c),S) \<in> system_clauses P \<and> k=(fst d,c) \<and>
      T=rename_schema (Pair (fst d)) (Pair (fst d)) id S)"
  by (auto simp: positioned_program_def intro: rev_image_eqI)

lemma positioned_definitions [simp]:
  "system_definitions (positioned_program P) = system_definitions P"
  by (auto simp: system_definitions_def rel_dom_def positioned_interface_entry)

lemma positioned_interface_functional:
  assumes "single_valued (system_interfaces P)"
  shows "single_valued (system_interfaces (positioned_program P))"
  using assms by (auto simp: single_valued_def positioned_interface_entry; blast)

lemma positioned_clauses_functional:
  assumes "single_valued (system_clauses P)"
  shows "single_valued (system_clauses (positioned_program P))"
  using assms by (auto simp: single_valued_def positioned_clause_entry; blast)

lemma positioned_schema_variant:
  "schema_alpha_variant S (rename_schema (Pair u) (Pair u) id S)"
  unfolding schema_alpha_variant_def
  by (rule exI[of _ "Pair u"], rule exI[of _ "Pair u"]) (auto simp: inj_on_def)

lemma positioned_program_formed:
  assumes formed: "schema_system_formed P"
  shows "schema_system_formed (positioned_program P)"
proof -
  have iff: "finite (system_interfaces (positioned_program P))"
    and cf: "finite (system_clauses (positioned_program P))"
    using formed by (auto simp: schema_system_formed_def positioned_program_def)
  have isv: "single_valued (system_interfaces (positioned_program P))"
    by (rule positioned_interface_functional) (use formed in \<open>simp add: schema_system_formed_def\<close>)
  have csv: "single_valued (system_clauses (positioned_program P))"
    by (rule positioned_clauses_functional) (use formed in \<open>simp add: schema_system_formed_def\<close>)
  have patterns: "\<forall>d p. (d,p) \<in> system_interfaces (positioned_program P) \<longrightarrow> pattern_formed p"
  proof (intro allI impI)
    fix d p assume member: "(d,p) \<in> system_interfaces (positioned_program P)"
    obtain q where source: "(d,q) \<in> system_interfaces P" and pp: "p=rename_pattern (Pair (fst d)) q"
      using member by (auto simp: positioned_interface_entry)
    have qf: "pattern_formed q" using formed source unfolding schema_system_formed_def by blast+
    have "pattern_formed (rename_pattern (Pair (fst d)) q)"
      using qf by (induction q) auto
    then show "pattern_formed p" using pp by simp
  qed
  have clauses: "\<forall>d c S. ((d,c),S) \<in> system_clauses (positioned_program P) \<longrightarrow>
    d \<in> system_definitions (positioned_program P) \<and> schema_formed S \<and>
    schema_dependencies S \<subseteq> system_definitions (positioned_program P)"
  proof (intro allI impI)
    fix d c S assume member: "((d,c),S) \<in> system_clauses (positioned_program P)"
    obtain k T where source: "((d,k),T) \<in> system_clauses P"
      and sp: "S=rename_schema (Pair (fst d)) (Pair (fst d)) id T"
      using member by (auto simp: positioned_clause_entry)
    have df: "d \<in> system_definitions P" and tf: "schema_formed T"
      and deps: "schema_dependencies T \<subseteq> system_definitions P"
      using formed source unfolding schema_system_formed_def by blast+
    have variant: "schema_alpha_variant T S" using positioned_schema_variant[of T "fst d"] sp by simp
    have sf: "schema_formed S" by (rule schema_alpha_formed[OF variant tf])
    have same: "schema_dependencies S=schema_dependencies T" by (rule schema_alpha_dependencies[OF variant])
    show "d \<in> system_definitions (positioned_program P) \<and> schema_formed S \<and>
      schema_dependencies S \<subseteq> system_definitions (positioned_program P)"
      using df sf deps same by simp
  qed
  show ?thesis using iff cf isv csv patterns clauses by (simp add: schema_system_formed_def)
qed

lemma positioned_interface:
  assumes formed: "schema_system_formed P" and member: "d \<in> system_definitions P"
  shows "system_interface (positioned_program P) d =
    rename_pattern (Pair (fst d)) (system_interface P d)"
proof -
  have source: "(d,system_interface P d) \<in> system_interfaces P"
    by (rule system_interface_member[OF formed member])
  have target: "(d,rename_pattern (Pair (fst d)) (system_interface P d)) \<in>
    system_interfaces (positioned_program P)"
    unfolding positioned_interface_entry by (rule exI[of _ "system_interface P d"]) (use source in simp)
  show ?thesis by (rule system_interface_unique[OF positioned_program_formed[OF formed] target])
qed

lemma positioned_clause_family:
  fixes P :: "(local_address,local_address,'u definition_site,local_address) schema_system"
  shows "system_clause_family (positioned_program P) d =
    map_prod (Pair (fst d)) (rename_schema (Pair (fst d)) (Pair (fst d)) id) ` system_clause_family P d"
proof (rule set_eqI)
  fix z :: "'u definition_site \<times> ('u definition_site,'u definition_site,'u definition_site) factor_schema"
  obtain k T where zp: "z=(k,T)" by (cases z) auto
  let ?F = "map_prod (Pair (fst d)) (rename_schema (Pair (fst d)) (Pair (fst d)) id)"
  show "z \<in> system_clause_family (positioned_program P) d \<longleftrightarrow> z \<in> ?F ` system_clause_family P d"
    unfolding zp
  proof
    assume member: "(k,T) \<in> system_clause_family (positioned_program P) d"
    have clause: "((d,k),T) \<in> system_clauses (positioned_program P)"
      using member by (simp only: system_clause_member)
    obtain c S where source: "((d,c),S) \<in> system_clauses P"
      and kp: "k=(fst d,c)" and tp: "T=rename_schema (Pair (fst d)) (Pair (fst d)) id S"
      using clause unfolding positioned_clause_entry by blast
    have old: "(c,S) \<in> system_clause_family P d" using source by (simp only: system_clause_member)
    show "(k,T) \<in> ?F ` system_clause_family P d"
      by (rule rev_image_eqI[OF old]) (use kp tp in simp)
  next
    assume member: "(k,T) \<in> ?F ` system_clause_family P d"
    obtain c S where old: "(c,S) \<in> system_clause_family P d"
      and kp: "k=(fst d,c)" and tp: "T=rename_schema (Pair (fst d)) (Pair (fst d)) id S"
      using member by (auto simp: map_prod_def)
    have source: "((d,c),S) \<in> system_clauses P" using old by (simp only: system_clause_member)
    have clause: "((d,k),T) \<in> system_clauses (positioned_program P)"
      unfolding positioned_clause_entry
      by (rule exI[of _ c], rule exI[of _ S]) (use source kp tp in simp)
    show "(k,T) \<in> system_clause_family (positioned_program P) d"
      using clause by (simp only: system_clause_member)
  qed
qed

lemma positioned_family_variant:
  assumes fin: "finite C" and sv: "single_valued C"
  shows "schema_family_variant (Pair u) C (map_prod (Pair u) (rename_schema (Pair u) (Pair u) id) ` C)"
proof -
  let ?D = "map_prod (Pair u) (rename_schema (Pair u) (Pair u) id) ` C"
  have inj: "inj_on (Pair u) (rel_dom C)" by (auto simp: inj_on_def)
  have dsv: "single_valued ?D"
    using single_valued_pair_image[OF sv inj, where g="rename_schema (Pair u) (Pair u) id"]
    by (simp add: map_prod_def)
  have domain: "rel_dom ?D=Pair u ` rel_dom C"
    using pair_image_domain[where R=C and f="Pair u" and g="rename_schema (Pair u) (Pair u) id"]
    by (simp add: map_prod_def)
  have variants: "\<forall>c S. (c,S) \<in> C \<longrightarrow> (\<exists>T. ((u,c),T) \<in> ?D \<and> schema_alpha_variant S T)"
  proof (intro allI impI)
    fix c S assume member: "(c,S) \<in> C"
    have image: "((u,c),rename_schema (Pair u) (Pair u) id S) \<in> ?D"
      using imageI[OF member, of "map_prod (Pair u) (rename_schema (Pair u) (Pair u) id)"] by simp
    show "\<exists>T. ((u,c),T) \<in> ?D \<and> schema_alpha_variant S T"
      by (rule exI[of _ "rename_schema (Pair u) (Pair u) id S"])
         (use image positioned_schema_variant[of S u] in simp)
  qed
  show ?thesis using inj fin dsv domain variants by (simp add: schema_family_variant_def)
qed

theorem positioned_program_variant:
  assumes formed: "schema_system_formed P"
  shows "system_alpha_variant P (positioned_program P)"
proof -
  have boundaries: "\<forall>d\<in>system_definitions P. \<exists>f h.
    inj_on f (pattern_variables (system_interface P d)) \<and>
    system_interface (positioned_program P) d=rename_pattern f (system_interface P d) \<and>
    schema_family_variant h (system_clause_family P d) (system_clause_family (positioned_program P) d)"
  proof (intro ballI)
    fix d assume member: "d \<in> system_definitions P"
    have family: "schema_family_variant (Pair (fst d)) (system_clause_family P d)
      (system_clause_family (positioned_program P) d)"
      unfolding positioned_clause_family
      by (rule positioned_family_variant[OF system_clause_family_finite[OF formed]
        system_clause_family_functional[OF formed]])
    show "\<exists>f h. inj_on f (pattern_variables (system_interface P d)) \<and>
      system_interface (positioned_program P) d=rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) (system_clause_family (positioned_program P) d)"
      by (rule exI[of _ "Pair (fst d)"], rule exI[of _ "Pair (fst d)"])
         (use family positioned_interface[OF formed member] in \<open>auto simp: inj_on_def\<close>)
  qed
  show ?thesis using formed positioned_program_formed[OF formed] boundaries
    by (simp add: system_alpha_variant_def)
qed

theorem positioned_program_meaning:
  assumes "schema_system_formed P"
  shows "positive_meaning (positioned_program P) = positive_meaning P"
  using system_alpha_positive_meaning[OF positioned_program_variant[OF assms]] by simp

theorem positioned_program_calls:
  assumes "schema_system_formed P"
  shows "schema_call_formed (positioned_program P) d t \<longleftrightarrow> schema_call_formed P d t"
  using system_alpha_calls[OF positioned_program_variant[OF assms]] by blast

text \<open>
  Each local clause, binder, and socket coordinate is paired with the use of its
  owning native definition. These are semantic-use sites, retaining the exact
  environment scope even when artifact values coincide. The construction is a
  derived program view; it adds no field to a native artifact. Private-coordinate
  equivalence proves that every application boundary and positive judgment is
  unchanged.
\<close>

section \<open>Every program coordinate is an actual native occurrence\<close>

lemma native_schema_coordinate_positions:
  assumes schema: "native_schema_at E u r S"
  shows "Pair u ` (schema_variables S \<union> schema_sockets S) \<subseteq> environment_positions E"
proof -
  obtain R b m V where parts: "environment_formed E" "artifact_at E u R" "binder_scope_at R b V"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
    "V=schema_variables S"
    using schema by (auto simp: native_schema_at_def)
  have variables: "schema_variables S \<subseteq> rra_carrier (object_structure R)"
    using binder_scope_properties(2)[OF parts(3)] parts(5) by simp
  obtain T M where family: "artifact_at E u T" "family_at T m M"
    "rel_dom (socket_sum (schema_premises S) (schema_material_premises S))=rel_dom M"
    using parts(4) by (auto simp: native_premise_family_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF parts(1) family(1) parts(2)])
  have sockets: "schema_sockets S \<subseteq> rra_carrier (object_structure R)"
    using family_interior_in_carrier[OF family(2)] family(3) same
    by (auto simp: schema_sockets_def)
  show ?thesis using variables sockets parts(2) by (auto; blast)
qed

lemma native_definition_clause_position:
  assumes definition_read: "native_definition_at E u r p C" and clause: "(c,S) \<in> C"
  shows "(u,c) \<in> environment_positions E"
proof -
  obtain m where family: "native_schema_family_at E u m C"
    using definition_read by (auto simp: native_definition_at_def)
  obtain R M a where source: "artifact_at E u R" "family_at R m M" "(c,a) \<in> M"
    using native_schema_family_origin[OF family clause] by blast
  have key: "c \<in> rel_dom M" by (rule rel_domI[OF source(3)])
  have inside: "c \<in> rra_carrier (object_structure R)"
    using family_interior_in_carrier[OF source(2)] key by blast
  show ?thesis using source(1) inside by auto
qed

lemma positioned_package_clause_positions:
  assumes package: "native_package_at E u r P"
    and clause: "((d,c),S) \<in> system_clauses (positioned_program P)"
  shows "c \<in> environment_positions E"
    "schema_variables S \<union> schema_sockets S \<subseteq> environment_positions E"
proof -
  obtain k T where source: "((d,k),T) \<in> system_clauses P" and cp: "c=(fst d,k)"
    and sp: "S=rename_schema (Pair (fst d)) (Pair (fst d)) id T"
    using clause unfolding positioned_clause_entry by blast
  obtain roots where projection: "P=native_program E roots"
    using package by (auto simp: native_package_at_def)
  obtain p C where definition_read: "native_definition_at E (fst d) (snd d) p C" and member: "(k,T) \<in> C"
    using source by (auto simp: projection native_definition_graph_def)
  have key: "(fst d,k) \<in> environment_positions E"
    by (rule native_definition_clause_position[OF definition_read member])
  show "c \<in> environment_positions E" using key cp by simp
  obtain a where schema: "native_schema_at E (fst d) a T"
    using native_definition_clause_origin[OF definition_read member] by blast
  have coordinates: "Pair (fst d) ` (schema_variables T \<union> schema_sockets T) \<subseteq> environment_positions E"
    by (rule native_schema_coordinate_positions[OF schema])
  show "schema_variables S \<union> schema_sockets S \<subseteq> environment_positions E"
    using coordinates by (simp add: sp renamed_schema_variables renamed_schema_sockets image_Un)
qed

end
