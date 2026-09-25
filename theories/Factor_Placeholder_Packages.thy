theory Factor_Placeholder_Packages
  imports Factor_Placeholder_Schemas Factor_Judgment_Retention
begin

section \<open>The package, the application and the least environments at the placeholder fill\<close>

text \<open>
  Where E reads a package or an application, the fill reads it too: the package with its program mapped by
  the parametricity map at the placeholder's leaf map (@{const map_system_leaves}), the application with its
  argument mapped (@{const map_term_leaves}), its callee, interior and slots kept; the reader's uniqueness at
  the fill closes each reading. Every set collected over these readings (roots, sites, sources, root
  requests, demanded slots) is E's, stated where E reads; a set collected where E does not read may differ,
  since at the fill an occurrence citation of a slot bound to a use holding the empty artifact reads into R.
  The least environments of the fill are then the fills of E's, through the fill's commutation with
  @{const read_environment}. Every statement holds for every formed R, R equal to an artifact E holds
  elsewhere or the empty artifact itself; none rests on the maps' injectivity.
\<close>

lemma placeholder_fill_read_environment:
  "read_environment (placeholder_fill E R) U D=placeholder_fill (read_environment E U D) R"
  unfolding placeholder_fill_def read_environment_payload_fill
proof (rule payload_fill_cong)
  fix u S assume "artifact_at (read_environment E U D) u S"
  then have "u\<in>read_environment_uses E U D" by (simp add: read_environment_def artifact_at_def)
  then show "u\<in>{u. artifact_at E u empty_artifact} \<longleftrightarrow> u\<in>{u. artifact_at (read_environment E U D) u empty_artifact}"
    by (simp add: read_environment_def artifact_at_def)
qed

lemma artifact_at_placeholder_fill_address:
  assumes formed: "environment_formed E" and held: "artifact_at E u S"
    and address: "r\<in>rra_carrier (object_structure S)"
  shows "artifact_at (placeholder_fill E R) u T \<longleftrightarrow> artifact_at E u T"
proof (rule artifact_at_placeholder_fill_kept[OF formed])
  show "\<not>artifact_at E u empty_artifact"
  proof
    assume "artifact_at E u empty_artifact"
    then have "S=empty_artifact" using environment_artifact_unique[OF formed held] by blast
    then show False using address by (simp add: empty_artifact_def)
  qed
qed

lemma requested_slots_placeholder_fill:
  assumes kept: "\<And>u r T. (u,r)\<in>Q \<Longrightarrow> artifact_at (placeholder_fill E R) u T \<longleftrightarrow> artifact_at E u T"
  shows "requested_slots (placeholder_fill E R) Q=requested_slots E Q"
  using kept by (rule requested_slots_locality)

section \<open>Root families\<close>

theorem native_root_family_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_root_family_at E u r Q"
  shows "native_root_family_at (placeholder_fill E R) u r Q"
proof -
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S r M" "finite Q" "single_valued Q"
      "rel_dom Q = rel_dom M" "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at E u a (fst d) (snd d))"
    by (rule native_root_family_atE[OF read]) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_family[OF S(1-3)])
  have rows: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at (placeholder_fill E R) u a (fst d) (snd d))"
    using S(7) located_at_placeholder_fill[OF S(1)] by blast
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3-6) rows
  show ?thesis unfolding native_root_family_at_def by (intro exI conjI) (fact facts)+
qed

corollary native_root_family_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_root_family_at E u r Q"
  shows "native_root_family_at (placeholder_fill E R) u r W \<longleftrightarrow> W=Q"
  using native_root_family_placeholder_fill[OF assms]
  by (auto dest: native_root_family_unique[OF _ native_root_family_placeholder_fill[OF assms]])

section \<open>Definition edges, sites and the program\<close>

lemma native_definition_edges_placeholder_fill:
  assumes R_formed: "exact_formed R" and edge: "(d,e)\<in>native_definition_edges E"
  shows "(d,e)\<in>native_definition_edges (placeholder_fill E R)"
proof -
  obtain p C c S where E': "native_definition_at E (fst d) (snd d) p C" "(c,S)\<in>C" "e\<in>schema_dependencies S"
    using edge by (auto simp: native_definition_edges_def)
  have row: "(c,map_schema_leaves (placeholder_leaf R) S)\<in>map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
    using E'(2) by auto
  have deps: "e\<in>schema_dependencies (map_schema_leaves (placeholder_leaf R) S)" using E'(3) by simp
  show ?thesis
    unfolding native_definition_edges_def
    using native_definition_placeholder_fill[OF R_formed E'(1)] row deps by blast
qed

lemma native_definition_edges_placeholder_fill_read:
  assumes R_formed: "exact_formed R" and read: "native_definition_at E (fst d) (snd d) p C"
    and edge: "(d,e)\<in>native_definition_edges (placeholder_fill E R)"
  shows "(d,e)\<in>native_definition_edges E"
proof -
  obtain q D c T where F: "native_definition_at (placeholder_fill E R) (fst d) (snd d) q D" "(c,T)\<in>D"
      "e\<in>schema_dependencies T"
    using edge by (auto simp: native_definition_edges_def)
  have "D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
    using F(1) native_definition_placeholder_fill_exact[OF R_formed read] by blast
  then obtain S where S: "(c,S)\<in>C" "T=map_schema_leaves (placeholder_leaf R) S" using F(2) by auto
  have "e\<in>schema_dependencies S" using F(3) S(2) by simp
  then show ?thesis unfolding native_definition_edges_def using read S(1) by blast
qed

theorem native_definition_sites_placeholder_fill:
  assumes R_formed: "exact_formed R" and formed: "native_package_formed E roots"
  shows "native_definition_sites (placeholder_fill E R) roots=native_definition_sites E roots"
proof
  show "native_definition_sites E roots \<subseteq> native_definition_sites (placeholder_fill E R) roots"
  proof
    fix d assume "d\<in>native_definition_sites E roots"
    then obtain r where r: "r\<in>roots" "(r,d)\<in>(native_definition_edges E)\<^sup>*"
      by (auto simp: native_definition_sites_def)
    have "native_definition_edges E \<subseteq> native_definition_edges (placeholder_fill E R)"
      using native_definition_edges_placeholder_fill[OF R_formed] by auto
    then have "(r,d)\<in>(native_definition_edges (placeholder_fill E R))\<^sup>*" using r(2) rtrancl_mono by blast
    then show "d\<in>native_definition_sites (placeholder_fill E R) roots"
      using r(1) by (auto simp: native_definition_sites_def)
  qed
next
  show "native_definition_sites (placeholder_fill E R) roots \<subseteq> native_definition_sites E roots"
  proof
    fix d assume "d\<in>native_definition_sites (placeholder_fill E R) roots"
    then obtain r where r: "r\<in>roots" "(r,d)\<in>(native_definition_edges (placeholder_fill E R))\<^sup>*"
      by (auto simp: native_definition_sites_def)
    from r(2) have "(r,d)\<in>(native_definition_edges E)\<^sup>*"
    proof (induction rule: rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step y z)
      have "y\<in>native_definition_sites E roots" using r(1) step.IH by (auto simp: native_definition_sites_def)
      then obtain p C where "native_definition_at E (fst y) (snd y) p C"
        using formed by (auto simp: native_package_formed_def)
      then have "(y,z)\<in>native_definition_edges E"
        by (rule native_definition_edges_placeholder_fill_read[OF R_formed _ step.hyps(2)])
      with step.IH show ?case by (rule rtrancl_into_rtrancl)
    qed
    then show "d\<in>native_definition_sites E roots" using r(1) by (auto simp: native_definition_sites_def)
  qed
qed

lemma native_package_formed_placeholder_fill:
  assumes R_formed: "exact_formed R" and formed: "native_package_formed E roots"
  shows "native_package_formed (placeholder_fill E R) roots"
proof -
  have ef: "environment_formed E"
    and each: "\<forall>d\<in>native_definition_sites E roots. \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    using formed by (simp_all add: native_package_formed_def)
  show ?thesis unfolding native_package_formed_def native_definition_sites_placeholder_fill[OF R_formed formed]
  proof (intro conjI ballI)
    show "environment_formed (placeholder_fill E R)" by (rule placeholder_fill_formed[OF ef R_formed])
  next
    fix d assume "d\<in>native_definition_sites E roots"
    then obtain p C where "native_definition_at E (fst d) (snd d) p C" using each by blast
    then show "\<exists>p C. native_definition_at (placeholder_fill E R) (fst d) (snd d) p C"
      by (blast dest: native_definition_placeholder_fill[OF R_formed])
  qed
qed

lemma native_definition_graph_placeholder_fill:
  assumes R_formed: "exact_formed R" and formed: "native_package_formed E roots"
  shows "(d,q,D)\<in>native_definition_graph (placeholder_fill E R) roots \<longleftrightarrow>
    (\<exists>p C. (d,p,C)\<in>native_definition_graph E roots \<and> q=map_pattern_leaves (placeholder_leaf R) p \<and>
      D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C)"
proof
  assume "(d,q,D)\<in>native_definition_graph (placeholder_fill E R) roots"
  then have x: "d\<in>native_definition_sites E roots" "native_definition_at (placeholder_fill E R) (fst d) (snd d) q D"
    by (simp_all add: native_definition_graph_def native_definition_sites_placeholder_fill[OF R_formed formed])
  obtain p C where read: "native_definition_at E (fst d) (snd d) p C"
    using x(1) formed unfolding native_package_formed_def by blast
  have maps: "q=map_pattern_leaves (placeholder_leaf R) p" "D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
    using native_definition_placeholder_fill_exact[OF R_formed read] x(2) by blast+
  have "(d,p,C)\<in>native_definition_graph E roots" using x(1) read by (simp add: native_definition_graph_def)
  then show "\<exists>p C. (d,p,C)\<in>native_definition_graph E roots \<and> q=map_pattern_leaves (placeholder_leaf R) p \<and>
      D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
    using maps by blast
next
  assume "\<exists>p C. (d,p,C)\<in>native_definition_graph E roots \<and> q=map_pattern_leaves (placeholder_leaf R) p \<and>
      D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
  then obtain p C where x: "d\<in>native_definition_sites E roots" "native_definition_at E (fst d) (snd d) p C"
      "q=map_pattern_leaves (placeholder_leaf R) p" "D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
    by (auto simp: native_definition_graph_def)
  have "native_definition_at (placeholder_fill E R) (fst d) (snd d) q D"
    using native_definition_placeholder_fill[OF R_formed x(2)] x(3,4) by simp
  then show "(d,q,D)\<in>native_definition_graph (placeholder_fill E R) roots"
    using x(1) by (simp add: native_definition_graph_def native_definition_sites_placeholder_fill[OF R_formed formed])
qed

theorem native_program_placeholder_fill:
  assumes R_formed: "exact_formed R" and formed: "native_package_formed E roots"
  shows "native_program (placeholder_fill E R) roots=map_system_leaves (placeholder_leaf R) (native_program E roots)"
proof -
  note graph=native_definition_graph_placeholder_fill[OF R_formed formed]
  have interfaces: "system_interfaces (native_program (placeholder_fill E R) roots)=
      map_relation_values (map_pattern_leaves (placeholder_leaf R)) (system_interfaces (native_program E roots))"
  proof (intro set_eqI iffI)
    fix z assume "z\<in>system_interfaces (native_program (placeholder_fill E R) roots)"
    then obtain d q D where z: "z=(d,q)" "(d,q,D)\<in>native_definition_graph (placeholder_fill E R) roots"
      by (auto simp: native_program_def)
    obtain p C where p: "(d,p,C)\<in>native_definition_graph E roots" "q=map_pattern_leaves (placeholder_leaf R) p"
      using z(2) graph by blast
    have "(d,p)\<in>system_interfaces (native_program E roots)" using p(1) by (auto simp: native_program_def)
    then show "z\<in>map_relation_values (map_pattern_leaves (placeholder_leaf R)) (system_interfaces (native_program E roots))"
      unfolding z(1) p(2) map_relation_values_member by blast
  next
    fix z assume "z\<in>map_relation_values (map_pattern_leaves (placeholder_leaf R)) (system_interfaces (native_program E roots))"
    then obtain d p C where z: "z=(d,map_pattern_leaves (placeholder_leaf R) p)" "(d,p,C)\<in>native_definition_graph E roots"
      by (auto simp: native_program_def map_relation_values_def)
    have "(d,map_pattern_leaves (placeholder_leaf R) p,map_relation_values (map_schema_leaves (placeholder_leaf R)) C)
        \<in>native_definition_graph (placeholder_fill E R) roots"
      using z(2) graph by blast
    then show "z\<in>system_interfaces (native_program (placeholder_fill E R) roots)"
      unfolding z(1) native_program_def by auto
  qed
  have clauses: "system_clauses (native_program (placeholder_fill E R) roots)=
      map_relation_values (map_schema_leaves (placeholder_leaf R)) (system_clauses (native_program E roots))"
  proof (intro set_eqI iffI)
    fix z assume "z\<in>system_clauses (native_program (placeholder_fill E R) roots)"
    then obtain d c T q D where z: "z=((d,c),T)" "(d,q,D)\<in>native_definition_graph (placeholder_fill E R) roots"
        "(c,T)\<in>D"
      by (auto simp: native_program_def)
    obtain p C where p: "(d,p,C)\<in>native_definition_graph E roots"
        "D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
      using z(2) graph by blast
    obtain S where S: "(c,S)\<in>C" "T=map_schema_leaves (placeholder_leaf R) S" using z(3) p(2) by auto
    have "((d,c),S)\<in>system_clauses (native_program E roots)" using p(1) S(1) by (auto simp: native_program_def)
    then show "z\<in>map_relation_values (map_schema_leaves (placeholder_leaf R)) (system_clauses (native_program E roots))"
      unfolding z(1) S(2) map_relation_values_member by blast
  next
    fix z assume "z\<in>map_relation_values (map_schema_leaves (placeholder_leaf R)) (system_clauses (native_program E roots))"
    then obtain d c S p C where z: "z=((d,c),map_schema_leaves (placeholder_leaf R) S)"
        "(d,p,C)\<in>native_definition_graph E roots" "(c,S)\<in>C"
      by (auto simp: native_program_def map_relation_values_def)
    have graph_fill: "(d,map_pattern_leaves (placeholder_leaf R) p,map_relation_values (map_schema_leaves (placeholder_leaf R)) C)
        \<in>native_definition_graph (placeholder_fill E R) roots"
      using z(2) graph by blast
    have row: "(c,map_schema_leaves (placeholder_leaf R) S)\<in>map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
      using z(3) by auto
    show "z\<in>system_clauses (native_program (placeholder_fill E R) roots)"
      unfolding z(1) by (simp add: native_program_def del: map_relation_values_member) (use graph_fill row in blast)
  qed
  show ?thesis by (rule schema_system.equality) (simp_all add: interfaces clauses)
qed

section \<open>The package\<close>

theorem native_package_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_at (placeholder_fill E R) u r (map_system_leaves (placeholder_leaf R) P)"
proof -
  obtain Q where Q: "native_root_family_at E u r Q" "native_package_formed E (rel_ran Q)"
      "P=native_program E (rel_ran Q)"
    by (rule native_package_atE[OF read]) (rule that; assumption)
  show ?thesis unfolding native_package_at_def
  proof (intro exI[of _ Q] conjI)
    show "native_root_family_at (placeholder_fill E R) u r Q"
      by (rule native_root_family_placeholder_fill[OF R_formed Q(1)])
    show "native_package_formed (placeholder_fill E R) (rel_ran Q)"
      by (rule native_package_formed_placeholder_fill[OF R_formed Q(2)])
    show "map_system_leaves (placeholder_leaf R) P=native_program (placeholder_fill E R) (rel_ran Q)"
      unfolding Q(3) native_program_placeholder_fill[OF R_formed Q(2)] ..
  qed
qed

corollary native_package_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_at (placeholder_fill E R) u r T \<longleftrightarrow> T=map_system_leaves (placeholder_leaf R) P"
  using native_package_placeholder_fill[OF assms]
  by (auto dest: native_package_unique[OF _ native_package_placeholder_fill[OF assms]])

section \<open>The application\<close>

theorem native_application_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_application_at E u r d t I K"
  shows "native_application_at (placeholder_fill E R) u r d (map_term_leaves (placeholder_leaf R) t) I K"
proof -
  obtain S ps c a cite C J A where S: "environment_formed E" "artifact_at E u S" "record_at S r ps [c,a]"
      "citation_at S c cite C" "citation_location E u cite (fst d) (snd d)" "term_quoted_at E u a t J A"
      "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}" "I = insert r (set ps \<union> C \<union> J)"
      "K = citation_slots cite \<union> A" "I \<inter> K = {}"
    by (rule native_application_atE[OF read]) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3,4,7-11)
    citation_location_placeholder_fill[OF S(1,5)] term_quoted_placeholder_fill[OF R_formed S(6)]
  show ?thesis unfolding native_application_at_def by (intro exI conjI) (fact facts)+
qed

corollary native_application_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_application_at E u r d t I K"
  shows "native_application_at (placeholder_fill E R) u r e x J W \<longleftrightarrow>
    e=d \<and> x=map_term_leaves (placeholder_leaf R) t \<and> J=I \<and> W=K"
  using native_application_placeholder_fill[OF assms]
  by (auto dest: native_application_unique[OF _ native_application_placeholder_fill[OF assms]])

section \<open>Slots read where E reads\<close>

lemma family_endpoints_placeholder_fill:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R"
    and art: "artifact_at E u S" and family: "family_at S r M"
  shows "family_endpoints (placeholder_fill E R) u r=family_endpoints E u r"
  using family_endpoints_from_read[OF placeholder_fill_formed[OF formed R_formed]
      artifact_at_placeholder_fill_family[OF formed art family] family]
    family_endpoints_from_read[OF formed art family] by simp

lemma pattern_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and quote: "pattern_quoted_at E u V c p I K"
  shows "pattern_slots (placeholder_fill E R) u V c=pattern_slots E u V c"
  using pattern_slots_of_quote[OF pattern_quoted_placeholder_fill[OF R_formed quote]] pattern_slots_of_quote[OF quote]
  by simp

lemma scoped_pattern_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and quote: "scoped_pattern_at E u i p I K"
  shows "scoped_pattern_slots (placeholder_fill E R) u i=scoped_pattern_slots E u i"
  using scoped_pattern_slots_of_quote[OF scoped_pattern_placeholder_fill[OF R_formed quote]]
    scoped_pattern_slots_of_quote[OF quote]
  by simp

lemma native_premise_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_premise_at E u V a p I K"
  shows "native_premise_slots (placeholder_fill E R) u V a=native_premise_slots E u V a"
  using native_premise_slots_of_read[OF native_premise_placeholder_fill[OF R_formed read]]
    native_premise_slots_of_read[OF read]
  by simp

lemma native_premise_family_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_premise_family_at E u V m Q C"
  shows "native_premise_family_slots (placeholder_fill E R) u V m=native_premise_family_slots E u V m"
proof -
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S m M"
      "finite (socket_sum Q C)" "single_valued (socket_sum Q C)" "rel_dom (socket_sum Q C)=rel_dom M"
      "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at E u V a p I K)"
    by (rule native_premise_family_atE[OF read]) (rule that; assumption)
  have each: "native_premise_slots (placeholder_fill E R) u V a=native_premise_slots E u V a"
    if "a\<in>family_endpoints E u m" for a
  proof -
    have "a\<in>rel_ran M" using that family_endpoints_from_read[OF S(1-3)] by simp
    then obtain s where "(s,a)\<in>M" by (auto simp: rel_ran_def)
    then obtain p I K where "native_premise_at E u V a p I K" using S(7) by blast
    then show ?thesis by (rule native_premise_slots_placeholder_fill[OF R_formed])
  qed
  show ?thesis
    unfolding native_premise_family_slots_def family_endpoints_placeholder_fill[OF S(1) R_formed S(2,3)]
    by (rule SUP_cong[OF refl]) (rule each)
qed

lemma native_schema_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_schema_at E u a S"
  shows "native_schema_slots (placeholder_fill E R) u a=native_schema_slots E u a"
proof -
  obtain T ps b c m V I K where T: "environment_formed E" "artifact_at E u T" "record_at T a ps [b,c,m]"
      "binder_scope_at T b V" "pattern_quoted_at E u V c (schema_conclusion S) I K"
      "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
      "V = schema_variables S"
      "insert a (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {}"
      "insert b V \<inter> I = {}" "b \<noteq> m" "m \<notin> I"
    by (rule native_schema_atE[OF read]) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u T" by (rule artifact_at_placeholder_fill_record[OF T(1-3)])
  show ?thesis
    using native_schema_slots_from_fields[OF placeholder_fill_formed[OF T(1) R_formed] art T(3,4)]
      native_schema_slots_from_fields[OF T(1-4)] pattern_slots_placeholder_fill[OF R_formed T(5)]
      native_premise_family_slots_placeholder_fill[OF R_formed T(6)]
    by simp
qed

lemma native_schema_family_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_schema_family_at E u m C"
  shows "native_schema_family_slots (placeholder_fill E R) u m=native_schema_family_slots E u m"
proof -
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S m M" "finite C" "single_valued C"
      "rel_dom C = rel_dom M" "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>T. (s,T) \<in> C \<and> native_schema_at E u a T)"
    by (rule native_schema_family_atE[OF read]) (rule that; assumption)
  have each: "native_schema_slots (placeholder_fill E R) u a=native_schema_slots E u a"
    if "a\<in>family_endpoints E u m" for a
  proof -
    have "a\<in>rel_ran M" using that family_endpoints_from_read[OF S(1-3)] by simp
    then obtain s where "(s,a)\<in>M" by (auto simp: rel_ran_def)
    then obtain T where "native_schema_at E u a T" using S(7) by blast
    then show ?thesis by (rule native_schema_slots_placeholder_fill[OF R_formed])
  qed
  show ?thesis
    unfolding native_schema_family_slots_def family_endpoints_placeholder_fill[OF S(1) R_formed S(2,3)]
    by (rule SUP_cong[OF refl]) (rule each)
qed

lemma native_definition_slots_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_definition_at E u r p C"
  shows "native_definition_slots (placeholder_fill E R) u r=native_definition_slots E u r"
proof -
  obtain S ps i m I K where S: "environment_formed E" "artifact_at E u S" "record_at S r ps [i,m]"
      "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
      "insert r (set ps) \<inter> (I \<union> {m}) = {}" "m \<notin> I"
    by (rule native_definition_atE[OF read]) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  show ?thesis
    using native_definition_slots_from_fields[OF placeholder_fill_formed[OF S(1) R_formed] art S(3)]
      native_definition_slots_from_fields[OF S(1-3)] scoped_pattern_slots_placeholder_fill[OF R_formed S(4)]
      native_schema_family_slots_placeholder_fill[OF R_formed S(5)]
    by simp
qed

section \<open>The package's and the application's sources and demands\<close>

theorem native_package_sites_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_roots (placeholder_fill E R) u r=native_package_roots E u r"
    and "native_package_sites (placeholder_fill E R) u r=native_package_sites E u r"
proof -
  obtain Q where Q: "native_root_family_at E u r Q" "native_package_formed E (rel_ran Q)"
    by (rule native_package_atE[OF read]) (rule that; assumption)
  have E_roots: "native_package_roots E u r=rel_ran Q" by (rule native_package_roots_from_family[OF Q(1)])
  have fill_roots: "native_package_roots (placeholder_fill E R) u r=rel_ran Q"
    by (rule native_package_roots_from_family[OF native_root_family_placeholder_fill[OF R_formed Q(1)]])
  show roots: "native_package_roots (placeholder_fill E R) u r=native_package_roots E u r"
    using E_roots fill_roots by simp
  show "native_package_sites (placeholder_fill E R) u r=native_package_sites E u r"
    unfolding native_package_sites_def roots E_roots by (rule native_definition_sites_placeholder_fill[OF R_formed Q(2)])
qed

corollary native_package_sources_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_sources (placeholder_fill E R) u r=native_package_sources E u r"
  unfolding native_package_sources_def native_package_sites_placeholder_fill(2)[OF assms] ..

theorem native_package_demands_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_demands (placeholder_fill E R) u r=native_package_demands E u r"
proof -
  obtain Q where Q: "native_root_family_at E u r Q" "native_package_formed E (rel_ran Q)"
    by (rule native_package_atE[OF read]) (rule that; assumption)
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S r M"
    by (rule native_root_family_atE[OF Q(1)]) (rule that; assumption)
  have address: "r\<in>rra_carrier (object_structure S)" using family_interior_in_carrier[OF S(3)] by auto
  have kept: "artifact_at (placeholder_fill E R) u T \<longleftrightarrow> artifact_at E u T" for T
    by (rule artifact_at_placeholder_fill_address[OF S(1,2) address])
  have requests: "native_root_requests (placeholder_fill E R) u r=native_root_requests E u r"
    unfolding native_root_requests_def family_endpoints_placeholder_fill[OF S(1) R_formed S(2,3)] ..
  have requested: "requested_slots (placeholder_fill E R) (native_root_requests E u r)=
      requested_slots E (native_root_requests E u r)"
    by (rule requested_slots_placeholder_fill) (auto simp: native_root_requests_def kept)
  have E_roots: "native_package_roots E u r=rel_ran Q" by (rule native_package_roots_from_family[OF Q(1)])
  have slots: "native_definition_slots (placeholder_fill E R) v a=native_definition_slots E v a"
    if "(v,a)\<in>native_package_sites E u r" for v a
  proof -
    have "(v,a)\<in>native_definition_sites E (rel_ran Q)" using that by (simp add: native_package_sites_def E_roots)
    then obtain p C where "native_definition_at E (fst (v,a)) (snd (v,a)) p C"
      using Q(2) unfolding native_package_formed_def by blast
    then have "native_definition_at E v a p C" by simp
    then show ?thesis by (rule native_definition_slots_placeholder_fill[OF R_formed])
  qed
  have definition_slots: "{(v,k). \<exists>a. (v,a)\<in>native_package_sites E u r \<and> k\<in>native_definition_slots (placeholder_fill E R) v a}=
      {(v,k). \<exists>a. (v,a)\<in>native_package_sites E u r \<and> k\<in>native_definition_slots E v a}"
    by (auto simp: slots)
  show ?thesis
    unfolding native_package_demands_def requests requested native_package_sites_placeholder_fill(2)[OF R_formed read]
      definition_slots ..
qed


theorem native_application_demands_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_application_at E u r d t I K"
  shows "native_application_demands (placeholder_fill E R) u r=native_application_demands E u r"
  using native_application_demands_at[OF native_application_placeholder_fill[OF R_formed read]]
    native_application_demands_at[OF read]
  by simp

corollary native_judgment_sources_placeholder_fill:
  assumes R_formed: "exact_formed R" and package: "native_package_at E pu pr P"
  shows "native_judgment_sources (placeholder_fill E R) pu pr au=native_judgment_sources E pu pr au"
  unfolding native_judgment_sources_def native_package_sources_placeholder_fill[OF R_formed package] ..

corollary native_judgment_demands_placeholder_fill:
  assumes R_formed: "exact_formed R" and package: "native_package_at E pu pr P"
    and application: "native_application_at E au ar d t I K"
  shows "native_judgment_demands (placeholder_fill E R) pu pr au ar=native_judgment_demands E pu pr au ar"
  unfolding native_judgment_demands_def native_package_demands_placeholder_fill[OF R_formed package]
    native_application_demands_placeholder_fill[OF R_formed application] ..

section \<open>The least environments\<close>

theorem native_package_environment_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_package_at E u r P"
  shows "native_package_environment (placeholder_fill E R) u r=placeholder_fill (native_package_environment E u r) R"
  unfolding native_package_environment_def native_package_sources_placeholder_fill[OF assms]
    native_package_demands_placeholder_fill[OF assms]
  by (rule placeholder_fill_read_environment)

theorem native_judgment_environment_placeholder_fill:
  assumes R_formed: "exact_formed R" and package: "native_package_at E pu pr P"
    and application: "native_application_at E au ar d t I K"
  shows "native_judgment_environment (placeholder_fill E R) pu pr au ar=
    placeholder_fill (native_judgment_environment E pu pr au ar) R"
  unfolding native_judgment_environment_def native_judgment_sources_placeholder_fill[OF R_formed package]
    native_judgment_demands_placeholder_fill[OF R_formed package application]
  by (rule placeholder_fill_read_environment)

end
