theory Factor_Use_Renaming
  imports Factor_Use_Actions Factor_Native_Transport Factor_Program_Entry_Presentations Factor_Packages
    Factor_System_Relocation
begin

section \<open>The Factor readers at renamed uses\<close>

text \<open>
  The upper part of the use instance (its low part is @{text Factor_Use_Actions}): the actions on site
  contexts and program entries, and the definition, schema and package readings at a renamed use. Each
  reading's renaming at a permutation is its forward renaming made exact by the inverse-permutation
  argument (@{thm [source] use_renaming_inverse}) and the reading's uniqueness.
\<close>

subsection \<open>Site contexts and program entries\<close>

abbreviation site_context_renaming ::
    "(local_address option \<Rightarrow> local_address option) \<Rightarrow> site_context \<Rightarrow> site_context" where
  "site_context_renaming \<equiv> product_action rename_environment (\<lambda>h. map_prod h id)"

theorem site_context_renaming_action: "renaming_action bij site_context_renaming site_context_formed"
proof (rule renaming_action_subdomain[OF renaming_action_product[OF environment_renaming_action
      site_renaming_action]])
  fix z :: site_context assume "site_context_formed z"
  then show "environment_formed (fst z) \<and> True" by simp
next
  fix h :: "local_address option \<Rightarrow> local_address option" and z :: site_context
  assume h: "bij h" and formed: "site_context_formed z"
  have environment: "environment_formed (rename_environment h (fst z))"
    using formed environment_renaming_formed bij_is_inj[OF h] by blast
  have site: "map_prod h id (snd z) \<in> environment_positions (rename_environment h (fst z))"
    using formed by (simp add: environment_positions_renaming)
  show "site_context_formed (site_context_renaming h z)"
    using environment site by (simp add: product_action_def)
qed

abbreviation program_entry_renaming ::
    "(local_address option \<Rightarrow> local_address option) \<Rightarrow> program_entry_context \<Rightarrow> program_entry_context" where
  "program_entry_renaming \<equiv> product_action site_context_renaming (\<lambda>h. map_prod h id)"

lemma program_entry_renaming_fields:
  "program_entry_renaming h ((E,(u,r)),d) = ((rename_environment h E,(h u,r)),map_prod h id d)"
  by simp

theorem program_entry_renaming_action:
  "renaming_action bij program_entry_renaming program_entry_context_formed"
proof (rule renaming_action_subdomain[OF renaming_action_product[OF site_context_renaming_action
      site_renaming_action]])
  fix z :: program_entry_context assume "program_entry_context_formed z"
  then show "site_context_formed (fst z) \<and> True" by (simp add: program_entry_context_formed_def)
next
  fix h :: "local_address option \<Rightarrow> local_address option" and z :: program_entry_context
  assume h: "bij h" and formed: "program_entry_context_formed z"
  have old: "site_context_formed (fst z)" using formed by (simp add: program_entry_context_formed_def)
  have site: "site_context_formed (site_context_renaming h (fst z))"
    by (rule renaming_action.act_domain[OF site_context_renaming_action h old])
  have entry: "map_prod h id (snd z) \<in> environment_positions (rename_environment h (fst (fst z)))"
    using formed by (simp add: program_entry_context_formed_def environment_positions_renaming)
  show "program_entry_context_formed (program_entry_renaming h z)"
    using site entry by (simp add: program_entry_context_formed_def product_action_def)
qed

text \<open>
  Each action stands on the domain of its class: @{text environment_presentations} over the formed
  environments, @{text site_presentations} over the formed site contexts, @{text program_entries}
  over the formed program-entry contexts; a client combines the notion's contract with the class
  and the action. Exact values carry no use and take the trivial action
  (@{thm [source] permutation_renaming_action}).
\<close>

subsection \<open>The Factor definition readers at a renamed use\<close>


theorem use_renaming_syntax_copy:
  assumes formed: "environment_formed E" and source: "artifact_at E u R" and injective: "inj h"
  shows "native_syntax_copy E u R (rename_environment h E) (h u) R id (map_prod h id)"
proof -
  have exact: "exact_formed R" using formed source by (simp add: environment_formed_def)
  have object: "object_formed R" using exact by (simp add: exact_formed_def)
  show ?thesis
  proof (unfold_locales)
    show "environment_formed E" by (rule formed)
    show "artifact_at E u R" by (rule source)
    show "environment_formed (rename_environment h E)" by (rule environment_renaming_formed[OF formed injective])
    show "artifact_at (rename_environment h E) (h u) R" using source by (simp add: artifact_at_renamed_use[OF injective])
    show "inj (id :: local_address \<Rightarrow> local_address)" by (rule inj_on_id)
    show "finite_addressing (rra_carrier (object_structure R)) id"
      using exact by (simp add: exact_formed_def finite_addressing_def)
    show "object_reads_agree (push_object id R) R (id ` rra_carrier (object_structure R))"
      by (simp add: push_object_identity[OF object] object_reads_agree_def)
    show "\<forall>k\<in>rra_carrier (object_structure R).
        external_slot_values E u k = external_slot_values (rename_environment h E) (h u) (id k)"
      by (auto simp: external_slot_values_def binds_slot_renaming artifact_at_renamed_use[OF injective]
          inj_eq[OF injective])
  next
    fix r c I v a assume "citation_at R r c I" and located: "citation_location E u c v a"
    show "citation_location (rename_environment h E) (h u) (map_citation_positions id c)
        (fst (map_prod h id (v,a))) (snd (map_prod h id (v,a)))"
      using located by (simp add: citation_location_use_renaming[OF injective])
  qed
qed

theorem native_definition_renamed_use:
  assumes formed: "environment_formed E" and injective: "inj h"
    and defined: "native_definition_at E u r p C"
  shows "native_definition_at (rename_environment h E) (h u) r p
    ((\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)"
proof -
  obtain R where source: "artifact_at E u R" using defined by (auto simp: native_definition_at_def)
  interpret copy: native_syntax_copy E u R "rename_environment h E" "h u" R id "map_prod h id"
    by (rule use_renaming_syntax_copy[OF formed source injective])
  show ?thesis using copy.copy_definition[OF defined] by simp
qed

theorem native_definition_use_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_definition_at (rename_environment h E) (h u) r p D \<longleftrightarrow>
    (\<exists>C. native_definition_at E u r p C \<and> D = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)"
  by (rule use_renaming_inverse[where read="\<lambda>F v C. native_definition_at F v r p C"
      and read'="\<lambda>F v C. native_definition_at F v r p C"
      and move="\<lambda>g C. (\<lambda>(s,A). (s,rename_schema id id (map_prod g id) A)) ` C"
      and move'="\<lambda>g C. (\<lambda>(s,A). (s,rename_schema id id (map_prod g id) A)) ` C",
      OF native_definition_renamed_use[OF _ bij_is_inj] native_definition_renamed_use[OF _ bij_is_inj]
        native_definition_unique[THEN conjunct2] formed permutation])

subsection \<open>The schema reading at a renamed use\<close>

text \<open>
  A schema read at a renamed use is the definition readers' copy (@{thm [source] use_renaming_syntax_copy},
  @{text copy_schema}) with its callees relocated and its binders and sockets unchanged.
\<close>

lemma native_schema_renamed_use:
  assumes formed: "environment_formed E" and injective: "inj h" and schema: "native_schema_at E u r S"
  shows "native_schema_at (rename_environment h E) (h u) r (rename_schema id id (map_prod h id) S)"
proof -
  obtain R where source: "artifact_at E u R" using schema by (auto simp: native_schema_at_def)
  interpret copy: native_syntax_copy E u R "rename_environment h E" "h u" R id "map_prod h id"
    by (rule use_renaming_syntax_copy[OF formed source injective])
  show ?thesis using copy.copy_schema[OF schema] by simp
qed

theorem native_schema_use_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_schema_at (rename_environment h E) (h u) r T \<longleftrightarrow>
    (\<exists>S. native_schema_at E u r S \<and> T=rename_schema id id (map_prod h id) S)"
  by (rule use_renaming_inverse[where read="\<lambda>F v S. native_schema_at F v r S"
      and read'="\<lambda>F v S. native_schema_at F v r S"
      and move="\<lambda>g S. rename_schema id id (map_prod g id) S"
      and move'="\<lambda>g S. rename_schema id id (map_prod g id) S",
      OF native_schema_renamed_use[OF _ bij_is_inj] native_schema_renamed_use[OF _ bij_is_inj]
        native_schema_unique formed permutation])

subsection \<open>The package reading at a renamed root use\<close>

text \<open>
  A package read at a root use read again at the renamed root use of the renamed environment is the
  same package with its program relocated by the site action: its root family's located readings, its
  definition edges, sites and graph all move with the renaming, and its positive meaning is the
  original's at the renamed sites and the same argument terms.
\<close>

lemma renamed_site_injective:
  assumes injective: "inj h"
  shows "inj (map_prod h id)"
  using map_prod_inj_on[OF injective inj_on_id[of UNIV]] by simp

lemma native_root_family_renamed_use:
  assumes injective: "inj h" and family: "native_root_family_at E u r Q"
  shows "native_root_family_at (rename_environment h E) (h u) r (map_relation_values (map_prod h id) Q)"
proof -
  obtain R M where parts: "environment_formed E" "artifact_at E u R" "family_at R r M" "finite Q"
      "single_valued Q" "rel_dom Q = rel_dom M"
      "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at E u a (fst d) (snd d))"
    using family unfolding native_root_family_at_def by blast
  have located: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> map_relation_values (map_prod h id) Q \<and>
      located_at (rename_environment h E) (h u) a (fst d) (snd d))"
  proof (intro allI impI)
    fix s a assume "(s,a) \<in> M"
    then obtain d where d: "(s,d) \<in> Q" "located_at E u a (fst d) (snd d)" using parts(7) by blast
    have "(s, map_prod h id d) \<in> map_relation_values (map_prod h id) Q"
      by (simp only: map_relation_values_member) (use d(1) in blast)
    moreover have "located_at (rename_environment h E) (h u) a (fst (map_prod h id d)) (snd (map_prod h id d))"
      using d(2) by (simp add: located_at_use_renaming[OF injective])
    ultimately show "\<exists>d. (s,d) \<in> map_relation_values (map_prod h id) Q \<and>
        located_at (rename_environment h E) (h u) a (fst d) (snd d)" by blast
  qed
  have artifact: "artifact_at (rename_environment h E) (h u) R"
    using parts(2) by (simp add: artifact_at_renamed_use[OF injective])
  have functional: "single_valued (map_relation_values (map_prod h id) Q)"
    using parts(5) by (simp add: map_relation_values_functional[OF renamed_site_injective[OF injective]])
  have domain: "rel_dom (map_relation_values (map_prod h id) Q) = rel_dom M" using parts(6) by simp
  have bounded: "finite (map_relation_values (map_prod h id) Q)" using parts(4) by simp
  show ?thesis unfolding native_root_family_at_def
    using environment_renaming_formed[OF parts(1) injective] artifact parts(3) bounded functional domain located
    by blast
qed

lemma native_definition_edges_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_definition_edges (rename_environment h E) =
    map_prod (map_prod h id) (map_prod h id) ` native_definition_edges E"
proof -
  have site_surjective: "surj (map_prod h id)" by (rule map_prod_surj[OF bij_is_surj[OF permutation] surj_id])
  have surjective: "surj (map_prod (map_prod h id) (map_prod h id))"
    by (rule map_prod_surj[OF site_surjective site_surjective])
  have injective: "inj (map_prod h id)" by (rule renamed_site_injective[OF bij_is_inj[OF permutation]])
  have pair_injective: "inj (map_prod (map_prod h id) (map_prod h id))"
    using map_prod_inj_on[OF injective injective] by simp
  have at: "map_prod (map_prod h id) (map_prod h id) z \<in> native_definition_edges (rename_environment h E) \<longleftrightarrow>
      z \<in> native_definition_edges E" for z
  proof -
    obtain d e where z: "z = (d,e)" by (cases z)
    have "(map_prod h id d, map_prod h id e) \<in> native_definition_edges (rename_environment h E) \<longleftrightarrow>
        (d,e) \<in> native_definition_edges E"
    proof
      assume "(map_prod h id d, map_prod h id e) \<in> native_definition_edges (rename_environment h E)"
      then obtain p C c S where renamed: "native_definition_at (rename_environment h E) (h (fst d)) (snd d) p C"
          "(c,S) \<in> C" "map_prod h id e \<in> schema_dependencies S"
        by (auto simp: native_definition_edges_def)
      obtain C0 where C0: "native_definition_at E (fst d) (snd d) p C0"
          "C = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C0"
        using renamed(1) native_definition_use_renaming[OF formed permutation] by blast
      obtain T where T: "(c,T) \<in> C0" "S = rename_schema id id (map_prod h id) T"
        using renamed(2) unfolding C0(2) map_relation_values_member[unfolded map_relation_values_def] by blast
      have "e \<in> schema_dependencies T"
        using renamed(3) by (simp add: T(2) renamed_schema_dependencies inj_image_mem_iff[OF injective])
      then show "(d,e) \<in> native_definition_edges E"
        by (simp add: native_definition_edges_def; use C0(1) T(1) in blast)
    next
      assume "(d,e) \<in> native_definition_edges E"
      then obtain p C c T where original: "native_definition_at E (fst d) (snd d) p C" "(c,T) \<in> C"
          "e \<in> schema_dependencies T"
        by (auto simp: native_definition_edges_def)
      have renamed: "native_definition_at (rename_environment h E) (h (fst d)) (snd d) p
          ((\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)"
        by (rule native_definition_renamed_use[OF formed bij_is_inj[OF permutation] original(1)])
      have clause: "(c, rename_schema id id (map_prod h id) T) \<in>
          (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C"
        by (rule rev_image_eqI[OF original(2)]) simp
      have "map_prod h id e \<in> schema_dependencies (rename_schema id id (map_prod h id) T)"
        using original(3) by (simp add: renamed_schema_dependencies)
      then show "(map_prod h id d, map_prod h id e) \<in> native_definition_edges (rename_environment h E)"
        by (simp add: native_definition_edges_def; use renamed clause in blast)
    qed
    then show ?thesis by (simp add: z)
  qed
  show ?thesis by (rule surjective_image_eq[OF surjective pair_injective at])
qed

lemma native_definition_sites_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_definition_sites (rename_environment h E) (map_prod h id ` roots) =
    map_prod h id ` native_definition_sites E roots"
proof (rule surjective_image_eq)
  show "surj (map_prod h id)" by (rule map_prod_surj[OF bij_is_surj[OF permutation] surj_id])
  have injective: "inj (map_prod h id)" by (rule renamed_site_injective[OF bij_is_inj[OF permutation]])
  then show "inj (map_prod h id)" .
  fix d
  show "map_prod h id d \<in> native_definition_sites (rename_environment h E) (map_prod h id ` roots) \<longleftrightarrow>
      d \<in> native_definition_sites E roots"
    by (auto simp: native_definition_sites_def native_definition_edges_renaming[OF formed permutation]
      rtrancl_injective_image[OF injective])
qed

lemma native_definition_graph_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "(map_prod h id d, p, D) \<in> native_definition_graph (rename_environment h E) (map_prod h id ` roots) \<longleftrightarrow>
    (\<exists>C. (d,p,C) \<in> native_definition_graph E roots \<and> D = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C)"
  by (auto simp: native_definition_graph_def native_definition_sites_renaming[OF formed permutation]
      inj_image_mem_iff[OF renamed_site_injective[OF bij_is_inj[OF permutation]]]
      native_definition_use_renaming[OF formed permutation])

lemma native_definition_exists_renamed:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "(\<exists>C. native_definition_at (rename_environment h E) (h u) r p C) \<longleftrightarrow>
    (\<exists>C. native_definition_at E u r p C)"
  using native_definition_use_renaming[OF formed permutation] by blast

lemma native_package_formed_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_package_formed (rename_environment h E) (map_prod h id ` roots) \<longleftrightarrow> native_package_formed E roots"
  by (auto simp: native_package_formed_def native_definition_sites_renaming[OF formed permutation]
      native_definition_exists_renamed[OF formed permutation]
      environment_renaming_formed[OF formed bij_is_inj[OF permutation]] formed)

theorem native_program_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_program (rename_environment h E) (map_prod h id ` roots) =
    rename_system (map_prod h id) (native_program E roots)"
proof -
  have injective: "inj (map_prod h id)" by (rule renamed_site_injective[OF bij_is_inj[OF permutation]])
  have surjective: "surj (map_prod h id)" by (rule map_prod_surj[OF bij_is_surj[OF permutation] surj_id])
  let ?g = "map_prod h id" and ?E = "rename_environment h E"
  have interface_at: "(a,p) \<in> system_interfaces (native_program ?E (?g ` roots)) \<longleftrightarrow>
      (a,p) \<in> system_interfaces (rename_system ?g (native_program E roots))" for a p
  proof -
    obtain d where d: "a = ?g d" using surjD[OF surjective] by blast
    have left: "(?g d,p) \<in> system_interfaces (native_program ?E (?g ` roots)) \<longleftrightarrow>
        (\<exists>C. (d,p,C) \<in> native_definition_graph E roots)"
    proof -
      have "(?g d,p) \<in> system_interfaces (native_program ?E (?g ` roots)) \<longleftrightarrow>
          (\<exists>D. (?g d,p,D) \<in> native_definition_graph ?E (?g ` roots))"
        by (simp add: native_program_def)
      also have "\<dots> \<longleftrightarrow> (\<exists>C. (d,p,C) \<in> native_definition_graph E roots)"
        by (simp only: native_definition_graph_renaming[OF formed permutation]; blast)
      finally show ?thesis .
    qed
    have right: "(?g d,p) \<in> system_interfaces (rename_system ?g (native_program E roots)) \<longleftrightarrow>
        (\<exists>C. (d,p,C) \<in> native_definition_graph E roots)"
    proof -
      have "(?g d,p) \<in> system_interfaces (rename_system ?g (native_program E roots)) \<longleftrightarrow>
          (d,p) \<in> system_interfaces (native_program E roots)"
        by (simp only: renamed_system_interface inj_eq[OF injective]; blast)
      also have "\<dots> \<longleftrightarrow> (\<exists>C. (d,p,C) \<in> native_definition_graph E roots)"
        by (simp add: native_program_def)
      finally show ?thesis .
    qed
    show ?thesis unfolding d using left right by simp
  qed
  have interfaces: "system_interfaces (native_program (rename_environment h E) (map_prod h id ` roots)) =
      system_interfaces (rename_system (map_prod h id) (native_program E roots))"
    by (simp only: set_eq_iff split_paired_All interface_at simp_thms)
  have clause_at: "((a,c),S) \<in> system_clauses (native_program ?E (?g ` roots)) \<longleftrightarrow>
      ((a,c),S) \<in> system_clauses (rename_system ?g (native_program E roots))" for a c S
  proof -
    obtain d where d: "a = ?g d" using surjD[OF surjective] by blast
    have left: "((?g d,c),S) \<in> system_clauses (native_program ?E (?g ` roots)) \<longleftrightarrow>
        (\<exists>p C T. (d,p,C) \<in> native_definition_graph E roots \<and> (c,T) \<in> C \<and> S = rename_schema id id ?g T)"
    proof -
      have "((?g d,c),S) \<in> system_clauses (native_program ?E (?g ` roots)) \<longleftrightarrow>
          (\<exists>p D. (?g d,p,D) \<in> native_definition_graph ?E (?g ` roots) \<and> (c,S) \<in> D)"
        by (simp add: native_program_def)
      also have "\<dots> \<longleftrightarrow> (\<exists>p C. (d,p,C) \<in> native_definition_graph E roots \<and>
          (c,S) \<in> (\<lambda>(s,A). (s,rename_schema id id ?g A)) ` C)"
        by (simp only: native_definition_graph_renaming[OF formed permutation]; blast)
      also have "\<dots> \<longleftrightarrow> (\<exists>p C T. (d,p,C) \<in> native_definition_graph E roots \<and> (c,T) \<in> C \<and>
          S = rename_schema id id ?g T)"
        by (simp only: map_relation_values_member[unfolded map_relation_values_def]; blast)
      finally show ?thesis .
    qed
    have right: "((?g d,c),S) \<in> system_clauses (rename_system ?g (native_program E roots)) \<longleftrightarrow>
        (\<exists>p C T. (d,p,C) \<in> native_definition_graph E roots \<and> (c,T) \<in> C \<and> S = rename_schema id id ?g T)"
    proof -
      have "((?g d,c),S) \<in> system_clauses (rename_system ?g (native_program E roots)) \<longleftrightarrow>
          (\<exists>T. ((d,c),T) \<in> system_clauses (native_program E roots) \<and> S = rename_schema id id ?g T)"
        by (simp only: renamed_system_clause inj_eq[OF injective]; blast)
      also have "\<dots> \<longleftrightarrow> (\<exists>p C T. (d,p,C) \<in> native_definition_graph E roots \<and> (c,T) \<in> C \<and>
          S = rename_schema id id ?g T)"
        by (simp add: native_program_def; blast)
      finally show ?thesis .
    qed
    show ?thesis unfolding d using left right by simp
  qed
  have clauses: "system_clauses (native_program (rename_environment h E) (map_prod h id ` roots)) =
      system_clauses (rename_system (map_prod h id) (native_program E roots))"
    by (simp only: set_eq_iff split_paired_All clause_at simp_thms)
  show ?thesis
    by (rule schema_system.equality) (rule interfaces, rule clauses, simp add: native_program_def rename_system_def)
qed

theorem native_package_renamed_use:
  assumes formed: "environment_formed E" and permutation: "bij h" and package: "native_package_at E u r P"
  shows "native_package_at (rename_environment h E) (h u) r (rename_system (map_prod h id) P)"
proof -
  obtain Q where Q: "native_root_family_at E u r Q" "native_package_formed E (rel_ran Q)"
      "P = native_program E (rel_ran Q)"
    using package by (auto simp: native_package_at_def)
  have family: "native_root_family_at (rename_environment h E) (h u) r (map_relation_values (map_prod h id) Q)"
    by (rule native_root_family_renamed_use[OF bij_is_inj[OF permutation] Q(1)])
  have roots: "rel_ran (map_relation_values (map_prod h id) Q) = map_prod h id ` rel_ran Q"
    by (rule map_relation_values_range)
  have packaged: "native_package_formed (rename_environment h E) (rel_ran (map_relation_values (map_prod h id) Q))"
    using Q(2) by (simp only: roots native_package_formed_renaming[OF formed permutation])
  have program: "native_program (rename_environment h E) (rel_ran (map_relation_values (map_prod h id) Q)) =
      rename_system (map_prod h id) P"
    by (simp only: roots native_program_renaming[OF formed permutation] Q(3))
  show ?thesis unfolding native_package_at_def
    by (intro exI[of _ "map_relation_values (map_prod h id) Q"] conjI family packaged program[symmetric])
qed

theorem native_package_use_renaming:
  assumes formed: "environment_formed E" and permutation: "bij h"
  shows "native_package_at (rename_environment h E) (h u) r Q \<longleftrightarrow>
    (\<exists>P. native_package_at E u r P \<and> Q = rename_system (map_prod h id) P)"
  by (rule use_renaming_inverse[where read="\<lambda>F v P. native_package_at F v r P"
      and read'="\<lambda>F v P. native_package_at F v r P"
      and move="\<lambda>g P. rename_system (map_prod g id) P"
      and move'="\<lambda>g P. rename_system (map_prod g id) P",
      OF native_package_renamed_use native_package_renamed_use native_package_unique formed permutation])

text \<open>
  The relocated program has the original's meaning at the renamed sites and the same argument terms
  (@{thm [source] renamed_system_positive_meaning}), at every site, a definition of the program or not.
\<close>

theorem native_package_renamed_meaning:
  assumes package: "native_package_at E u r P" and injective: "inj h"
  shows "(map_prod h id d, t) \<in> positive_meaning (rename_system (map_prod h id) P) \<longleftrightarrow>
    (d,t) \<in> positive_meaning P"
proof -
  have program: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have sites: "inj_on (map_prod h id) (system_definitions P)"
    by (rule inj_on_subset[OF renamed_site_injective[OF injective]]) simp
  have pair: "inj (map_prod (map_prod h id) (id :: factor_term \<Rightarrow> factor_term))"
    using map_prod_inj_on[OF renamed_site_injective[OF injective] inj_on_id[of UNIV]] by simp
  have "(map_prod h id d, t) \<in> map_prod (map_prod h id) id ` positive_meaning P \<longleftrightarrow> (d,t) \<in> positive_meaning P"
    using inj_image_mem_iff[OF pair, of "(d,t)"] by simp
  then show ?thesis by (simp only: renamed_system_positive_meaning[OF program sites])
qed

end
