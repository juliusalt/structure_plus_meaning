theory Factor_Use_Renaming
  imports Presentation_Equivariance RRA_Structural_Syntax Factor_Native_Transport
    Factor_Program_Entry_Presentations Factor_Packages Factor_System_Relocation
begin

section \<open>Uses are renamed by permutations\<close>

text \<open>
  Non-nominality of uses is the notion of @{text Presentation_Equivariance} at the permutations of
  uses, every permutation admissible and one permutation acting on all of a relation's arguments.
  The RRA readers locate a use and never inspect it; their renaming facts are consumed as they stand:
  @{thm [source] environment_renaming_formed}, @{thm [source] artifact_at_renamed_use},
  @{thm [source] binds_slot_renamed_use}, @{thm [source] citation_use_renaming},
  @{thm [source] citation_location_use_renaming}, @{thm [source] anchored_at_use_renaming} and
  @{thm [source] located_at_use_renaming}. This theory adds the laws of the action and the renaming
  of the Factor definition readers and of uses compared as data.
\<close>

subsection \<open>The action on environments\<close>

lemma rename_environment_id [simp]: "rename_environment id E = E"
  by (cases E) (simp add: rename_environment_def split_def)

lemma rename_environment_comp:
  "rename_environment (g \<circ> h) E = rename_environment g (rename_environment h E)"
  by (cases E) (simp add: rename_environment_def image_image split_def)

theorem environment_renaming_action: "renaming_action bij rename_environment environment_formed"
  by unfold_locales
    (auto intro: bij_comp bij_imp_bij_inv environment_renaming_formed bij_is_inj simp: rename_environment_comp)

text \<open>A renaming reads only the environment's uses.\<close>

lemma rename_environment_cong:
  assumes formed: "environment_formed E" and agree: "\<And>u. u \<in> environment_uses E \<Longrightarrow> g u = h u"
  shows "rename_environment g E = rename_environment h E"
proof -
  have artifacts: "(\<lambda>(u,R). (g u,R)) ` environment_artifacts E = (\<lambda>(u,R). (h u,R)) ` environment_artifacts E"
  proof (rule image_cong[OF refl])
    fix x assume member: "x \<in> environment_artifacts E"

    have "fst x \<in> environment_uses E"
      using member rel_domI[of "fst x" "snd x"] by (simp add: environment_uses_def)
    then show "(\<lambda>(u,R). (g u,R)) x = (\<lambda>(u,R). (h u,R)) x" using agree by (simp add: split_def)
  qed
  have bindings: "(\<lambda>((u,k),v). ((g u,k),g v)) ` environment_bindings E =
      (\<lambda>((u,k),v). ((h u,k),h v)) ` environment_bindings E"
  proof (rule image_cong[OF refl])
    fix x assume member: "x \<in> environment_bindings E"
    have bound: "binds_slot E (fst (fst x)) (snd (fst x)) (snd x)" using member by (simp add: binds_slot_def)
    show "(\<lambda>((u,k),v). ((g u,k),g v)) x = (\<lambda>((u,k),v). ((h u,k),h v)) x"
      using agree[OF environment_binding_uses(1)[OF formed bound]]
        agree[OF environment_binding_uses(2)[OF formed bound]] by (simp add: split_def)
  qed
  show ?thesis by (simp add: rename_environment_def artifacts bindings)
qed

text \<open>
  An injective renaming of a formed environment's finitely many uses is the renaming by a permutation
  (@{thm [source] finite_injection_permutation}), so the RRA facts, stated for injections, hold at the
  group's renamings and nothing is lost by admitting permutations only.
\<close>

theorem injective_renaming_permutation:
  fixes f :: "'u \<Rightarrow> 'u"
  assumes formed: "environment_formed E" and injective: "inj_on f (environment_uses E)"
  shows "\<exists>h. bij h \<and> (\<forall>u\<in>environment_uses E. h u = f u) \<and> rename_environment f E = rename_environment h E"
proof -
  obtain h where h: "bij h" "\<forall>u\<in>environment_uses E. h u = f u"
    using finite_injection_permutation[OF environment_uses_finite[OF formed] injective] by blast
  have "rename_environment f E = rename_environment h E"
    by (rule rename_environment_cong[OF formed]) (simp add: h(2))
  then show ?thesis using h by blast
qed

subsection \<open>Positions, uses, sites, site contexts and program entries\<close>

lemma environment_positions_renaming:
  "environment_positions (rename_environment h E) = map_prod h id ` environment_positions E"
proof -
  have renamed: "(v,a) \<in> environment_positions (rename_environment h E) \<longleftrightarrow>
      (\<exists>u. v = h u \<and> (u,a) \<in> environment_positions E)" for v a
    by (simp add: artifact_at_renaming) blast
  have image: "(v,a) \<in> map_prod h id ` environment_positions E \<longleftrightarrow>
      (\<exists>u. v = h u \<and> (u,a) \<in> environment_positions E)" for v a
  proof
    assume "(v,a) \<in> map_prod h id ` environment_positions E"
    then obtain y where member: "y \<in> environment_positions E" and moved: "(v,a) = map_prod h id y"
      by (rule imageE)
    obtain u b where y: "y = (u,b)" by (cases y)
    have "v = h u" "a = b" using moved unfolding y by simp_all
    then show "\<exists>u. v = h u \<and> (u,a) \<in> environment_positions E" using member unfolding y by blast
  next
    assume "\<exists>u. v = h u \<and> (u,a) \<in> environment_positions E"
    then obtain u where v: "v = h u" and member: "(u,a) \<in> environment_positions E" by blast
    show "(v,a) \<in> map_prod h id ` environment_positions E" by (rule rev_image_eqI[OF member]) (simp add: v)
  qed
  show ?thesis by (simp only: set_eq_iff split_paired_All renamed image simp_thms)
qed

lemma product_action_map_prod: "product_action actL actR h = map_prod (actL h) (actR h)"
  by (simp add: fun_eq_iff product_action_def map_prod_def split_def)

text \<open>The site action is the product of the use action and the trivial action on addresses.\<close>

lemma site_renaming_product: "map_prod h id = product_action (\<lambda>h. h) (\<lambda>h a. a) h"
  by (simp add: product_action_map_prod id_def)

theorem use_renaming_action: "renaming_action bij (\<lambda>h. h) (\<lambda>_. True)"
  by unfold_locales (auto intro: bij_comp bij_imp_bij_inv)

theorem site_renaming_action: "renaming_action bij (\<lambda>h. map_prod h id) (\<lambda>_. True)"
proof -
  have product: "renaming_action bij (product_action (\<lambda>h. h) (\<lambda>h a. a)) (\<lambda>_. True)"
    by (rule renaming_action_subdomain[OF renaming_action_product[OF use_renaming_action
        permutation_renaming_action[where D="\<lambda>_. True"]]]) simp_all
  have act: "product_action (\<lambda>h. h) (\<lambda>h a. a) = (\<lambda>h. map_prod h id)"
    by (rule ext) (rule site_renaming_product[symmetric])
  show ?thesis using product by (simp only: act)
qed

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

lemma map_citation_positions_id [simp]: "map_citation_positions id c = c"
  by (cases c) simp_all

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
proof
  assume renamed: "native_definition_at (rename_environment h E) (h u) r p D"
  have injective: "inj h" by (rule bij_is_inj[OF permutation])
  have inverse_injective: "inj (inv h)" by (rule bij_is_inj[OF bij_imp_bij_inv[OF permutation]])
  have renamed_formed: "environment_formed (rename_environment h E)"
    by (rule environment_renaming_formed[OF formed injective])
  have inverse_environment: "rename_environment (inv h) (rename_environment h E) = E"
    by (simp only: rename_environment_comp[symmetric] inv_o_cancel[OF injective] rename_environment_id)
  have inverse_use: "inv h (h u) = u" by (rule inv_f_f[OF injective])
  let ?C = "(\<lambda>(s,A). (s,rename_schema id id (map_prod (inv h) id) A)) ` D"
  have original: "native_definition_at E u r p ?C"
    using native_definition_renamed_use[OF renamed_formed inverse_injective renamed]
    by (simp only: inverse_environment inverse_use)
  have renamed_again: "native_definition_at (rename_environment h E) (h u) r p
      ((\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` ?C)"
    by (rule native_definition_renamed_use[OF formed injective original])
  have "D = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` ?C"
    using native_definition_unique[OF renamed renamed_again] by blast
  then show "\<exists>C. native_definition_at E u r p C \<and> D = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C"
    using original by blast
next
  assume "\<exists>C. native_definition_at E u r p C \<and> D = (\<lambda>(s,A). (s,rename_schema id id (map_prod h id) A)) ` C"
  then show "native_definition_at (rename_environment h E) (h u) r p D"
    using native_definition_renamed_use[OF formed bij_is_inj[OF permutation]] by blast
qed

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


lemma surjective_image_eq:
  assumes surjective: "surj g" and injective: "inj g" and at: "\<And>d. g d \<in> A' \<longleftrightarrow> d \<in> A"
  shows "A' = g ` A"
proof (rule set_eqI)
  fix x
  obtain d where x: "x = g d" using surjD[OF surjective] by blast
  show "x \<in> A' \<longleftrightarrow> x \<in> g ` A" by (simp add: x at inj_image_mem_iff[OF injective])
qed

lemma rtrancl_injective_image:
  assumes injective: "inj f"
  shows "(f x, f y) \<in> (map_prod f f ` R)\<^sup>* \<longleftrightarrow> (x,y) \<in> R\<^sup>*"
proof
  assume "(x,y) \<in> R\<^sup>*"
  then show "(f x, f y) \<in> (map_prod f f ` R)\<^sup>*"
  proof (induction rule: rtrancl_induct)
    case base then show ?case by simp
  next
    case (step m n)
    have "(f m, f n) \<in> map_prod f f ` R" by (rule rev_image_eqI[OF step.hyps(2)]) simp
    then show ?case by (rule rtrancl_into_rtrancl[OF step.IH])
  qed
next
  assume path: "(f x, f y) \<in> (map_prod f f ` R)\<^sup>*"
  have reached: "\<exists>z. b = f z \<and> (x,z) \<in> R\<^sup>*" if "(f x, b) \<in> (map_prod f f ` R)\<^sup>*" for b
    using that
  proof (induction rule: rtrancl_induct)
    case base then show ?case by blast
  next
    case (step m n)
    obtain z where z: "m = f z" "(x,z) \<in> R\<^sup>*" using step.IH by blast
    from step.hyps(2) obtain q where q: "q \<in> R" "(m,n) = map_prod f f q" by (rule imageE)
    obtain v w where vw: "q = (v,w)" by (cases q)
    have edge: "(v,w) \<in> R" "m = f v" "n = f w" using q vw by simp_all
    have vz: "v = z" using edge(2) z(1) injD[OF injective] by metis
    have "(x,v) \<in> R\<^sup>*" using z(2) vz by simp
    then have "(x,w) \<in> R\<^sup>*" by (rule rtrancl_into_rtrancl[OF _ edge(1)])
    then show ?case using edge(3) by blast
  qed
  obtain z where "f y = f z" "(x,z) \<in> R\<^sup>*" using reached[OF path] by blast
  then show "(x,y) \<in> R\<^sup>*" using injD[OF injective] by metis
qed

lemma rel_ran_map_relation_values: "rel_ran (map_relation_values f R) = f ` rel_ran R"
  by (auto simp: rel_ran_def)


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
    by (rule rel_ran_map_relation_values)
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
proof
  assume renamed: "native_package_at (rename_environment h E) (h u) r Q"
  have injective: "inj h" by (rule bij_is_inj[OF permutation])
  have inverse: "bij (inv h)" by (rule bij_imp_bij_inv[OF permutation])
  have renamed_formed: "environment_formed (rename_environment h E)"
    by (rule environment_renaming_formed[OF formed injective])
  have inverse_environment: "rename_environment (inv h) (rename_environment h E) = E"
    by (simp only: rename_environment_comp[symmetric] inv_o_cancel[OF injective] rename_environment_id)
  have inverse_use: "inv h (h u) = u" by (rule inv_f_f[OF injective])
  let ?P = "rename_system (map_prod (inv h) id) Q"
  have original: "native_package_at E u r ?P"
    using native_package_renamed_use[OF renamed_formed inverse renamed]
    by (simp only: inverse_environment inverse_use)
  have renamed_again: "native_package_at (rename_environment h E) (h u) r (rename_system (map_prod h id) ?P)"
    by (rule native_package_renamed_use[OF formed permutation original])
  have "Q = rename_system (map_prod h id) ?P" by (rule native_package_unique[OF renamed renamed_again])
  then show "\<exists>P. native_package_at E u r P \<and> Q = rename_system (map_prod h id) P" using original by blast
next
  assume "\<exists>P. native_package_at E u r P \<and> Q = rename_system (map_prod h id) P"
  then show "native_package_at (rename_environment h E) (h u) r Q"
    using native_package_renamed_use[OF formed permutation] by blast
qed

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

subsection \<open>Uses compared as data\<close>

lemma use_data_equality_renaming:
  assumes "inj h"
  shows "use_data_term (h u) = use_data_term (h v) \<longleftrightarrow> use_data_term u = use_data_term v"
  by (simp add: inj_eq[OF use_data_term_injective] inj_eq[OF assms])

lemma use_data_inequality_renaming:
  assumes "inj h"
  shows "use_data_term (h u) \<noteq> use_data_term (h v) \<longleftrightarrow> use_data_term u \<noteq> use_data_term v"
  using use_data_equality_renaming[OF assms] by simp

theorem use_data_comparison_renaming:
  assumes "inj h"
  shows "(3,Pair_Term (use_data_term (h u)) (use_data_term (h v))) \<in> positive_meaning data_comparison_system
    \<longleftrightarrow> (3,Pair_Term (use_data_term u) (use_data_term v)) \<in> positive_meaning data_comparison_system"
  by (simp add: data_comparison_exact inj_eq[OF use_data_term_injective] inj_eq[OF assms])

text \<open>
  One permutation acts on both uses of a pair: the product of the use action with itself, on the
  domain of all pairs, which a client feeds with the clauses below to the notion's contract.
\<close>

theorem use_pair_renaming_action: "renaming_action bij (product_action (\<lambda>h. h) (\<lambda>h. h)) (\<lambda>z. True)"
  by (rule renaming_action_subdomain[OF renaming_action_product[OF use_renaming_action use_renaming_action]])
    simp_all

theorem use_data_equality_equivariant:
  "renaming_equivariant bij (product_action (\<lambda>h. h) (\<lambda>h. h)) (\<lambda>z. True)
    (\<lambda>z. use_data_term (fst z) = use_data_term (snd z))"
  by (auto simp: renaming_equivariant_def product_action_def use_data_equality_renaming[OF bij_is_inj])

theorem use_data_comparison_equivariant:
  "renaming_equivariant bij (product_action (\<lambda>h. h) (\<lambda>h. h)) (\<lambda>z. True)
    (\<lambda>z. (3,Pair_Term (use_data_term (fst z)) (use_data_term (snd z))) \<in> positive_meaning data_comparison_system)"
  by (auto simp: renaming_equivariant_def product_action_def use_data_comparison_renaming[OF bij_is_inj])

text \<open>
  The data comparison entry, as @{thm [source] native_data_inequality} compiles it, relates two use
  presentations exactly when the uses differ, so a relation that compares the uses it reads for
  equality is equivariant under every permutation of uses: that is what "sites are compared for
  equality" means natively.
\<close>

end
