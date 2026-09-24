theory Factor_Use_Renaming
  imports Presentation_Equivariance RRA_Structural_Syntax Factor_Native_Transport
    Factor_Program_Entry_Presentations
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
  by unfold_locales (auto intro: bij_comp bij_imp_bij_inv simp: map_prod_def split_def)

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
