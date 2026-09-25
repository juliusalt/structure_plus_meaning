theory Factor_Use_Actions
  imports Presentation_Equivariance RRA_Citation_Closure Factor_Coordinate_Values
begin

section \<open>Uses are renamed by permutations\<close>

text \<open>
  Non-nominality of uses is the notion of @{text Presentation_Equivariance} at the permutations of
  uses, every permutation admissible and one permutation acting on all of a relation's arguments.
  The RRA readers locate a use and never inspect it; their renaming facts are consumed as they stand:
  @{thm [source] environment_renaming_formed}, @{thm [source] artifact_at_renamed_use},
  @{thm [source] binds_slot_renamed_use}, @{thm [source] citation_use_renaming},
  @{thm [source] citation_location_use_renaming}, @{thm [source] anchored_at_use_renaming} and
  @{thm [source] located_at_use_renaming}. This theory is the low part of the use instance: the laws of
  the actions on environments, uses and sites, the renaming of an environment's positions, the comparison
  of uses as data, and the inverse-permutation argument every reading's renaming consumes. The Factor
  readers' renamings stand in @{text Factor_Use_Renaming}; the clauses of data inequality and key absence
  at uses beside their contracts (@{text Factor_Data_Comparison}, @{text Factor_Keyed_Lists}).
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

subsection \<open>Positions, uses and sites\<close>

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

subsection \<open>Uses compared as data\<close>

lemma use_data_equality_renaming:
  assumes "inj h"
  shows "use_data_term (h u) = use_data_term (h v) \<longleftrightarrow> use_data_term u = use_data_term v"
  by (simp add: inj_eq[OF use_data_term_injective] inj_eq[OF assms])

lemma use_data_inequality_renaming:
  assumes "inj h"
  shows "use_data_term (h u) \<noteq> use_data_term (h v) \<longleftrightarrow> use_data_term u \<noteq> use_data_term v"
  using use_data_equality_renaming[OF assms] by simp

text \<open>
  One permutation acts on both uses of a pair: the product of the use action with itself, on the
  domain of all pairs, which a client feeds with a pair's clause to the notion's contract.
\<close>

theorem use_pair_renaming_action: "renaming_action bij (product_action (\<lambda>h. h) (\<lambda>h. h)) (\<lambda>z. True)"
  by (rule renaming_action_subdomain[OF renaming_action_product[OF use_renaming_action use_renaming_action]])
    simp_all

theorem use_data_equality_equivariant:
  "renaming_equivariant bij (product_action (\<lambda>h. h) (\<lambda>h. h)) (\<lambda>z. True)
    (\<lambda>z. use_data_term (fst z) = use_data_term (snd z))"
  by (auto simp: renaming_equivariant_def product_action_def use_data_equality_renaming[OF bij_is_inj])

subsection \<open>A reading at a permuted use\<close>

text \<open>
  The inverse-permutation argument, stated once for any reading of an environment at a use: a reading
  carried forward to the renamed use of the renamed environment by every permutation, and unique at each
  use, holds at a permuted use exactly of the renamed readings of the original use. The inverse
  permutation carries a reading back, and uniqueness identifies its renaming again with the reading it
  came from. A permutation may move uses between two use types, so the reading and its renaming are
  given at each type (a polymorphic reading supplies both). The definition, schema and package
  readings' renamings instantiate it.
\<close>

theorem use_renaming_inverse:
  fixes read :: "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> 'x \<Rightarrow> bool" and move :: "('u \<Rightarrow> 'v) \<Rightarrow> 'x \<Rightarrow> 'y"
    and read' :: "'v artifact_environment \<Rightarrow> 'v \<Rightarrow> 'y \<Rightarrow> bool" and move' :: "('v \<Rightarrow> 'u) \<Rightarrow> 'y \<Rightarrow> 'x"
  assumes forward: "\<And>E h u x. environment_formed E \<Longrightarrow> bij h \<Longrightarrow> read E u x \<Longrightarrow>
      read' (rename_environment h E) (h u) (move h x)"
    and backward: "\<And>F g v y. environment_formed F \<Longrightarrow> bij g \<Longrightarrow> read' F v y \<Longrightarrow>
      read (rename_environment g F) (g v) (move' g y)"
    and unique: "\<And>F v y z. read' F v y \<Longrightarrow> read' F v z \<Longrightarrow> y = z"
    and formed: "environment_formed E" and permutation: "bij h"
  shows "read' (rename_environment h E) (h u) y \<longleftrightarrow> (\<exists>x. read E u x \<and> y = move h x)"
proof
  assume renamed: "read' (rename_environment h E) (h u) y"
  have inverse: "bij (inv h)" by (rule bij_imp_bij_inv[OF permutation])
  have renamed_formed: "environment_formed (rename_environment h E)"
    by (rule environment_renaming_formed[OF formed bij_is_inj[OF permutation]])
  have undone: "rename_environment (inv h) (rename_environment h E) = E"
    by (simp only: rename_environment_comp[symmetric] inv_o_cancel[OF bij_is_inj[OF permutation]]
      rename_environment_id)
  have back_use: "inv h (h u) = u" by (rule inv_f_f[OF bij_is_inj[OF permutation]])
  have original: "read E u (move' (inv h) y)"
    using backward[OF renamed_formed inverse renamed] by (simp only: undone back_use)
  have "y = move h (move' (inv h) y)" by (rule unique[OF renamed forward[OF formed permutation original]])
  then show "\<exists>x. read E u x \<and> y = move h x" using original by blast
next
  assume "\<exists>x. read E u x \<and> y = move h x"
  then show "read' (rename_environment h E) (h u) y" using forward[OF formed permutation] by blast
qed

end
