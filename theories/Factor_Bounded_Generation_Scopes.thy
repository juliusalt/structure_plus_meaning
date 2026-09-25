theory Factor_Bounded_Generation_Scopes
  imports Factor_Policy_Causes Factor_Use_Actions
begin

section \<open>The fill: an environment's placeholders replaced by one artifact\<close>

text \<open>
  A scope whose uses V hold the payload is recorded with those uses as its boundary: the recorded
  environment F0 holds the empty artifact at V, and the fill puts the payload back. Every binding is
  kept. When F0 is formed and every use of V holds the empty artifact, no binding has its source in V
  (a bound slot lies in its source artifact's carrier, and the empty artifact has none), so the fill is
  formed exactly when the payload is, or V is empty.
\<close>

definition payload_fill :: "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> exact_artifact \<Rightarrow> 'u artifact_environment" where
  "payload_fill F0 V R =
    \<lparr>environment_artifacts = (\<lambda>(u,S). (u, if u\<in>V then R else S)) ` environment_artifacts F0,
     environment_bindings = environment_bindings F0\<rparr>"

lemma artifact_at_payload_fill:
  "artifact_at (payload_fill F0 V R) u S \<longleftrightarrow> (\<exists>T. artifact_at F0 u T \<and> S=(if u\<in>V then R else T))"
proof
  assume "artifact_at (payload_fill F0 V R) u S"
  then obtain x where x: "x\<in>environment_artifacts F0" "(u,S)=(\<lambda>(u,S). (u, if u\<in>V then R else S)) x"
    unfolding artifact_at_def payload_fill_def by auto
  obtain v T where pair: "x=(v,T)" by (cases x)
  show "\<exists>T. artifact_at F0 u T \<and> S=(if u\<in>V then R else T)"
    using x unfolding pair by (auto simp: artifact_at_def)
next
  assume "\<exists>T. artifact_at F0 u T \<and> S=(if u\<in>V then R else T)"
  then obtain T where T: "(u,T)\<in>environment_artifacts F0" "S=(if u\<in>V then R else T)"
    unfolding artifact_at_def by blast
  show "artifact_at (payload_fill F0 V R) u S"
    unfolding artifact_at_def payload_fill_def using T by (auto intro: rev_image_eqI[of "(u,T)"])
qed

lemma binds_slot_payload_fill [simp]:
  "binds_slot (payload_fill F0 V R) u k v \<longleftrightarrow> binds_slot F0 u k v"
  by (simp add: binds_slot_def payload_fill_def)

lemma environment_uses_payload_fill [simp]:
  "environment_uses (payload_fill F0 V R) = environment_uses F0"
  by (simp add: environment_uses_def rel_dom_image payload_fill_def image_image split_def)

theorem payload_fill_formed:
  assumes formed: "environment_formed F0"
    and placeholders: "\<forall>u\<in>V. artifact_at F0 u empty_artifact"
  shows "environment_formed (payload_fill F0 V R) \<longleftrightarrow> V={} \<or> exact_formed R"
proof -
  have unique: "S=T" if "artifact_at F0 u S" "artifact_at F0 u T" for u S T
    by (rule environment_artifact_unique[OF formed that])
  have sources: "u\<notin>V" if bound: "binds_slot F0 u k v" for u k v
  proof
    assume member: "u\<in>V"
    obtain T where T: "artifact_at F0 u T" "k\<in>rra_carrier (object_structure T)"
      using formed bound unfolding environment_formed_def by blast
    have "T=empty_artifact" using unique[OF T(1)] placeholders member by blast
    then show False using T(2) by (simp add: empty_artifact_def)
  qed
  show ?thesis
  proof
    assume filled: "environment_formed (payload_fill F0 V R)"
    show "V={} \<or> exact_formed R"
    proof (cases "V={}")
      case False
      then obtain u where "u\<in>V" by blast
      then have "artifact_at (payload_fill F0 V R) u R"
        using placeholders by (auto simp: artifact_at_payload_fill)
      then show ?thesis using filled unfolding environment_formed_def by blast
    qed simp
  next
    assume "V={} \<or> exact_formed R"
    then have exact: "exact_formed R" if "u\<in>V" for u using that by blast
    have arts_finite: "finite (environment_artifacts (payload_fill F0 V R))"
      using formed by (simp add: payload_fill_def environment_formed_def)
    have arts_sv: "single_valued (environment_artifacts (payload_fill F0 V R))"
      unfolding single_valued_def
    proof (intro allI impI)
      fix u S S'
      assume "(u,S)\<in>environment_artifacts (payload_fill F0 V R)"
        "(u,S')\<in>environment_artifacts (payload_fill F0 V R)"
      then have "artifact_at (payload_fill F0 V R) u S" "artifact_at (payload_fill F0 V R) u S'"
        by (simp_all only: artifact_at_def)
      then show "S=S'" by (metis artifact_at_payload_fill unique)
    qed
    have arts_exact: "\<forall>u S. artifact_at (payload_fill F0 V R) u S \<longrightarrow> exact_formed S"
      using formed exact by (auto simp: artifact_at_payload_fill environment_formed_def)
    have binds_finite: "finite (environment_bindings (payload_fill F0 V R))"
      and binds_sv: "single_valued (environment_bindings (payload_fill F0 V R))"
      using formed by (simp_all add: payload_fill_def environment_formed_def)
    have binds: "\<forall>u k v. binds_slot (payload_fill F0 V R) u k v \<longrightarrow>
        (\<exists>S. artifact_at (payload_fill F0 V R) u S \<and> k\<in>rra_carrier (object_structure S)) \<and>
        v\<in>environment_uses (payload_fill F0 V R)"
    proof (intro allI impI)
      fix u k v assume "binds_slot (payload_fill F0 V R) u k v"
      then have bound: "binds_slot F0 u k v" by simp
      obtain T where T: "artifact_at F0 u T" "k\<in>rra_carrier (object_structure T)" "v\<in>environment_uses F0"
        using formed bound unfolding environment_formed_def by blast
      have "artifact_at (payload_fill F0 V R) u T"
        using T(1) sources[OF bound] by (auto simp: artifact_at_payload_fill)
      then show "(\<exists>S. artifact_at (payload_fill F0 V R) u S \<and> k\<in>rra_carrier (object_structure S)) \<and>
        v\<in>environment_uses (payload_fill F0 V R)" using T(2,3) by auto
    qed
    show "environment_formed (payload_fill F0 V R)"
      unfolding environment_formed_def
      using arts_finite arts_sv arts_exact binds_finite binds_sv binds by blast
  qed
qed

corollary payload_fill_formed_exact:
  assumes "environment_formed F0" "\<forall>u\<in>V. artifact_at F0 u empty_artifact" "exact_formed R"
  shows "environment_formed (payload_fill F0 V R)"
  using payload_fill_formed[OF assms(1,2)] assms(3) by blast

section \<open>The fill commutes with the use action\<close>

theorem payload_fill_renaming:
  assumes inj: "inj h"
  shows "rename_environment h (payload_fill F0 V R) = payload_fill (rename_environment h F0) (h ` V) R"
  by (simp add: payload_fill_def rename_environment_def image_image split_def inj_image_mem_iff[OF inj]
    cong: if_cong)

text \<open>
  The relation of a filled environment, its placeholder environment and its boundary the bounded scope
  states is equivariant under every permutation of uses, one permutation acting on all three
  (@{thm [source] environment_renaming_action}, and the use action on the boundary), as task 383's
  entry reads non-nominality of uses.
\<close>

theorem payload_fill_equivariant:
  "renaming_equivariant bij
    (product_action rename_environment (product_action rename_environment (\<lambda>h. image h))) (\<lambda>z. True)
    (\<lambda>z. fst z=payload_fill (fst (snd z)) (snd (snd z)) R \<and>
      (\<forall>u\<in>snd (snd z). artifact_at (fst (snd z)) u empty_artifact))"
  unfolding renaming_equivariant_def
proof (intro allI impI)
  fix h :: "'u \<Rightarrow> 'u" and z :: "'u artifact_environment \<times> 'u artifact_environment \<times> 'u set"
  assume h: "bij h"
  obtain F F0 V where z: "z=(F,F0,V)" by (cases z) auto
  have inj: "inj h" by (rule bij_is_inj[OF h])
  have undo: "rename_environment (inv h) (rename_environment h E)=E" for E :: "'u artifact_environment"
    by (simp only: rename_environment_comp[symmetric] inv_o_cancel[OF inj] rename_environment_id)
  have fills: "rename_environment h F=payload_fill (rename_environment h F0) (h ` V) R \<longleftrightarrow>
      F=payload_fill F0 V R"
  proof
    assume "rename_environment h F=payload_fill (rename_environment h F0) (h ` V) R"
    then have "rename_environment (inv h) (rename_environment h F)=
        rename_environment (inv h) (rename_environment h (payload_fill F0 V R))"
      by (simp add: payload_fill_renaming[OF inj])
    then show "F=payload_fill F0 V R" by (simp only: undo)
  qed (simp add: payload_fill_renaming[OF inj])
  have at: "artifact_at (rename_environment h F0) (h u) empty_artifact \<longleftrightarrow> artifact_at F0 u empty_artifact"
    for u by (rule artifact_at_renamed_use[OF inj])

  show "(fst (product_action rename_environment (product_action rename_environment (\<lambda>h. image h)) h z)=
      payload_fill (fst (snd (product_action rename_environment (product_action rename_environment (\<lambda>h. image h)) h z)))
        (snd (snd (product_action rename_environment (product_action rename_environment (\<lambda>h. image h)) h z))) R \<and>
      (\<forall>u\<in>snd (snd (product_action rename_environment (product_action rename_environment (\<lambda>h. image h)) h z)).
        artifact_at (fst (snd (product_action rename_environment (product_action rename_environment (\<lambda>h. image h)) h z))) u
          empty_artifact)) \<longleftrightarrow>
    (fst z=payload_fill (fst (snd z)) (snd (snd z)) R \<and> (\<forall>u\<in>snd (snd z). artifact_at (fst (snd z)) u empty_artifact))"
    by (simp add: z fills at)
qed

section \<open>The bounded value and its quotation\<close>

text \<open>
  The bounded value pairs the judgment value of the placeholder environment at its program and call
  sites with the data list of the boundary's uses, every enumeration of the boundary admitted. Its
  complete data quotation recovers the environment, both sites and the boundary, and its root.
\<close>

definition bounded_scope_value_presents ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "bounded_scope_value_presents F0 pu pr au ar V t \<longleftrightarrow>
    (\<exists>j b. judgment_value_presents F0 pu pr au ar j \<and>
      data_collection_presents (\<lambda>u v. v=use_data_term u) V b \<and> t=Pair_Term j b)"

theorem bounded_scope_value_presents_unique:
  assumes first: "bounded_scope_value_presents F0 pu pr au ar V t"
    and second: "bounded_scope_value_presents F1 qu qr bu br W t"
  shows "F0=F1 \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> V=W"
proof -
  obtain j b where left: "judgment_value_presents F0 pu pr au ar j"
      "data_collection_presents (\<lambda>u v. v=use_data_term u) V b" "t=Pair_Term j b"
    using first unfolding bounded_scope_value_presents_def by blast
  obtain j' b' where right: "judgment_value_presents F1 qu qr bu br j'"
      "data_collection_presents (\<lambda>u v. v=use_data_term u) W b'" "t=Pair_Term j' b'"
    using second unfolding bounded_scope_value_presents_def by blast
  have parts: "j'=j" "b'=b" using left(3) right(3) by simp_all
  have sites: "F0=F1 \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    using judgment_value_presents_unique[OF left(1)] right(1) parts(1) by blast
  have other: "data_collection_presents (\<lambda>u v. v=use_data_term u) W b" using right(2) parts(2) by simp
  have uses: "V=W"
    by (rule data_collection_presents_unique[OF left(2) other])
      (auto simp: inj_eq[OF use_data_term_injective])
  show ?thesis using sites uses by blast
qed

lemma bounded_scope_value_presents_formed:
  assumes present: "bounded_scope_value_presents F0 pu pr au ar V t"
  shows "environment_formed F0 \<and> finite V \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain j b where parts: "judgment_value_presents F0 pu pr au ar j"
      "data_collection_presents (\<lambda>u v. v=use_data_term u) V b" "t=Pair_Term j b"
    using present unfolding bounded_scope_value_presents_def by blast
  have bf: "term_formed b" by (rule data_collection_presents_formed[OF parts(2)]) simp
  have bc: "self_contained_term b" by (rule data_collection_presents_self_contained[OF parts(2)]) simp
  show ?thesis using judgment_value_presents_formed[OF parts(1)] data_collection_presents_finite[OF parts(2)]
    bf bc parts(3) by simp
qed

theorem bounded_scope_value_presents_total:
  assumes ef: "environment_formed F0" and program: "(pu,pr)\<in>environment_positions F0"
    and app: "(au,ar)\<in>environment_positions F0" and fin: "finite V"
  shows "\<exists>t. bounded_scope_value_presents F0 pu pr au ar V t"
proof -
  obtain j where j: "judgment_value_presents F0 pu pr au ar j"
    using judgment_value_presents_total[OF ef program app] by blast
  obtain b where b: "data_collection_presents (\<lambda>u v. v=use_data_term u) V b"
    using data_collection_presents_total[OF fin, of "\<lambda>u v. v=use_data_term u"] by auto
  show ?thesis using j b unfolding bounded_scope_value_presents_def by blast
qed

definition bounded_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option set \<Rightarrow> bool" where
  "bounded_scope_quoted_at C r F0 pu pr au ar V \<longleftrightarrow>
    (\<exists>t. bounded_scope_value_presents F0 pu pr au ar V t \<and> complete_data_quoted_at C r t)"

theorem bounded_scope_whole_unique:
  assumes first: "bounded_scope_quoted_at C r F0 pu pr au ar V"
    and second: "bounded_scope_quoted_at C s F1 qu qr bu br W"
  shows "r=s \<and> F0=F1 \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> V=W"
proof -
  obtain t where t: "bounded_scope_value_presents F0 pu pr au ar V t" "complete_data_quoted_at C r t"
    using first unfolding bounded_scope_quoted_at_def by blast
  obtain v where v: "bounded_scope_value_presents F1 qu qr bu br W v" "complete_data_quoted_at C s v"
    using second unfolding bounded_scope_quoted_at_def by blast
  have same: "r=s \<and> t=v" by (rule complete_data_quotation_whole_unique[OF t(2) v(2)])
  have other: "bounded_scope_value_presents F1 qu qr bu br W t" using v(1) same by simp
  show ?thesis using same bounded_scope_value_presents_unique[OF t(1) other] by blast
qed

theorem bounded_scope_quoted_total:
  assumes "environment_formed F0" "(pu,pr)\<in>environment_positions F0"
    "(au,ar)\<in>environment_positions F0" "finite V"
  shows "\<exists>C. bounded_scope_quoted_at C [] F0 pu pr au ar V"
proof -
  obtain t where t: "bounded_scope_value_presents F0 pu pr au ar V t"
    using bounded_scope_value_presents_total[OF assms] by blast
  have "term_formed t" "self_contained_term t" using bounded_scope_value_presents_formed[OF t] by simp_all
  then have "complete_data_quoted_at (term_syntax t) [] t" by (rule complete_data_quotation_total)
  then show ?thesis using t unfolding bounded_scope_quoted_at_def by blast
qed

section \<open>The payload-bounded scope of a generation\<close>

definition generation_bounded_scope_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_bounded_scope_at E gu gr G F pu pr au ar \<longleftrightarrow>
    generation_at E gu gr G \<and>
    (\<exists>C cr F0 V R. generation_cause G=Whole_Artifact C \<and> bounded_scope_quoted_at C cr F0 pu pr au ar V \<and>
      generation_payload G=Whole_Artifact R \<and> (\<forall>u\<in>V. artifact_at F0 u empty_artifact) \<and>
      F=payload_fill F0 V R)"

lemma generation_bounded_scope_from_core:
  assumes "generation_at E gu gr G" "generation_cause G=Whole_Artifact C"
    "bounded_scope_quoted_at C cr F0 pu pr au ar V" "generation_payload G=Whole_Artifact R"
    "\<forall>u\<in>V. artifact_at F0 u empty_artifact"
  shows "generation_bounded_scope_at E gu gr G (payload_fill F0 V R) pu pr au ar"
  using assms unfolding generation_bounded_scope_at_def by blast

theorem generation_bounded_scope_unique:
  assumes first: "generation_bounded_scope_at E gu gr G F pu pr au ar"
    and second: "generation_bounded_scope_at E' hu hr H F' qu qr bu br"
    and cause: "generation_cause G=generation_cause H"
    and payload: "generation_payload G=generation_payload H"
  shows "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain C cr F0 V R where left: "generation_cause G=Whole_Artifact C"
      "bounded_scope_quoted_at C cr F0 pu pr au ar V" "generation_payload G=Whole_Artifact R"
      "F=payload_fill F0 V R"
    using first unfolding generation_bounded_scope_at_def by blast
  obtain D dr F1 W S where right: "generation_cause H=Whole_Artifact D"
      "bounded_scope_quoted_at D dr F1 qu qr bu br W" "generation_payload H=Whole_Artifact S"
      "F'=payload_fill F1 W S"
    using second unfolding generation_bounded_scope_at_def by blast
  have targets: "D=C" "S=R" using left(1,3) right(1,3) cause payload by auto
  have other: "bounded_scope_quoted_at C dr F1 qu qr bu br W" using right(2) targets(1) by simp
  have same: "cr=dr \<and> F0=F1 \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> V=W"
    by (rule bounded_scope_whole_unique[OF left(2) other])
  show ?thesis using same left(4) right(4) targets(2) by simp
qed

theorem generation_bounded_scope_formed:
  assumes scope: "generation_bounded_scope_at E gu gr G F pu pr au ar"
  shows "environment_formed F"
proof -
  obtain C cr F0 V R where gen: "generation_at E gu gr G"
    and parts: "bounded_scope_quoted_at C cr F0 pu pr au ar V" "generation_payload G=Whole_Artifact R"
      "\<forall>u\<in>V. artifact_at F0 u empty_artifact" "F=payload_fill F0 V R"
    using scope unfolding generation_bounded_scope_at_def by blast
  have f0: "environment_formed F0"
    using parts(1) bounded_scope_value_presents_formed unfolding bounded_scope_quoted_at_def by blast
  have "target_formed (generation_payload G)"
    using generation_formed_fields[OF generation_at_formed[OF gen]] by blast
  then have r: "exact_formed R" using parts(2) by simp
  show ?thesis using payload_fill_formed_exact[OF f0 parts(3) r] parts(4) by simp
qed

theorem generation_bounded_scope_outer_transfer:
  assumes source: "generation_bounded_scope_at E gu gr G F pu pr au ar"
    and target: "generation_at E' hu hr G"
  shows "generation_bounded_scope_at E' hu hr G F pu pr au ar"
  using source target unfolding generation_bounded_scope_at_def by blast

lemma generation_bounded_scope_determined:
  "scope_reading_determined generation_bounded_scope_at E gu gr G"
  unfolding scope_reading_determined_def by (blast dest: generation_bounded_scope_unique[OF _ _ refl refl])

lemma generation_bounded_scope_transfers:
  "scope_reading_transfers generation_bounded_scope_at generation_bounded_scope_at"
  unfolding scope_reading_transfers_def using generation_bounded_scope_outer_transfer by blast

section \<open>The certified causes at the bounded scope\<close>

text \<open>
  The bounded instances of the certified base and policy causes are the general forms at the
  bounded reading; their soundness, refusal, exact join, transfer and totality are the general ones'.
  The cause alone does not determine the bounded scope (the cause and the payload do), so no payload
  uniqueness from the cause is claimed here.
\<close>

definition bounded_recorded_base_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "bounded_recorded_base_cause_at E gu gr G R \<longleftrightarrow>
    scope_recorded_base_cause_at generation_bounded_scope_at E gu gr G R"

definition bounded_certified_base_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "bounded_certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    scope_certified_base_cause_at generation_bounded_scope_at E gu gr G H root R"

definition bounded_certified_policy_cause_at where
  "bounded_certified_policy_cause_at K pu pr d E gu gr G H root R \<longleftrightarrow>
    scope_certified_policy_cause_at generation_bounded_scope_at K pu pr d E gu gr G H root R"

theorem bounded_certified_base_cause_sound:
  assumes "bounded_certified_base_cause_at E gu gr G H root R"
  shows "bounded_recorded_base_cause_at E gu gr G R"
  unfolding bounded_recorded_base_cause_at_def
  by (rule scope_certified_base_cause_sound[OF assms[unfolded bounded_certified_base_cause_at_def]])

theorem bounded_certified_base_cause_exact_join:
  assumes scope: "generation_bounded_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "bounded_certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    bounded_recorded_base_cause_at E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
  unfolding bounded_certified_base_cause_at_def bounded_recorded_base_cause_at_def
  by (rule scope_certified_base_cause_exact_join[OF generation_bounded_scope_determined scope package app included])

theorem bounded_certified_base_outer_transfer:
  assumes "bounded_certified_base_cause_at E gu gr G H root R" "generation_at E' hu hr G"
  shows "bounded_certified_base_cause_at E' hu hr G H root R"
  unfolding bounded_certified_base_cause_at_def
  by (rule scope_certified_base_outer_transfer[OF generation_bounded_scope_transfers
    assms(1)[unfolded bounded_certified_base_cause_at_def] assms(2)])

theorem bounded_recorded_base_outer_transfer:
  assumes "bounded_recorded_base_cause_at E gu gr G R" "generation_at E' hu hr G"
  shows "bounded_recorded_base_cause_at E' hu hr G R"
  unfolding bounded_recorded_base_cause_at_def
  by (rule scope_recorded_base_outer_transfer[OF generation_bounded_scope_transfers
    assms(1)[unfolded bounded_recorded_base_cause_at_def] assms(2)])

theorem bounded_recorded_base_certification_total:
  assumes "bounded_recorded_base_cause_at E gu gr G R"
  shows "\<exists>H root. bounded_certified_base_cause_at E gu gr G H root R"
  unfolding bounded_certified_base_cause_at_def
  by (rule scope_recorded_base_certification_total[OF assms[unfolded bounded_recorded_base_cause_at_def]])

theorem bounded_certified_policy_cause_sound:
  assumes policy: "native_package_at K pu pr P"
    and certified: "bounded_certified_policy_cause_at K pu pr d E gu gr G H root R"
  shows "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
  by (rule scope_certified_policy_cause_sound[OF generation_bounded_scope_determined policy
    certified[unfolded bounded_certified_policy_cause_at_def]])

theorem bounded_certified_policy_cause_refuses_false_call:
  assumes "native_package_at K pu pr P" "(d,Target_Term (Whole_Artifact R))\<notin>positive_meaning P"
  shows "\<not>bounded_certified_policy_cause_at K pu pr d E gu gr G H root R"
  unfolding bounded_certified_policy_cause_at_def
  by (rule scope_certified_policy_cause_refuses_false_call[OF generation_bounded_scope_determined assms])

end
