theory Factor_Replay_Presentations
  imports Factor_Derivation_Presentations Factor_Replay_Admission Factor_Replay_Scopes
begin

section \<open>The replay context determines its exact assertion boundary\<close>

abbreviation replay_at_context :: "replay_context \<Rightarrow> native_claims \<Rightarrow> bool" where
  "replay_at_context z H \<equiv> native_replay_at (fst (fst z))
    (fst (fst (snd (fst z)))) (snd (fst (snd (fst z))))
    (fst (snd (snd (fst z)))) (snd (snd (snd (fst z)))) (snd z) H"

abbreviation replay_subject :: "(replay_context\<times>native_claims) \<Rightarrow> bool" where
  "replay_subject z \<equiv> replay_at_context (fst z) (snd z)"

abbreviation replay_scope_presents :: "(replay_context\<times>native_claims) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "replay_scope_presents z t \<equiv> replay_context_presents (fst z) t \<and> replay_subject z"

abbreviation replay_scope_quotation_presents ::
  "(replay_context\<times>native_claims) \<Rightarrow> (exact_artifact\<times>local_address) \<Rightarrow> bool" where
  "replay_scope_quotation_presents z p \<equiv>
    replay_quotation_presents (fst z) p \<and> replay_subject z"

lemma replay_context_bound:
  assumes replay: "replay_at_context z H"
  shows "replay_context_formed z"
  using native_replay_sites[OF replay]
  by (simp add: replay_context_formed_def judgment_context_formed_def)

lemma replay_assertions_finite:
  assumes replay: "replay_at_context z H"
  shows "finite H"
proof -
  obtain P d t G where derived: "schema_graph_derives (positioned_program P) G (snd z) d t H"
    using replay unfolding native_replay_at_def by blast
  show ?thesis by (rule schema_graph_exact_assertions(2)[OF derived])
qed

lemma replay_scope_presents_formed:
  assumes "replay_scope_presents z t"
  shows "term_formed t \<and> self_contained_term t"
  using assms replay_context_formed_value by blast

lemma replay_scope_admissible:
  "(\<exists>z H. replay_context_presents z t \<and> replay_at_context z H) \<longleftrightarrow>
    (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
proof
  assume "\<exists>z H. replay_context_presents z t \<and> replay_at_context z H"
  then obtain z H where parts: "replay_context_presents z t" "replay_at_context z H" by blast
  obtain hs where rows: "distinct hs" "set hs=H"
    using finite_distinct_list[OF replay_assertions_finite[OF parts(2)]] by blast
  have read: "(111,Pair_Term t (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system"
    by (rule replay_admission_complete[OF parts(1) rows(1)]) (use parts(2) rows(2) in simp)
  show "\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system" using read by blast
next
  assume "\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system"
  then obtain h where read: "(111,Pair_Term t h)\<in>positive_meaning replay_admission_system" by blast
  obtain E pu pr au ar root c hs where parts:
    "Pair_Term t h=Pair_Term c (positioned_call_rows_term hs)" "replay_value_presents E pu pr au ar root c"
    "distinct hs" "native_replay_at E pu pr au ar root (set hs)"
    using replay_admission_sound[OF read] by (elim exE conjE) (rule that; assumption)
  show "\<exists>z H. replay_context_presents z t \<and> replay_at_context z H"
    by (rule exI[of _ "((E,((pu,pr),(au,ar))),root)"], rule exI[of _ "set hs"])
      (use parts in simp)
qed

theorem replay_scope_presentation_class:
  "presentation_class replay_scope_presents replay_subject
    (\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
proof -
  have functional: "H=J" if "replay_at_context z H" "replay_at_context z J" for z H J
    by (rule native_replay_assumptions_unique[OF that])
  have result: "presentation_class replay_scope_presents
      (\<lambda>z. replay_context_formed (fst z) \<and> replay_subject z)
      (\<lambda>t. \<exists>z H. replay_context_presents z t \<and> replay_at_context z H)"
    by (rule presentation_class_determined[OF replay_context_presentation_class functional])
  have domain: "(\<lambda>z. replay_context_formed (fst z) \<and> replay_subject z)=replay_subject"
    by (rule ext) (use replay_context_bound in blast)
  have admission: "(\<lambda>t. \<exists>z H. replay_context_presents z t \<and> replay_at_context z H) =
      (\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
    by (rule ext) (rule replay_scope_admissible)
  show ?thesis using result by (simp only: domain admission)
qed

interpretation replay_scopes: presentation_class replay_scope_presents replay_subject
  "\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system"
  by (rule replay_scope_presentation_class)

lemma claim_collection_at_rows:
  "claim_collection_presents H (positioned_call_rows_term hs) \<longleftrightarrow> distinct hs \<and> set hs=H"
  by (simp only: claim_collection_fields positioned_call_rows_term_injective) blast

lemma claim_collection_empty [simp]:
  "claim_collection_presents H (Payload_Term []) \<longleftrightarrow> H={}"
  using claim_collection_at_rows[where H=H and hs="[]"] by (simp add: eq_commute)

theorem replay_admission_presented_relation:
  "(111,Pair_Term p h)\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    presented_relation replay_context_presents claim_collection_presents replay_at_context p h"
proof
  assume read: "(111,Pair_Term p h)\<in>positive_meaning replay_admission_system"
  obtain E pu pr au ar root c hs where parts:
    "Pair_Term p h=Pair_Term c (positioned_call_rows_term hs)" "replay_value_presents E pu pr au ar root c"
    "distinct hs" "native_replay_at E pu pr au ar root (set hs)"
    using replay_admission_sound[OF read] by (elim exE conjE) (rule that; assumption)
  have coordinates: "p=c" "h=positioned_call_rows_term hs" using parts(1) by auto
  have assertions: "claim_collection_presents (set hs) (positioned_call_rows_term hs)"
    by (simp only: claim_collection_at_rows; use parts(3) in simp)
  show "presented_relation replay_context_presents claim_collection_presents replay_at_context p h"
    unfolding presented_relation_def
    by (rule exI[of _ "((E,((pu,pr),(au,ar))),root)"], rule exI[of _ "set hs"])
      (use parts(2,4) assertions in \<open>simp only: fst_conv snd_conv coordinates\<close>)
next
  assume "presented_relation replay_context_presents claim_collection_presents replay_at_context p h"
  then obtain z H where parts: "replay_context_presents z p" "claim_collection_presents H h" "replay_at_context z H"
    by (auto simp: presented_relation_def)
  obtain hs where rows: "distinct hs" "set hs=H" "h=positioned_call_rows_term hs"
    using parts(2) by (simp only: claim_collection_fields) blast
  show "(111,Pair_Term p h)\<in>positive_meaning replay_admission_system"
    by (simp only: rows(3); rule replay_admission_complete[OF parts(1) rows(1)])
      (use parts(3) rows(2) in simp)
qed

theorem replay_joint_presentation_class:
  "presentation_class
    (\<lambda>z t. factor_pair_presents replay_context_presents claim_collection_presents z t \<and>
      (111,t)\<in>positive_meaning replay_admission_system)
    replay_subject (\<lambda>t. (111,t)\<in>positive_meaning replay_admission_system)"
proof -
  have result: "presentation_class
      (\<lambda>z t. factor_pair_presents replay_context_presents claim_collection_presents z t \<and>
        (111,t)\<in>positive_meaning replay_admission_system)
      (\<lambda>z. (replay_context_formed (fst z) \<and> finite (snd z)) \<and> replay_subject z)
      (\<lambda>t. (111,t)\<in>positive_meaning replay_admission_system)"
    by (rule factor_relation_presentation_class[OF replay_context_presentation_class
      claim_collection_presentation_class replay_admission_presented_relation])
      (auto simp: replay_admission_exact)
  have domain: "(\<lambda>z. (replay_context_formed (fst z) \<and> finite (snd z)) \<and> replay_subject z)=replay_subject"
    by (rule ext) (use replay_context_bound replay_assertions_finite in blast)
  show ?thesis using result by (simp only: domain)
qed

abbreviation closed_replay_subject :: "(replay_context\<times>native_claims) \<Rightarrow> bool" where
  "closed_replay_subject z \<equiv> replay_subject z \<and> snd z={}"

abbreviation closed_replay_scope_presents :: "(replay_context\<times>native_claims) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "closed_replay_scope_presents z t \<equiv> replay_scope_presents z t \<and> snd z={}"

lemma closed_replay_scope_admissible:
  "(\<exists>z. closed_replay_scope_presents z t) \<longleftrightarrow>
    (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system"
  by (simp only: replay_admission_presented_relation presented_relation_def claim_collection_empty)
    (auto; metis fst_conv snd_conv)

theorem closed_replay_scope_presentation_class:
  "presentation_class closed_replay_scope_presents closed_replay_subject
    (\<lambda>t. (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system)"
proof -
  have constrained: "presentation_class (\<lambda>z t. closed_replay_subject z \<and> replay_scope_presents z t)
      closed_replay_subject (\<lambda>t. \<exists>z. closed_replay_subject z \<and> replay_scope_presents z t)"
    by (rule presentation_class_subdomain[OF replay_scope_presentation_class]) blast
  have reading: "(\<lambda>z t. closed_replay_subject z \<and> replay_scope_presents z t)=closed_replay_scope_presents"
    by (intro ext) blast
  have admission: "(\<lambda>t. \<exists>z. closed_replay_subject z \<and> replay_scope_presents z t) =
      (\<lambda>t. (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system)"
    by (rule ext) (simp only: closed_replay_scope_admissible[symmetric]; blast)
  show ?thesis using constrained by (simp only: reading admission)
qed

interpretation closed_replay_scopes: presentation_class closed_replay_scope_presents closed_replay_subject
  "\<lambda>t. (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system"
  by (rule closed_replay_scope_presentation_class)

type_synonym replay_details =
  "local_address option native_system \<times> ((local_address option definition_site \<times> factor_term) \<times>
    ((local_address set \<times> local_address set) \<times> (local_address option native_derivation_graph \<times> native_claims)))"

definition replay_record_reading ::
  "(replay_context\<times>native_claims) \<Rightarrow> replay_details \<Rightarrow> bool" where
  "replay_record_reading z b \<longleftrightarrow>
    (case (z,b) of ((((E,(p,a)),root),H),(P,(q,((I,K),(G,J))))) \<Rightarrow>
      native_package_at E (fst p) (snd p) P \<and>
      native_application_at E (fst a) (snd a) (fst q) (snd q) I K \<and>
      native_schema_graph_at E root G \<and>
      schema_graph_reading (positioned_program P) G root (fst q) (snd q) J \<and>
      H=schema_graph_assumptions G J \<and>
      environment_closed E {fst p,fst a,fst root}
        (native_replay_demands E (fst p) (snd p) (fst a) (snd a) G))"

lemma replay_record_reading_fields:
  "replay_record_reading (((E,(p,a)),root),H) (P,(q,((I,K),(G,J)))) \<longleftrightarrow>
    native_package_at E (fst p) (snd p) P \<and>
    native_application_at E (fst a) (snd a) (fst q) (snd q) I K \<and>
    native_schema_graph_at E root G \<and>
    schema_graph_reading (positioned_program P) G root (fst q) (snd q) J \<and>
    H=schema_graph_assumptions G J \<and>
    environment_closed E {fst p,fst a,fst root}
      (native_replay_demands E (fst p) (snd p) (fst a) (snd a) G)"
  by (simp only: replay_record_reading_def case_prod_conv)

lemma replay_subject_cases:
  fixes z :: "replay_context\<times>native_claims"
  obtains E p a root H where "z=(((E,(p,a)),root),H)"
  by (rule that[of "fst (fst (fst z))" "fst (snd (fst (fst z)))"
    "snd (snd (fst (fst z)))" "snd (fst z)" "snd z"]) simp

lemma replay_reading_valid:
  assumes "replay_record_reading z b"
  shows "replay_subject z"
  using assms by (auto simp: replay_record_reading_def native_replay_at_def
    schema_graph_derives_def split: prod.splits; blast)

lemma replay_reading_total:
  assumes subject: "replay_subject z"
  shows "\<exists>b. replay_record_reading z b"
proof -
  obtain E p a root H where shape: "z=(((E,(p,a)),root),H)"
    by (rule replay_subject_cases[of z]) (rule that; assumption)
  have replay: "native_replay_at E (fst p) (snd p) (fst a) (snd a) root H"
    using subject by (simp only: shape fst_conv snd_conv)
  obtain P d t I K G where parts: "native_package_at E (fst p) (snd p) P"
    "native_application_at E (fst a) (snd a) d t I K" "native_schema_graph_at E root G"
    "schema_graph_derives (positioned_program P) G root d t H"
    "environment_closed E {fst p,fst a,fst root} (native_replay_demands E (fst p) (snd p) (fst a) (snd a) G)"
    using replay unfolding native_replay_at_def by (elim exE conjE) (rule that; assumption)
  obtain J where read: "schema_graph_reading (positioned_program P) G root d t J"
    and boundary: "H=schema_graph_assumptions G J"
    using parts(4) by (auto simp: schema_graph_derives_def)
  show ?thesis by (rule exI[of _ "(P,((d,t),((I,K),(G,J))))"])
    (use parts(1-3,5) read boundary in \<open>simp only: shape replay_record_reading_fields fst_conv snd_conv\<close>)
qed

lemma replay_details_cases:
  fixes b :: replay_details
  obtains P q I K G J where "b=(P,(q,((I,K),(G,J))))"
  by (rule that[of "fst b" "fst (snd b)" "fst (fst (snd (snd b)))" "snd (fst (snd (snd b)))"
    "fst (snd (snd (snd b)))" "snd (snd (snd (snd b)))"]) simp

lemma replay_reading_unique:
  assumes first: "replay_record_reading z b" and second: "replay_record_reading z c"
  shows "b=c"
proof -
  obtain E p a root H where shape: "z=(((E,(p,a)),root),H)"
    by (rule replay_subject_cases[of z]) (rule that; assumption)
  obtain P q I K G J where b: "b=(P,(q,((I,K),(G,J))))"
    by (rule replay_details_cases[of b]) (rule that; assumption)
  obtain Q r L M F U where c: "c=(Q,(r,((L,M),(F,U))))"
    by (rule replay_details_cases[of c]) (rule that; assumption)
  have left: "native_package_at E (fst p) (snd p) P"
    "native_application_at E (fst a) (snd a) (fst q) (snd q) I K" "native_schema_graph_at E root G"
    "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    using first by (auto simp: shape b replay_record_reading_fields)
  have right: "native_package_at E (fst p) (snd p) Q"
    "native_application_at E (fst a) (snd a) (fst r) (snd r) L M" "native_schema_graph_at E root F"
    "schema_graph_reading (positioned_program Q) F root (fst r) (snd r) U"
    using second by (auto simp: shape c replay_record_reading_fields)
  have programs: "P=Q" by (rule native_package_unique[OF left(1) right(1)])
  have calls: "fst q=fst r \<and> snd q=snd r \<and> I=L \<and> K=M"
    by (rule native_application_unique[OF left(2) right(2)])
  have graphs: "G=F" by (rule native_schema_graph_unique[OF left(3) right(3)])
  have other: "schema_graph_reading (positioned_program P) G root (fst q) (snd q) U"
    using right(4) programs calls graphs by simp
  have claims: "J=U" by (rule schema_graph_reading_unique[OF left(4) other])
  show ?thesis using programs calls graphs claims b c by (simp add: prod_eq_iff)
qed

abbreviation replay_with_reading_presents ::
  "((replay_context\<times>native_claims)\<times>replay_details) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "replay_with_reading_presents z t \<equiv>
    replay_scope_presents (fst z) t \<and> replay_record_reading (fst z) (snd z)"

theorem replay_record_presentation_class:
  "presentation_class replay_with_reading_presents
    (\<lambda>z. replay_record_reading (fst z) (snd z))
    (\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
proof -
  have result: "presentation_class replay_with_reading_presents
      (\<lambda>z. replay_subject (fst z) \<and> replay_record_reading (fst z) (snd z))
      (\<lambda>t. \<exists>z b. replay_scope_presents z t \<and> replay_record_reading z b)"
    by (rule presentation_class_determined[OF replay_scope_presentation_class replay_reading_unique])
  have domain: "(\<lambda>z. replay_subject (fst z) \<and> replay_record_reading (fst z) (snd z)) =
      (\<lambda>z. replay_record_reading (fst z) (snd z))"
    by (rule ext) (use replay_reading_valid in blast)
  have admission: "(\<lambda>t. \<exists>z b. replay_scope_presents z t \<and> replay_record_reading z b) =
      (\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
    by (rule ext) (simp only: replay_scopes.admissible_iff;
      use replay_scopes.subject_boundary replay_reading_total in blast)
  show ?thesis using result by (simp only: domain admission)
qed

interpretation replay_readings: presentation_class replay_with_reading_presents
  "\<lambda>z. replay_record_reading (fst z) (snd z)"
  "\<lambda>t. \<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system"
  by (rule replay_record_presentation_class)

theorem replay_scope_quotation_presentation_class:
  "presentation_class replay_scope_quotation_presents replay_subject
    (\<lambda>p. \<exists>t. (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system) \<and>
      complete_data_quoted_at (fst p) (snd p) t)"
proof -
  have composed: "presentation_class (composed_presentation replay_scope_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)) replay_subject
      (\<lambda>p. \<exists>t. (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system) \<and>
        complete_data_quoted_at (fst p) (snd p) t)"
    by (rule complete_quotation_presentation_class[OF replay_scope_presentation_class])
      (use replay_scopes.admitted replay_scope_presents_formed in blast)
  have reading: "composed_presentation replay_scope_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)=replay_scope_quotation_presents"
    by (intro ext) (auto simp: composed_presentation_def replay_value_quoted_at_def)
  show ?thesis using composed by (simp only: reading)
qed

abbreviation replay_quoted_body_presents ::
  "(replay_context\<times>native_claims) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "replay_quoted_body_presents \<equiv> composed_presentation replay_scope_presents quoted_body_presents"

abbreviation closed_replay_quoted_body_presents ::
  "(replay_context\<times>native_claims) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "closed_replay_quoted_body_presents \<equiv> composed_presentation closed_replay_scope_presents quoted_body_presents"

theorem replay_quoted_body_presentation_class:
  "presentation_class replay_quoted_body_presents replay_subject
    (\<lambda>v. \<exists>t. (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system) \<and>
      quoted_body_presents t v)"
  by (rule quoted_body_presentation_class[OF replay_scope_presentation_class])
    (use replay_scopes.admitted replay_scope_presents_formed in blast)

theorem closed_replay_quoted_body_presentation_class:
  "presentation_class closed_replay_quoted_body_presents closed_replay_subject
    (\<lambda>v. \<exists>t. (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system \<and>
      quoted_body_presents t v)"
  by (rule quoted_body_presentation_class[OF closed_replay_scope_presentation_class])
    (use closed_replay_scopes.admitted replay_scope_presents_formed in blast)

theorem replay_presented_reading:
  assumes presented: "replay_with_reading_presents ((((E,(p,a)),root),H),(P,(q,((I,K),(G,J))))) v"
  shows "native_package_at E (fst p) (snd p) P"
    and "native_application_at E (fst a) (snd a) (fst q) (snd q) I K"
    and "native_schema_graph_at E root G"
    and "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    and "H=schema_graph_assumptions G J"
    and "environment_closed E {fst p,fst a,fst root}
      (native_replay_demands E (fst p) (snd p) (fst a) (snd a) G)"
  using presented by (auto simp: fst_conv snd_conv replay_record_reading_fields)

theorem replay_presented_retention:
  assumes presented: "replay_with_reading_presents ((((E,(p,a)),root),H),(P,(q,((I,K),(G,J))))) v"
  shows "native_replay_environment E (fst p) (snd p) (fst a) (snd a) G=E"
proof -
  have package: "native_package_at E (fst p) (snd p) P"
    and app: "native_application_at E (fst a) (snd a) (fst q) (snd q) I K"
    and graph: "native_schema_graph_at E root G"
    and closed: "environment_closed E {fst p,fst a,fst root}
      (native_replay_demands E (fst p) (snd p) (fst a) (snd a) G)"
    using replay_presented_reading[OF presented] by blast+
  have coverage: "rel_dom (environment_bindings E)\<subseteq>native_replay_demands E (fst p) (snd p) (fst a) (snd a) G \<and>
    environment_uses E\<subseteq>native_replay_sources E (fst p) (snd p) (fst a) G\<union>rel_ran (environment_bindings E)"
    using closed by (simp only: native_replay_closed_coverage[OF package app graph])
  show ?thesis using coverage by (simp only: native_replay_environment_def read_environment_fixed_coverage)
qed

theorem replay_presented_conditional_sound:
  assumes presented: "replay_with_reading_presents ((((E,(p,a)),root),H),(P,(q,((I,K),(G,J))))) v"
    and support: "\<forall>n e x. (n,e,x)\<in>H \<longrightarrow> (e,x)\<in>positive_meaning P"
  shows "native_positive_holds E (fst p) (snd p) (fst a) (snd a)"
proof -
  have replay: "native_replay_at E (fst p) (snd p) (fst a) (snd a) root H"
    using presented by simp
  show ?thesis by (rule native_replay_conditional_sound[
    OF replay_presented_reading(1-3)[OF presented] replay support])
qed

corollary closed_replay_presented_sound:
  assumes "closed_replay_scope_presents (((E,(p,a)),root),{}) v"
  shows "native_positive_holds E (fst p) (snd p) (fst a) (snd a)"
  by (rule native_replay_closed_sound[where root=root]) (use assms in auto)

corollary replay_admission_at_presentations:
  assumes context_value: "replay_context_presents z p" and assertions: "claim_collection_presents H h"
  shows "(111,Pair_Term p h)\<in>positive_meaning replay_admission_system \<longleftrightarrow> replay_at_context z H"
  by (simp only: replay_admission_presented_relation)
    (rule presented_relation_at[OF replay_context_presentation_class claim_collection_presentation_class
      context_value assertions])

theorem native_replay_presentation_total:
  assumes replay: "native_replay_at E pu pr au ar root H"
  shows "\<exists>v h b. replay_with_reading_presents
      ((((E,((pu,pr),(au,ar))),root),H),b) v \<and>
    claim_collection_presents H h \<and> (111,Pair_Term v h)\<in>positive_meaning replay_admission_system \<and>
    term_formed v \<and> self_contained_term v"
proof -
  let ?z="(((E,((pu,pr),(au,ar))),root),H)"
  have subject: "replay_subject ?z" using replay by simp
  obtain b where reading: "replay_record_reading ?z b" using replay_reading_total[OF subject] by blast
  obtain v where presented: "replay_with_reading_presents (?z,b) v"
    using replay_readings.total[of "(?z,b)"] reading by (simp only: fst_conv snd_conv; blast)
  have context_value: "replay_context_presents (fst ?z) v" using presented by simp
  have formed: "term_formed v \<and> self_contained_term v"
    by (rule replay_context_formed_value[OF context_value])
  have finite: "finite H" by (rule replay_assertions_finite[where z="fst ?z"]) (use subject in simp)
  obtain h where assertions: "claim_collection_presents H h"
    using claim_collections.total[OF finite] by blast
  have admitted: "(111,Pair_Term v h)\<in>positive_meaning replay_admission_system"
    using subject by (simp only: replay_admission_at_presentations[OF context_value assertions] fst_conv snd_conv)
  show ?thesis by (rule exI[of _ v], rule exI[of _ h], rule exI[of _ b])
    (use presented assertions admitted formed in simp)
qed

text \<open>
  The replay class derives its assertion boundary from one complete context.
  A separate joint class presents the context and an explicit assertion report,
  with compatibility supplied by the native replay relation. Closed replay
  checks that exact boundary against the empty collection.

  Program, application, syntax boundaries, proof graph, and complete reading
  are recovered components of the same context. The retention equation uses
  all three actual readers and makes the represented environment a fixed point
  of their restriction. Assertions remain conditional.

  Complete quotation and quoted-body records compose through the actual
  context term. A source artifact determines its stored body; a different
  presentation of the same replay subject must satisfy the corresponding
  quotation relation. Native readers for these classes are supplied next.
\<close>

end
