theory Factor_Generation_Requests
  imports Factor_Generation_Read_Sites Factor_Generation_Citation_Roots
begin

section \<open>Requests combine an actual read site with its citation roots\<close>

abbreviation generation_request_observed where
  "generation_request_observed e u r v x \<equiv> \<exists>a material.
    (169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system \<and>
    (37,artifact_lookup_argument e v material)\<in>positive_meaning artifact_lookup_system \<and>
    (170,rooted_rows_argument material a x)\<in>positive_meaning generation_retention_system"

lemma generation_request_valuation:
  "(171,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6}. term_formed (h i)) \<and>
      t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)) \<and>
      (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 5)))\<in>positive_meaning generation_retention_system \<and>
      (37,artifact_lookup_argument (h 0) (h 3) (h 6))\<in>positive_meaning artifact_lookup_system \<and>
      (170,rooted_rows_argument (h 6) (h 5) (h 4))\<in>positive_meaning generation_retention_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_request_schema_def schema_variables_def generation_retention_call generation_retention_components)

lemma generation_request_fields:
  "(171,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>e u r v x. t=Pair_Term (generation_source_term e u r) (Pair_Term v x) \<and>
      generation_request_observed e u r v x)"
proof
  assume "(171,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>e u r v x. t=Pair_Term (generation_source_term e u r) (Pair_Term v x) \<and>
      generation_request_observed e u r v x" by (simp only: generation_request_valuation) blast
next
  assume "\<exists>e u r v x. t=Pair_Term (generation_source_term e u r) (Pair_Term v x) \<and>
      generation_request_observed e u r v x"
  then obtain e u r v x a material where shape: "t=Pair_Term (generation_source_term e u r) (Pair_Term v x)"
    and calls: "(169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system"
      "(37,artifact_lookup_argument e v material)\<in>positive_meaning artifact_lookup_system"
      "(170,rooted_rows_argument material a x)\<in>positive_meaning generation_retention_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed x" "term_formed a" "term_formed material"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r
    else if i=3 then v else if i=4 then x else if i=5 then a else material"
  show "(171,t)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_request_valuation, rule exI[of _ ?h]) (use shape calls formed in auto)
qed

corollary generation_request_at_source:
  assumes source: "environment_value_presents E e"
  shows "(171,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>G v x. q=site_data_term v x \<and> generation_at E u r G \<and> (v,x)\<in>generation_requests E {(u,r)})"
proof
  assume holds: "(171,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system"
  obtain v x a material where shape: "q=Pair_Term v x"
    and calls: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (Pair_Term v a))
      \<in>positive_meaning generation_retention_system"
      "(37,artifact_lookup_argument e v material)\<in>positive_meaning artifact_lookup_system"
      "(170,rooted_rows_argument material a x)\<in>positive_meaning generation_retention_system"
    using holds by (auto simp: generation_request_fields)
  obtain G w b where native: "generation_at E u r G" and coordinate: "v=use_data_term w" "a=Payload_Term b"
    and site: "(w,b)\<in>generation_read_sites E {(u,r)}"
    using calls(1) by (auto simp: generation_read_site_at_source[OF source] site_data_term_def)
  obtain R where material: "artifact_at E w R" "artifact_value_presents R material"
    using calls(2) by (auto simp: coordinate(1) artifact_lookup_at_source[OF source]
      inj_eq[OF use_data_term_injective])
  obtain k where endpoint: "x=Payload_Term k" "k\<in>generation_citation_roots R b"
    using calls(3) by (simp only: coordinate(2) generation_citation_root_at_source[OF material(2)]) blast
  have request: "(w,k)\<in>generation_requests E {(u,r)}"
    using site material(1) endpoint(2) by (auto simp: generation_requests_def)
  show "\<exists>G v x. q=site_data_term v x \<and> generation_at E u r G \<and> (v,x)\<in>generation_requests E {(u,r)}"
    using shape coordinate(1) endpoint(1) native request by (auto simp: site_data_term_def)
next
  assume "\<exists>G v x. q=site_data_term v x \<and> generation_at E u r G \<and> (v,x)\<in>generation_requests E {(u,r)}"
  then obtain G v x a R where shape: "q=site_data_term v x" and native: "generation_at E u r G"
    and site: "(v,a)\<in>generation_read_sites E {(u,r)}" and material: "artifact_at E v R"
    and endpoint: "x\<in>generation_citation_roots R a" by (auto simp: generation_requests_def)
  have formed: "exact_formed R" using generation_at_environment_formed[OF native] material
    by (auto simp: environment_formed_def)
  obtain m where presented: "artifact_value_presents R m" using artifact_value_presents_total[OF formed] by blast
  have reached: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v a))
      \<in>positive_meaning generation_retention_system" by (rule generation_read_site_complete[OF source native site])
  have lookup: "(37,artifact_lookup_argument e (use_data_term v) m)\<in>positive_meaning artifact_lookup_system"
    using source material presented by (auto simp: artifact_lookup_exact)
  have citation: "(170,rooted_rows_argument m (Payload_Term a) (Payload_Term x))\<in>positive_meaning generation_retention_system"
    by (rule generation_citation_root_complete[OF presented endpoint])
  show "(171,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)\<in>positive_meaning generation_retention_system"
    using reached lookup citation by (auto simp: generation_request_fields shape site_data_term_def)
qed

abbreviation generation_request_result :: "factor_term \<Rightarrow> bool" where
  "generation_request_result t \<equiv> \<exists>E e u r G v x.
    t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v x) \<and>
    environment_value_presents E e \<and> generation_at E u r G \<and> (v,x)\<in>generation_requests E {(u,r)}"

theorem generation_request_exact:
  "(171,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_request_result t"
proof
  assume holds: "(171,t)\<in>positive_meaning generation_retention_system"
  obtain E e u r G q where source: "environment_value_presents E e" and native: "generation_at E u r G"
    and shape: "t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q"
    using holds by (auto simp: generation_request_fields generation_read_site_exact site_data_term_def)
  show "generation_request_result t" using holds source
    by (simp only: shape generation_request_at_source[OF source]) blast
next
  assume "generation_request_result t"
  then show "(171,t)\<in>positive_meaning generation_retention_system"
    using generation_request_at_source by blast
qed

section \<open>Each demanded binding belongs to an actual requested citation\<close>

abbreviation generation_slot_observed where
  "generation_slot_observed e u r v k \<equiv> \<exists>x slots address interior.
    (171,Pair_Term (generation_source_term e u r) (Pair_Term v x))\<in>positive_meaning generation_retention_system \<and>
    (42,citation_reading_argument e v x (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system \<and>
    selected_data_member k slots"

lemma generation_demanded_slot_valuation:
  "(172,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9}. term_formed (h i)) \<and>
      t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)) \<and>
      (171,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 5)))\<in>positive_meaning generation_retention_system \<and>
      (42,citation_reading_argument (h 0) (h 3) (h 5) (Pair_Term (h 6) (h 7)) (h 8))\<in>positive_meaning citation_reading_system \<and>
      (5,Pair_Term (h 4) (Pair_Term (h 6) (h 9)))\<in>positive_meaning bag_comparison_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_demanded_slot_schema_def schema_variables_def generation_retention_call generation_retention_components)

lemma generation_demanded_slot_fields:
  "(172,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>e u r v k. t=Pair_Term (generation_source_term e u r) (Pair_Term v k) \<and> generation_slot_observed e u r v k)"
proof
  assume "(172,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>e u r v k. t=Pair_Term (generation_source_term e u r) (Pair_Term v k) \<and> generation_slot_observed e u r v k"
    by (simp only: generation_demanded_slot_valuation) blast
next
  assume "\<exists>e u r v k. t=Pair_Term (generation_source_term e u r) (Pair_Term v k) \<and> generation_slot_observed e u r v k"
  then obtain e u r v k x slots address interior rest where shape: "t=Pair_Term (generation_source_term e u r) (Pair_Term v k)"
    and calls: "(171,Pair_Term (generation_source_term e u r) (Pair_Term v x))\<in>positive_meaning generation_retention_system"
      "(42,citation_reading_argument e v x (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system"
      "(5,Pair_Term k (Pair_Term slots rest))\<in>positive_meaning bag_comparison_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed k" "term_formed x"
    "term_formed slots" "term_formed address" "term_formed interior" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else if i=4 then k
    else if i=5 then x else if i=6 then slots else if i=7 then address else if i=8 then interior else rest"
  show "(172,t)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_demanded_slot_valuation, rule exI[of _ ?h]) (use shape calls formed in auto)
qed

corollary generation_demanded_slot_at_source:
  assumes source: "environment_value_presents E e"
  shows "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>G v k. q=site_data_term v k \<and> generation_at E u r G \<and>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)}))"
proof
  assume holds: "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system"
  obtain v k x slots address interior where shape: "q=Pair_Term v k"
    and calls: "(171,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (Pair_Term v x))
        \<in>positive_meaning generation_retention_system"
      "(42,citation_reading_argument e v x (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system"
      "selected_data_member k slots" using holds by (auto simp: generation_demanded_slot_fields; blast)
  obtain G w a where native: "generation_at E u r G" and coordinate: "v=use_data_term w" "x=Payload_Term a"
    and request: "(w,a)\<in>generation_requests E {(u,r)}"
    using calls(1) by (auto simp: generation_request_at_source[OF source] site_data_term_def)
  obtain key R cite I where citation: "k=Payload_Term key" "artifact_at E w R" "citation_at R a cite I" "key\<in>citation_slots cite"
    using citation_slot_observation[OF source, where u=w and r=a and x=k] calls(2,3) coordinate by blast
  have demand: "(w,key)\<in>requested_slots E (generation_requests E {(u,r)})"
    using request citation(2-4) by (auto simp: requested_slots_def)
  show "\<exists>G v k. q=site_data_term v k \<and> generation_at E u r G \<and>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)})"
    using shape coordinate(1) citation(1) native demand by (auto simp: site_data_term_def)
next
  assume "\<exists>G v k. q=site_data_term v k \<and> generation_at E u r G \<and>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)})"
  then obtain G v k a R cite I where shape: "q=site_data_term v k" and native: "generation_at E u r G"
    and request: "(v,a)\<in>generation_requests E {(u,r)}"
    and citation: "artifact_at E v R" "citation_at R a cite I" "k\<in>citation_slots cite"
    by (auto simp: requested_slots_def)
  have requested: "(171,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v a))
      \<in>positive_meaning generation_retention_system"
    using native request by (simp only: generation_request_at_source[OF source]) blast
  obtain slots address interior where read:
    "(42,citation_reading_argument e (use_data_term v) (Payload_Term a) (Pair_Term slots address) interior)
      \<in>positive_meaning citation_reading_system" "selected_data_member (Payload_Term k) slots"
    using citation_slot_observation[OF source, where u=v and r=a and x="Payload_Term k"] citation by blast
  show "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)\<in>positive_meaning generation_retention_system"
    using requested read by (auto simp: generation_demanded_slot_fields shape site_data_term_def; blast)
qed

abbreviation generation_demanded_slot_result :: "factor_term \<Rightarrow> bool" where
  "generation_demanded_slot_result t \<equiv> \<exists>E e u r G v k.
    t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v k) \<and>
    environment_value_presents E e \<and> generation_at E u r G \<and>
    (v,k)\<in>requested_slots E (generation_requests E {(u,r)})"

theorem generation_demanded_slot_exact:
  "(172,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_demanded_slot_result t"
proof
  assume holds: "(172,t)\<in>positive_meaning generation_retention_system"
  obtain E e u r G q where source: "environment_value_presents E e" and native: "generation_at E u r G"
    and shape: "t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q"
    using holds by (auto simp: generation_demanded_slot_fields generation_request_exact site_data_term_def)
  show "generation_demanded_slot_result t" using holds source
    by (simp only: shape generation_demanded_slot_at_source[OF source]) blast
next
  assume "generation_demanded_slot_result t"
  then show "(172,t)\<in>positive_meaning generation_retention_system" using generation_demanded_slot_at_source by blast
qed

section \<open>Required uses are read sources and targets of demanded slots\<close>

abbreviation generation_use_observed where
  "generation_use_observed e u r v \<equiv>
    (\<exists>a. (169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system) \<or>
    (\<exists>w k. (172,Pair_Term (generation_source_term e u r) (Pair_Term w k))\<in>positive_meaning generation_retention_system \<and>
      (38,binding_lookup_argument e w k v)\<in>positive_meaning binding_lookup_system)"

lemma generation_required_use_valuation:
  "(173,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3) \<and>
      (((\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
        (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)))\<in>positive_meaning generation_retention_system) \<or>
       ((\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
        (172,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 4) (h 5)))\<in>positive_meaning generation_retention_system \<and>
        (38,binding_lookup_argument (h 0) (h 4) (h 5) (h 3))\<in>positive_meaning binding_lookup_system)))"
proof -
  have ordinary: "schema_material_premises S={}"
    if "((173,c),S)\<in>system_clauses generation_retention_system" for c S
    using that by (auto simp: generation_required_source_schema_def generation_required_target_schema_def)
  have valuation: "(173,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>c S h. ((173,c),S)\<in>system_clauses generation_retention_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      t=evaluate_pattern h (schema_conclusion S) \<and>
      schema_call_formed generation_retention_system 173 t \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning generation_retention_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  show ?thesis
  proof
    assume "(173,t)\<in>positive_meaning generation_retention_system"
    then show "\<exists>h::nat\<Rightarrow>factor_term. t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3) \<and>
      (((\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
        (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)))\<in>positive_meaning generation_retention_system) \<or>
       ((\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
        (172,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 4) (h 5)))\<in>positive_meaning generation_retention_system \<and>
        (38,binding_lookup_argument (h 0) (h 4) (h 5) (h 3))\<in>positive_meaning binding_lookup_system))"
      by (simp only: valuation)
        (auto simp: generation_required_source_schema_def generation_required_target_schema_def schema_variables_def
          generation_retention_call generation_retention_components; blast)
  next
    assume "\<exists>h::nat\<Rightarrow>factor_term. t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3) \<and>
      (((\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
        (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)))\<in>positive_meaning generation_retention_system) \<or>
       ((\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
        (172,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 4) (h 5)))\<in>positive_meaning generation_retention_system \<and>
        (38,binding_lookup_argument (h 0) (h 4) (h 5) (h 3))\<in>positive_meaning binding_lookup_system))"
    then obtain h :: "nat\<Rightarrow>factor_term" where shape: "t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3)"
      and alternatives:
        "((\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
          (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)))
            \<in>positive_meaning generation_retention_system) \<or>
         ((\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
          (172,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 4) (h 5)))
            \<in>positive_meaning generation_retention_system \<and>
          (38,binding_lookup_argument (h 0) (h 4) (h 5) (h 3))\<in>positive_meaning binding_lookup_system)"
      by blast
    from alternatives show "(173,t)\<in>positive_meaning generation_retention_system"
    proof
      assume first: "(\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
        (169,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4)))
          \<in>positive_meaning generation_retention_system"
      have admitted: "(173,evaluate_pattern h (schema_conclusion generation_required_source_schema))
          \<in>positive_meaning generation_retention_system"
        by (rule generation_retention_rule[where c=0])
          (use first in \<open>auto simp: generation_retention_group_clauses_def generation_required_source_schema_def
            schema_variables_def\<close>)
      show "(173,t)\<in>positive_meaning generation_retention_system"
        using admitted by (simp add: shape generation_required_source_schema_def)
    next
      assume second: "(\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
        (172,Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 4) (h 5)))
          \<in>positive_meaning generation_retention_system \<and>
        (38,binding_lookup_argument (h 0) (h 4) (h 5) (h 3))\<in>positive_meaning binding_lookup_system"
      have admitted: "(173,evaluate_pattern h (schema_conclusion generation_required_target_schema))
          \<in>positive_meaning generation_retention_system"
        by (rule generation_retention_rule[where c=1])
          (use second in \<open>auto simp: generation_retention_group_clauses_def generation_required_target_schema_def
            schema_variables_def generation_retention_components\<close>)
      show "(173,t)\<in>positive_meaning generation_retention_system"
        using admitted by (simp add: shape generation_required_target_schema_def)
    qed
  qed
qed

lemma generation_required_use_fields:
  "(173,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>e u r v. t=Pair_Term (generation_source_term e u r) v \<and> generation_use_observed e u r v)"
proof
  assume "(173,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>e u r v. t=Pair_Term (generation_source_term e u r) v \<and> generation_use_observed e u r v"
    by (simp only: generation_required_use_valuation) blast
next
  assume "\<exists>e u r v. t=Pair_Term (generation_source_term e u r) v \<and> generation_use_observed e u r v"
  then obtain e u r v where shape: "t=Pair_Term (generation_source_term e u r) v"
    and observed: "generation_use_observed e u r v" by blast
  show "(173,t)\<in>positive_meaning generation_retention_system"
  proof (cases "\<exists>a. (169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system")
    case True
    then obtain a where call: "(169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system" by blast
    have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed a"
      using schema_call_formed_target[OF positive_meaning_formed[OF call]] by auto
    let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else a"
    show ?thesis by (simp only: generation_required_use_valuation, rule exI[of _ ?h]) (use shape call formed in auto)
  next
    case False
    obtain w k where calls: "(172,Pair_Term (generation_source_term e u r) (Pair_Term w k))\<in>positive_meaning generation_retention_system"
      "(38,binding_lookup_argument e w k v)\<in>positive_meaning binding_lookup_system" using observed False by blast
    have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed v" "term_formed w" "term_formed k"
      using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]] by auto
    let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v else if i=4 then w else k"
    show ?thesis by (simp only: generation_required_use_valuation, rule exI[of _ ?h]) (use shape calls formed in auto)
  qed
qed

corollary generation_required_use_at_source:
  assumes source: "environment_value_presents E e"
  shows "(173,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>G v. q=use_data_term v \<and> generation_at E u r G \<and>
      v\<in>requested_uses E (generation_requests E {(u,r)}))"
proof
  assume holds: "(173,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system"
  have observed: "generation_use_observed e (use_data_term u) (Payload_Term r) q"
    using holds by (auto simp: generation_required_use_fields)
  show "\<exists>G v. q=use_data_term v \<and> generation_at E u r G \<and> v\<in>requested_uses E (generation_requests E {(u,r)})"
  proof (cases "\<exists>a. (169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (Pair_Term q a))
      \<in>positive_meaning generation_retention_system")
    case True
    then obtain G v a where coordinate: "q=use_data_term v" and native: "generation_at E u r G"
      and site: "(v,a)\<in>generation_read_sites E {(u,r)}"
      by (auto simp: generation_read_site_at_source[OF source] site_data_term_def)
    have needed: "v\<in>fst ` generation_requests E {(u,r)}"
      using site by (simp only: generation_request_source_uses[OF native]) force
    show ?thesis using coordinate native needed by (auto simp: requested_uses_def)
  next
    case False
    obtain w k where calls:
      "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (Pair_Term w k))\<in>positive_meaning generation_retention_system"
      "(38,binding_lookup_argument e w k q)\<in>positive_meaning binding_lookup_system" using observed False by blast
    obtain G v key where native: "generation_at E u r G" and coordinate: "w=use_data_term v" "k=Payload_Term key"
      and demand: "(v,key)\<in>requested_slots E (generation_requests E {(u,r)})"
      using calls(1) by (auto simp: generation_demanded_slot_at_source[OF source] site_data_term_def)
    obtain target where bound: "q=use_data_term target" "binds_slot E v key target"
      using calls(2) by (auto simp: coordinate binding_lookup_at_source[OF source] inj_eq[OF use_data_term_injective])
    have needed: "target\<in>requested_uses E (generation_requests E {(u,r)})"
      using demand bound(2) unfolding requested_uses_def by blast
    show ?thesis by (rule exI[of _ G], rule exI[of _ target]) (use native bound(1) needed in blast)
  qed
next
  assume "\<exists>G v. q=use_data_term v \<and> generation_at E u r G \<and> v\<in>requested_uses E (generation_requests E {(u,r)})"
  then obtain G v where coordinate: "q=use_data_term v" and native: "generation_at E u r G"
    and needed: "v\<in>requested_uses E (generation_requests E {(u,r)})" by blast
  have observed: "generation_use_observed e (use_data_term u) (Payload_Term r) q"
  proof (cases "v\<in>fst ` generation_requests E {(u,r)}")
    case True
    obtain a where site: "(v,a)\<in>generation_read_sites E {(u,r)}"
      using True by (simp only: generation_request_source_uses[OF native]) force
    have reached: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v a))
        \<in>positive_meaning generation_retention_system" by (rule generation_read_site_complete[OF source native site])
    show ?thesis using reached by (auto simp: coordinate site_data_term_def)
  next
    case False
    obtain w k where demand: "(w,k)\<in>requested_slots E (generation_requests E {(u,r)})" and binding: "binds_slot E w k v"
      using needed False by (auto simp: requested_uses_def)
    have slot: "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term w k))
        \<in>positive_meaning generation_retention_system"
      using native demand by (simp only: generation_demanded_slot_at_source[OF source]) blast
    have bound: "(38,binding_lookup_argument e (use_data_term w) (Payload_Term k) q)\<in>positive_meaning binding_lookup_system"
      using source binding coordinate by (auto simp: binding_lookup_exact)
    show ?thesis using slot bound by (auto simp: site_data_term_def)
  qed
  show "(173,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)\<in>positive_meaning generation_retention_system"
    using observed by (simp only: generation_required_use_fields) blast
qed

abbreviation generation_required_use_result :: "factor_term \<Rightarrow> bool" where
  "generation_required_use_result t \<equiv> \<exists>E e u r G v.
    t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (use_data_term v) \<and>
    environment_value_presents E e \<and> generation_at E u r G \<and>
    v\<in>requested_uses E (generation_requests E {(u,r)})"

theorem generation_required_use_exact:
  "(173,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_required_use_result t"
proof
  assume holds: "(173,t)\<in>positive_meaning generation_retention_system"
  obtain E e u r G q where source: "environment_value_presents E e" and native: "generation_at E u r G"
    and shape: "t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q"
    using holds by (auto simp: generation_required_use_fields generation_read_site_exact generation_demanded_slot_exact site_data_term_def)
  show "generation_required_use_result t" using holds source
    by (simp only: shape generation_required_use_at_source[OF source]) blast
next
  assume "generation_required_use_result t"
  then show "(173,t)\<in>positive_meaning generation_retention_system" using generation_required_use_at_source by blast
qed

text \<open>
  These exact operations recover the existing request, slot, and use sets.
  The actual complete citation reader supplies each slot. An artifact target
  is required here only through a demanded binding; a stored binding outside
  the request set cannot justify its own source or destination.

  Every operation keeps the actual source environment and root. Reading a
  whole locus, payload, or cause artifact does not continue generation reading
  into that target. Only actual predecessor edges supply recursive read sites.
\<close>

end
