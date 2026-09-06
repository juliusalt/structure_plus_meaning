theory Factor_Replay
  imports Factor_Replay_Retention Factor_Native_Proofs Factor_Judgment_Retention
begin

section \<open>Replay joins validity, native realization, and explicit retention\<close>

definition native_replay_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> ('u definition_site\<times>('u definition_site\<times>factor_term)) set \<Rightarrow> bool" where
  "native_replay_at E pu pr au ar root H \<longleftrightarrow>
    (\<exists>P d t I K G. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      native_schema_graph_at E root G \<and> schema_graph_derives (positioned_program P) G root d t H \<and>
      environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G))"

theorem native_replay_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "native_replay_at E pu pr au ar root H \<longleftrightarrow>
    schema_graph_derives (positioned_program P) G root d t H \<and>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
proof
  assume replay: "native_replay_at E pu pr au ar root H"
  obtain Q e v J L X where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "native_schema_graph_at E root X" "schema_graph_derives (positioned_program Q) X root e v H"
    "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar X)"
    using replay by (auto simp: native_replay_at_def)
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  have graphs: "X=G" by (rule native_schema_graph_unique[OF other(3) graph])
  show "schema_graph_derives (positioned_program P) G root d t H \<and>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
    using other(4,5) programs calls graphs by simp
next
  assume "schema_graph_derives (positioned_program P) G root d t H \<and>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
  then show "native_replay_at E pu pr au ar root H"
    using package app graph unfolding native_replay_at_def by blast
qed

theorem native_replay_retention:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
    and derived: "schema_graph_derives (positioned_program P) G root d t H"
  shows "native_replay_at (native_replay_environment E pu pr au ar G) pu pr au ar root H"
  using native_replay_with_reads[
      OF native_replay_environment_recovers(1-3)[OF package app graph]]
    native_replay_environment_closed[OF package app graph] derived by blast

theorem native_replay_retention_cannot_create_validity:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
    and invalid: "\<not>schema_graph_derives (positioned_program P) G root d t H"
  shows "\<not>native_replay_at E pu pr au ar root H"
    "\<not>native_replay_at (native_replay_environment E pu pr au ar G) pu pr au ar root H"
  using native_replay_with_reads[OF package app graph]
    native_replay_with_reads[OF native_replay_environment_recovers(1-3)[OF package app graph]] invalid by blast+

theorem native_replay_assumptions_unique:
  assumes first: "native_replay_at E pu pr au ar root H" and second: "native_replay_at E pu pr au ar root J"
  shows "H=J"
proof -
  obtain P d t I K G where source: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "native_schema_graph_at E root G" "schema_graph_derives (positioned_program P) G root d t H"
    using first by (auto simp: native_replay_at_def)
  have other: "schema_graph_derives (positioned_program P) G root d t J"
    using native_replay_with_reads[OF source(1-3)] second by blast
  show ?thesis by (rule schema_graph_assumptions_unique[OF source(4) other])
qed

theorem native_replay_conditional_sound:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G" and replay: "native_replay_at E pu pr au ar root H"
    and assumptions: "\<forall>n e v. (n,e,v)\<in>H \<longrightarrow> (e,v)\<in>positive_meaning P"
  shows "native_positive_holds E pu pr au ar"
proof -
  have derived: "schema_graph_derives (positioned_program P) G root d t H"
    using native_replay_with_reads[OF package app graph] replay by blast
  have formed: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have supplied: "\<forall>n e v. (n,e,v)\<in>H \<longrightarrow> (e,v)\<in>positive_meaning (positioned_program P)"
    using assumptions positioned_program_meaning[OF formed] by simp
  have positive: "(d,t)\<in>positive_meaning (positioned_program P)"
  proof (rule schema_graph_conditional_sound[OF derived])
    fix n q assume member: "(n,q)\<in>H"
    obtain e v where shape: "q=(e,v)" by (cases q) auto
    show "q\<in>positive_meaning (positioned_program P)" using supplied member shape by blast
  qed
  have original: "(d,t)\<in>positive_meaning P" using positive positioned_program_meaning[OF formed] by simp
  show ?thesis using native_positive_holds_with_reads[OF package app] original by blast
qed

theorem native_replay_closed_sound:
  assumes replay: "native_replay_at E pu pr au ar root {}"
  shows "native_positive_holds E pu pr au ar"
proof -
  obtain P d t I K G where source: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "native_schema_graph_at E root G" using replay by (auto simp: native_replay_at_def)
  show ?thesis by (rule native_replay_conditional_sound[OF source replay]) simp
qed

theorem native_positive_replay_total:
  fixes E :: "local_address option artifact_environment"
  assumes positive: "native_positive_holds E pu pr au ar"
  shows "\<exists>R P d t I K root. native_replay_at R pu pr au ar root {} \<and>
    native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
    native_package_at R pu pr P \<and> native_application_at R au ar d t I K \<and>
    native_package_environment R pu pr=native_package_environment E pu pr \<and>
    environment_included (native_judgment_environment E pu pr au ar) R \<and>
    native_judgment_environment R pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  obtain F P d t I K G root where ff: "environment_formed F" and included: "environment_included E F"
    and source: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and built: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    "native_schema_graph_at F root G" "schema_graph_derives (positioned_program P) G root d t {}"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_positive_proof_total[OF positive] by blast
  let ?R = "native_replay_environment F pu pr au ar G"
  have replay: "native_replay_at ?R pu pr au ar root {}"
    by (rule native_replay_retention[OF built])
  have kept: "native_package_at ?R pu pr P" "native_application_at ?R au ar d t I K"
    using native_replay_environment_recovers(1,2)[OF built(1-3)] by blast+
  have canonical: "native_package_environment ?R pu pr=native_package_environment E pu pr"
    using native_package_environment_extension[
      OF kept(1) native_replay_environment_included ff] program by simp
  have old_scope: "native_judgment_environment F pu pr au ar=native_judgment_environment E pu pr au ar"
    by (rule native_judgment_environment_extension[OF source included ff])
  have new_scope: "native_judgment_environment F pu pr au ar=native_judgment_environment ?R pu pr au ar"
    by (rule native_judgment_environment_extension[OF kept native_replay_environment_included ff])
  have scope: "native_judgment_environment ?R pu pr au ar=native_judgment_environment E pu pr au ar"
    using old_scope new_scope by simp
  have retains: "environment_included (native_judgment_environment E pu pr au ar) ?R"
    using native_judgment_environment_included[of ?R pu pr au ar] scope by simp
  show ?thesis
    by (rule exI[of _ ?R], rule exI[of _ P], rule exI[of _ d], rule exI[of _ t],
        rule exI[of _ I], rule exI[of _ K], rule exI[of _ root])
       (use replay source kept canonical retains scope in blast)
qed


theorem native_replay_exact_call_adequate:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_positive_holds E pu pr au ar \<longleftrightarrow>
    (\<exists>H root. native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_replay_at H pu pr au ar root {} \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H)"
proof
  assume positive: "native_positive_holds E pu pr au ar"
  obtain H Q e x J W root where source: "native_package_at E pu pr Q"
    "native_application_at E au ar e x J W"
    and kept: "native_package_at H pu pr Q" "native_application_at H au ar e x J W"
    and certificate: "native_replay_at H pu pr au ar root {}"
    and canonical: "native_package_environment H pu pr=native_package_environment E pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
      "environment_included (native_judgment_environment E pu pr au ar) H"
    using native_positive_replay_total[OF positive] by blast
  have programs: "Q=P" by (rule native_package_unique[OF source(1) package])
  have calls: "e=d \<and> x=t \<and> J=I \<and> W=K" by (rule native_application_unique[OF source(2) app])
  show "\<exists>H root. native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
    native_replay_at H pu pr au ar root {} \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
    environment_included (native_judgment_environment E pu pr au ar) H"
    using kept certificate canonical programs calls by blast
next
  assume witness: "\<exists>H root. native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
    native_replay_at H pu pr au ar root {} \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
    environment_included (native_judgment_environment E pu pr au ar) H"
  obtain H root where target: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and replay: "native_replay_at H pu pr au ar root {}" using witness by blast
  have positive: "native_positive_holds H pu pr au ar" by (rule native_replay_closed_sound[OF replay])
  have meaning: "(d,t)\<in>positive_meaning P" using native_positive_holds_with_reads[OF target] positive by blast
  show "native_positive_holds E pu pr au ar" using native_positive_holds_with_reads[OF package app] meaning by blast
qed

text \<open>
  Replay checks the independently defined derivation, its complete native
  realization, and the grammar-derived closed retention boundary. The exact
  identified assumptions are recovered uniquely; they do not acquire truth
  through retention. A closed replay establishes native positive truth, and
  every positive native call has a closed replay with its exact program and
  argument preserved. No construction-specific field belongs to this join.
\<close>

end
