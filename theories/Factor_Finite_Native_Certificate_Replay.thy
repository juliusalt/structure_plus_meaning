theory Factor_Finite_Native_Certificate_Replay
  imports Factor_Finite_Native_Certificate_Graphs Factor_Finite_Application_Construction
    Factor_Executable_Replay Factor_Proof_Inclusion Factor_Program_Scopes
begin

lemma finite_source_application_ready:
  assumes source: "finite_native_source E u r=Some P"
    and call: "schema_call_formed (decode_finite_system P) d (decode_finite_term t)"
  shows "finite_application_ready E d t"
proof -
  have package: "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  have formed: "environment_formed (decode_finite_environment E)"
    using native_package_projection(1)[OF package] by (simp only: native_package_formed_def; blast)
  have member: "d\<in>system_definitions (decode_finite_system P)"
    and argument: "term_formed (decode_finite_term t)"
    using schema_call_formed_target[OF call] by blast+
  have position: "d\<in>environment_positions (decode_finite_environment E)"
    by (rule native_package_entry_position[OF package member])
  show ?thesis by (simp only: finite_application_ready_exact formed position argument simp_thms)
qed

definition finite_native_certificate_replay where
  "finite_native_certificate_replay E u r p d t=(case finite_native_certificate_graph E u r p d t of None \<Rightarrow> None
    | Some (F,M,root,G) \<Rightarrow> map_option (\<lambda>(A,au,I,K).
      (A,M,root,G,au,I,K,finite_native_replay_environment A u r au [] G))
      (finite_extend_native_application F d t))"

lemma finite_native_certificate_replay_result:
  "finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B) \<longleftrightarrow>
    (\<exists>F. finite_native_certificate_graph E u r p d t=Some (F,M,root,G) \<and>
      finite_extend_native_application F d t=Some (A,au,I,K) \<and>
      B=finite_native_replay_environment A u r au [] G)"
  by (cases root) (auto simp: finite_native_certificate_replay_def split: option.splits prod.splits)

theorem finite_native_certificate_replay_domain:
  "(\<exists>A M root G au I K B. finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t)"
proof
  assume "\<exists>A M root G au I K B. finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)"
  then show "\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t"
    by (simp only: finite_native_certificate_replay_result finite_native_certificate_graph_result; blast)
next
  assume "\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t"
  then obtain P where source: "finite_native_source E u r=Some P" and checked: "finite_checks_schema_proof P p d t" by blast
  have available: "\<exists>F M root G. finite_native_certificate_graph E u r p d t=Some (F,M,root,G)"
    using source checked by (simp only: finite_native_certificate_graph_domain; blast)
  obtain F M root G where graph: "finite_native_certificate_graph E u r p d t=Some (F,M,root,G)"
    using available by blast
  have kept: "finite_native_source F u r=Some P"
    by (rule finite_native_certificate_graph_correct(10)[OF graph source])
  have certificate: "checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
    using checked by (simp only: finite_checks_schema_proof_exact)
  have call: "schema_call_formed (decode_finite_system P) d (decode_finite_term t)"
    by (rule positive_meaning_formed[OF schema_proof_sound[OF certificate]])
  have ready: "finite_application_ready F d t" by (rule finite_source_application_ready[OF kept call])
  obtain A au I K where app: "finite_extend_native_application F d t=Some (A,au,I,K)"
    using ready by (simp only: finite_extend_native_application_domain[symmetric]; blast)
  show "\<exists>A M root G au I K B. finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)"
    using graph app by (simp only: finite_native_certificate_replay_result; blast)
qed

theorem finite_native_certificate_replay_correct:
  assumes result: "finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)"
    and source: "finite_native_source E u r=Some P"
  shows "finite_environment_formed A"
    "environment_included (decode_finite_environment E) (decode_finite_environment A)"
    "finite_environment_agrees_on E A (finite_environment_uses E)"
    "finite_native_source A u r=Some P"
    "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) G root"
    "single_valued ((fset M)\<inverse>)"
    "G |\<in>| finite_native_graph_readings A root"
    "((d,t),I,K) |\<in>| finite_application_readings A au []"
    "B=finite_native_replay_environment A u r au [] G"
    "finite_environment_formed B"
    "environment_included (decode_finite_environment B) (decode_finite_environment A)"
    "P |\<in>| finite_native_package_readings B u r"
    "G |\<in>| finite_native_graph_readings B root"
    "((d,t),I,K) |\<in>| finite_application_readings B au []"
    "{||} |\<in>| finite_native_replay_readings B u r au [] root"
    "image fst (fset (finite_graph_nodes G))\<inter>fset (finite_environment_uses E)={}"
proof -
  obtain F where graph: "finite_native_certificate_graph E u r p d t=Some (F,M,root,G)"
    and app: "finite_extend_native_application F d t=Some (A,au,I,K)"
    and retained: "B=finite_native_replay_environment A u r au [] G"
    using result by (simp only: finite_native_certificate_replay_result; blast)
  have formed: "finite_environment_formed A"
    and included: "environment_included (decode_finite_environment F) (decode_finite_environment A)"
    and agree: "finite_environment_agrees_on F A (finite_environment_uses F)"
    and application: "((d,t),I,K) |\<in>| finite_application_readings A au []"
    by (rule finite_extend_native_application_correct[OF app])+
  have ff: "environment_formed (decode_finite_environment A)"
    using formed by (simp only: finite_environment_formed_correct)
  have earlier: "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    and old_agree: "finite_environment_agrees_on E F (finite_environment_uses E)"
    and native_graph: "G |\<in>| finite_native_graph_readings F root"
    and package: "finite_native_source F u r=Some P"
    and derived: "schema_graph_derives (decode_finite_system (finite_positioned_program P))
      (decode_finite_graph G) root d (decode_finite_term t) {}"
    by (rule finite_native_certificate_graph_correct[OF graph source])+
  show "finite_environment_formed A" by (rule formed)
  show "environment_included (decode_finite_environment E) (decode_finite_environment A)"
    by (rule environment_included_trans[OF earlier included])
  have uses: "finite_environment_uses E |\<subseteq>| finite_environment_uses F"
    using included_uses[OF earlier]
    by (simp only: less_eq_fset.rep_eq finite_environment_uses_correct)
  show "finite_environment_agrees_on E A (finite_environment_uses E)"
    by (rule finite_environment_agrees_on_trans[OF old_agree agree uses])
  have original_package: "native_package_at (decode_finite_environment F) u r (decode_finite_system P)"
    using package by (simp only: finite_native_source_correct)
  have full_package: "finite_native_source A u r=Some P"
    using native_package_included[OF original_package included ff]
    by (simp only: finite_native_source_correct)
  then show "finite_native_source A u r=Some P" .
  show "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) G root"
    "single_valued ((fset M)\<inverse>)"
    by (rule finite_native_certificate_graph_correct[OF graph source])+
  have original_graph: "native_schema_graph_at (decode_finite_environment F) root (decode_finite_graph G)"
    using native_graph by (simp only: finite_native_graph_readings_correct)
  have full_graph: "G |\<in>| finite_native_graph_readings A root"
    using native_schema_graph_included[OF original_graph included ff]
    by (simp only: finite_native_graph_readings_correct)
  then show "G |\<in>| finite_native_graph_readings A root" .
  show "((d,t),I,K) |\<in>| finite_application_readings A au []" by (rule application)
  show "B=finite_native_replay_environment A u r au [] G" by (rule retained)
  have source_row: "P |\<in>| finite_native_package_readings A u r"
    using full_package by (simp only: finite_native_source_member)
  have recovered: "P |\<in>| finite_native_package_readings B u r"
    "((d,t),I,K) |\<in>| finite_application_readings B au []"
    "G |\<in>| finite_native_graph_readings B root"
    "finite_environment_formed B"
    by (simp only: retained; rule finite_native_replay_environment_recovers[OF source_row application full_graph])+
  show "finite_environment_formed B" "P |\<in>| finite_native_package_readings B u r"
    "G |\<in>| finite_native_graph_readings B root" "((d,t),I,K) |\<in>| finite_application_readings B au []"
    using recovered by blast+
  show "environment_included (decode_finite_environment B) (decode_finite_environment A)"
    by (simp only: retained finite_native_replay_environment_correct; rule native_replay_environment_included)
  have closed: "finite_environment_closed B {|u,au,fst root|} (finite_native_replay_demands B u r au [] G)"
    by (simp only: retained; rule finite_native_replay_environment_closed[OF source_row application full_graph])
  have derivation: "{||} |\<in>| finite_graph_derivation_readings (finite_positioned_program P) G root d t"
    using derived by (simp only: finite_graph_derivation_readings_correct decode_finite_premises_def
      bot_fset.rep_eq map_relation_values_def image_empty)
  show "{||} |\<in>| finite_native_replay_readings B u r au [] root"
    using recovered(1-3) closed derivation by (simp only: finite_native_replay_readings_step; blast)
  show "image fst (fset (finite_graph_nodes G))\<inter>fset (finite_environment_uses E)={}"
    by (rule finite_native_certificate_graph_correct(7)[OF graph source])

qed

text \<open>
  A checked certificate constructs both the complete native proof graph and
  its actual source call. The full extending environment preserves every old
  artifact and outgoing binding. The separately computed replay environment
  retains the same source, call and graph, and the ordinary native replay
  checker returns the empty assertion boundary there. Construction, extension
  and least replay retention remain distinct results. This does not establish
  workflow-policy adequacy, historical permission, physical cost or genesis.
\<close>

end
