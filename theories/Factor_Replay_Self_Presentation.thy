theory Factor_Replay_Self_Presentation
  imports Factor_Replay_Reading Factor_Native_Equality
begin

section \<open>Proof retention preserves all material of a fixed program\<close>

theorem replay_retention_preserves_program_material:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
    and canonical: "native_package_environment E pu pr=C"
    and artifacts: "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at E u A \<longleftrightarrow> artifact_at C u A"
    and bindings: "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot E u s v \<longleftrightarrow> binds_slot C u s v"
  shows "environment_included C (native_replay_environment E pu pr au ar G)"
    and "native_package_environment (native_replay_environment E pu pr au ar G) pu pr=C"
    and "\<forall>u\<in>environment_uses C. \<forall>A.
      artifact_at (native_replay_environment E pu pr au ar G) u A \<longleftrightarrow> artifact_at C u A"
    and "\<forall>u\<in>environment_uses C. \<forall>s v.
      binds_slot (native_replay_environment E pu pr au ar G) u s v \<longleftrightarrow> binds_slot C u s v"
proof -
  let ?R="native_replay_environment E pu pr au ar G"
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have kept: "native_package_at ?R pu pr P"
    by (rule native_replay_environment_recovers(1)[OF package app graph])
  have restricted: "environment_included ?R E" by (rule native_replay_environment_included)
  have same: "native_package_environment ?R pu pr=C"
    using native_package_environment_extension[OF kept restricted ef] canonical by simp
  have lower: "environment_included C ?R"
    using native_package_environment_included[of ?R pu pr] same by simp
  show "environment_included C ?R" by (rule lower)
  show "native_package_environment ?R pu pr=C" by (rule same)
  show "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at ?R u A \<longleftrightarrow> artifact_at C u A"
    using artifacts included_artifact[OF restricted] included_artifact[OF lower] by blast
  show "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot ?R u s v \<longleftrightarrow> binds_slot C u s v"
    using bindings included_binding[OF restricted] included_binding[OF lower] by blast
qed

theorem native_positive_replay_preserves_program:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and positive: "native_positive_holds E pu pr au ar"
    and canonical: "native_package_environment E pu pr=C"
    and artifacts: "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at E u A \<longleftrightarrow> artifact_at C u A"
    and bindings: "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot E u s v \<longleftrightarrow> binds_slot C u s v"
  shows "\<exists>R root. environment_formed R \<and> environment_included C R \<and>
    native_package_at R pu pr P \<and> native_application_at R au ar d t I K \<and>
    native_replay_at R pu pr au ar root {} \<and> native_package_environment R pu pr=C \<and>
    native_judgment_environment R pu pr au ar=native_judgment_environment E pu pr au ar \<and>
    (\<forall>u\<in>environment_uses C. \<forall>A. artifact_at R u A \<longleftrightarrow> artifact_at C u A) \<and>
    (\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot R u s v \<longleftrightarrow> binds_slot C u s v)"
proof -
  obtain W Q e x L M G root where built: "environment_formed W" "environment_included E W"
    "native_package_at E pu pr Q" "native_application_at E au ar e x L M"
    "native_package_at W pu pr Q" "native_application_at W au ar e x L M"
    "native_schema_graph_at W root G" "schema_graph_derives (positioned_program Q) G root e x {}"
    "native_package_environment W pu pr=native_package_environment E pu pr"
    "\<forall>u\<in>environment_uses E. \<forall>A. artifact_at W u A \<longleftrightarrow> artifact_at E u A"
    "\<forall>u\<in>environment_uses E. \<forall>s v. binds_slot W u s v \<longleftrightarrow> binds_slot E u s v"
    using native_positive_proof_total[OF positive] by (elim exE conjE) (rule that; assumption)
  have programs: "Q=P" by (rule native_package_unique[OF built(3) package])
  have calls: "e=d \<and> x=t \<and> L=I \<and> M=K"
    by (rule native_application_unique[OF built(4) app])
  have wp: "native_package_at W pu pr P" and wa: "native_application_at W au ar d t I K"
    and derived: "schema_graph_derives (positioned_program P) G root d t {}"
    using built(5,6,8) programs calls by auto
  have scope: "native_package_environment W pu pr=C" using built(9) canonical by simp
  have lower: "environment_included C E"
    using native_package_environment_included[of E pu pr] canonical by simp
  have uses: "environment_uses C\<subseteq>environment_uses E" by (rule included_uses[OF lower])
  have arts: "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at W u A \<longleftrightarrow> artifact_at C u A"
    using built(10) artifacts uses by blast
  have binds: "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot W u s v \<longleftrightarrow> binds_slot C u s v"
    using built(11) bindings uses by blast
  let ?R="native_replay_environment W pu pr au ar G"
  have retained: "environment_included C ?R" "native_package_environment ?R pu pr=C"
    "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at ?R u A \<longleftrightarrow> artifact_at C u A"
    "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot ?R u s v \<longleftrightarrow> binds_slot C u s v"
    using replay_retention_preserves_program_material[OF wp wa built(7) scope arts binds] by blast+
  have kept: "native_package_at ?R pu pr P" "native_application_at ?R au ar d t I K" "environment_formed ?R"
    using native_replay_environment_recovers(1,2,4)[OF wp wa built(7)] by blast+
  have replay: "native_replay_at ?R pu pr au ar root {}"
    by (rule native_replay_retention[OF wp wa built(7) derived])
  have old_scope: "native_judgment_environment W pu pr au ar=native_judgment_environment E pu pr au ar"
    by (rule native_judgment_environment_extension[OF package app built(2,1)])
  have new_scope: "native_judgment_environment W pu pr au ar=native_judgment_environment ?R pu pr au ar"
    by (rule native_judgment_environment_extension[OF kept(1,2) native_replay_environment_included built(1)])
  have judgment_scope: "native_judgment_environment ?R pu pr au ar=native_judgment_environment E pu pr au ar"
    using old_scope new_scope by simp
  show ?thesis by (rule exI[of _ ?R], rule exI[of _ root])
    (use kept retained replay judgment_scope in blast)
qed

section \<open>An asserted false call is a replay but is not a closed proof\<close>

theorem native_false_call_conditional_replay:
  fixes E :: "local_address option artifact_environment"
  assumes formed: "native_application_formed E pu pr au ar"
    and false_call: "\<not>native_positive_holds E pu pr au ar"
  shows "\<exists>R P d t I K root c v.
    native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
    native_package_at R pu pr P \<and> native_application_at R au ar d t I K \<and>
    native_replay_at R pu pr au ar root {(root,d,t)} \<and>
    \<not>native_replay_at R pu pr au ar root {} \<and> \<not>native_positive_holds R pu pr au ar \<and>
    native_package_environment R pu pr=native_package_environment E pu pr \<and>
    artifact_value_presents (term_syntax v) c \<and> complete_data_quoted_at (term_syntax v) [] v \<and>
    replay_value_presents R pu pr au ar root v \<and>
    (128,v)\<in>positive_meaning replay_reading_system \<and>
    (129,v)\<notin>positive_meaning replay_reading_system \<and>
    (130,Pair_Term c v)\<in>positive_meaning replay_reading_system \<and>
    (131,Pair_Term c v)\<notin>positive_meaning replay_reading_system"
proof -
  obtain P d t I K where source: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and call: "schema_call_formed P d t"
    using formed by (auto simp: native_application_formed_def)
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF source(1)])
  have located: "schema_call_formed (positioned_program P) d t"
    using call by (simp only: positioned_program_calls[OF pf])
  let ?n="(None,[])::local_address option definition_site"
  have assertion: "schema_graph_derives (positioned_program P) (assertion_graph ?n) ?n d t {(?n,d,t)}"
    by (rule schema_graph_assertion[OF located])
  obtain W h where built: "environment_formed W" "environment_included E W"
    "native_package_at W pu pr P"
    "native_package_environment W pu pr=native_package_environment E pu pr"
    "native_schema_graph_at W (h ?n) (rename_schema_graph h (assertion_graph ?n))"
    "schema_graph_derives (positioned_program P) (rename_schema_graph h (assertion_graph ?n))
      (h ?n) d t (image (map_prod h id) {(?n,d,t)})"
    using derived_graph_native_realization[OF source(1) assertion]
    by (elim exE conjE) (rule that; assumption)
  let ?root="h ?n"
  let ?G="rename_schema_graph h (assertion_graph ?n)"
  have app: "native_application_at W au ar d t I K"
    by (rule native_application_included[OF source(2) built(2,1)])
  have derived: "schema_graph_derives (positioned_program P) ?G ?root d t {(?root,d,t)}"
    using built(6) by simp
  let ?R="native_replay_environment W pu pr au ar ?G"
  have replay: "native_replay_at ?R pu pr au ar ?root {(?root,d,t)}"
    by (rule native_replay_retention[OF built(3) app built(5) derived])
  have kept: "native_package_at ?R pu pr P" "native_application_at ?R au ar d t I K"
    using native_replay_environment_recovers(1,2)[OF built(3) app built(5)] by blast+
  have same: "native_package_environment ?R pu pr=native_package_environment E pu pr"
    using native_package_environment_extension[OF kept(1) native_replay_environment_included built(1)]
      built(4) by simp
  have false_result: "\<not>native_positive_holds ?R pu pr au ar"
    using false_call native_positive_holds_with_reads[OF source]
      native_positive_holds_with_reads[OF kept] by blast
  have open_boundary: "\<not>native_replay_at ?R pu pr au ar ?root {}"
    using native_replay_assumptions_unique[OF replay] by auto
  obtain c v where quoted: "artifact_value_presents (term_syntax v) c"
    "complete_data_quoted_at (term_syntax v) [] v" "replay_value_presents ?R pu pr au ar ?root v"
    "(130,Pair_Term c v)\<in>positive_meaning replay_reading_system"
    "((131,Pair_Term c v)\<in>positive_meaning replay_reading_system \<longleftrightarrow> {(?root,d,t)}={})"
    using replay_reading_total[OF replay] by (elim exE conjE) (rule that; assumption)
  have conditional: "(128,v)\<in>positive_meaning replay_reading_system"
    using replay by (simp only: replay_source_on_values(1)[OF quoted(3)] fst_conv snd_conv; blast)
  have closed: "(129,v)\<notin>positive_meaning replay_reading_system"
    using open_boundary replay_source_on_values(2)[OF quoted(3)] by blast
  show ?thesis
    by (rule exI[of _ ?R], rule exI[of _ P], rule exI[of _ d], rule exI[of _ t],
      rule exI[of _ I], rule exI[of _ K], rule exI[of _ ?root], rule exI[of _ c], rule exI[of _ v])
      (use source kept replay open_boundary false_result same quoted conditional closed in auto)
qed

corollary native_replay_readers_distinguish_assertions:
  "\<exists>R root c v.
    native_replay_at R None [0] (Some []) [] root {(root,(None,[Suc 0]),Payload_Term [])} \<and>
    \<not>native_positive_holds R None [0] (Some []) [] \<and>
    artifact_value_presents (term_syntax v) c \<and> complete_data_quoted_at (term_syntax v) [] v \<and>
    replay_value_presents R None [0] (Some []) [] root v \<and>
    (128,v)\<in>positive_meaning replay_reading_system \<and>
    (129,v)\<notin>positive_meaning replay_reading_system \<and>
    (130,Pair_Term c v)\<in>positive_meaning replay_reading_system \<and>
    (131,Pair_Term c v)\<notin>positive_meaning replay_reading_system"
proof -
  let ?E="equality_query_environment (Payload_Term [])"
  have tf: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  have formed: "native_application_formed ?E None [0] (Some []) []"
    by (rule native_equality_future_application_formed[OF tf])
  have false_call: "\<not>native_positive_holds ?E None [0] (Some []) []"
    by (simp only: native_equality_future_truth[OF tf]) simp
  obtain I K where app: "native_application_at ?E (Some []) [] (None,[Suc 0]) (Payload_Term []) I K"
    using equality_query_application[OF tf] by blast
  obtain R d t L M root c v where actual: "native_application_at ?E (Some []) [] d t L M"
    and witness: "native_replay_at R None [0] (Some []) [] root {(root,d,t)}"
    "\<not>native_positive_holds R None [0] (Some []) []"
    "artifact_value_presents (term_syntax v) c" "complete_data_quoted_at (term_syntax v) [] v"
    "replay_value_presents R None [0] (Some []) [] root v"
    "(128,v)\<in>positive_meaning replay_reading_system" "(129,v)\<notin>positive_meaning replay_reading_system"
    "(130,Pair_Term c v)\<in>positive_meaning replay_reading_system"
    "(131,Pair_Term c v)\<notin>positive_meaning replay_reading_system"
    using native_false_call_conditional_replay[OF formed false_call]
    by (elim exE conjE) (rule that; assumption)
  have same: "d=(None,[Suc 0]) \<and> t=Payload_Term []"
    using native_application_unique[OF actual app] by blast
  show ?thesis by (rule exI[of _ R], rule exI[of _ root], rule exI[of _ c], rule exI[of _ v])
    (use witness same in auto)
qed

section \<open>One native compilation precedes all supplied proof records\<close>

locale native_replay_reader =
  fixes g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu :: "local_address option"
    and Q :: "local_address option native_system"
  assumes injective: "inj_on g (system_definitions replay_reading_system)"
    and closed_package: "closed_native_package_at C cu [] Q"
    and canonical: "native_package_environment C cu []=C"
    and variant: "system_alpha_variant (rename_system g replay_reading_system) Q"
begin

lemma package: "native_package_at C cu [] Q"
  using closed_package by (simp add: closed_native_package_at_def)

lemma formed: "environment_formed C"
  using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)

lemma definitions: "system_definitions Q=image g (system_definitions replay_reading_system)"
proof -
  have domains: "system_definitions (rename_system g replay_reading_system)=system_definitions Q"
    using variant unfolding system_alpha_variant_def by blast
  show ?thesis using domains by (simp only: renamed_system_definitions; blast)
qed

lemma meaning:
  "positive_meaning Q=image (map_prod g id) (positive_meaning replay_reading_system)"
  using system_alpha_positive_meaning[OF variant]
    renamed_system_positive_meaning[OF replay_reading_system_formed injective] by simp

theorem rule_contracts:
  assumes profile: "(d,S)\<in>{(128,replay_source_schema),(129,closed_replay_source_schema),
    (130,replay_reading_schema),(131,closed_replay_reading_schema)}"
  shows "\<exists>T p v. native_single_clause_at C (fst (g d)) (snd (g d)) T \<and>
    schema_alpha_variant (rename_schema id id g S) T \<and>
    site_value_presents C (fst (g d)) (snd (g d)) p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance (rename_schema id id g S) X t)"
  by (rule compiled_single_clause_reading[OF replay_reading_system_formed injective variant package
      replay_reading_rule_profiles(1-3)[OF profile]])

theorem future_application:
  assumes member: "d\<in>system_definitions replay_reading_system" and arg: "term_formed t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
    native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
    native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
    (native_positive_holds F cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning replay_reading_system) \<and>
    (\<forall>u\<in>environment_uses C. \<forall>A. artifact_at F u A \<longleftrightarrow> artifact_at C u A) \<and>
    (\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot F u s v \<longleftrightarrow> binds_slot C u s v)"
proof -
  have inside: "g d\<in>system_definitions Q" using member by (simp only: definitions) blast
  have call: "schema_call_formed Q (g d) t"
    by (simp only: compiled_system_call_boundary[OF replay_reading_system_formed injective variant member]
      replay_reading_call) (use member arg in blast)
  have truth: "(g d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning replay_reading_system"
    by (rule compiled_system_meaning_at[OF injective member meaning])
  show ?thesis using native_application_extension_total[OF package inside arg]
    by (simp only: canonical call truth) simp
qed

theorem check_closed_replay:
  assumes replay: "native_replay_at R pu pr au ar root {}"
    and material: "artifact_value_presents A a" and quotation: "complete_data_quoted_at A r v"
    and context_value: "replay_value_presents R pu pr au ar root v"
  shows "\<exists>F bu I K. environment_formed F \<and> environment_included C F \<and> bu\<notin>environment_uses C \<and>
    native_package_at F cu [] Q \<and> native_application_at F bu [] (g 131) (Pair_Term a v) I K \<and>
    native_package_environment F cu []=C \<and> native_application_formed F cu [] bu [] \<and>
    native_positive_holds F cu [] bu [] \<and>
    (\<forall>u\<in>environment_uses C. \<forall>B. artifact_at F u B \<longleftrightarrow> artifact_at C u B) \<and>
    (\<forall>u\<in>environment_uses C. \<forall>s w. binds_slot F u s w \<longleftrightarrow> binds_slot C u s w)"
proof -
  have entry: "131\<in>system_definitions replay_reading_system" by simp
  have tf: "term_formed (Pair_Term a v)"
    using artifact_value_presents_formed[OF material] replay_value_presents_formed[OF context_value] by simp
  have admitted: "(131,Pair_Term a v)\<in>positive_meaning replay_reading_system"
    using replay by (simp only: replay_reading_on_values(2)[OF material quotation context_value]
      fst_conv snd_conv)
  show ?thesis using future_application[OF entry tf] admitted by blast
qed

theorem positive_call_exists:
  "\<exists>d t. (d,t)\<in>positive_meaning Q"
proof -
  have tf: "term_formed (Payload_Term [])" and closed: "self_contained_term (Payload_Term [])"
    by (simp_all add: octets_formed_def)
  obtain c where read: "(123,complete_data_quotation_argument c (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning complete_data_admission_system"
    using complete_data_admission_total[OF tf closed] by blast
  have source: "(123,complete_data_quotation_argument c (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning replay_reading_system"
    using read by (simp only: replay_reading_quotation_meaning)
  have own: "(g 123,complete_data_quotation_argument c (Payload_Term []) (Payload_Term []))\<in>positive_meaning Q"
    using imageI[OF source, of "map_prod g id"] meaning by simp
  show ?thesis using own by blast
qed

theorem own_positive_call:
  assumes positive: "(d,t)\<in>positive_meaning Q"
  shows "\<exists>E au I K R root.
    environment_formed E \<and> environment_included C E \<and> au\<notin>environment_uses C \<and>
    native_package_at E cu [] Q \<and> native_application_at E au [] d t I K \<and>
    native_positive_holds E cu [] au [] \<and>
    environment_formed R \<and> environment_included C R \<and>
    native_package_at R cu [] Q \<and> native_application_at R au [] d t I K \<and>
    native_replay_at R cu [] au [] root {} \<and> native_package_environment R cu []=C \<and>
    native_judgment_environment R cu [] au []=native_judgment_environment E cu [] au [] \<and>
    (\<forall>u\<in>environment_uses C. \<forall>A. artifact_at R u A \<longleftrightarrow> artifact_at C u A) \<and>
    (\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot R u s v \<longleftrightarrow> binds_slot C u s v) \<and>
    (\<exists>a v. artifact_value_presents (term_syntax v) a \<and> complete_data_quoted_at (term_syntax v) [] v \<and>
      replay_value_presents R cu [] au [] root v) \<and>
    (\<forall>A a r v. artifact_value_presents A a \<longrightarrow> complete_data_quoted_at A r v \<longrightarrow>
      replay_value_presents R cu [] au [] root v \<longrightarrow>
      (\<exists>F bu J L. environment_formed F \<and> environment_included C F \<and> bu\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F bu [] (g 131) (Pair_Term a v) J L \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] bu [] \<and>
        native_positive_holds F cu [] bu [] \<and>
        (\<forall>u\<in>environment_uses C. \<forall>B. artifact_at F u B \<longleftrightarrow> artifact_at C u B) \<and>
        (\<forall>u\<in>environment_uses C. \<forall>s w. binds_slot F u s w \<longleftrightarrow> binds_slot C u s w)))"
proof -
  have call: "schema_call_formed Q d t" by (rule positive_meaning_formed[OF positive])
  have inside: "d\<in>system_definitions Q" and tf: "term_formed t"
    using schema_call_formed_target[OF call] by blast+
  obtain E au I K where future: "environment_formed E" "environment_included C E" "au\<notin>environment_uses C"
    "native_package_at E cu [] Q" "native_application_at E au [] d t I K"
    "native_package_environment E cu []=native_package_environment C cu []"
    "native_positive_holds E cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
    "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at E u A \<longleftrightarrow> artifact_at C u A"
    "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot E u s v \<longleftrightarrow> binds_slot C u s v"
    using native_application_extension_total[OF package inside tf]
    by (elim exE conjE) (rule that; assumption)
  have holds: "native_positive_holds E cu [] au []" using future(7) positive by blast
  have same: "native_package_environment E cu []=C" using future(6) canonical by simp
  obtain R root where retained: "environment_formed R" "environment_included C R"
    "native_package_at R cu [] Q" "native_application_at R au [] d t I K"
    "native_replay_at R cu [] au [] root {}" "native_package_environment R cu []=C"
    "native_judgment_environment R cu [] au []=native_judgment_environment E cu [] au []"
    "\<forall>u\<in>environment_uses C. \<forall>A. artifact_at R u A \<longleftrightarrow> artifact_at C u A"
    "\<forall>u\<in>environment_uses C. \<forall>s v. binds_slot R u s v \<longleftrightarrow> binds_slot C u s v"
    using native_positive_replay_preserves_program[OF future(4,5) holds same future(8,9)]
    by (elim exE conjE) (rule that; assumption)
  have presentations: "\<exists>a v. artifact_value_presents (term_syntax v) a \<and>
      complete_data_quoted_at (term_syntax v) [] v \<and> replay_value_presents R cu [] au [] root v"
    using replay_reading_total[OF retained(5)] by (elim exE conjE) blast
  have checks: "\<forall>A a r v. artifact_value_presents A a \<longrightarrow> complete_data_quoted_at A r v \<longrightarrow>
      replay_value_presents R cu [] au [] root v \<longrightarrow>
      (\<exists>F bu J L. environment_formed F \<and> environment_included C F \<and> bu\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F bu [] (g 131) (Pair_Term a v) J L \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] bu [] \<and>
        native_positive_holds F cu [] bu [] \<and>
        (\<forall>u\<in>environment_uses C. \<forall>B. artifact_at F u B \<longleftrightarrow> artifact_at C u B) \<and>
        (\<forall>u\<in>environment_uses C. \<forall>s w. binds_slot F u s w \<longleftrightarrow> binds_slot C u s w))"
    by (intro allI impI; rule check_closed_replay[OF retained(5)]; assumption)
  show ?thesis by (rule exI[of _ E], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K],
      rule exI[of _ R], rule exI[of _ root])
    (intro conjI; fact future(1-5) holds retained presentations checks)
qed

corollary positive_native_application_exists:
  "\<exists>E au d t I K. native_package_at E cu [] Q \<and>
    native_application_at E au [] d t I K \<and> native_positive_holds E cu [] au []"
proof -
  obtain d t where positive: "(d,t)\<in>positive_meaning Q" using positive_call_exists by blast
  obtain E au I K where actual: "native_package_at E cu [] Q"
    "native_application_at E au [] d t I K" "native_positive_holds E cu [] au []"
    using own_positive_call[OF positive] by (elim exE conjE) (rule that; assumption)
  show ?thesis by (rule exI[of _ E], rule exI[of _ au], rule exI[of _ d], rule exI[of _ t],
      rule exI[of _ I], rule exI[of _ K]) (intro conjI; fact actual)
qed

end

theorem native_replay_reader_exists:
  "\<exists>g C cu Q. native_replay_reader g C cu Q"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site" and C cu Q where compiled:
    "inj_on g (system_definitions replay_reading_system)" "closed_native_package_at C cu [] Q"
    "native_package_environment C cu []=C" "system_alpha_variant (rename_system g replay_reading_system) Q"
    using compiled_program_with_future_applications[OF replay_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have reader: "native_replay_reader g C cu Q" by (unfold_locales) (fact compiled)+
  show ?thesis by (rule exI[of _ g], rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q]) (rule reader)
qed

text \<open>
  A native reader is an actual closed compilation of the four ordinary views
  and their existing dependencies. The locale records its coordinates and
  canonical environment; its existence follows from the native compiler.
  Its rule contracts check the complete native definitions with reader 127.

  Every formed future input has an actual application of that fixed program.
  The preceding admission equations give the four entry contracts. A complete
  quotation of the empty payload supplies a positive call, so the statement
  about all positive calls has an inhabited domain.

  Every positive call of the actual compiled program has a closed native
  replay retaining that same program, the selected application, and the
  minimal judgment scope. Every original program artifact and outgoing binding
  is preserved. Each replay has complete quotations and body presentations.
  Every compatible pair is checked by entry 131 of the original fixed
  compilation, with the same full preservation of program material. That
  checking call is itself among the program's positive calls.

  Assertions do not acquire truth through presentation or retention. A
  concrete false equality call has a conditional replay and complete admitted
  quotation, while the closed readers reject it. The self-presentation theorem
  concerns native proofs of the program's operative judgments. It does not
  claim that Isabelle's general presentation-class proofs have become native
  derivations of their full mathematical contracts.
\<close>

end
