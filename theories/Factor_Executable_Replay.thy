theory Factor_Executable_Replay
  imports Factor_Executable_Replay_Retention Factor_Executable_Positions Factor_Executable_Recovery Factor_Replay
begin

section \<open>Valid graphs compute their exact explicit assertions\<close>

definition finite_graph_derivation_readings ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('n \<times> ('d \<times> finite_factor_term)) fset fset" where
  "finite_graph_derivation_readings P G root d t =
    (if finite_graph_valid P G root d t
     then {|finite_graph_assumptions G (finite_graph_claims P G root d t)|} else {||})"

lemma finite_graph_derivation_readings_sound:
  assumes member: "H |\<in>| finite_graph_derivation_readings P G root d t"
  shows "schema_graph_derives (decode_finite_system P) (decode_finite_graph G)
    root d (decode_finite_term t) (decode_finite_premises H)"
proof -
  have valid: "finite_graph_valid P G root d t"
    and chosen: "H=finite_graph_assumptions G (finite_graph_claims P G root d t)"
    using member by (auto simp: finite_graph_derivation_readings_def split: if_splits)
  have read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises (finite_graph_claims P G root d t))"
    using valid by (simp add: finite_graph_valid_def finite_graph_reading_correct)
  have boundary: "decode_finite_premises H = schema_graph_assumptions (decode_finite_graph G)
      (decode_finite_premises (finite_graph_claims P G root d t))"
    by (simp only: chosen finite_graph_assumptions_correct)
  show ?thesis using read boundary unfolding schema_graph_derives_def by blast
qed

theorem finite_graph_derivation_readings_complete:
  assumes derived: "schema_graph_derives (decode_finite_system P) (decode_finite_graph G)
    root d (decode_finite_term t) H"
  shows "\<exists>F. F |\<in>| finite_graph_derivation_readings P G root d t \<and> decode_finite_premises F=H"
proof -
  obtain J where read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J" and boundary: "schema_graph_assumptions (decode_finite_graph G) J=H"
    using derived unfolding schema_graph_derives_def by blast
  have valid: "finite_graph_valid P G root d t" using read by (auto simp: finite_graph_valid_correct)
  have decoded: "decode_finite_premises (finite_graph_assumptions G (finite_graph_claims P G root d t))=H"
    by (simp only: finite_graph_assumptions_correct finite_graph_claims_recovers[OF read] boundary)
  show ?thesis by (rule exI[of _ "finite_graph_assumptions G (finite_graph_claims P G root d t)"])
    (use valid decoded in \<open>simp add: finite_graph_derivation_readings_def\<close>)
qed

theorem finite_graph_derivation_readings_correct:
  "H |\<in>| finite_graph_derivation_readings P G root d t \<longleftrightarrow>
    schema_graph_derives (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises H)"
  using finite_graph_derivation_readings_sound[of H P G root d t]
    finite_graph_derivation_readings_complete[of P G root d t "decode_finite_premises H"] by auto

section \<open>Replay is checked from the complete native environment and roots\<close>

type_synonym 'u finite_native_assertions =
  "('u definition_site \<times> ('u definition_site \<times> finite_factor_term)) fset"

definition finite_native_replay_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> 'u finite_native_assertions fset" where
  "finite_native_replay_readings E pu pr au ar root = ffUnion (fimage (\<lambda>P.
    ffUnion (fimage (\<lambda>((d,t),I,K). ffUnion (fimage (\<lambda>G.
      if finite_environment_closed E {|pu,au,fst root|} (finite_native_replay_demands E pu pr au ar G)
      then finite_graph_derivation_readings (finite_positioned_program P) G root d t else {||})
      (finite_native_graph_readings E root))) (finite_application_readings E au ar)))
      (finite_native_package_readings E pu pr))"

lemma finite_native_replay_readings_step:
  "H |\<in>| finite_native_replay_readings E pu pr au ar root \<longleftrightarrow>
    (\<exists>P d t I K G. P |\<in>| finite_native_package_readings E pu pr \<and>
      ((d,t),I,K) |\<in>| finite_application_readings E au ar \<and>
      G |\<in>| finite_native_graph_readings E root \<and>
      finite_environment_closed E {|pu,au,fst root|} (finite_native_replay_demands E pu pr au ar G) \<and>
      H |\<in>| finite_graph_derivation_readings (finite_positioned_program P) G root d t)"
  by (auto simp: finite_native_replay_readings_def finite_union_image_member split: prod.splits if_splits; blast)

theorem finite_native_replay_readings_sound:
  assumes member: "H |\<in>| finite_native_replay_readings E pu pr au ar root"
  shows "native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises H)"
proof -
  obtain P d t I K G where package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    and graph: "G |\<in>| finite_native_graph_readings E root"
    and closed: "finite_environment_closed E {|pu,au,fst root|} (finite_native_replay_demands E pu pr au ar G)"
    and derived: "H |\<in>| finite_graph_derivation_readings (finite_positioned_program P) G root d t"
    using member by (simp only: finite_native_replay_readings_step; blast)
  have program: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using package by (simp add: finite_native_package_readings_correct)
  have application: "native_application_at (decode_finite_environment E) au ar d (decode_finite_term t) (fset I) (fset K)"
    using app by (simp add: finite_application_readings_correct)
  have realization: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    using graph by (simp add: finite_native_graph_readings_correct)
  have derivation: "schema_graph_derives (positioned_program (decode_finite_system P)) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises H)"
    using derived by (simp add: finite_graph_derivation_readings_correct finite_positioned_program_correct)
  have retained: "environment_closed (decode_finite_environment E) {pu,au,fst root}
      (native_replay_demands (decode_finite_environment E) pu pr au ar (decode_finite_graph G))"
    using closed by (simp add: finite_environment_closed_correct finite_native_replay_demands_correct)
  show ?thesis unfolding native_replay_at_def
    apply (rule exI[of _ "decode_finite_system P"], rule exI[of _ d], rule exI[of _ "decode_finite_term t"])
    apply (rule exI[of _ "fset I"], rule exI[of _ "fset K"], rule exI[of _ "decode_finite_graph G"])
    using program application realization derivation retained by simp
qed

theorem finite_native_replay_readings_complete:
  assumes replay: "native_replay_at (decode_finite_environment E) pu pr au ar root H"
  shows "\<exists>F. F |\<in>| finite_native_replay_readings E pu pr au ar root \<and> decode_finite_premises F=H"
proof -
  obtain P d t I K G where package: "native_package_at (decode_finite_environment E) pu pr P"
    and app: "native_application_at (decode_finite_environment E) au ar d t I K"
    and graph: "native_schema_graph_at (decode_finite_environment E) root G"
    and derived: "schema_graph_derives (positioned_program P) G root d t H"
    and closed: "environment_closed (decode_finite_environment E) {pu,au,fst root}
      (native_replay_demands (decode_finite_environment E) pu pr au ar G)"
    using replay by (simp only: native_replay_at_def; blast)
  obtain PF where program: "PF |\<in>| finite_native_package_readings E pu pr"
    and program_value: "decode_finite_system PF=P"
    using finite_native_package_readings_complete[OF package] by blast
  obtain T J A where application: "((d,T),J,A) |\<in>| finite_application_readings E au ar"
    and term_value: "decode_finite_term T=t"
    using finite_application_readings_complete[OF app] by blast
  obtain GF where realization: "GF |\<in>| finite_native_graph_readings E root"
    and graph_value: "decode_finite_graph GF=G"
    using finite_native_graph_readings_complete[OF graph] by blast
  have derivation: "schema_graph_derives (decode_finite_system (finite_positioned_program PF))
      (decode_finite_graph GF) root d (decode_finite_term T) H"
    using derived by (simp add: finite_positioned_program_correct program_value graph_value term_value)
  obtain F where boundary: "F |\<in>| finite_graph_derivation_readings (finite_positioned_program PF) GF root d T"
    and decoded: "decode_finite_premises F=H"
    using finite_graph_derivation_readings_complete[OF derivation] by blast
  have retained: "finite_environment_closed E {|pu,au,fst root|} (finite_native_replay_demands E pu pr au ar GF)"
    using closed by (simp add: finite_environment_closed_correct finite_native_replay_demands_correct graph_value)
  have member: "F |\<in>| finite_native_replay_readings E pu pr au ar root"
    unfolding finite_native_replay_readings_step
    apply (rule exI[of _ PF], rule exI[of _ d], rule exI[of _ T])
    apply (rule exI[of _ J], rule exI[of _ A], rule exI[of _ GF])
    using program application realization boundary retained by simp
  show ?thesis using member decoded by blast
qed

theorem finite_native_replay_readings_correct:
  "H |\<in>| finite_native_replay_readings E pu pr au ar root \<longleftrightarrow>
    native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises H)"
proof
  assume "H |\<in>| finite_native_replay_readings E pu pr au ar root"
  then show "native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises H)"
    by (rule finite_native_replay_readings_sound)
next
  assume replay: "native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises H)"
  show "H |\<in>| finite_native_replay_readings E pu pr au ar root"
    using finite_native_replay_readings_complete[OF replay] by auto
qed

corollary finite_native_replay_readings_unique:
  assumes "H |\<in>| finite_native_replay_readings E pu pr au ar root"
    "J |\<in>| finite_native_replay_readings E pu pr au ar root"
  shows "H=J"
proof -
  have first: "native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises H)"
    and second: "native_replay_at (decode_finite_environment E) pu pr au ar root (decode_finite_premises J)"
    using assms by (simp_all add: finite_native_replay_readings_correct)
  show ?thesis using native_replay_assumptions_unique[OF first second] by simp
qed

theorem finite_native_replay_retention:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    and graph: "G |\<in>| finite_native_graph_readings E root"
    and derived: "H |\<in>| finite_graph_derivation_readings (finite_positioned_program P) G root d t"
  shows "H |\<in>| finite_native_replay_readings (finite_native_replay_environment E pu pr au ar G) pu pr au ar root"
  unfolding finite_native_replay_readings_step
  apply (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t])
  apply (rule exI[of _ I], rule exI[of _ K], rule exI[of _ G])
  using finite_native_replay_environment_recovers(1-3)[OF package app graph]
    finite_native_replay_environment_closed[OF package app graph] derived by simp

definition finite_native_replay_proves ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> bool" where
  "finite_native_replay_proves E pu pr au ar root \<longleftrightarrow> {||} |\<in>| finite_native_replay_readings E pu pr au ar root"

theorem finite_native_replay_proves_correct:
  "finite_native_replay_proves E pu pr au ar root \<longleftrightarrow>
    native_replay_at (decode_finite_environment E) pu pr au ar root {}"
  by (simp add: finite_native_replay_proves_def finite_native_replay_readings_correct)

corollary finite_native_replay_proves_sound:
  assumes "finite_native_replay_proves E pu pr au ar root"
  shows "native_positive_holds (decode_finite_environment E) pu pr au ar"
  by (rule native_replay_closed_sound) (use assms in \<open>simp add: finite_native_replay_proves_correct\<close>)

export_code finite_graph_derivation_readings finite_native_replay_readings finite_native_replay_proves checking SML

text \<open>
  The supplied finite environment and the program, application, and proof roots
  determine the entire check. Recovery supplies the program and graph, finite
  claim propagation supplies the reading, and the grammar supplies the complete
  retention boundary. Every accepted replay returns its exact assertion
  occurrences. Empty assertions give the closed replay check and imply native
  positive truth. Correspondence and coverage include every native replay on
  a represented environment. This checks a supplied proof; it does not search
  for a proof of an arbitrary judgment or establish the native grammar's
  admission evidence.
\<close>

end
