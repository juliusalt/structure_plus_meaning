theory Factor_Compiled_Applications
  imports Factor_Program_Compilation Factor_Future_Applications
begin

section \<open>The compiled program accepts exactly the source application boundary\<close>

lemma compiled_system_call_boundary:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and variant: "system_alpha_variant (rename_system g P) Q" and member: "d \<in> system_definitions P"
  shows "schema_call_formed Q (g d) t \<longleftrightarrow> schema_call_formed P d t"
  using system_alpha_calls[OF variant, of "g d" t] renamed_system_call[OF formed injective member, of t] by blast

lemma compiled_system_meaning_at:
  assumes injective: "inj_on g (system_definitions P)" and member: "d \<in> system_definitions P"
    and meaning: "positive_meaning Q = map_prod g id ` positive_meaning P"
  shows "(g d,t) \<in> positive_meaning Q \<longleftrightarrow> (d,t) \<in> positive_meaning P"
proof
  assume "(g d,t) \<in> positive_meaning Q"
  then obtain e x where source: "(e,x) \<in> positive_meaning P" "g d=g e" "t=x"
    using meaning by (auto simp: map_prod_def)
  have call: "schema_call_formed P e x" by (rule positive_meaning_formed[OF source(1)])
  have inside: "e \<in> system_definitions P" using schema_call_formed_target[OF call] by blast
  have same: "d=e" by (rule inj_onD[OF injective source(2) member inside])
  show "(d,t) \<in> positive_meaning P" using source(1,3) same by simp
next
  assume source: "(d,t) \<in> positive_meaning P"
  have "map_prod g id (d,t) \<in> map_prod g id ` positive_meaning P" by (rule imageI[OF source])
  then show "(g d,t) \<in> positive_meaning Q" using meaning by simp
qed

lemma native_package_definition_anchor:
  assumes package: "native_package_at E pu pr Q" and member: "d \<in> system_definitions Q"
  shows "\<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
proof -
  have formed: "native_package_formed E (native_package_roots E pu pr)" by (rule native_package_projection(1)[OF package])
  have site: "d \<in> native_definition_sites E (native_package_roots E pu pr)"
    using member native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  obtain p C where read: "native_definition_at E (fst d) (snd d) p C"
    using formed site by (auto simp: native_package_formed_def)
  show ?thesis by (rule native_definition_has_anchor[OF read])
qed

section \<open>One closed finite native program for all future formed arguments\<close>

theorem compiled_program_future_applications:
  assumes formed: "schema_system_formed P"
  shows "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E pu Q.
    inj_on g (system_definitions P) \<and> closed_native_package_at E pu [] Q \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au \<notin> environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu [] = E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed P d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t) \<in> positive_meaning P) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu and Q where compiled:
    "inj_on g (system_definitions P)" "closed_native_package_at E pu [] Q"
    "native_package_environment E pu [] = E" "system_alpha_variant (rename_system g P) Q"
    "positive_meaning Q = map_prod g id ` positive_meaning P"
    using program_compilation_total[OF formed] by metis
  have package: "native_package_at E pu [] Q" using compiled(2) by (simp add: closed_native_package_at_def)
  have ef: "environment_formed E" using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have defs: "system_definitions Q = g ` system_definitions P"
    using compiled(4) by (simp add: system_alpha_variant_def renamed_system_definitions)
  have all_calls: "\<forall>d\<in>system_definitions P. \<forall>t. term_formed t \<longrightarrow>
    (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au \<notin> environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu [] = E \<and>
      (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed P d t) \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t) \<in> positive_meaning P) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
  proof (intro ballI allI impI)
    fix d t assume member: "d \<in> system_definitions P" and arg: "term_formed t"
    have target: "g d \<in> system_definitions Q" using imageI[OF member, of g] defs by simp
    obtain R where source: "artifact_at E (fst (g d)) R" "anchor_formed (R,snd (g d))"
      using native_package_definition_anchor[OF package target] by blast
    let ?F = "future_call_environment E (fst (g d)) R (snd (g d)) t"
    let ?au = "future_call_use E (fst (g d))"
    have ff: "environment_formed ?F" by (rule future_call_environment_formed[OF ef source arg])
    have included: "environment_included E ?F" by (rule future_call_includes_existing)
    have fresh: "?au \<notin> environment_uses E" by (rule future_call_use_fresh[OF ef])
    obtain I K where app: "native_application_at ?F ?au [] (g d) t I K"
      using future_call_representation[OF ef source arg] by auto
    have preserved: "native_package_at ?F pu [] Q" by (rule future_call_preserves_program(1)[OF package source arg])
    have canonical: "native_package_environment ?F pu [] = E"
      using future_call_preserves_program(2)[OF package source arg] compiled(3) by simp
    have boundary: "native_application_formed ?F pu [] ?au [] \<longleftrightarrow> schema_call_formed P d t"
      using native_application_formed_with_reads[OF preserved app]
        compiled_system_call_boundary[OF formed compiled(1,4) member] by blast
    have truth: "native_positive_holds ?F pu [] ?au [] \<longleftrightarrow> (d,t) \<in> positive_meaning P"
      using native_positive_holds_with_reads[OF preserved app]
        compiled_system_meaning_at[OF compiled(1) member compiled(5)] by blast
    have artifacts: "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
      by (intro ballI allI) (rule future_call_existing_artifacts[OF ef source arg]; assumption)
    have bindings: "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w"
      by (intro ballI allI) (rule future_call_existing_bindings[OF ef]; assumption)
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au \<notin> environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu [] = E \<and>
      (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed P d t) \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t) \<in> positive_meaning P) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
      by (rule exI[of _ ?F], rule exI[of _ ?au], rule exI[of _ I], rule exI[of _ K])
         (use ff included fresh preserved app canonical boundary truth artifacts bindings in blast)
  qed
  show ?thesis by (rule exI[of _ g], rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q])
    (use compiled(1,2) all_calls in blast)
qed

text \<open>
  A single finite closed compilation serves every formed future argument at
  every source definition. Each call has actual native syntax, the original
  interface boundary, and exactly the original positive truth. The canonical
  program environment and all of its existing artifacts and bindings remain
  unchanged when those future arguments are added.
\<close>

end
