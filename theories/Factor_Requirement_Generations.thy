theory Factor_Requirement_Generations
  imports Factor_Requirement_Artifact_Admission Factor_Closed_Base_Programs
begin

section \<open>One native artifact admission boundary precedes all candidate generations\<close>

theorem closed_requirement_artifact_program:
  assumes finite: "finite D"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_base_program E pu Q d \<and>
    (\<forall>R. (d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q \<longleftrightarrow>
      requirement_artifact_admitted D gs n R)"
proof -
  let ?P="requirement_artifact_system D gs n"
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q where compiled:
    "inj_on g (system_definitions ?P)" "closed_native_package_at E pu [] Q"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g ?P) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning ?P"
    using program_compilation_total[OF requirement_artifact_system_formed[where D=D and gs=gs and n=n]]
    by (elim exE conjE) (rule that; assumption)
  have member: "369\<in>system_definitions ?P" by simp
  have definitions: "system_definitions Q=g ` system_definitions ?P"
    using compiled(4) unfolding system_alpha_variant_def renamed_system_definitions by blast
  have native_member: "g 369\<in>system_definitions Q" using member definitions by blast
  have boundary: "closed_base_program E pu Q (g 369)"
    by (rule closed_base_program.intro[OF compiled(2,3) native_member])
  have exact: "(g 369,Target_Term (Whole_Artifact R))\<in>positive_meaning Q \<longleftrightarrow>
      requirement_artifact_admitted D gs n R" for R
    by (simp only: compiled_system_meaning_at[OF compiled(1) member compiled(5)]
      requirement_artifact_at_literal[OF finite])
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 369"])
    (use boundary exact in blast)
qed

theorem requirement_generation_installation:
  assumes source: "schema_system_formed P"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_base_program E pu Q d \<and>
    (\<forall>R. (d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q \<longleftrightarrow>
      requirement_artifact_admitted (system_definitions P) gs n R) \<and>
    (\<forall>R l previous. requirement_artifact_admitted (system_definitions P) gs n R \<longrightarrow>
      target_formed l \<longrightarrow> (\<forall>G\<in>fset previous. generation_formed G) \<longrightarrow>
      (\<exists>C. \<exists>A :: local_address option artifact_environment. \<exists>u F au H root.
        generation_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) \<and>
        generation_environment_closed A {(u,[])} \<and>
        generation_judgment_scope_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) F pu [] au [] \<and>
        F=native_judgment_environment F pu [] au [] \<and> native_package_environment F pu []=E \<and>
        recorded_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) R \<and>
        certified_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) H root R))"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d
    where program: "closed_base_program E pu Q d" and exact:
    "\<forall>R. (d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q \<longleftrightarrow>
      requirement_artifact_admitted (system_definitions P) gs n R"
    using closed_requirement_artifact_program[OF system_definitions_finite[OF source], where gs=gs and n=n] by blast
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ d])
    (use program exact closed_base_program.certified_generation[OF program] in blast)
qed

text \<open>
  The quantified program is chosen before all future artifacts, loci, and
  predecessor families. The complete source domain and the original request
  govern every payload admitted through that program. Its own candidate
  output cannot choose a replacement request or a different cause program.

  The artifact-installation theorem supplies the resulting program's exact
  requirement meaning. Generation construction and replay certification
  preserve that local result without asserting a full development protocol
  or the bootstrap handoff.
\<close>

end
