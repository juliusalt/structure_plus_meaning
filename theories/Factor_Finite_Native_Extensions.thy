theory Factor_Finite_Native_Extensions
  imports Factor_Finite_Code_Installation Factor_Finite_Root_Environments Factor_Finite_System_Agreement
    Factor_Native_Definition_Extensions Factor_Program_Scopes
    "HOL-Library.Product_Lexorder" "HOL-Library.List_Lexorder" "HOL-Library.Option_ord"
begin

section \<open>One finite operation builds and selects the complete extension\<close>

definition finite_native_extension_ready where
  "finite_native_extension_ready E P Q \<longleftrightarrow>
    finite_environment_formed E \<and> finite_system_formed P \<and> finite_system_formed Q \<and>
    finite_system_agrees_on P Q (finite_system_definitions P) \<and>
    fBall (finite_system_definitions Q |-| finite_system_definitions P) (\<lambda>d. snd d=[]) \<and>
    fimage fst (finite_system_definitions Q |-| finite_system_definitions P) |\<inter>| finite_environment_uses E={||}"

definition finite_extend_native :: "local_address option finite_artifact_environment\<Rightarrow>
    ('a::linorder,'s::linorder,local_address option definition_site,'c::linorder) finite_schema_system\<Rightarrow>
    ('a,'s,local_address option definition_site,'c) finite_schema_system\<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option) option" where
  "finite_extend_native E P Q=(if finite_native_extension_ready E P Q then
    map_option (\<lambda>rows. finite_select_roots (finite_install_code_rows E rows) (sorted_list_of_fset (finite_system_definitions Q)))
      (finite_compile_definitions Q (sorted_list_of_fset (finite_system_definitions Q |-| finite_system_definitions P)))
    else None)"

locale finite_native_extension =
  fixes E :: "local_address option finite_artifact_environment"
    and P Q :: "('a::linorder,'s::linorder,local_address option definition_site,'c::linorder) finite_schema_system"
    and pu :: "local_address option" and pr :: local_address
    and N :: "local_address option native_system"
  assumes native: "native_package_at (decode_finite_environment E) pu pr N"
    and source_variant: "system_alpha_variant (decode_finite_system P) N"
    and target: "finite_system_formed Q"
    and agreement: "systems_agree_on (decode_finite_system P) (decode_finite_system Q)
      (system_definitions (decode_finite_system P))"
    and roots: "\<forall>d\<in>fset (finite_system_definitions Q)-fset (finite_system_definitions P). snd d=[]"
    and fresh: "image fst (fset (finite_system_definitions Q)-fset (finite_system_definitions P))\<inter>
      fset (finite_environment_uses E)={}"
begin

abbreviation source where "source \<equiv> decode_finite_system P"
abbreviation goal where "goal \<equiv> decode_finite_system Q"
abbreviation additions where "additions \<equiv> finite_system_definitions Q |-| finite_system_definitions P"
abbreviation ds where "ds \<equiv> sorted_list_of_fset additions"
abbreviation selected where "selected \<equiv> sorted_list_of_fset (finite_system_definitions Q)"

lemma source_formed: "schema_system_formed source" using source_variant by (simp add: system_alpha_variant_def)
lemma goal_formed: "schema_system_formed goal" using target by (simp only: finite_system_formed_correct)
lemma environment: "finite_environment_formed E"
  using native_package_projection(1)[OF native]
  by (simp add: native_package_formed_def finite_environment_formed_correct)
lemma source_definitions: "system_definitions source=system_definitions N"
  using source_variant by (simp add: system_alpha_variant_def)
lemma source_inside: "system_definitions source\<subseteq>system_definitions goal"
  by (rule whole_agreement_definitions[OF agreement])
lemma old_positions: "system_definitions source\<subseteq>environment_positions (decode_finite_environment E)"
  using native_package_entry_position[OF native] by (simp only: source_definitions; blast)
lemma new_definitions: "set ds=system_definitions goal-system_definitions source"
  by (simp add: finite_system_definitions_correct)
lemma members: "set ds\<subseteq>fset (finite_system_definitions Q)" by auto

lemma ready: "finite_native_extension_ready E P Q"
  using environment source_formed target agreement roots fresh
  by (auto simp: finite_native_extension_ready_def finite_system_formed_correct
    finite_system_agrees_on_correct finite_system_definitions_correct fset_inject[symmetric])

lemma addresses: "\<forall>d\<in>system_definitions goal. octets_formed (snd d)"
proof (intro ballI)
  fix d assume member: "d\<in>system_definitions goal"
  show "octets_formed (snd d)"
  proof (cases "d\<in>system_definitions source")
    case True
    have ef: "environment_formed (decode_finite_environment E)" using environment by (simp only: finite_environment_formed_correct)
    show ?thesis by (rule environment_position_address[OF ef]) (use old_positions True in blast)
  next
    case False
    have empty: "snd d=[]" using roots member False by (simp only: finite_system_definitions_correct; blast)
    show ?thesis by (simp add: empty octets_formed_def)
  qed
qed

theorem total: "\<exists>F u. finite_extend_native E P Q=Some (F,u)"
proof -
  obtain rows where compiled: "finite_compile_definitions Q ds=Some rows"
    using finite_compile_definitions_total[OF target members addresses] by blast
  show ?thesis by (simp add: finite_extend_native_def ready compiled)
qed

theorem correct:
  assumes result: "finite_extend_native E P Q=Some (F,u)"
  shows "finite_environment_formed F \<and>
    environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr N \<and>
    (\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_definitions T=system_definitions goal \<and> system_alpha_variant goal T \<and>
      positive_meaning T=positive_meaning goal \<and>
      (\<forall>d t. schema_call_formed T d t \<longleftrightarrow> schema_call_formed goal d t)) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
proof -
  obtain rows where compiled: "finite_compile_definitions Q ds=Some rows"
    and selection: "finite_select_roots (finite_install_code_rows E rows) selected=(F,u)"
    using result by (auto simp: finite_extend_native_def ready split: option.splits)
  let ?H="finite_install_code_rows E rows"
  let ?K="\<lambda>d. decode_finite_definition_code (the (map_of rows d))"
  let ?H'="decode_finite_environment ?H"
  let ?F="decode_finite_environment F"
  have unique: "distinct ds" by simp
  have at_roots: "\<forall>d\<in>set ds. snd d=[]" using roots by simp
  have separate: "image fst (set ds)\<inter>fset (finite_environment_uses E)={}" using fresh by simp
  have old: "system_definitions goal-set ds\<subseteq>environment_positions (decode_finite_environment E)"
    using old_positions by (simp only: new_definitions; blast)
  have built: "finite_environment_formed ?H" "environment_included (decode_finite_environment E) ?H'"
    "\<forall>d\<in>set ds. definition_code_for (system_interface goal d) (system_clause_family goal d) (?K d) \<and>
      native_definition_at ?H' (fst d) (snd d) (code_interface (?K d)) (code_clauses (?K d))"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A. artifact_at ?H' w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v. binds_slot ?H' w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v"
    using finite_install_code_rows_correct[OF environment target members unique at_roots separate old compiled]
    by (simp only: Let_def decode_finite_definition_code_def definition_code.select_convs; blast)+
  have hf: "environment_formed ?H'" using built(1) by (simp only: finite_environment_formed_correct)
  have copied: "native_package_at ?H' pu pr N" by (rule native_package_included[OF native built(2) hf])
  interpret content: native_definition_extension ?H' source goal pu pr N ?K
    by (rule native_definition_extension.intro[OF copied source_variant goal_formed agreement])
      (use built(3) in \<open>simp only: new_definitions; blast\<close>)+
  have positions: "set selected\<subseteq>environment_positions ?H'"
    using native_package_sites(1)[OF content.package_formed]
    by (simp only: content.sites sorted_list_of_fset_simps finite_system_definitions_correct)
  have selected: "finite_environment_formed F" "environment_included ?H' ?F"
    "native_root_family_at ?F u [] (set (zip (family_ports (length selected)) selected))"
    "rel_ran (set (zip (family_ports (length selected)) selected))=system_definitions goal"
    "\<forall>w\<in>fset (finite_environment_uses ?H). \<forall>A. artifact_at ?F w A \<longleftrightarrow> artifact_at ?H' w A"
    "\<forall>w\<in>fset (finite_environment_uses ?H). \<forall>k v. binds_slot ?F w k v \<longleftrightarrow> binds_slot ?H' w k v"
    using finite_select_roots_correct[OF built(1) positions selection]
    by (simp only: sorted_list_of_fset_simps finite_system_definitions_correct; blast)+
  have ff: "environment_formed ?F" using selected(1) by (simp only: finite_environment_formed_correct)
  have included: "environment_included (decode_finite_environment E) ?F"
    by (rule environment_included_trans[OF built(2) selected(2)])
  have original: "native_package_at ?F pu pr N" by (rule native_package_included[OF native included ff])
  let ?T="native_program ?H' (system_definitions goal)"
  have kept: "native_package_formed ?F (system_definitions goal) \<and> native_program ?F (system_definitions goal)=?T"
    by (rule native_dependency_package_included[OF content.package_formed selected(2) ff])
  have package: "native_package_at ?F u [] ?T"
    unfolding native_package_at_def
    by (rule exI[of _ "set (zip (family_ports (length selected)) selected)"])
      (use selected(3,4) kept in auto)
  have definitions: "system_definitions ?T=system_definitions goal"
    by (simp only: native_program_definitions[OF content.package_formed] content.sites)
  have meaning: "positive_meaning ?T=positive_meaning goal"
    using system_alpha_positive_meaning[OF content.program_variant] by simp
  have calls: "\<forall>d t. schema_call_formed ?T d t \<longleftrightarrow> schema_call_formed goal d t"
    using system_alpha_calls[OF content.program_variant] by blast
  have target: "\<exists>T. native_package_at ?F u [] T \<and> system_definitions T=system_definitions goal \<and>
    system_alpha_variant goal T \<and> positive_meaning T=positive_meaning goal \<and>
    (\<forall>d t. schema_call_formed T d t \<longleftrightarrow> schema_call_formed goal d t)"
    by (rule exI[of _ ?T]) (use package definitions content.program_variant meaning calls in blast)
  have uses: "fset (finite_environment_uses E)\<subseteq>fset (finite_environment_uses ?H)"
    using included_uses[OF built(2)] by (simp only: finite_environment_uses_correct)
  show ?thesis using selected(1,5,6) included original target uses built(4,5) by blast
qed

end

text \<open>
  The operation checks formation, every old interface and clause, fresh uses,
  and the complete selected compilation. Its successful result is the actual
  constructed environment and selector. The source correspondence premise
  concerns the whole program recovered from the original native package.
  Under that premise the resulting native package has the complete target
  meaning, and every original artifact and outgoing binding is unchanged.
\<close>

end
