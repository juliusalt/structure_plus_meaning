theory Factor_Finite_Ground_Source
  imports Factor_Finite_Exact_Patterns Factor_Finite_Relations Factor_Finite_View_Installation Factor_Finite_Source_Entry_Installation Factor_Requirement_Source_Examples_Base
begin

definition finite_ground_rule :: "finite_factor_term \<Rightarrow>
    (local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "finite_ground_rule t=\<lparr>finite_schema_conclusion=finite_exact_term_pattern t,
    finite_schema_premises={||},finite_schema_materials={||}\<rparr>"

lemma finite_ground_rule_correct [simp]:
  "decode_finite_schema (finite_ground_rule t)=recognizer_schema (exact_term_pattern (decode_finite_term t))"
  by (simp add: finite_ground_rule_def decode_finite_schema_def recognizer_schema_def map_relation_values_def)

definition finite_ground_clauses where
  "finite_ground_clauses xs=fset_of_list (map (\<lambda>i. ([i],finite_ground_rule (xs!i))) [0..<length xs])"

definition ground_clause_family :: "finite_factor_term list \<Rightarrow>
    (local_address\<times>local_address option native_schema) set" where
  "ground_clause_family xs=(\<lambda>i. ([i],recognizer_schema (exact_term_pattern (decode_finite_term (xs!i)))))
    ` {0..<length xs}"

lemma finite_ground_clauses_correct:
  "map_relation_values decode_finite_schema (fset (finite_ground_clauses xs))=ground_clause_family xs"
  by (simp add: finite_ground_clauses_def ground_clause_family_def map_relation_values_def
    fset_of_list.rep_eq image_image split_def)

lemma ground_clause_view:
  assumes source: "schema_system_formed P" and fresh: "e\<notin>system_definitions P"
    and formed: "list_all finite_term_formed xs"
  shows "positive_view P e (Pattern_Variable []) (ground_clause_family xs)"
proof (rule positive_view.intro[OF source fresh])
  show "pattern_formed (Pattern_Variable [])" by simp
  show "finite (ground_clause_family xs)" by (simp add: ground_clause_family_def)
  show "single_valued (ground_clause_family xs)"
    by (auto simp: ground_clause_family_def single_valued_def)
  show "\<forall>c S. (c,S)\<in>ground_clause_family xs \<longrightarrow> schema_formed S"
    using formed by (auto simp: ground_clause_family_def list_all_iff finite_term_formed_correct
      recognizer_schema_def schema_formed_def single_valued_def)
  show "\<forall>c S. (c,S)\<in>ground_clause_family xs \<longrightarrow> schema_dependencies S\<subseteq>system_definitions P"
    by (auto simp: ground_clause_family_def recognizer_schema_def schema_dependencies_def rel_ran_def)
qed

definition finite_ground_program :: "finite_factor_term list \<Rightarrow> local_address option finite_native_system" where
  "finite_ground_program xs=finite_add_view_definition (finite_guard_source_program True)
    (Some [],[]) (Finite_Variable []) (finite_ground_clauses xs)"

lemma ground_program_view:
  "list_all finite_term_formed xs \<Longrightarrow>
    positive_view (decode_finite_system (finite_guard_source_program True)) (Some [],[])
      (Pattern_Variable []) (ground_clause_family xs)"
  by (rule ground_clause_view[OF native_package_system_formed[OF finite_guard_source_package]]) simp_all

lemma finite_ground_program_correct:
  "decode_finite_system (finite_ground_program xs)=
    add_view_definition (decode_finite_system (finite_guard_source_program True)) (Some [],[])
      (Pattern_Variable []) (ground_clause_family xs)"
  by (simp add: finite_ground_program_def finite_ground_clauses_correct)

lemma finite_ground_program_entry:
  "(Some [],[]) |\<in>| finite_system_definitions (finite_ground_program xs)"
  by (simp add: finite_ground_program_def finite_system_definitions_def finite_add_view_definition_def)

lemma exact_recognizer_rule:
  "schema_rule_instance (recognizer_schema (exact_term_pattern x)) X t \<longleftrightarrow> term_formed x \<and> t=x"
  by (simp only: schema_rule_instance_def exact_recognizer_instance;
    simp add: schema_material_satisfied_def recognizer_schema_def)

lemma ground_clause_family_rule:
  assumes formed: "list_all finite_term_formed xs"
  shows "(\<exists>c S. (c,S)\<in>ground_clause_family xs \<and> schema_rule_instance S X t)
    \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof
  assume rule: "\<exists>c S. (c,S)\<in>ground_clause_family xs \<and> schema_rule_instance S X t"
  then obtain i where bound: "i<length xs" and same: "t=decode_finite_term (xs!i)"
    by (auto simp: ground_clause_family_def exact_recognizer_rule)
  show "t\<in>decode_finite_term ` set xs"
    unfolding same by (rule imageI, rule nth_mem[OF bound])
next
  assume member: "t\<in>decode_finite_term ` set xs"
  then obtain x where inside: "x\<in>set xs" and same: "t=decode_finite_term x" by blast
  obtain i where bound: "i<length xs" and index: "x=xs!i"
    using inside by (auto simp: in_set_conv_nth; blast)
  let ?S="recognizer_schema (exact_term_pattern (decode_finite_term (xs!i))) :: local_address option native_schema"
  have clause: "([i],?S)\<in>ground_clause_family xs"
    unfolding ground_clause_family_def by (rule imageI) (use bound in auto)
  have wellformed: "term_formed (decode_finite_term x)"
    using formed inside by (auto simp: list_all_iff finite_term_formed_correct)
  have actual: "schema_rule_instance ?S X t"
    using wellformed same by (simp only: exact_recognizer_rule index; blast)
  show "\<exists>c S. (c,S)\<in>ground_clause_family xs \<and> schema_rule_instance S X t"
    by (rule exI[of _ "[i]"], rule exI[of _ ?S], rule conjI[OF clause actual])
qed

lemma finite_ground_program_meaning:
  assumes formed: "list_all finite_term_formed xs"
  shows "((Some [],[]),t)\<in>positive_meaning (decode_finite_system (finite_ground_program xs))
    \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof -
  interpret ground: positive_view "decode_finite_system (finite_guard_source_program True)" "(Some [],[])"
    "Pattern_Variable []" "ground_clause_family xs" by (rule ground_program_view[OF formed])
  show ?thesis
    using formed by (simp only: finite_ground_program_correct ground.view_meaning ground_clause_family_rule[OF formed];
      auto simp: list_all_iff finite_term_formed_correct)
qed

lemma finite_ground_source_context:
  assumes formed: "list_all finite_term_formed xs"
  shows "finite_source_extension_context (finite_guard_source True) None [0] (finite_ground_program xs)=
    Some (finite_guard_source_program True)"
proof -
  interpret ground: positive_view "decode_finite_system (finite_guard_source_program True)" "(Some [],[])"
    "Pattern_Variable []" "ground_clause_family xs" by (rule ground_program_view[OF formed])
  show ?thesis using finite_guard_source_package[where b=True] ground.formed ground.old_agreement
    by (simp only: finite_source_extension_context_correct finite_ground_program_correct; blast)
qed

definition finite_ground_source where
  "finite_ground_source xs=(if list_all finite_term_formed xs then
    finite_install_source_entry (finite_guard_source True) None [0] (finite_ground_program xs) (Some [],[]) else None)"

theorem finite_ground_source_total:
  "(\<exists>d F u. finite_ground_source xs=Some (d,F,u)) \<longleftrightarrow> list_all finite_term_formed xs"
  using finite_install_source_entry_total[of "finite_guard_source True" None "[0]" "finite_ground_program xs" "(Some [],[])"]
    finite_ground_source_context[of xs]
  by (auto simp: finite_ground_source_def finite_ground_program_entry split: if_splits)

theorem finite_ground_source_meaning:
  assumes installed: "finite_ground_source xs=Some (d,F,u)"
  obtains P where "native_package_at (decode_finite_environment F) u [] P"
    "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof -
  have formed: "list_all finite_term_formed xs" and result:
    "finite_install_source_entry (finite_guard_source True) None [0] (finite_ground_program xs) (Some [],[])=Some (d,F,u)"
    using installed by (auto simp: finite_ground_source_def split: if_splits)
  obtain P where native: "native_package_at (decode_finite_environment F) u [] P" and exact:
    "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow>
      ((Some [],[]),t)\<in>positive_meaning (decode_finite_system (finite_ground_program xs))"
    using finite_install_source_entry_correct[OF result finite_ground_source_context[OF formed]] by blast
  show thesis by (rule that[OF native]) (use exact finite_ground_program_meaning[OF formed] in blast)
qed

text \<open>The reusable construction installs ordinary ground clauses with distinct
  occurrence keys, including repeated values. Its only semantic claim is exact
  membership of the declared term family. A later computed-observation use must
  separately prove where that family came from and what its members mean.\<close>

end
