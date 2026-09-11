theory Factor_Assembly_Clauses
  imports Factor_Assembly_Components Factor_List_Folds Factor_Related_List_Maps
    Factor_Reader_Clauses Factor_Artifact_Difference
begin

section \<open>One shared origin table transports each actual piece occurrence\<close>

definition assembly_tag_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_tag_schema=data_rule (context_relation_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)))
    {}"

definition assembly_incidence_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_incidence_schema=data_rule (context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Pair (Pattern_Variable 2) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 4))) (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))))
    {(0,5,(Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 2)) (Pattern_Variable 5)) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 8)))),
     (1,5,(Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 3)) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 9)))),
     (2,5,(Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 4)) (Pattern_Variable 7)) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 10))))}"

definition assembly_attachment_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_attachment_schema=data_rule (context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)) (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 3)))
    {(0,5,(Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 2)) (Pattern_Variable 4)) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 5))))}"

definition assembly_piece_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_piece_schema=data_rule (context_relation_pattern (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (artifact_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5))) (artifact_fields_pattern (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)))
    {(0,221,(context_relation_pattern (Pattern_Variable 1) (Pattern_Variable 2) (Pattern_Variable 6))),
     (1,223,(context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 3) (Pattern_Variable 7))),
     (2,225,(context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 4) (Pattern_Variable 8))),
     (3,225,(context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 5) (Pattern_Variable 9)))}"

definition assembly_fields_append_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_fields_append_schema=data_rule (collection_join_pattern (artifact_fields_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2) (Pattern_Variable 3)) (artifact_fields_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (artifact_fields_pattern (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)))
    {(0,46,(collection_join_pattern (Pattern_Variable 0) (Pattern_Variable 4) (Pattern_Variable 8))),
     (1,46,(collection_join_pattern (Pattern_Variable 1) (Pattern_Variable 5) (Pattern_Variable 9))),
     (2,46,(collection_join_pattern (Pattern_Variable 2) (Pattern_Variable 6) (Pattern_Variable 10))),
     (3,46,(collection_join_pattern (Pattern_Variable 3) (Pattern_Variable 7) (Pattern_Variable 11)))}"

definition assembly_report_schema :: "(nat,nat,nat) factor_schema" where
  "assembly_report_schema=data_rule (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (artifact_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5)))
    {(0,213,(Pattern_Variable 0)),
     (1,216,(Pattern_Variable 1)),
     (2,11,(artifact_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5))),
     (3,227,(context_relation_pattern (Pattern_Variable 1) (Pattern_Variable 0) (Pattern_Variable 6))),
     (4,229,(collection_join_pattern (artifact_fields_pattern (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload [])) (Pattern_Variable 6) (artifact_fields_pattern (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10)))),
     (5,51,(Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 11))),
     (6,219,(Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 7))),
     (7,59,(Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 12))),
     (8,219,(Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 2))),
     (9,219,(Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 3))),
     (10,6,(Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 4))),
     (11,219,(Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 5)))}"

lemmas assembly_schema_defs = assembly_tag_schema_def assembly_incidence_schema_def assembly_attachment_schema_def
  assembly_piece_schema_def assembly_fields_append_schema_def assembly_report_schema_def
  related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def
  list_fold_clauses_def list_fold_nil_schema_def list_fold_step_schema_def reader_projection_clause_def

definition assembly_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "assembly_clause_family d=(if d=220 then {(0,assembly_tag_schema)}
    else if d=221 then related_list_clauses 220 221
    else if d=222 then {(0,assembly_incidence_schema)}
    else if d=223 then related_list_clauses 222 223
    else if d=224 then {(0,assembly_attachment_schema)}
    else if d=225 then related_list_clauses 224 225
    else if d=226 then {(0,assembly_piece_schema)}
    else if d=227 then related_list_clauses 226 227
    else if d=228 then {(0,assembly_fields_append_schema)}
    else if d=229 then list_fold_clauses 228 229
    else if d=230 then {(0,assembly_report_schema)}
    else if d=231 then {(0,reader_projection_clause 0 1 0 230)} else {})"

section \<open>The actual external callees select the least complete base\<close>

definition assembly_group_system :: "(nat,nat,nat,nat) schema_system" where
  "assembly_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{220,221,222,223,224,225,226,227,228,229,230,231}},
    system_clauses={((d,c),S). d\<in>{220,221,222,223,224,225,226,227,228,229,230,231} \<and> (c,S)\<in>assembly_clause_family d}\<rparr>"

lemma assembly_group_definitions [simp]:
  "system_definitions assembly_group_system={220,221,222,223,224,225,226,227,228,229,230,231}"
  by (auto simp: assembly_group_system_def system_definitions_def rel_dom_def)

lemma assembly_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces assembly_group_system \<longleftrightarrow>
    d\<in>system_definitions assembly_group_system \<and> p=Pattern_Variable 0"
  by (simp only: assembly_group_definitions; auto simp: assembly_group_system_def)

lemma assembly_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses assembly_group_system \<longleftrightarrow>
    d\<in>system_definitions assembly_group_system \<and> (c,S)\<in>assembly_clause_family d"
  by (simp only: assembly_group_definitions; auto simp: assembly_group_system_def)

lemma assembly_group_formed_over:
  "schema_system_formed_over {5,6,11,46,51,59,213,216,219} assembly_group_system"
proof -
  have family_finite: "finite (assembly_clause_family d)" for d
    by (simp add: assembly_clause_family_def related_list_clauses_def list_fold_clauses_def)
  have family_functional: "single_valued (assembly_clause_family d)" for d
    by (auto simp: assembly_clause_family_def related_list_clauses_def list_fold_clauses_def
      single_valued_def split: if_splits)
  have family_formed: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{5,6,11,46,51,59,213,216,219}\<union>system_definitions assembly_group_system"
    if "(c,S)\<in>assembly_clause_family d" for c S d
    using that by (auto simp: assembly_clause_family_def assembly_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def
      octets_formed_def split: if_splits)
  show ?thesis
    by (rule schema_system_formed_over_families[where D="system_definitions assembly_group_system"
        and p="\<lambda>_. Pattern_Variable 0" and C=assembly_clause_family])
      (use family_finite family_functional family_formed in
        \<open>simp_all only: assembly_group_definitions; auto simp: assembly_group_system_def\<close>)+
qed

lemma assembly_external_dependencies:
  "system_external_dependencies assembly_group_system={5,6,11,46,51,59,213,216,219}"
proof -
  have bounded: "system_external_dependencies assembly_group_system\<subseteq>{5,6,11,46,51,59,213,216,219}"
    by (rule system_external_dependencies_boundary[OF assembly_group_formed_over])
  have reached: "e\<in>system_external_dependencies assembly_group_system"
    if "((d,c),S)\<in>system_clauses assembly_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions assembly_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses assembly_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3)
      by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have selection: "5\<in>system_external_dependencies assembly_group_system"
    by (rule reached[where d=222 and c=0 and S=assembly_incidence_schema])
      (auto simp: assembly_clause_family_def assembly_incidence_schema_def schema_dependencies_def rel_ran_image)
  have append: "46\<in>system_external_dependencies assembly_group_system"
    by (rule reached[where d=228 and c=0 and S=assembly_fields_append_schema])
      (auto simp: assembly_clause_family_def assembly_fields_append_schema_def schema_dependencies_def rel_ran_image)
  have report: "e\<in>system_external_dependencies assembly_group_system"
    if "e\<in>{6,11,51,59,213,216,219}" for e
    by (rule reached[where d=230 and c=0 and S=assembly_report_schema])
      (use that in \<open>auto simp: assembly_clause_family_def assembly_report_schema_def
        schema_dependencies_def rel_ran_image\<close>)
  show ?thesis using bounded selection append report by auto
qed

definition assembly_base_system :: "(nat,nat,nat,nat) schema_system" where
  "assembly_base_system=rooted_system assembly_components_system (system_external_dependencies assembly_group_system)"

lemma assembly_base_formed [simp]: "schema_system_formed assembly_base_system"
  unfolding assembly_base_system_def by (rule rooted_system_formed[OF assembly_components_formed])

lemma assembly_base_subdomain:
  "system_definitions assembly_base_system\<subseteq>system_definitions assembly_components_system"
  unfolding assembly_base_system_def by (rule rooted_system_subdomain)

lemma assembly_base_roots:
  "{5,6,11,46,51,59,213,216,219}\<subseteq>system_definitions assembly_base_system"
  unfolding assembly_base_system_def assembly_external_dependencies
  by (rule rooted_system_roots[OF assembly_components_formed]) auto

lemma assembly_base_least:
  assumes "{5,6,11,46,51,59,213,216,219}\<subseteq>U" "system_dependency_closed assembly_components_system U"
  shows "system_definitions assembly_base_system\<subseteq>U"
  unfolding assembly_base_system_def assembly_external_dependencies
  by (rule rooted_system_least[OF assembly_components_formed _ assms]) auto

lemma assembly_base_call:
  "schema_call_formed assembly_base_system d t \<longleftrightarrow>
    d\<in>system_definitions assembly_base_system \<and> term_formed t"
  unfolding assembly_base_system_def
  by (rule rooted_system_variable_calls[OF assembly_components_formed assembly_components_call])

interpretation assembly_group: positive_definition_group assembly_base_system assembly_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF assembly_group_formed_over assembly_base_roots]
      assembly_base_subdomain in auto)

definition assembly_checking_system :: "(nat,nat,nat,nat) schema_system" where
  "assembly_checking_system=system_union assembly_base_system assembly_group_system"

lemma assembly_checking_system_formed [simp]: "schema_system_formed assembly_checking_system"
  using assembly_group.formed by (simp only: assembly_checking_system_def)

lemma assembly_checking_definitions [simp]:
  "system_definitions assembly_checking_system=system_definitions assembly_base_system\<union>system_definitions assembly_group_system"
  by (simp add: assembly_checking_system_def)

lemma assembly_checking_call:
  "schema_call_formed assembly_checking_system d t \<longleftrightarrow>
    d\<in>system_definitions assembly_checking_system \<and> term_formed t"
  unfolding assembly_checking_system_def
  by (rule assembly_group.variable_calls[OF assembly_base_call assembly_group_interfaces])

lemma assembly_checking_clause:
  assumes "d\<in>system_definitions assembly_group_system"
  shows "((d,c),S)\<in>system_clauses assembly_checking_system \<longleftrightarrow> (c,S)\<in>assembly_clause_family d"
  using assembly_group.group_clauses[OF assms] assms by (simp add: assembly_checking_system_def)

lemma assembly_previous_meaning:
  assumes "d\<in>{5,6,11,46,51,59,213,216,219}"
  shows "(d,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning assembly_components_system"
proof -
  have member: "d\<in>system_definitions assembly_base_system" using assembly_base_roots assms by blast
  show ?thesis using assembly_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF assembly_components_formed member[unfolded assembly_base_system_def], of t]
    by (simp only: assembly_checking_system_def assembly_base_system_def; blast)
qed

interpretation assembly_tags: related_list_profile assembly_checking_system 220 221
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

interpretation assembly_edges: related_list_profile assembly_checking_system 222 223
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

interpretation assembly_attachments: related_list_profile assembly_checking_system 224 225
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

interpretation assembly_piece_list: related_list_profile assembly_checking_system 226 227
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

interpretation assembly_fields_fold: list_fold_profile assembly_checking_system 228 229
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

interpretation assembly_source: reader_projection_profile assembly_checking_system 231 230 0 1 0 0
  by (unfold_locales) (auto simp: assembly_checking_clause assembly_clause_family_def assembly_checking_call)

text \<open>
  Twelve definitions contain seventeen ordinary clauses. Four complete
  correspondence traversals and one right fold reuse the existing general
  profiles. The incidence and attachment steps consult one shared actual
  origin table; each occurrence has its own premise socket and private
  selection remainder. Counted and functional attachments share that step.

  The report calls complete piece-table, origin-table, and output admission,
  even for empty inputs. It compares the whole copied carrier with origin
  keys, origin values with output atoms, and every pushed field with its
  output counterpart. Counted attachments use bag comparison; the other
  fields use set comparison. Source admission projects an actual full report.

  The base is the least closure of the nine actual external callees. All
  component interfaces, clauses, and native meanings remain accounted for.
  These clauses specify the implementation; the following local contracts
  establish its correspondence with the complete assembly relation.
\<close>

end
