theory Native_Control_Guard_Construction
  imports Native_Control_Guard_Transport Native_Control_Quotation_Representation
    Native_Control_Definition_Facts
begin

section \<open>Finite constructors retain every original schema field\<close>

definition finite_judgment_recognizer :: "finite_factor_term \<Rightarrow> ('a,'s,'d) finite_factor_schema" where
  "finite_judgment_recognizer t=finite_control_rule (finite_exact_term_pattern t) {||}"

lemma finite_judgment_recognizer_exact [simp]:
  "decode_finite_schema (finite_judgment_recognizer t)=
    recognizer_schema (exact_term_pattern (decode_finite_term t))"
  by (simp add: finite_judgment_recognizer_def finite_control_rule_def decode_finite_schema_def
    recognizer_schema_def map_relation_values_def)

definition finite_judgment_clauses :: "finite_factor_term list \<Rightarrow>
    (nat\<times>(nat,nat,nat) finite_factor_schema) fset" where
  "finite_judgment_clauses xs=fset_of_list (map (\<lambda>i. (i,finite_judgment_recognizer (xs!i))) [0..<length xs])"

lemma finite_judgment_clauses_exact:
  "map_relation_values decode_finite_schema (fset (finite_judgment_clauses xs))=judgment_ground_clauses xs"
  by (simp add: finite_judgment_clauses_def judgment_ground_clauses_def map_relation_values_def
    fset_of_list.rep_eq image_image split_def)

definition finite_quoted_guard_schema where
  "finite_quoted_guard_schema=finite_schema_of (quoted_body_guard_schema 10 123 368)"

lemmas finite_quoted_guard_schema_code [code]=finite_quoted_guard_schema_def
  [unfolded quoted_body_guard_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma finite_quoted_guard_schema_exact [simp]:
  "decode_finite_schema finite_quoted_guard_schema=quoted_body_guard_schema 10 123 368"
  unfolding finite_quoted_guard_schema_def by (rule decode_finite_schema_of) simp

definition finite_guard_constructor where
  "finite_guard_constructor xs=finite_add_view_definition
    (finite_add_view_definition finite_request_quotation_program 368 (Finite_Variable 0) (finite_judgment_clauses xs))
    369 (Finite_Variable 0) {|(0,finite_quoted_guard_schema)|}"

local_setup \<open>Native_Control_Definition_Facts.note @{binding original_artifact_system_definition}
  @{const_name quoted_judgment_rows.artifact_system}\<close>
local_setup \<open>Native_Control_Definition_Facts.note @{binding original_body_system_definition}
  @{const_name quoted_judgment_rows.body_system}\<close>

lemma finite_guard_constructor_exact:
  "decode_finite_system (finite_guard_constructor xs)=quoted_judgment_rows.artifact_system xs"
  unfolding finite_guard_constructor_def original_artifact_system_definition
    original_body_system_definition
  by (simp only: finite_add_view_definition_correct decode_finite_pattern.simps
      finite_request_quotation_program_exact finite_judgment_clauses_exact)
    (simp add: map_relation_values_def)


context quoted_judgment_rows
begin

lemma finite_guard_constructor_representation:
  "finite_guard_constructor xs=finite_quoted_judgment xs"
  by (simp only: decode_finite_system_injective[symmetric] finite_guard_constructor_exact finite_guard_exact)

lemma finite_guard_constructor_formed: "finite_system_formed (finite_guard_constructor xs)"
  by (simp only: finite_guard_constructor_representation finite_guard_formed)

end

section \<open>Placement and installation execute on the complete constructed target\<close>

definition finite_install_quoted_guard where
  "finite_install_quoted_guard E xs=(if finite_environment_formed E \<and> list_all finite_term_formed xs then
    (let Q=finite_guard_constructor xs; (F,u)=finite_select_roots E [];
      g=finite_program_coordinates F (finite_system_definitions (empty_installation_program::(nat,nat,nat,nat) finite_schema_system))
        (finite_system_definitions Q) (\<lambda>_. (None,[])) in
      map_option (\<lambda>(K,v). (g 369,K,v))
        (finite_extend_mapped_native F empty_installation_program Q (\<lambda>_. (None,[]))))
    else None)"

lemma finite_install_quoted_guard_total:
  assumes environment: "finite_environment_formed E" and rows: "list_all finite_term_formed xs"
  shows "\<exists>d K v. finite_install_quoted_guard E xs=Some (d,K,v)"
proof -
  obtain F u where selected: "finite_select_roots E []=(F,u)" by (cases "finite_select_roots E []") auto
  interpret install: finite_guard_installation xs E F u
    by (unfold_locales) (rule rows, rule environment, rule selected)
  obtain K v where built: "finite_extend_mapped_native F empty_installation_program (finite_quoted_judgment xs)
      (\<lambda>_. (None,[]))=Some (K,v)" using install.total by blast
  show ?thesis using environment rows
    by (simp add: finite_install_quoted_guard_def selected install.finite_guard_constructor_representation built)
qed

theorem finite_install_quoted_guard_correct:
  assumes installed: "finite_install_quoted_guard E xs=Some (d,K,v)"
  obtains T where "finite_environment_formed E" "list_all finite_term_formed xs"
    "finite_environment_formed K"
    "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    "native_package_at (decode_finite_environment K) v [] T"
    "\<And>z. (d,z)\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set xs)"
proof -
  obtain F u where selected: "finite_select_roots E []=(F,u)" by (cases "finite_select_roots E []") auto
  let ?g="finite_program_coordinates F (finite_system_definitions (empty_installation_program::(nat,nat,nat,nat) finite_schema_system))
    (finite_system_definitions (finite_guard_constructor xs)) (\<lambda>_. (None,[]))"
  have environment: "finite_environment_formed E" and rows: "list_all finite_term_formed xs"
    and entry: "d=?g 369"
    and built: "finite_extend_mapped_native F empty_installation_program (finite_guard_constructor xs)
      (\<lambda>_. (None,[]))=Some (K,v)"
    using installed by (auto simp: finite_install_quoted_guard_def selected Let_def split: if_splits option.splits)
  interpret install: finite_guard_installation xs E F u
    by (unfold_locales) (rule rows, rule environment, rule selected)
  have built': "finite_extend_mapped_native F empty_installation_program (finite_quoted_judgment xs)
      (\<lambda>_. (None,[]))=Some (K,v)"
    using built by (simp only: install.finite_guard_constructor_representation)
  obtain T where k: "finite_environment_formed K"
    and preserve: "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    and native: "native_package_at (decode_finite_environment K) v [] T"
    and meaning: "\<And>z. (install.placement 369,z)\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set xs)"
    by (rule install.installed_guard[OF built']) blast
  have actual_entry: "d=install.placement 369"
    using entry by (simp only: install.finite_guard_constructor_representation)
  show thesis by (rule that[OF environment rows k preserve native]) (simp only: actual_entry meaning)
qed


end
