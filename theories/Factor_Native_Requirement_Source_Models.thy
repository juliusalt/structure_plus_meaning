theory Factor_Native_Requirement_Source_Models
  imports Factor_Requirement_Source_Examples Factor_Native_Program_Variants
begin

section \<open>Ordinary coordinates recover the actual complete source clauses\<close>

definition native_guard_source_coordinate :: "nat\<Rightarrow>local_address option definition_site" where
  "native_guard_source_coordinate d=(None,[Suc 0])"

definition nat_guard_source_clause :: "bool\<Rightarrow>(nat,nat,nat) factor_schema" where
  "nat_guard_source_clause b=rename_schema (\<lambda>_. 0) (\<lambda>_. 0) (\<lambda>_. 0)
    (decode_finite_schema (if b then finite_variable_schema else finite_equality_schema))"

definition nat_guard_source_model :: "bool\<Rightarrow>(nat,nat,nat,nat) schema_system" where
  "nat_guard_source_model b=\<lparr>system_interfaces={(0,data_x)},
    system_clauses={((0,0),nat_guard_source_clause b)}\<rparr>"

lemma nat_guard_source_model_definitions [simp]: "system_definitions (nat_guard_source_model b)={0}"
  by (auto simp: nat_guard_source_model_def system_definitions_def rel_dom_def)

lemma nat_guard_source_model_formed [simp]: "schema_system_formed (nat_guard_source_model b)"
  by (cases b; auto simp: nat_guard_source_model_def nat_guard_source_clause_def
    finite_variable_schema_def finite_equality_schema_def decode_finite_schema_def
    rename_schema_def map_socket_graph_def map_relation_values_def
    schema_system_formed_def schema_formed_def single_valued_def system_definitions_def
    schema_dependencies_def rel_dom_def rel_ran_def)

lemma nat_guard_source_coordinate_injective:
  "inj_on native_guard_source_coordinate (system_definitions (nat_guard_source_model b))"
  by simp

lemma nat_guard_source_schema_variant:
  "schema_alpha_variant (rename_schema id id native_guard_source_coordinate (nat_guard_source_clause b))
    (decode_finite_schema (if b then finite_variable_schema else finite_equality_schema))"
  unfolding schema_alpha_variant_def
  by (rule exI[of _ "\<lambda>_. [10]"], rule exI[of _ "\<lambda>_. []"])
    (cases b; auto simp: nat_guard_source_clause_def finite_variable_schema_def finite_equality_schema_def
      decode_finite_schema_def rename_schema_def map_socket_graph_def map_relation_values_def
      schema_variables_def schema_sockets_def rel_dom_def)

theorem nat_guard_source_model_variant:
  "system_alpha_variant (rename_system native_guard_source_coordinate (nat_guard_source_model b))
    (decode_finite_system (finite_guard_source_program b))"
proof -
  let ?P="rename_system native_guard_source_coordinate (nat_guard_source_model b)"
  let ?E="decode_finite_environment (finite_guard_source b)"
  let ?S="decode_finite_schema (if b then finite_variable_schema else finite_equality_schema)"
  let ?d="(None,[Suc 0])::local_address option definition_site"
  have formed: "schema_system_formed ?P"
    by (rule renamed_system_formed[OF nat_guard_source_model_formed nat_guard_source_coordinate_injective])
  have domain: "system_definitions ?P={?d}"
    by (simp add: renamed_system_definitions native_guard_source_coordinate_def)
  have interface: "system_interface ?P ?d=data_x"
    by (rule system_interface_unique[OF formed])
      (auto simp: renamed_system_interface native_guard_source_coordinate_def nat_guard_source_model_def)
  have clauses: "system_clause_family ?P ?d={(0,rename_schema id id native_guard_source_coordinate (nat_guard_source_clause b))}"
    by (auto simp: system_clause_family_def rename_system_def map_prod_def
      native_guard_source_coordinate_def nat_guard_source_model_def)
  show ?thesis
  proof (rule native_package_variant_from_readings[OF formed finite_guard_source_package[where b=b]])
    show "system_definitions ?P=system_definitions (decode_finite_system (finite_guard_source_program b))"
      by (simp only: domain finite_guard_source_definitions)
  next
    fix d assume member: "d\<in>system_definitions ?P"
    have site: "d=?d" using member by (simp only: domain; simp)
    have read: "native_definition_at ?E (fst d) (snd d) (Pattern_Variable [4]) {([7],?S)}"
      using finite_source_definition[where b=b] by (simp add: site)
    have family: "schema_family_variant (\<lambda>_. [7]) (system_clause_family ?P d) {([7],?S)}"
      by (simp only: site clauses schema_family_variant_singleton_iff)
        (use nat_guard_source_schema_variant[where b=b] in auto)
    show "\<exists>p C f h. native_definition_at ?E (fst d) (snd d) p C \<and>
      inj_on f (pattern_variables (system_interface ?P d)) \<and>
      p=rename_pattern f (system_interface ?P d) \<and>
      schema_family_variant h (system_clause_family ?P d) C"
      by (rule exI[of _ "Pattern_Variable [4]"], rule exI[of _ "{([7],?S)}"],
        rule exI[of _ "\<lambda>_. [4]"], rule exI[of _ "\<lambda>_. [7]"])
        (use read family in \<open>simp add: site interface\<close>)
  qed
qed

abbreviation native_guard_source_calls where
  "native_guard_source_calls b \<equiv> {(d,t). d=0 \<and>
    (native_guard_source_coordinate d,t)\<in>positive_meaning (decode_finite_system (finite_guard_source_program b))}"

lemma nat_guard_source_model_basis:
  "positive_meaning (nat_guard_source_model b)=native_guard_source_calls b"
  using system_variant_renamed_meaning_source[OF nat_guard_source_model_formed[where b=b]
    nat_guard_source_coordinate_injective[where b=b] nat_guard_source_model_variant[where b=b]] by simp

lemma nat_guard_source_model_meaning:
  "(0,t)\<in>positive_meaning (nat_guard_source_model b) \<longleftrightarrow>
    (if b then term_formed t else (\<exists>x. term_formed x \<and> t=Pair_Term x x))"
  by (simp only: nat_guard_source_model_basis; simp add: native_guard_source_coordinate_def finite_guard_source_meaning)

text \<open>
  The ordinary clause is a coordinate projection of the complete schema
  recovered from the actual finite source artifact. The proved whole-program
  variant recovers its complete interface and clause family. Equal definition
  domains therefore do not replace the source's actual variable or repeated
  variable clause. All source meanings follow through that correspondence.
\<close>

end
