theory Factor_Schema_Socket_Investigation
  imports Factor_Clause_Specialization_Instances Finite_Investigation_Interface
begin

section \<open>Rule meaning and exact substitution have different socket requirements\<close>

definition socket_investigation_schema :: "nat \<Rightarrow> local_address option native_schema" where
  "socket_investigation_schema c=rename_schema id (\<lambda>_. if c=0 then [18] else [19]) id native_incidence_schema"

lemma socket_investigation_fields:
  "schema_conclusion (socket_investigation_schema c)=schema_conclusion native_incidence_schema"
  "schema_premises (socket_investigation_schema c)={}"
  "schema_material_premises (socket_investigation_schema c)={(if c=0 then [18] else [19],native_incidence_material)}"
  "schema_sockets (socket_investigation_schema c)={if c=0 then [18] else [19]}"
  by (simp_all add: socket_investigation_schema_def native_incidence_schema_def rename_schema_def
    rename_material_pattern_def material_fields_def map_socket_graph_def schema_sockets_def rel_dom_def)

lemma socket_investigation_formed: "schema_formed (socket_investigation_schema c)"
  unfolding socket_investigation_schema_def
  by (rule renamed_schema_formed[OF native_schema_formed[OF incidence_schema_at]])
    (simp add: native_incidence_schema_def schema_sockets_def rel_dom_def inj_on_def)

theorem socket_investigation_rule_meaning:
  "schema_rule_instance (socket_investigation_schema c) X t \<longleftrightarrow> schema_rule_instance native_incidence_schema X t"
  unfolding socket_investigation_schema_def
  by (rule schema_rule_instance_alpha)
    (simp_all add: native_incidence_schema_def schema_sockets_def rel_dom_def inj_on_def)

lemma socket_investigation_unkeyed_materials:
  "rel_ran (evaluate_schema_materials v (socket_investigation_schema c))=
    rel_ran (evaluate_schema_materials v native_incidence_schema)"
  by (simp add: evaluate_schema_materials_def socket_investigation_fields native_incidence_schema_def rel_ran_def)

definition socket_investigation_compare :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "socket_investigation_compare c d \<longleftrightarrow>
    (\<exists>s. socket_investigation_schema d=schema_substitute s (socket_investigation_schema c))"

lemma socket_investigation_compare_code [code]:
  "socket_investigation_compare c d=((c=0)=(d=0))"
proof
  assume compared: "socket_investigation_compare c d"
  obtain s where substitution: "socket_investigation_schema d=schema_substitute s (socket_investigation_schema c)"
    using compared by (simp only: socket_investigation_compare_def; blast)
  have sockets: "schema_sockets (socket_investigation_schema d)=schema_sockets (socket_investigation_schema c)"
    by (simp only: substitution schema_substitute_sockets)
  show "(c=0)=(d=0)" using sockets by (simp only: socket_investigation_fields; auto split: if_splits)
next
  assume same: "(c=0)=(d=0)"
  have schemas: "socket_investigation_schema d=socket_investigation_schema c"
    using same by (simp add: socket_investigation_schema_def)
  show "socket_investigation_compare c d" unfolding socket_investigation_compare_def
    by (rule exI[of _ Pattern_Variable]) (simp only: schema_substitute_identity schemas)
qed

definition socket_investigation_observation :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "socket_investigation_observation f c=
    (if f=0 then if schema_conclusion (socket_investigation_schema c)=schema_conclusion native_incidence_schema then 0 else 1
     else if f=1 then if (\<forall>v. rel_ran (evaluate_schema_materials v (socket_investigation_schema c))=
       rel_ran (evaluate_schema_materials v native_incidence_schema)) then 0 else 1
     else if [18]\<in>schema_sockets (socket_investigation_schema c) then 18 else 19)"

lemma socket_investigation_observation_code [code]:
  "socket_investigation_observation f c=(if f=0 \<or> f=1 then 0 else if c=0 then 18 else 19)"
  by (simp add: socket_investigation_observation_def socket_investigation_fields socket_investigation_unkeyed_materials)

theorem socket_investigation_observation_exact:
  "socket_investigation_observation f c=socket_investigation_observation f d \<longleftrightarrow>
    (if f=0 then schema_conclusion (socket_investigation_schema c)=schema_conclusion (socket_investigation_schema d)
     else if f=1 then (\<forall>v. rel_ran (evaluate_schema_materials v (socket_investigation_schema c))=
       rel_ran (evaluate_schema_materials v (socket_investigation_schema d)))
     else schema_sockets (socket_investigation_schema c)=schema_sockets (socket_investigation_schema d))"
  by (auto simp: socket_investigation_observation_code socket_investigation_fields socket_investigation_unkeyed_materials)

definition schema_sockets_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "schema_sockets_investigation_observations=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,socket_investigation_observation f c)) [0,1,2]) [0,1])"

definition schema_sockets_investigation_relation :: "(nat\<times>nat) list" where
  "schema_sockets_investigation_relation=filter (\<lambda>(c,d). socket_investigation_compare c d) (investigation_pairs [0,1])"

lemma schema_sockets_observations_literal:
  "schema_sockets_investigation_observations=[(0,0,0),(1,0,0),(2,0,18),(0,1,0),(1,1,0),(2,1,19)]"
  by (simp add: schema_sockets_investigation_observations_def socket_investigation_observation_code)

lemma schema_sockets_relation_literal: "schema_sockets_investigation_relation=[(0,0),(1,1)]"
  by (simp add: schema_sockets_investigation_relation_def investigation_pairs_def socket_investigation_compare_code)

lemma schema_sockets_observations_exact:
  "finite_table_observations (fset_of_list schema_sockets_investigation_observations) f c=
    (if f\<in>{0,1,2} \<and> c\<in>{0,1} then {socket_investigation_observation f c} else {})"
  by (auto simp: finite_table_observations_def schema_sockets_investigation_observations_def)

lemma schema_sockets_relation_exact:
  "(c,d)\<in>set schema_sockets_investigation_relation \<longleftrightarrow>
    c\<in>{0,1} \<and> d\<in>{0,1} \<and>
    (\<exists>s. socket_investigation_schema d=schema_substitute s (socket_investigation_schema c))"
  by (simp only: schema_sockets_investigation_relation_def set_filter mem_Collect_eq split_conv
    investigation_pairs_exact mem_Times_iff socket_investigation_compare_def set_simps conj_assoc fst_conv snd_conv)

definition schema_sockets_investigation where
  "schema_sockets_investigation selected=investigation_basis [0,1] [0,1,2] selected
    schema_sockets_investigation_observations schema_sockets_investigation_relation"

theorem schema_sockets_unkeyed_comparisons_remain:
  "fst (schema_sockets_investigation [0,1]) \<and>
    set (fst (snd (schema_sockets_investigation [0,1])))={(0,1),(1,0)}"
  by (simp add: schema_sockets_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def schema_sockets_observations_literal schema_sockets_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def; blast)

theorem schema_sockets_keyed_comparisons_complete:
  "fst (schema_sockets_investigation [0,1,2]) \<and> fst (snd (schema_sockets_investigation [0,1,2]))=[]"
  by (simp add: schema_sockets_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def schema_sockets_observations_literal schema_sockets_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def)

theorem schema_sockets_key_alone_complete:
  "fst (schema_sockets_investigation [2]) \<and> fst (snd (schema_sockets_investigation [2]))=[]"
  by (simp add: schema_sockets_investigation_def investigation_basis_def Let_def investigation_select_def
    investigation_pairs_def schema_sockets_observations_literal schema_sockets_relation_literal
    finite_basis_residual_def finite_candidate_profile_def finite_basis_evaluation_def finite_observation_table_formed_def)

theorem schema_sockets_complete_selection:
  assumes selected: "set selected\<subseteq>{0,1,2}"
  shows "fst (snd (schema_sockets_investigation selected))=[] \<longleftrightarrow> 2\<in>set selected"
proof -
  let ?table="fset_of_list schema_sockets_investigation_observations"
  let ?relation="\<lambda>c d. (c,d)\<in>set schema_sockets_investigation_relation"
  let ?residual="finite_basis_residual (fset_of_list [0,1]) (fset_of_list selected) ?table ?relation"
  let ?profile="candidate_profile (set selected) (finite_table_observations ?table)"
  have left: "?profile 0\<subseteq>?profile 1 \<longleftrightarrow> 2\<notin>set selected"
    using selected by (auto simp: candidate_profile_comparison schema_sockets_observations_exact
      socket_investigation_observation_code)
  have right: "?profile 1\<subseteq>?profile 0 \<longleftrightarrow> 2\<notin>set selected"
    using selected by (auto simp: candidate_profile_comparison schema_sockets_observations_exact
      socket_investigation_observation_code)
  have basis: "comparison_basis {0,1} ?relation (set selected) (finite_table_observations ?table)
      \<longleftrightarrow> 2\<in>set selected"
    using left right by (simp add: comparison_basis_def schema_sockets_relation_literal)
  have actual: "set (fst (snd (schema_sockets_investigation selected)))=fset ?residual"
    by (simp only: schema_sockets_investigation_def investigation_basis_residual)
  have empty: "fst (snd (schema_sockets_investigation selected))=[] \<longleftrightarrow> fset ?residual={}"
    using actual by auto
  have transfer: "(fset ?residual=fset {||}) \<longleftrightarrow> ?residual={||}" by (rule fset_inject)
  have characterized: "?residual={||} \<longleftrightarrow> 2\<in>set selected"
    by (simp only: finite_basis_residual_empty fset_of_list.rep_eq set_simps basis)
  show ?thesis using empty transfer characterized by simp
qed

export_code investigation_inference investigation_basis schema_sockets_investigation
  schema_sockets_investigation_observations schema_sockets_investigation_relation
  nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

text \<open>
  The candidates are the existing native incidence schema with its original
  material socket and with that socket readdressed. They have the same head,
  the same unkeyed material operands at every valuation, and the same complete
  rule-instance relation. Exact substitution still separates them because it
  retains the source socket.

  The executed comparison asks for an actual substitution between these
  schemas. Omitting the material key leaves both directed comparisons
  unresolved; the socket facet alone determines this finite case. The two
  invariant facets add no distinction here. The code equations
  follow from the actual schema fields and the general socket-preservation
  theorem. They do not approximate a universal observation by finitely many
  valuations. This case directs the prescribed-coordinate constructor and
  the complete keyed report already used by the specialization checker.
\<close>

end
