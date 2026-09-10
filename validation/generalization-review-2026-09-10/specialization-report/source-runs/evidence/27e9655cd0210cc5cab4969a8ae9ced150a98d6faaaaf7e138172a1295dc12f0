theory Factor_Native_Syntax_Determination
  imports Factor_Schema_Determination Factor_Schema_Instantiation Factor_Scoped_Instantiation
begin

section \<open>Two admitted instances identify the actual quoted pattern\<close>

theorem quoted_pattern_two_instances:
  assumes source: "environment_value_presents E e"
    and formed: "pattern_formed p" "\<forall>a\<in>set Vs. octets_formed a"
    and scope: "pattern_variables p\<subseteq>set Vs" "pattern_variables p=set Us"
    and orders: "distinct Vs" "distinct xs" "distinct ys" "distinct Us" "distinct Is" "distinct Ks"
    and tables: "set xs=(\<lambda>a. (a,Payload_Term a)) ` set Vs"
      "set ys=(\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) ` set Vs"
  shows "pattern_quoted_at E u (set Vs) r p (set Is) (set Ks) \<longleftrightarrow>
    (55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (evaluate_pattern Payload_Term p)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is))
      (data_list_term (map Payload_Term Ks)))\<in>positive_meaning pattern_instantiation_system \<and>
    (55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term ys) (Payload_Term r)
      (evaluate_pattern (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) p)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is))
      (data_list_term (map Payload_Term Ks)))\<in>positive_meaning pattern_instantiation_system"
proof -
  let ?k="Whole_Artifact empty_artifact"
  let ?x="evaluate_pattern Payload_Term p"
  let ?y="evaluate_pattern (\<lambda>_. Target_Term ?k) p"
  have bindings: "term_bindings_formed (set Vs) (set xs)" "term_bindings_formed (set Vs) (set ys)"
    unfolding tables by (rule graph_term_bindings_formed; use formed in auto)+
  have instances: "pattern_instance (set xs) p ?x" "pattern_instance (set ys) p ?y"
    using formed(1) scope(1) by (simp_all add: tables graph_pattern_instance)
  have recover: "q=p" if quote: "pattern_quoted_at E u (set Vs) r q (set Is) (set Ks)"
      and left: "pattern_instance (set xs) q ?x"
      and other: "pattern_quoted_at E u (set Vs) r s (set Is) (set Ks)"
      and right: "pattern_instance (set ys) s ?y" for q s
  proof -
    have same: "s=q" using pattern_quoted_unique[OF other quote] by blast
    have second: "pattern_instance (set ys) q ?y" using right same by simp
    show ?thesis
      by (rule pattern_instances_determine[where f="\<lambda>a. a" and B="set Vs" and k="?k"])
        (use left second instances in \<open>auto simp: tables\<close>)
  qed
  show ?thesis
    by (simp only: pattern_instantiation_on_values[OF source])
      (use bindings instances formed scope orders recover in blast)
qed

section \<open>The same criterion retains the exact enclosing binder\<close>

theorem scoped_pattern_two_instances:
  assumes source: "environment_value_presents E e"
    and formed: "pattern_formed p" "\<forall>a\<in>pattern_variables p. octets_formed a"
    and orders: "distinct xs" "distinct ys" "distinct Is" "distinct Ks"
    and tables: "set xs=(\<lambda>a. (a,Payload_Term a)) ` pattern_variables p"
      "set ys=(\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) ` pattern_variables p"
  shows "scoped_pattern_at E u r p (set Is) (set Ks) \<longleftrightarrow>
    (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs)
      (evaluate_pattern Payload_Term p) (data_list_term (map Payload_Term Is))
      (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system \<and>
    (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys)
      (evaluate_pattern (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) p)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
proof -
  let ?k="Whole_Artifact empty_artifact"
  let ?B="pattern_variables p"
  let ?x="evaluate_pattern Payload_Term p"
  let ?y="evaluate_pattern (\<lambda>_. Target_Term ?k) p"
  have bindings: "term_bindings_formed ?B (set xs)" "term_bindings_formed ?B (set ys)"
    unfolding tables by (rule graph_term_bindings_formed; use formed in auto)+
  have instances: "pattern_instance (set xs) p ?x" "pattern_instance (set ys) p ?y"
    using formed(1) by (simp_all add: tables graph_pattern_instance)
  have recover: "q=p" if quote: "scoped_pattern_at E u r q (set Is) (set Ks)"
      and left: "pattern_instance (set xs) q ?x"
      and other: "scoped_pattern_at E u r s (set Is) (set Ks)"
      and right: "pattern_instance (set ys) s ?y" for q s
  proof -
    have same: "s=q" using scoped_pattern_unique[OF other quote] by blast
    have second: "pattern_instance (set ys) q ?y" using right same by simp
    show ?thesis
      by (rule pattern_instances_determine[where f="\<lambda>a. a" and B="?B" and k="?k"])
        (use left second instances in \<open>auto simp: tables\<close>)
  qed
  show ?thesis
    by (simp only: scoped_instantiation_on_values[OF source])
      (use bindings instances orders recover in blast)
qed

section \<open>Finite reference outputs identify the actual complete native schema\<close>

theorem native_schema_two_instances:
  assumes source: "environment_value_presents E e"
    and tables: "set xs=(\<lambda>a. (a,Payload_Term a)) ` B"
      "set ys=(\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) ` B"
    and expected: "schema_instance S (set xs) t (set qs)" "schema_instance S (set ys) v (set ws)"
    and materials: "set cs=material_instance_relation (set xs) (schema_material_premises S)"
      "set ds=material_instance_relation (set ys) (schema_material_premises S)"
    and orders: "distinct xs" "distinct ys" "distinct qs" "distinct ws" "distinct cs" "distinct ds"
  shows "native_schema_at E u r S \<longleftrightarrow>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) v
      (call_instance_rows_term ws) (binding_rows_term ds))\<in>positive_meaning schema_instantiation_system"
proof
  assume raw: "native_schema_at E u r S"
  show "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) v
      (call_instance_rows_term ws) (binding_rows_term ds))\<in>positive_meaning schema_instantiation_system"
    by (simp only: schema_instantiation_at_schema[OF source raw]) (use expected materials orders in blast)
next
  assume holds: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) v
      (call_instance_rows_term ws) (binding_rows_term ds))\<in>positive_meaning schema_instantiation_system"
  obtain T where actual: "native_schema_at E u r T" "schema_instance T (set xs) t (set qs)"
    "set cs=material_instance_relation (set xs) (schema_material_premises T)"
    using holds by (simp only: schema_instantiation_on_values[OF source]) blast
  have second: "schema_instance T (set ys) v (set ws)"
    "set ds=material_instance_relation (set ys) (schema_material_premises T)"
    using holds by (simp_all only: schema_instantiation_at_schema[OF source actual(1)])
  have same: "T=S"
    by (rule schema_instances_determine[where f="\<lambda>a. a" and B=B and k="Whole_Artifact empty_artifact"])
      (use actual(2,3) second expected materials in \<open>auto simp: tables\<close>)
  show "native_schema_at E u r S" using actual(1) same by simp
qed

section \<open>Every native schema supplies both complete admitted readings\<close>

lemma native_schema_variables_formed:
  assumes raw: "native_schema_at E u r S"
  shows "\<forall>a\<in>schema_variables S. octets_formed a"
proof -
  obtain R b where parts: "environment_formed E" "artifact_at E u R"
    "binder_scope_at R b (schema_variables S)"
    using raw by (auto simp: native_schema_at_def)
  have formed: "exact_formed R" using parts(1,2) by (auto simp: environment_formed_def)
  show ?thesis using binder_scope_properties(2)[OF parts(3)] formed
    by (auto simp: exact_formed_def)
qed

theorem native_schema_two_readings_total:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
  shows "\<exists>Vs t qs cs v ws ds. distinct Vs \<and> set Vs=schema_variables S \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs)) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<and>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)) v
      (call_instance_rows_term ws) (binding_rows_term ds))\<in>positive_meaning schema_instantiation_system"
proof -
  have sf: "schema_formed S" by (rule native_schema_formed[OF raw])
  obtain Vs where scope: "set Vs=schema_variables S" "distinct Vs"
    using finite_distinct_list[OF schema_variables_finite[OF sf]] by blast
  let ?xs="map (\<lambda>a. (a,Payload_Term a)) Vs"
  let ?ys="map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs"
  have formed: "\<forall>a\<in>set Vs. octets_formed a"
    using native_schema_variables_formed[OF raw] by (simp only: scope(1))
  have bindings: "term_bindings_formed (schema_variables S) (set ?xs)"
    "term_bindings_formed (schema_variables S) (set ?ys)"
    unfolding set_map scope(1)
    by (rule graph_term_bindings_formed; use sf formed scope in \<open>auto intro: schema_variables_finite\<close>)+
  have orders: "distinct ?xs" "distinct ?ys"
    using scope(2) by (auto simp: distinct_map inj_on_def)
  obtain t qs cs where first: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term ?xs) t (call_instance_rows_term qs) (binding_rows_term cs))
      \<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw bindings(1) orders(1)] by blast
  obtain v ws ds where second: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term ?ys) v (call_instance_rows_term ws) (binding_rows_term ds))
      \<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw bindings(2) orders(2)] by blast
  show ?thesis using scope first second by blast
qed

text \<open>
  All three criteria use the existing ordinary instantiation readers.
  The source environment, actual use, root, complete binding rows, and output
  metadata retain their existing encodings and admission conditions. The
  first table maps each native binder address to its own payload. The second
  maps every address to one formed target. Neither table changes the source
  artifact or its variable identities.

  The schema criterion starts with the finite outputs calculated from the
  expected schema, including every prospective row and every complete material
  tuple. The two positive readings recover one actual source schema; the
  grammar theorem then identifies it with that expected schema. Every native
  schema has both complete readings. Distinct enumeration orders and complete
  environment presentations remain governed by the existing reader theorems.

  These results identify syntax relative to its actual binder coordinates.
  They do not identify distinct artifacts, omit material fields, or infer
  universal semantic equivalence from two successful program calls. No new
  entry or native operator is introduced. Checking a whole submitted
  interpreter still requires complete program structure and its actual
  semantic dependencies, together with a proved correctness profile.
\<close>

end
