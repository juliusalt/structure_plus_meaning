theory Factor_Pattern_Call_Readings
  imports Factor_Pattern_Specialization Factor_Substitution_Admission Factor_Program_Call_Admission
    Factor_Program_Positions
begin

section \<open>A submitted pattern retains its own source and complete binder\<close>

definition schema_pattern_call_at where
  "schema_pattern_call_at E pu pr d F v q \<longleftrightarrow>
    (\<exists>P p I K. native_package_at E pu pr P \<and> scoped_pattern_at F v q p I K \<and>
      schema_pattern_call P d p)"

definition pattern_call_reading_calls where
  "pattern_call_reading_calls e u r d f v q \<longleftrightarrow>
    (\<exists>b xb yb x y i k.
      (125,reference_bindings_value b xb yb)\<in>positive_meaning reference_bindings_system \<and>
      (56,scoped_instantiation_argument f v q xb x i k)\<in>positive_meaning scoped_instantiation_system \<and>
      (56,scoped_instantiation_argument f v q yb y i k)\<in>positive_meaning scoped_instantiation_system \<and>
      (84,package_subject_argument e u r (Pair_Term d x))\<in>positive_meaning program_call_admission_system \<and>
      (84,package_subject_argument e u r (Pair_Term d y))\<in>positive_meaning program_call_admission_system)"

theorem pattern_call_readings_sound:
  assumes package_source: "environment_value_presents E e" and pattern_source: "environment_value_presents F f"
    and reads: "pattern_call_reading_calls e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
      f (use_data_term v) (Payload_Term q)"
  shows "schema_pattern_call_at E pu pr d F v q"
proof -
  obtain b xb yb x y i k where calls:
    "(125,reference_bindings_value b xb yb)\<in>positive_meaning reference_bindings_system"
    "(56,scoped_instantiation_argument f (use_data_term v) (Payload_Term q) xb x i k)
      \<in>positive_meaning scoped_instantiation_system"
    "(56,scoped_instantiation_argument f (use_data_term v) (Payload_Term q) yb y i k)
      \<in>positive_meaning scoped_instantiation_system"
    "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) x))
      \<in>positive_meaning program_call_admission_system"
    "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) y))
      \<in>positive_meaning program_call_admission_system"
    using reads by (auto simp: pattern_call_reading_calls_def)
  obtain Bs where markers: "\<forall>a\<in>set Bs. octets_formed a"
    "xb=binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Bs)"
    "yb=binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Bs)"
    using calls(1) by (simp only: reference_bindings_exact factor_term.inject) blast
  obtain p Is Ks where first: "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "scoped_pattern_at F v q p (set Is) (set Ks)"
    "term_bindings_formed (pattern_variables p) ((\<lambda>a. (a,Payload_Term a)) ` set Bs)"
    "pattern_instance ((\<lambda>a. (a,Payload_Term a)) ` set Bs) p x"
    using calls(2) by (simp only: markers(2) scoped_instantiation_at_source[OF pattern_source]
      inj_eq[OF use_data_term_injective] factor_term.inject binding_rows_term_injective)
      (auto simp only: set_map)
  obtain s where second: "scoped_pattern_at F v q s (set Is) (set Ks)"
    "pattern_instance ((\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) ` set Bs) s y"
    using calls(3) by (simp only: markers(3) first(1,2) scoped_instantiation_on_values[OF pattern_source] set_map) blast
  have same: "s=p" using scoped_pattern_unique[OF second(1) first(3)] by blast
  have scope: "pattern_variables p=set Bs" using first(4) by (auto simp: term_bindings_formed_def rel_dom_def)
  have formed: "pattern_formed p" and outputs:
    "x=evaluate_pattern Payload_Term p" "y=evaluate_pattern (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) p"
    using first(5) second(2) by (simp_all add: same graph_pattern_instance)
  obtain P where package: "native_package_at E pu pr P" and left: "schema_call_formed P d x"
    using calls(4) by (simp only: program_call_admission_on_values[OF package_source]) blast
  have right: "schema_call_formed P d y"
    using calls(5) by (simp only: program_call_admission_at_package[OF package_source package])
  have admitted: "schema_pattern_call P d p"
    using schema_pattern_call_two_evaluations[where f=id and B="set Bs" and k="Whole_Artifact empty_artifact"
      and P=P and d=d and p=p] markers(1) scope formed left right outputs by auto
  show ?thesis unfolding schema_pattern_call_at_def
    by (rule exI[of _ P], rule exI[of _ p], rule exI[of _ "set Is"], rule exI[of _ "set Ks"])
      (use package first(3) admitted in blast)
qed

theorem pattern_call_readings_complete:
  assumes package_source: "environment_value_presents E e" and pattern_source: "environment_value_presents F f"
    and admitted: "schema_pattern_call_at E pu pr d F v q"
  shows "pattern_call_reading_calls e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
    f (use_data_term v) (Payload_Term q)"
proof -
  obtain P p I K where package: "native_package_at E pu pr P" and quote: "scoped_pattern_at F v q p I K"
    and call: "schema_pattern_call P d p" using admitted by (auto simp: schema_pattern_call_at_def)
  have finite: "finite (pattern_variables p)" "finite I" "finite K"
    and formed: "pattern_formed p" using scoped_pattern_formed[OF quote] by auto
  obtain b a J where body: "pattern_quoted_at F v b a p J K"
    using quote by (auto simp: scoped_pattern_at_def)
  have variables: "\<forall>a\<in>pattern_variables p. octets_formed a"
    using pattern_quoted_addresses_formed[OF body] by auto
  obtain Bs Is Ks where orders: "distinct Bs" "set Bs=pattern_variables p"
    "distinct Is" "set Is=I" "distinct Ks" "set Ks=K"
    using finite_distinct_list[OF finite(1)] finite_distinct_list[OF finite(2)] finite_distinct_list[OF finite(3)] by blast
  let ?xs="map (\<lambda>a. (a,Payload_Term a)) Bs"
  let ?ys="map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Bs"
  let ?x="evaluate_pattern Payload_Term p"
  let ?y="evaluate_pattern (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) p"
  have distinct: "distinct ?xs" "distinct ?ys" using orders(1) by (auto simp: distinct_map inj_on_def)
  have bindings: "term_bindings_formed (pattern_variables p) (set ?xs)"
    "term_bindings_formed (pattern_variables p) (set ?ys)"
    using graph_term_bindings_formed[OF finite(1), where h=Payload_Term]
      graph_term_bindings_formed[OF finite(1), where h="\<lambda>_. Target_Term (Whole_Artifact empty_artifact)"] variables
    by (simp_all add: orders(2))
  have instances: "pattern_instance (set ?xs) p ?x" "pattern_instance (set ?ys) p ?y"
    using formed by (simp_all add: orders(2) graph_pattern_instance)
  have markers: "(125,reference_bindings_value (data_list_term (map Payload_Term Bs))
      (binding_rows_term ?xs) (binding_rows_term ?ys))\<in>positive_meaning reference_bindings_system"
    by (rule reference_bindings_complete) (use variables orders(2) in simp)
  have first: "(56,scoped_instantiation_argument f (use_data_term v) (Payload_Term q) (binding_rows_term ?xs) ?x
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    by (simp only: scoped_instantiation_on_values[OF pattern_source])
      (use distinct orders quote bindings instances in blast)
  have second: "(56,scoped_instantiation_argument f (use_data_term v) (Payload_Term q) (binding_rows_term ?ys) ?y
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    by (simp only: scoped_instantiation_on_values[OF pattern_source])
      (use distinct orders quote bindings instances in blast)
  have left: "schema_call_formed P d ?x" by (rule schema_pattern_call_evaluation[OF call]) (use variables in auto)
  have right: "schema_call_formed P d ?y" by (rule schema_pattern_call_evaluation[OF call]) simp
  have calls:
    "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) ?x))
      \<in>positive_meaning program_call_admission_system"
    "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) ?y))
      \<in>positive_meaning program_call_admission_system"
    using left right by (simp_all only: program_call_admission_at_package[OF package_source package])
  show ?thesis unfolding pattern_call_reading_calls_def
    by (rule exI[of _ "data_list_term (map Payload_Term Bs)"], rule exI[of _ "binding_rows_term ?xs"],
      rule exI[of _ "binding_rows_term ?ys"], rule exI[of _ ?x], rule exI[of _ ?y],
      rule exI[of _ "data_list_term (map Payload_Term Is)"], rule exI[of _ "data_list_term (map Payload_Term Ks)"])
      (use markers first second calls in blast)
qed

theorem pattern_call_readings_exact:
  assumes "environment_value_presents E e" "environment_value_presents F f"
  shows "pattern_call_reading_calls e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
    f (use_data_term v) (Payload_Term q) \<longleftrightarrow> schema_pattern_call_at E pu pr d F v q"
  using pattern_call_readings_sound[OF assms] pattern_call_readings_complete[OF assms] by blast

lemma schema_pattern_call_at_reads:
  assumes package: "native_package_at E pu pr P" and quote: "scoped_pattern_at F v q p I K"
  shows "schema_pattern_call_at E pu pr d F v q \<longleftrightarrow> schema_pattern_call P d p"
proof -
  have packages: "Q=P" if "native_package_at E pu pr Q" for Q
    by (rule native_package_unique[OF that package])
  have patterns: "s=p" if "scoped_pattern_at F v q s J W" for s J W
    using scoped_pattern_unique[OF that quote] by blast
  show ?thesis unfolding schema_pattern_call_at_def using package quote packages patterns by blast
qed

corollary schema_pattern_call_at_positioned:
  assumes package: "native_package_at E pu pr P" and quote: "scoped_pattern_at F v q p I K"
  shows "schema_pattern_call_at E pu pr d F v q \<longleftrightarrow> schema_pattern_call (positioned_program P) d p"
  using schema_pattern_call_agreement[OF positioned_program_calls[OF native_package_system_formed[OF package]], of d p]
  by (simp only: schema_pattern_call_at_reads[OF package quote])

section \<open>Every submitted value retains both complete source environments\<close>

abbreviation pattern_call_reading_argument where
  "pattern_call_reading_argument e u r d f v q \<equiv>
    Pair_Term (package_subject_argument e u r d) (Pair_Term f (Pair_Term v q))"

definition pattern_call_reading_result :: "factor_term \<Rightarrow> bool" where
  "pattern_call_reading_result z \<longleftrightarrow>
    (\<exists>E e u r d F f v q. environment_value_presents E e \<and> environment_value_presents F f \<and>
      z=pattern_call_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
        f (use_data_term v) (Payload_Term q) \<and> schema_pattern_call_at E u r d F v q)"

lemma pattern_call_reading_sources:
  assumes reads: "pattern_call_reading_calls e u r d f v q"
  shows "\<exists>E pu pr a F w s. environment_value_presents E e \<and> u=use_data_term pu \<and> r=Payload_Term pr \<and>
    d=definition_site_value a \<and> environment_value_presents F f \<and> v=use_data_term w \<and> q=Payload_Term s"
proof -
  obtain xb x i k where calls:
    "(56,scoped_instantiation_argument f v q xb x i k)\<in>positive_meaning scoped_instantiation_system"
    "(84,package_subject_argument e u r (Pair_Term d x))\<in>positive_meaning program_call_admission_system"
    using reads by (auto simp: pattern_call_reading_calls_def)
  obtain E pu pr a where package: "environment_value_presents E e" "u=use_data_term pu"
    "r=Payload_Term pr" "d=definition_site_value a"
    using calls(2) by (simp only: program_call_admission_exact factor_term.inject) blast
  obtain F w s where pattern: "environment_value_presents F f" "v=use_data_term w" "q=Payload_Term s"
    using calls(1) by (simp only: scoped_instantiation_exact factor_term.inject) blast
  show ?thesis using package pattern by blast
qed

theorem pattern_call_reading_calls_result:
  "pattern_call_reading_calls e u r d f v q \<longleftrightarrow>
    pattern_call_reading_result (pattern_call_reading_argument e u r d f v q)"
proof
  assume reads: "pattern_call_reading_calls e u r d f v q"
  obtain E pu pr a F w s where inputs: "environment_value_presents E e" "u=use_data_term pu"
    "r=Payload_Term pr" "d=definition_site_value a" "environment_value_presents F f"
    "v=use_data_term w" "q=Payload_Term s" using pattern_call_reading_sources[OF reads] by blast
  have actual: "schema_pattern_call_at E pu pr a F w s"
    by (rule pattern_call_readings_sound[OF inputs(1,5)]) (use reads inputs in simp)
  show "pattern_call_reading_result (pattern_call_reading_argument e u r d f v q)"
    unfolding pattern_call_reading_result_def
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ a],
      rule exI[of _ F], rule exI[of _ f], rule exI[of _ w], rule exI[of _ s]) (use inputs actual in simp)
next
  assume result: "pattern_call_reading_result (pattern_call_reading_argument e u r d f v q)"
  obtain E pu pr a F w s where inputs: "environment_value_presents E e" "u=use_data_term pu"
    "r=Payload_Term pr" "d=definition_site_value a" "environment_value_presents F f"
    "v=use_data_term w" "q=Payload_Term s" "schema_pattern_call_at E pu pr a F w s"
    using result by (simp only: pattern_call_reading_result_def factor_term.inject) blast
  show "pattern_call_reading_calls e u r d f v q"
    using pattern_call_readings_complete[OF inputs(1,5,8)] inputs(2,3,4,6,7) by simp
qed

text \<open>
  Five existing readings recover a scoped pattern and test its two complete
  instances against one admitted package and reached definition. The two
  pattern readings share the actual source, scope, private positions, and
  external slots. The package and pattern source may be different environments;
  neither environment supplies an implicit argument to the other.

  The recovered relation is the existing symbolic call boundary, including
  after program coordinates are qualified by their owning use. No clause
  instance or material truth is required to establish call formation. Complete
  proof-scheme admission still has to check every inference and both of its
  assumption boundaries.
\<close>

end
