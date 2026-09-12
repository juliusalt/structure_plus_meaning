theory Factor_Clause_Specialization_Readings
  imports Factor_Schema_Pattern_Admission Factor_Clause_Specialization_Graphs
begin

section \<open>The package clause, replacement record, and substituted schema remain explicit\<close>

definition schema_clause_specialization_at where
  "schema_clause_specialization_at E u r d c F v q G w t \<longleftrightarrow>
    (\<exists>P S s As I K. native_package_at E u r P \<and> ((d,c),S)\<in>system_clauses P \<and>
      distinct As \<and> set As=schema_variables S \<and>
      pattern_record_at F v (schema_variables (schema_substitute s S)) q (substitution_row_patterns As s) I K \<and>
      native_schema_at G w t (schema_substitute s S) \<and> schema_pattern_boundary P d (schema_substitute s S))"

definition clause_specialization_reading_calls where
  "clause_specialization_reading_calls e u r du dr c f v q g w t \<longleftrightarrow>
    (\<exists>a.
      (81,citation_observation_argument e du dr (Pair_Term c a))\<in>positive_meaning definition_clause_reading_system \<and>
      (291,substitution_reading_argument e du a f v q g w t)\<in>positive_meaning substitution_reading_system \<and>
      (293,pattern_call_reading_argument e u r (Pair_Term du dr) g w t)\<in>positive_meaning schema_pattern_reading_system)"

theorem clause_specialization_readings_sound:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
    and reads: "clause_specialization_reading_calls e (use_data_term u) (Payload_Term r)
      (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term q)
      g (use_data_term w) (Payload_Term t)"
  shows "schema_clause_specialization_at E u r (du,dr) c F v q G w t"
proof -
  obtain a where calls:
    "(81,citation_observation_argument e (use_data_term du) (Payload_Term dr) (Pair_Term (Payload_Term c) a))
      \<in>positive_meaning definition_clause_reading_system"
    "(291,substitution_reading_argument e (use_data_term du) a f (use_data_term v) (Payload_Term q)
      g (use_data_term w) (Payload_Term t))\<in>positive_meaning substitution_reading_system"
    "(293,pattern_call_reading_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (use_data_term du) (Payload_Term dr)) g (use_data_term w) (Payload_Term t))
      \<in>positive_meaning schema_pattern_reading_system"
    using reads by (auto simp: clause_specialization_reading_calls_def)
  obtain ar where root: "a=Payload_Term ar"
    using calls(1) by (simp only: definition_clause_reading_exact factor_term.inject; blast)
  have substitution: "schema_substitution_at E du ar F v q G w t"
    using calls(2) by (simp only: root substitution_reading_on_sources[OF sources])
  obtain S s As I K where raw: "native_schema_at E du ar S" "distinct As" "set As=schema_variables S"
    "pattern_record_at F v (schema_variables (schema_substitute s S)) q (substitution_row_patterns As s) I K"
    "native_schema_at G w t (schema_substitute s S)"
    using substitution by (auto simp: schema_substitution_at_def)
  have head_reading: "(293,pattern_call_reading_argument e (use_data_term u) (Payload_Term r)
      (definition_site_value (du,dr)) g (use_data_term w) (Payload_Term t))
      \<in>positive_meaning schema_pattern_reading_system"
    using calls(3) by (simp add: site_data_term_def)
  have boundary: "schema_pattern_boundary_at E u r (du,dr) G w t"
    using head_reading by (simp only: schema_pattern_reading_on_sources[OF sources(1,3)])
  obtain P T where package: "native_package_at E u r P" and target: "native_schema_at G w t T"
    and formed: "schema_pattern_boundary P (du,dr) T"
    using boundary by (auto simp: schema_pattern_boundary_at_def)
  have same: "T=schema_substitute s S" by (rule native_schema_unique[OF target raw(5)])
  have actual_clause: "(81,citation_observation_argument e (use_data_term du) (Payload_Term dr)
      (Pair_Term (Payload_Term c) (Payload_Term ar)))\<in>positive_meaning definition_clause_reading_system"
    using calls(1) by (simp only: root)
  obtain p C where definition_read: "native_definition_at E du dr p C" and member: "(c,S)\<in>C"
    using definition_clause_reading_recovers[OF sources(1) actual_clause raw(1)] by blast
  have reached: "(du,dr)\<in>native_definition_sites E (native_package_roots E u r)"
    using schema_pattern_call_formed(2)[of P "(du,dr)" "schema_conclusion T"] formed
      native_package_projection(3)[OF package] by (auto simp: schema_pattern_boundary_def native_package_sites_def)
  have clause: "(((du,dr),c),S)\<in>system_clauses P"
    using native_program_complete_at(2)[OF reached, where p=p and C=C and c=c and S=S]
      definition_read member native_package_projection(2)[OF package] by simp
  show ?thesis unfolding schema_clause_specialization_at_def
    by (rule exI[of _ P], rule exI[of _ S], rule exI[of _ s], rule exI[of _ As],
      rule exI[of _ I], rule exI[of _ K])
      (use package clause raw formed same in blast)
qed

theorem clause_specialization_readings_complete:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
    and actual: "schema_clause_specialization_at E u r (du,dr) c F v q G w t"
  shows "clause_specialization_reading_calls e (use_data_term u) (Payload_Term r)
    (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term q)
    g (use_data_term w) (Payload_Term t)"
proof -
  obtain P S s As I K where package: "native_package_at E u r P" and clause: "(((du,dr),c),S)\<in>system_clauses P"
    and replacements: "distinct As" "set As=schema_variables S"
      "pattern_record_at F v (schema_variables (schema_substitute s S)) q (substitution_row_patterns As s) I K"
    and raw: "native_schema_at G w t (schema_substitute s S)"
    and boundary: "schema_pattern_boundary P (du,dr) (schema_substitute s S)"
    using actual by (auto simp: schema_clause_specialization_at_def)
  obtain p C where definition_read: "native_definition_at E du dr p C" and member: "(c,S)\<in>C"
    using clause native_package_projection(2)[OF package] by (auto simp: native_definition_graph_def)
  obtain a where citation: "(81,citation_observation_argument e (use_data_term du) (Payload_Term dr)
      (Pair_Term (Payload_Term c) (Payload_Term a)))\<in>positive_meaning definition_clause_reading_system"
    and source: "native_schema_at E du a S"
    using definition_clause_reading_total[OF sources(1) definition_read member] by blast
  have substitution: "schema_substitution_at E du a F v q G w t"
    unfolding schema_substitution_at_def
    by (rule exI[of _ S], rule exI[of _ s], rule exI[of _ As], rule exI[of _ I], rule exI[of _ K])
      (use source replacements raw in blast)
  have substitution_call: "(291,substitution_reading_argument e (use_data_term du) (Payload_Term a)
      f (use_data_term v) (Payload_Term q) g (use_data_term w) (Payload_Term t))
      \<in>positive_meaning substitution_reading_system"
    by (simp only: substitution_reading_on_sources[OF sources]) (rule substitution)
  have head_reading: "(293,pattern_call_reading_argument e (use_data_term u) (Payload_Term r)
      (definition_site_value (du,dr)) g (use_data_term w) (Payload_Term t))
      \<in>positive_meaning schema_pattern_reading_system"
    using boundary by (simp only: schema_pattern_reading_on_sources[OF sources(1,3)]
      schema_pattern_boundary_at_reads[OF package raw])
  have boundary_call: "(293,pattern_call_reading_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (use_data_term du) (Payload_Term dr)) g (use_data_term w) (Payload_Term t))
      \<in>positive_meaning schema_pattern_reading_system"
    using head_reading by (simp add: site_data_term_def)
  show ?thesis unfolding clause_specialization_reading_calls_def
    by (rule exI[of _ "Payload_Term a"]) (use citation substitution_call boundary_call in blast)
qed

theorem clause_specialization_readings_exact:
  assumes "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
  shows "clause_specialization_reading_calls e (use_data_term u) (Payload_Term r)
    (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term q)
    g (use_data_term w) (Payload_Term t) \<longleftrightarrow>
    schema_clause_specialization_at E u r (du,dr) c F v q G w t"
  using clause_specialization_readings_sound[OF assms] clause_specialization_readings_complete[OF assms] by blast

section \<open>The native relation supplies the same complete abstract specialization\<close>

theorem native_clause_specialization_relation:
  assumes actual: "schema_clause_specialization_at E u r d c F v q G w t"
    and package: "native_package_at E u r P" and source: "((d,c),S)\<in>system_clauses P"
    and target: "native_schema_at G w t T"
  shows "\<exists>V As I K. schema_clause_specialization P d c V T \<and> distinct As \<and> set As=schema_variables S \<and>
    pattern_record_at F v (schema_variables T) q (substitution_row_patterns As (rel_value V)) I K"
proof -
  obtain Q R s As I K where read: "native_package_at E u r Q" "((d,c),R)\<in>system_clauses Q"
    "distinct As" "set As=schema_variables R"
    "pattern_record_at F v (schema_variables (schema_substitute s R)) q (substitution_row_patterns As s) I K"
    "native_schema_at G w t (schema_substitute s R)" "schema_pattern_boundary Q d (schema_substitute s R)"
    using actual by (auto simp: schema_clause_specialization_at_def)
  have program: "Q=P" by (rule native_package_unique[OF read(1) package])
  have csv: "single_valued (system_clauses P)"
    using native_package_system_formed[OF package] by (simp add: schema_system_formed_def)
  have clause: "R=S" using single_valued_outputs[OF csv _ source] read(2) program by blast
  have schema: "T=schema_substitute s S" using native_schema_unique[OF target read(6)] clause by simp
  have scope: "set As=schema_variables S" using read(4) clause by simp
  have replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
  proof -
    have rows: "\<forall>p\<in>set (substitution_row_patterns As s). pattern_formed p"
      using pattern_record_formed[OF read(5)] by blast
    have formed_rows: "\<forall>a\<in>set As. octets_formed a \<and> pattern_formed (s a)"
      using rows by (simp only: substitution_row_formed)
    show ?thesis using formed_rows scope by blast
  qed
  let ?V="image (\<lambda>a. (a,s a)) (schema_variables S)"
  have graph_boundary: "schema_pattern_boundary P d (schema_substitute s S)"
    using read(7) program clause by simp
  have relation: "schema_clause_specialization P d c ?V T"
    using schema_clause_specialization_graph(1)[OF source graph_boundary replacements]
    by (simp only: schema)
  have lookup: "rel_value ?V a=s a" if "a\<in>schema_variables S" for a
    by (rule schema_clause_specialization_graph(2)[OF source graph_boundary replacements that])
  have row_patterns: "substitution_row_patterns As (rel_value ?V)=substitution_row_patterns As s"
    by (simp only: substitution_row_patterns_def; rule map_cong) (use lookup scope in auto)
  show ?thesis by (rule exI[of _ ?V], rule exI[of _ As], rule exI[of _ I], rule exI[of _ K])
    (use relation read(3,5) scope clause schema row_patterns in simp)
qed

section \<open>Every submitted term retains the three environments and actual clause key\<close>

theorem native_clause_specialization_iff:
  assumes package: "native_package_at E u r P" and source: "((d,c),S)\<in>system_clauses P"
    and target: "native_schema_at G w t T"
  shows "schema_clause_specialization_at E u r d c F v q G w t \<longleftrightarrow>
    (\<exists>V As I K. schema_clause_specialization P d c V T \<and> distinct As \<and> set As=schema_variables S \<and>
      pattern_record_at F v (schema_variables T) q (substitution_row_patterns As (rel_value V)) I K)"
proof
  assume actual: "schema_clause_specialization_at E u r d c F v q G w t"
  show "\<exists>V As I K. schema_clause_specialization P d c V T \<and> distinct As \<and> set As=schema_variables S \<and>
      pattern_record_at F v (schema_variables T) q (substitution_row_patterns As (rel_value V)) I K"
    by (rule native_clause_specialization_relation[OF actual package source target])
next
  assume "\<exists>V As I K. schema_clause_specialization P d c V T \<and> distinct As \<and> set As=schema_variables S \<and>
    pattern_record_at F v (schema_variables T) q (substitution_row_patterns As (rel_value V)) I K"
  then obtain V As I K where actual: "schema_clause_specialization P d c V T" and rows: "distinct As"
    "set As=schema_variables S" "pattern_record_at F v (schema_variables T) q (substitution_row_patterns As (rel_value V)) I K"
    by blast
  have substitution: "T=schema_substitute (rel_value V) S"
    by (rule schema_clause_specialization_source(2)[OF actual source])
  show "schema_clause_specialization_at E u r d c F v q G w t"
    unfolding schema_clause_specialization_at_def
    by (rule exI[of _ P], rule exI[of _ S], rule exI[of _ "rel_value V"], rule exI[of _ As],
      rule exI[of _ I], rule exI[of _ K])
      (use package source rows target actual substitution in \<open>auto simp: schema_clause_specialization_def\<close>)
qed

abbreviation clause_specialization_reading_argument where
  "clause_specialization_reading_argument e u r d c f v q g w t \<equiv>
    Pair_Term (package_subject_argument e u r (Pair_Term d c))
      (Pair_Term (Pair_Term f (Pair_Term v q)) (Pair_Term g (Pair_Term w t)))"

definition clause_specialization_reading_result :: "factor_term \<Rightarrow> bool" where
  "clause_specialization_reading_result z \<longleftrightarrow>
    (\<exists>E e u r d c F f v q G g w t. environment_value_presents E e \<and>
      environment_value_presents F f \<and> environment_value_presents G g \<and>
      z=clause_specialization_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
        (Payload_Term c) f (use_data_term v) (Payload_Term q) g (use_data_term w) (Payload_Term t) \<and>
      schema_clause_specialization_at E u r d c F v q G w t)"

lemma clause_specialization_reading_sources:
  assumes reads: "clause_specialization_reading_calls e u r du dr c f v q g w t"
  shows "\<exists>E pu pr a b k F fv fq G gw gt. environment_value_presents E e \<and>
    u=use_data_term pu \<and> r=Payload_Term pr \<and> du=use_data_term a \<and> dr=Payload_Term b \<and> c=Payload_Term k \<and>
    environment_value_presents F f \<and> v=use_data_term fv \<and> q=Payload_Term fq \<and>
    environment_value_presents G g \<and> w=use_data_term gw \<and> t=Payload_Term gt"
proof -
  obtain ar where calls:
    "(81,citation_observation_argument e du dr (Pair_Term c ar))\<in>positive_meaning definition_clause_reading_system"
    "(291,substitution_reading_argument e du ar f v q g w t)\<in>positive_meaning substitution_reading_system"
    "(293,pattern_call_reading_argument e u r (Pair_Term du dr) g w t)\<in>positive_meaning schema_pattern_reading_system"
    using reads by (auto simp: clause_specialization_reading_calls_def)
  obtain E pu pr a b where package: "environment_value_presents E e" "u=use_data_term pu"
    "r=Payload_Term pr" "du=use_data_term a" "dr=Payload_Term b"
    using calls(3) by (simp only: schema_pattern_reading_exact schema_pattern_reading_result_def
      site_data_term_def factor_term.inject; blast)
  obtain k where key: "c=Payload_Term k"
    using calls(1) by (simp only: definition_clause_reading_exact factor_term.inject; blast)
  obtain F fv fq G gw gt where sources: "environment_value_presents F f" "v=use_data_term fv" "q=Payload_Term fq"
    "environment_value_presents G g" "w=use_data_term gw" "t=Payload_Term gt"
    using calls(2) by (simp only: substitution_reading_exact substitution_reading_result_def factor_term.inject; blast)
  show ?thesis using package key sources by blast
qed

theorem clause_specialization_reading_calls_result:
  "clause_specialization_reading_calls e u r du dr c f v q g w t \<longleftrightarrow>
    clause_specialization_reading_result (clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)"
proof
  assume reads: "clause_specialization_reading_calls e u r du dr c f v q g w t"
  obtain E pu pr a b k F fv fq G gw gt where inputs: "environment_value_presents E e"
    "u=use_data_term pu" "r=Payload_Term pr" "du=use_data_term a" "dr=Payload_Term b" "c=Payload_Term k"
    "environment_value_presents F f" "v=use_data_term fv" "q=Payload_Term fq"
    "environment_value_presents G g" "w=use_data_term gw" "t=Payload_Term gt"
    using clause_specialization_reading_sources[OF reads] by blast
  have actual: "schema_clause_specialization_at E pu pr (a,b) k F fv fq G gw gt"
    by (rule clause_specialization_readings_sound[OF inputs(1,7,10)]) (use reads inputs in simp)
  show "clause_specialization_reading_result (clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)"
    unfolding clause_specialization_reading_result_def
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ "(a,b)"],
      rule exI[of _ k], rule exI[of _ F], rule exI[of _ f], rule exI[of _ fv], rule exI[of _ fq],
      rule exI[of _ G], rule exI[of _ g], rule exI[of _ gw], rule exI[of _ gt])
      (use inputs actual in \<open>simp add: site_data_term_def\<close>)
next
  assume result: "clause_specialization_reading_result
    (clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)"
  obtain E e0 pu pr d0 k F f0 fv fq G g0 gw gt where raw:
    "environment_value_presents E e0" "environment_value_presents F f0" "environment_value_presents G g0"
    "clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t=
      clause_specialization_reading_argument e0 (use_data_term pu) (Payload_Term pr) (definition_site_value d0)
        (Payload_Term k) f0 (use_data_term fv) (Payload_Term fq) g0 (use_data_term gw) (Payload_Term gt)"
    "schema_clause_specialization_at E pu pr d0 k F fv fq G gw gt"
    using result unfolding clause_specialization_reading_result_def
    by (elim exE conjE) (rule that; assumption)
  obtain a b where site: "d0=(a,b)" by (cases d0)
  have fields: "e=e0" "u=use_data_term pu" "r=Payload_Term pr" "du=use_data_term a" "dr=Payload_Term b"
    "c=Payload_Term k" "f=f0" "v=use_data_term fv" "q=Payload_Term fq"
    "g=g0" "w=use_data_term gw" "t=Payload_Term gt"
    using raw(4) by (simp only: site site_data_term_def fst_conv snd_conv factor_term.inject; blast)+
  have actual: "schema_clause_specialization_at E pu pr (a,b) k F fv fq G gw gt"
    using raw(5) by (simp only: site)
  show "clause_specialization_reading_calls e u r du dr c f v q g w t"
    using clause_specialization_readings_complete[OF raw(1-3) actual] by (simp only: fields)
qed

text \<open>
  The three calls share the exact source package, definition coordinates,
  clause socket, replacement site, and target schema site. Clause selection
  recovers the actual source root; substitution checks every replacement and
  material operand; the complete target boundary checks every callee against
  the same package. Equal local addresses in other artifact uses do not select
  this clause.

  The independent native relation yields the same complete replacement
  relation and substituted schema used by the abstract specialization.
  No truth under a private marker valuation is required.
\<close>

end
