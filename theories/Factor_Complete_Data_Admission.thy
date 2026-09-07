theory Factor_Complete_Data_Admission
  imports Factor_Complete_Data_Recognition Factor_Package_Retention_Admission
begin

section \<open>A complete artifact value supplies its own reading environment\<close>

abbreviation data_quotation_environment_term :: "factor_term \<Rightarrow> factor_term" where
  "data_quotation_environment_term c \<equiv>
    Pair_Term (data_list_term [Pair_Term (Payload_Term []) c]) (Payload_Term [])"

abbreviation data_quotation_environment_pattern :: "'a term_pattern \<Rightarrow> 'a term_pattern" where
  "data_quotation_environment_pattern c \<equiv>
    Pattern_Pair (data_list_pattern [Pattern_Pair (Pattern_Payload []) c]) (Pattern_Payload [])"

lemma data_quotation_environment_presents:
  assumes present: "artifact_value_presents C c"
  shows "environment_value_presents (literal_environment C {}) (data_quotation_environment_term c)"
proof -
  let ?E="literal_environment C {}"
  have cf: "exact_formed C" using artifact_value_presents_formed[OF present] by blast
  have formed: "environment_formed ?E"
    by (rule literal_environment_formed[OF cf]) (auto simp: single_valued_def)
  have artifacts: "data_collection_presents environment_artifact_entry_presents
    (environment_artifacts ?E)
    (data_list_term (map (\<lambda>z. Pair_Term (Payload_Term []) c)
      ([(None,C)] :: (local_address option\<times>exact_artifact) list)))"
    by (rule data_collection_presents_map[where xs="[(None,C)]"])
      (use present in \<open>auto simp: literal_environment_def environment_artifact_entry_presents_def\<close>)
  have bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings ?E)
    (data_list_term [])"
    unfolding data_collection_presents_def
    by (rule exI[of _ "[]"], rule exI[of _ "[]"]) (simp add: literal_environment_def)
  show ?thesis using formed artifacts bindings
    unfolding environment_value_presents_def by auto
qed

lemma data_quotation_environment_recovers:
  assumes source: "environment_value_presents E (data_quotation_environment_term c)"
    and actual: "artifact_at E None C"
  shows "artifact_value_presents C c \<and> E=literal_environment C {}"
proof -
  obtain v where selected: "selected_data_member (Pair_Term (use_data_term None) v)
      (data_list_term [Pair_Term (Payload_Term []) c])"
    and material: "artifact_value_presents C v"
    using environment_artifact_selection[OF source] actual by blast
  have same: "v=c"
    using selected by (simp only: selected_data_member_exact data_list_term_injective; auto)
  have present: "artifact_value_presents C c" using material same by simp
  have environment: "E=literal_environment C {}"
    by (rule environment_value_presents_unique[OF source data_quotation_environment_presents[OF present]])
  show ?thesis using present environment by blast
qed

lemma artifact_value_carrier_field:
  assumes present: "artifact_value_presents C (Pair_Term a b)"
  shows "\<exists>A. a=data_list_term (map Payload_Term A) \<and> distinct A \<and>
    set A=rra_carrier (object_structure C)"
proof -
  obtain A E B F where enumeration: "artifact_enumeration C A E B F"
    and shape: "Pair_Term a b=artifact_data_term A E B F"
    using present unfolding artifact_value_presents_def by blast
  show ?thesis using shape artifact_enumeration_material(2)[OF enumeration]
    artifact_enumeration_no_repeated_set_entry[OF enumeration]
    by (auto simp: artifact_data_term_def)
qed

section \<open>One ordinary quotation premise uses the complete carrier\<close>

abbreviation complete_data_quotation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "complete_data_quotation_argument c r t \<equiv> Pair_Term c (Pair_Term r t)"

abbreviation complete_data_quotation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "complete_data_quotation_pattern c r t \<equiv> Pattern_Pair c (Pattern_Pair r t)"

abbreviation complete_data_admission_result :: "factor_term \<Rightarrow> bool" where
  "complete_data_admission_result z \<equiv>
    \<exists>C c r t. z=complete_data_quotation_argument c (Payload_Term r) t \<and>
      artifact_value_presents C c \<and> complete_data_quoted_at C r t"

definition complete_data_admission_schema :: "(nat,nat,nat) factor_schema" where
  "complete_data_admission_schema=data_rule
    (complete_data_quotation_pattern (Pattern_Pair data_x data_y) data_z data_w)
    {(0,50,term_quotation_pattern (data_quotation_environment_pattern (Pattern_Pair data_x data_y))
      (Pattern_Payload []) data_z data_w data_x (Pattern_Payload []))}"

definition complete_data_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "complete_data_admission_system=add_view_definition package_retention_admission_system 123 data_x {(0,complete_data_admission_schema)}"

lemma complete_data_admission_system_formed [simp]: "schema_system_formed complete_data_admission_system"
  unfolding complete_data_admission_system_def
  by (rule add_recursive_definition_formed[OF package_retention_admission_system_formed])
    (auto simp: complete_data_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma complete_data_admission_definitions [simp]:
  "system_definitions complete_data_admission_system=insert 123 (system_definitions package_retention_admission_system)"
  by (simp add: complete_data_admission_system_def)

lemma complete_data_admission_call:
  "schema_call_formed complete_data_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions complete_data_admission_system \<and> term_formed t"
  using added_variable_calls[OF package_retention_admission_system_formed
    complete_data_admission_system_formed[unfolded complete_data_admission_system_def] package_retention_admission_call]
  by (simp only: complete_data_admission_system_def[symmetric])

lemma complete_data_admission_old_meaning:
  assumes "d\<in>system_definitions package_retention_admission_system"
  shows "(d,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_retention_admission_system"
  using added_definition_preserves_old(2)[OF package_retention_admission_system_formed
    complete_data_admission_system_formed[unfolded complete_data_admission_system_def], of d t] assms
  by (auto simp: complete_data_admission_system_def)

lemma complete_data_admission_clause [simp]:
  "((123,c),S)\<in>system_clauses complete_data_admission_system \<longleftrightarrow> (c,S)\<in>{(0,complete_data_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_retention_admission_system \<Longrightarrow>
    d\<in>system_definitions package_retention_admission_system" for d c S
    using package_retention_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((123,c),S)\<notin>system_clauses package_retention_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: complete_data_admission_system_def)
qed

lemma complete_data_admission_quotation_meaning:
  "(50,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (50,t)\<in>positive_meaning quotation_admission_system"
  using complete_data_admission_old_meaning[of 50 t]
    package_retention_admission_replay_meaning[of 50 t]
    replay_slot_reading_pattern_meaning[of 50 t]
    pattern_instantiation_quotation_meaning[of 50 t] by auto

lemma complete_data_admission_step:
  assumes read: "(50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
    (Payload_Term []) r t a (Payload_Term []))\<in>positive_meaning quotation_admission_system"
  shows "(123,complete_data_quotation_argument (Pair_Term a b) r t)
    \<in>positive_meaning complete_data_admission_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then a else if j=1 then b else if j=2 then r else t"
  have result: "(123,evaluate_pattern ?h (schema_conclusion complete_data_admission_schema))
    \<in>positive_meaning complete_data_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: complete_data_admission_schema_def schema_variables_def
          complete_data_admission_call complete_data_admission_quotation_meaning octets_formed_def\<close>)
  show ?thesis using result by (simp add: complete_data_admission_schema_def)
qed

lemma complete_data_admission_fields:
  "(123,z)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (\<exists>a b r t. z=complete_data_quotation_argument (Pair_Term a b) r t \<and>
      (50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
        (Payload_Term []) r t a (Payload_Term []))\<in>positive_meaning quotation_admission_system)"
proof
  assume holds: "(123,z)\<in>positive_meaning complete_data_admission_system"
  have ordinary: "schema_material_premises S={}"
    if "((123,c),S)\<in>system_clauses complete_data_admission_system" for c S
    using that by (simp add: complete_data_admission_schema_def)
  have valuation: "(123,z)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (\<exists>c S h. ((123,c),S)\<in>system_clauses complete_data_admission_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
      z=evaluate_pattern h (schema_conclusion S) \<and> schema_call_formed complete_data_admission_system 123 z \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning complete_data_admission_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((123,c),S)\<in>system_clauses complete_data_admission_system"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning complete_data_admission_system"
    using iffD1[OF valuation holds] by blast
  show "\<exists>a b r t. z=complete_data_quotation_argument (Pair_Term a b) r t \<and>
      (50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
        (Payload_Term []) r t a (Payload_Term []))\<in>positive_meaning quotation_admission_system"
    using clause shape support by (auto simp: complete_data_admission_schema_def
      complete_data_admission_quotation_meaning)
next
  assume "\<exists>a b r t. z=complete_data_quotation_argument (Pair_Term a b) r t \<and>
      (50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
        (Payload_Term []) r t a (Payload_Term []))\<in>positive_meaning quotation_admission_system"
  then show "(123,z)\<in>positive_meaning complete_data_admission_system"
    using complete_data_admission_step by blast
qed

theorem complete_data_admission_sound:
  assumes holds: "(123,z)\<in>positive_meaning complete_data_admission_system"
  shows "complete_data_admission_result z"
proof -
  obtain a b r t where shape: "z=complete_data_quotation_argument (Pair_Term a b) r t"
    and read: "(50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
      (Payload_Term []) r t a (Payload_Term []))\<in>positive_meaning quotation_admission_system"
    using holds by (simp only: complete_data_admission_fields) blast
  obtain E u q Is Ks where source: "environment_value_presents E (data_quotation_environment_term (Pair_Term a b))"
    and fields: "Payload_Term []=use_data_term u" "r=Payload_Term q"
      "a=data_list_term (map Payload_Term Is)" "Payload_Term []=data_list_term (map Payload_Term Ks)"
      "distinct Is" "distinct Ks" "term_quoted_at E u q t (set Is) (set Ks)"
    using quotation_admission_sound[OF read] by auto
  have use: "u=None" using fields(1) by (cases u) auto
  have slots: "Ks=[]" using fields(4) by (cases Ks) auto
  have native: "term_quoted_at E None q t (set Is) {}" using fields(7) use slots by simp
  obtain C where actual: "artifact_at E None C"
    using term_quoted_has_artifact[OF native] by blast
  have material: "artifact_value_presents C (Pair_Term a b)"
    using data_quotation_environment_recovers[OF source actual] by blast
  obtain A where carrier: "a=data_list_term (map Payload_Term A)" "distinct A"
    "set A=rra_carrier (object_structure C)"
    using artifact_value_carrier_field[OF material] by blast
  have lists: "Is=A"
    using fields(3) carrier(1) by (simp add: data_list_term_injective injective_mapped_lists[OF payload_term_inj])
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have complete: "complete_data_quoted_at C q t"
    by (simp only: complete_data_quotation_at_source[OF formed actual])
      (use native lists carrier(3) in simp)
  show ?thesis using shape fields(2) material complete by blast
qed

theorem complete_data_admission_complete:
  assumes material: "artifact_value_presents C c" and quote: "complete_data_quoted_at C q t"
  shows "(123,complete_data_quotation_argument c (Payload_Term q) t)
    \<in>positive_meaning complete_data_admission_system"
proof -
  obtain a b where c: "c=Pair_Term a b"
    using material by (auto simp: artifact_value_presents_def artifact_data_term_def)
  have presented: "artifact_value_presents C (Pair_Term a b)" using material c by simp
  obtain A where carrier: "a=data_list_term (map Payload_Term A)" "distinct A"
    "set A=rra_carrier (object_structure C)"
    using artifact_value_carrier_field[OF presented] by blast
  let ?E="literal_environment C {}"
  have source: "environment_value_presents ?E (data_quotation_environment_term (Pair_Term a b))"
    by (rule data_quotation_environment_presents[OF presented])
  have formed: "environment_formed ?E" using environment_value_presents_formed[OF source] by blast
  have actual: "artifact_at ?E None C" by simp
  have native: "term_quoted_at ?E None q t (set A) {}"
    using quote by (simp only: complete_data_quotation_at_source[OF formed actual] carrier(3))
  have read: "(50,term_quotation_argument (data_quotation_environment_term (Pair_Term a b))
      (Payload_Term []) (Payload_Term q) t a (Payload_Term []))\<in>positive_meaning quotation_admission_system"
    using quotation_admission_complete[OF native source carrier(2), where Ks="[]"] by (simp add: carrier(1))
  show ?thesis using complete_data_admission_step[OF read] c by simp
qed

theorem complete_data_admission_exact:
  "(123,z)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow> complete_data_admission_result z"
  using complete_data_admission_sound complete_data_admission_complete by blast

corollary complete_data_admission_at_artifact:
  assumes material: "artifact_value_presents C c"
  shows "(123,complete_data_quotation_argument c r t)\<in>positive_meaning complete_data_admission_system
    \<longleftrightarrow> (\<exists>q. r=Payload_Term q \<and> complete_data_quoted_at C q t)"
proof
  assume holds: "(123,complete_data_quotation_argument c r t)\<in>positive_meaning complete_data_admission_system"
  obtain D q where parts: "artifact_value_presents D c" "r=Payload_Term q" "complete_data_quoted_at D q t"
    using holds by (simp only: complete_data_admission_exact factor_term.inject; blast)
  have same: "D=C" by (rule artifact_value_presents_unique[OF parts(1) material])
  show "\<exists>q. r=Payload_Term q \<and> complete_data_quoted_at C q t"
    using parts(2,3) same by blast
next
  assume "\<exists>q. r=Payload_Term q \<and> complete_data_quoted_at C q t"
  then obtain q where parts: "r=Payload_Term q" "complete_data_quoted_at C q t" by blast
  show "(123,complete_data_quotation_argument c r t)\<in>positive_meaning complete_data_admission_system"
    using complete_data_admission_complete[OF material parts(2)] by (simp only: parts(1))
qed

corollary complete_data_admission_on_values:
  assumes material: "artifact_value_presents C c"
  shows "(123,complete_data_quotation_argument c (Payload_Term q) t)\<in>positive_meaning complete_data_admission_system
    \<longleftrightarrow> complete_data_quoted_at C q t"
  by (simp only: complete_data_admission_at_artifact[OF material]) auto

corollary complete_data_admission_presentation_invariance:
  assumes "artifact_value_presents C c" "artifact_value_presents C d"
  shows "(123,complete_data_quotation_argument c r t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (123,complete_data_quotation_argument d r t)\<in>positive_meaning complete_data_admission_system"
  by (simp only: complete_data_admission_at_artifact[OF assms(1)]
    complete_data_admission_at_artifact[OF assms(2)])

theorem complete_data_admission_unique:
  assumes material: "artifact_value_presents C c"
    and first: "(123,complete_data_quotation_argument c r t)\<in>positive_meaning complete_data_admission_system"
    and second: "(123,complete_data_quotation_argument c s v)\<in>positive_meaning complete_data_admission_system"
  shows "r=s \<and> t=v"
  using first second complete_data_quotation_whole_unique
  by (auto simp: complete_data_admission_at_artifact[OF material])

theorem complete_data_admission_every_copy:
  assumes formed: "term_formed t" and closed: "self_contained_term t"
    and address: "finite_addressing (rra_carrier (object_structure (term_syntax t))) f"
    and material: "artifact_value_presents (push_object f (term_syntax t)) c"
  shows "(123,complete_data_quotation_argument c (Payload_Term (f [])) t)
    \<in>positive_meaning complete_data_admission_system"
  by (rule complete_data_admission_complete[OF material
    complete_data_quotation_every_addressing[OF formed closed address]])

theorem complete_data_admission_total:
  assumes "term_formed t" "self_contained_term t"
  shows "\<exists>c. artifact_value_presents (term_syntax t) c \<and>
    (123,complete_data_quotation_argument c (Payload_Term []) t)\<in>positive_meaning complete_data_admission_system"
  using artifact_value_presents_total[OF term_syntax_formed[OF assms(1)]]
    complete_data_admission_complete[OF _ complete_data_quotation_total[OF assms]] by blast

theorem complete_data_admission_rejects_empty_carrier:
  assumes material: "artifact_value_presents C c" and empty: "rra_carrier (object_structure C)={}"
  shows "(123,complete_data_quotation_argument c r t)\<notin>positive_meaning complete_data_admission_system"
  using complete_data_quotation_anchor empty
  by (auto simp: complete_data_admission_at_artifact[OF material] anchor_formed_def)

text \<open>
  The sole ordinary premise reads the supplied artifact in a derived environment
  containing exactly that artifact and no bindings. Its interior is the complete
  carrier field of the supplied artifact value. The existing quotation reader
  checks the environment and artifact data; an empty slot boundary derives the
  self-contained term property.

  Admission is exact on every term, including malformed inputs, and accepts
  every complete presentation of each source artifact. Every formed data term
  and every formed injective copy supplies admitted material. Root and body are
  recovered uniquely from that complete artifact within this presentation class.

  This establishes the link between complete artifact data, native quotation,
  and the existing complete-copy profile. It gives no intrinsic privilege to
  this topology among other presentation classes. Program-scope reading is the
  next explicit composition with the package-retention relation.
\<close>

end
