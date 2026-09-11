theory Factor_Replay_Reading
  imports Factor_Replay_Presentations Factor_Complete_Data_Admission
    Factor_Reader_Contracts Factor_Constrained_Contracts
begin

section \<open>Four ordinary views read replay sources and compatible quotations\<close>

abbreviation replay_source_schema :: "(nat,nat,nat) factor_schema" where
  "replay_source_schema \<equiv> reader_projection_clause 0 1 0 111"

abbreviation closed_replay_source_schema :: "(nat,nat,nat) factor_schema" where
  "closed_replay_source_schema \<equiv> fixed_result_clause 0 0 111 (Payload_Term [])"

abbreviation replay_reading_schema :: "(nat,nat,nat) factor_schema" where
  "replay_reading_schema \<equiv> constrained_reading_schema 123 128"

abbreviation closed_replay_reading_schema :: "(nat,nat,nat) factor_schema" where
  "closed_replay_reading_schema \<equiv> constrained_reading_schema 123 129"

definition replay_source_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_source_system=add_view_definition complete_data_admission_system 128 data_x {(0,replay_source_schema)}"

interpretation replay_source_view: positive_view complete_data_admission_system 128 data_x "{(0,replay_source_schema)}"
  by (rule reader_projection_view) auto

lemma replay_source_system_formed [simp]: "schema_system_formed replay_source_system"
  using replay_source_view.formed by (simp only: replay_source_system_def)

lemma replay_source_definitions [simp]:
  "system_definitions replay_source_system=insert 128 (system_definitions complete_data_admission_system)"
  by (simp add: replay_source_system_def)

lemma replay_source_call:
  "schema_call_formed replay_source_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_source_system \<and> term_formed t"
  using added_variable_calls[OF complete_data_admission_system_formed
    replay_source_system_formed[unfolded replay_source_system_def] complete_data_admission_call]
  by (simp only: replay_source_system_def[symmetric])

lemma replay_source_old_meaning:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "(d,t)\<in>positive_meaning replay_source_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning complete_data_admission_system"
  using replay_source_view.old_meaning[OF assms, of t]
  by (simp only: replay_source_system_def)

definition closed_replay_source_system :: "(nat,nat,nat,nat) schema_system" where
  "closed_replay_source_system=add_view_definition replay_source_system 129 data_x {(0,closed_replay_source_schema)}"

interpretation closed_replay_source_view: positive_view replay_source_system 129 data_x "{(0,closed_replay_source_schema)}"
  by (rule fixed_result_view) (auto simp: octets_formed_def)

lemma closed_replay_source_system_formed [simp]: "schema_system_formed closed_replay_source_system"
  using closed_replay_source_view.formed by (simp only: closed_replay_source_system_def)

lemma closed_replay_source_definitions [simp]:
  "system_definitions closed_replay_source_system=insert 129 (system_definitions replay_source_system)"
  by (simp add: closed_replay_source_system_def)

lemma closed_replay_source_call:
  "schema_call_formed closed_replay_source_system d t \<longleftrightarrow>
    d\<in>system_definitions closed_replay_source_system \<and> term_formed t"
  using added_variable_calls[OF replay_source_system_formed
    closed_replay_source_system_formed[unfolded closed_replay_source_system_def] replay_source_call]
  by (simp only: closed_replay_source_system_def[symmetric])

lemma closed_replay_source_old_meaning:
  assumes "d\<in>system_definitions replay_source_system"
  shows "(d,t)\<in>positive_meaning closed_replay_source_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_source_system"
  using closed_replay_source_view.old_meaning[OF assms, of t]
  by (simp only: closed_replay_source_system_def)

definition replay_reading_stage_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_reading_stage_system=add_view_definition closed_replay_source_system 130 data_x {(0,replay_reading_schema)}"

interpretation replay_reading_stage_view: positive_view closed_replay_source_system 130 data_x "{(0,replay_reading_schema)}"
  by (rule constrained_reading_view) auto

lemma replay_reading_stage_system_formed [simp]: "schema_system_formed replay_reading_stage_system"
  using replay_reading_stage_view.formed by (simp only: replay_reading_stage_system_def)

lemma replay_reading_stage_definitions [simp]:
  "system_definitions replay_reading_stage_system=insert 130 (system_definitions closed_replay_source_system)"
  by (simp add: replay_reading_stage_system_def)

lemma replay_reading_stage_call:
  "schema_call_formed replay_reading_stage_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_reading_stage_system \<and> term_formed t"
  using added_variable_calls[OF closed_replay_source_system_formed
    replay_reading_stage_system_formed[unfolded replay_reading_stage_system_def] closed_replay_source_call]
  by (simp only: replay_reading_stage_system_def[symmetric])

lemma replay_reading_stage_old_meaning:
  assumes "d\<in>system_definitions closed_replay_source_system"
  shows "(d,t)\<in>positive_meaning replay_reading_stage_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning closed_replay_source_system"
  using replay_reading_stage_view.old_meaning[OF assms, of t]
  by (simp only: replay_reading_stage_system_def)

definition replay_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_reading_system=add_view_definition replay_reading_stage_system 131 data_x {(0,closed_replay_reading_schema)}"

interpretation replay_reading_view: positive_view replay_reading_stage_system 131 data_x "{(0,closed_replay_reading_schema)}"
  by (rule constrained_reading_view) auto

lemma replay_reading_system_formed [simp]: "schema_system_formed replay_reading_system"
  using replay_reading_view.formed by (simp only: replay_reading_system_def)

lemma replay_reading_definitions [simp]:
  "system_definitions replay_reading_system=insert 131 (system_definitions replay_reading_stage_system)"
  by (simp add: replay_reading_system_def)

lemma replay_reading_call:
  "schema_call_formed replay_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_reading_system \<and> term_formed t"
  using added_variable_calls[OF replay_reading_stage_system_formed
    replay_reading_system_formed[unfolded replay_reading_system_def] replay_reading_stage_call]
  by (simp only: replay_reading_system_def[symmetric])

lemma replay_reading_old_meaning:
  assumes "d\<in>system_definitions replay_reading_stage_system"
  shows "(d,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_reading_stage_system"
  using replay_reading_view.old_meaning[OF assms, of t]
  by (simp only: replay_reading_system_def)

lemma replay_reading_base_meaning:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "(d,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning complete_data_admission_system"
  using replay_reading_old_meaning[of d t] replay_reading_stage_old_meaning[of d t]
    closed_replay_source_old_meaning[of d t] replay_source_old_meaning[OF assms, of t] assms by auto

lemma complete_data_admission_replay_meaning:
  assumes "d\<in>system_definitions replay_admission_system"
  shows "(d,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_admission_system"
  using complete_data_admission_old_meaning[of d t] package_retention_admission_old_meaning[of d t]
    package_lists_previous_meaning[of d t] package_slot_reading_old_meaning[of d t]
    package_source_reading_old_meaning[of d t] scope_forwarding_old_meaning[of d t]
    native_positive_admission_previous_meaning[OF assms, of t] assms by auto

lemma replay_source_exact:
  "(128,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system)"
proof -
  have source: "(128,t)\<in>positive_meaning replay_source_system \<longleftrightarrow>
      (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning complete_data_admission_system)"
    unfolding replay_source_system_def
    by (rule reader_projection_view_meaning[OF replay_source_view.positive_view_axioms]) simp
  show ?thesis using replay_reading_old_meaning[of 128 t] replay_reading_stage_old_meaning[of 128 t]
    closed_replay_source_old_meaning[of 128 t] source
    complete_data_admission_replay_meaning[of 111] by auto
qed

lemma closed_replay_source_exact:
  "(129,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system"
proof -
  have source: "(129,t)\<in>positive_meaning closed_replay_source_system \<longleftrightarrow>
      (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_source_system"
    unfolding closed_replay_source_system_def
    by (rule fixed_result_view_meaning[OF closed_replay_source_view.positive_view_axioms])
  show ?thesis using replay_reading_old_meaning[of 129 t] replay_reading_stage_old_meaning[of 129 t]
    source replay_source_old_meaning[of 111 "Pair_Term t (Payload_Term [])"]
    complete_data_admission_replay_meaning[of 111 "Pair_Term t (Payload_Term [])"] by auto
qed

lemma replay_reading_clause:
  "((130,c),S)\<in>system_clauses replay_reading_system \<longleftrightarrow>
    (c,S)\<in>{(0,replay_reading_schema)}"
  using replay_reading_stage_view.no_old_clause[of c S]
  by (simp add: replay_reading_system_def replay_reading_stage_system_def)

lemma closed_replay_reading_clause:
  "((131,c),S)\<in>system_clauses replay_reading_system \<longleftrightarrow>
    (c,S)\<in>{(0,closed_replay_reading_schema)}"
  using replay_reading_view.no_old_clause[of c S] by (simp add: replay_reading_system_def)

lemma replay_reading_source_clause:
  "((128,c),S)\<in>system_clauses replay_reading_system \<longleftrightarrow>
    (c,S)\<in>{(0,replay_source_schema)}"
  using replay_source_view.no_old_clause[of c S]
  by (simp add: replay_reading_system_def replay_reading_stage_system_def
    closed_replay_source_system_def replay_source_system_def)

lemma replay_reading_closed_source_clause:
  "((129,c),S)\<in>system_clauses replay_reading_system \<longleftrightarrow>
    (c,S)\<in>{(0,closed_replay_source_schema)}"
  using closed_replay_source_view.no_old_clause[of c S]
  by (simp add: replay_reading_system_def replay_reading_stage_system_def closed_replay_source_system_def)

lemma replay_reading_rule_profiles:
  assumes profile: "(d,S)\<in>{(128,replay_source_schema),(129,closed_replay_source_schema),
    (130,replay_reading_schema),(131,closed_replay_reading_schema)}"
  shows "d\<in>system_definitions replay_reading_system"
    and "system_interface replay_reading_system d=Pattern_Variable 0"
    and "system_clause_family replay_reading_system d={(0,S)}"
proof -
  show "d\<in>system_definitions replay_reading_system" using profile by auto
  have entry: "(d,Pattern_Variable 0)\<in>system_interfaces replay_reading_system"
    using profile by (auto simp: replay_reading_system_def replay_reading_stage_system_def
      closed_replay_source_system_def replay_source_system_def)
  show "system_interface replay_reading_system d=Pattern_Variable 0"
    by (rule system_interface_unique[OF replay_reading_system_formed entry])
  show "system_clause_family replay_reading_system d={(0,S)}"
    by (rule set_eqI; rename_tac z; case_tac z)
      (use profile in \<open>auto simp: replay_reading_source_clause replay_reading_closed_source_clause
        replay_reading_clause closed_replay_reading_clause\<close>)
qed

interpretation replay_composition: constrained_reading_profile replay_reading_system 130 123 128
  by (unfold_locales) (auto simp: replay_reading_clause replay_reading_call)

interpretation closed_replay_composition: constrained_reading_profile replay_reading_system 131 123 129
  by (unfold_locales) (auto simp: closed_replay_reading_clause replay_reading_call)

lemma replay_reading_quotation_meaning:
  "(123,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  by (rule replay_reading_base_meaning) simp

theorem replay_reading_exact:
  "(130,v)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (\<exists>t. (\<exists>h. (111,Pair_Term t h)\<in>positive_meaning replay_admission_system) \<and>
      quoted_body_presents t v)"
  by (simp only: replay_composition.exact replay_reading_quotation_meaning
      complete_data_admission_exact replay_source_exact)
    (auto simp: quoted_body_presents_def; blast)

theorem closed_replay_reading_exact:
  "(131,v)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (\<exists>t. (111,Pair_Term t (Payload_Term []))\<in>positive_meaning replay_admission_system \<and>
      quoted_body_presents t v)"
  by (simp only: closed_replay_composition.exact replay_reading_quotation_meaning
      complete_data_admission_exact closed_replay_source_exact)
    (auto simp: quoted_body_presents_def; blast)

section \<open>The native entries admit exactly the derived classes\<close>

theorem replay_source_presentation_class:
  "presentation_class replay_scope_presents replay_subject
    (\<lambda>t. (128,t)\<in>positive_meaning replay_reading_system)"
  using replay_scope_presentation_class by (simp only: replay_source_exact)

theorem closed_replay_source_presentation_class:
  "presentation_class closed_replay_scope_presents closed_replay_subject
    (\<lambda>t. (129,t)\<in>positive_meaning replay_reading_system)"
  using closed_replay_scope_presentation_class by (simp only: closed_replay_source_exact)

theorem replay_reading_presentation_class:
  "presentation_class replay_quoted_body_presents replay_subject
    (\<lambda>v. (130,v)\<in>positive_meaning replay_reading_system)"
  using replay_quoted_body_presentation_class by (simp only: replay_reading_exact)

theorem closed_replay_reading_presentation_class:
  "presentation_class closed_replay_quoted_body_presents closed_replay_subject
    (\<lambda>v. (131,v)\<in>positive_meaning replay_reading_system)"
  using closed_replay_quoted_body_presentation_class by (simp only: closed_replay_reading_exact)

theorem replay_source_at_context:
  assumes context_value: "replay_context_presents z t"
  shows "(128,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (\<exists>H. replay_at_context z H)"
  using context_value replay_contexts.recovery
  by (simp only: replay_source_exact replay_scope_admissible[symmetric]) blast

theorem closed_replay_source_at_context:
  assumes context_value: "replay_context_presents z t"
  shows "(129,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow> replay_at_context z {}"
  by (simp only: closed_replay_source_exact;
      rule replay_admission_at_presentations[OF context_value]) simp

theorem replay_source_on_values:
  assumes presented: "replay_value_presents E pu pr au ar root t"
  shows "(128,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      (\<exists>H. native_replay_at E pu pr au ar root H)"
    and "(129,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      native_replay_at E pu pr au ar root {}"
proof -
  have context_value: "replay_context_presents ((E,((pu,pr),(au,ar))),root) t"
    using presented by simp
  show "(128,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      (\<exists>H. native_replay_at E pu pr au ar root H)"
    by (simp only: replay_source_at_context[OF context_value] fst_conv snd_conv)
  show "(129,t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      native_replay_at E pu pr au ar root {}"
    by (simp only: closed_replay_source_at_context[OF context_value] fst_conv snd_conv)
qed

theorem replay_reading_at_body:
  assumes material: "artifact_value_presents C c" and quotation: "complete_data_quoted_at C r t"
  shows "(130,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (128,t)\<in>positive_meaning replay_reading_system"
  using assms by (auto simp: replay_reading_exact replay_source_exact quoted_body_at_pair)

theorem closed_replay_reading_at_body:
  assumes material: "artifact_value_presents C c" and quotation: "complete_data_quoted_at C r t"
  shows "(131,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (129,t)\<in>positive_meaning replay_reading_system"
  using assms by (auto simp: closed_replay_reading_exact closed_replay_source_exact quoted_body_at_pair)

theorem replay_reading_at_context:
  assumes material: "artifact_value_presents C c" and quotation: "complete_data_quoted_at C r t"
    and context_value: "replay_context_presents z t"
  shows "(130,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
    (\<exists>H. replay_at_context z H)"
    and "(131,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow> replay_at_context z {}"
  by (simp_all only: replay_reading_at_body[OF material quotation]
    closed_replay_reading_at_body[OF material quotation]
    replay_source_at_context[OF context_value] closed_replay_source_at_context[OF context_value])

theorem replay_reading_on_values:
  assumes material: "artifact_value_presents C c" and quotation: "complete_data_quoted_at C r t"
    and presented: "replay_value_presents E pu pr au ar root t"
  shows "(130,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      (\<exists>H. native_replay_at E pu pr au ar root H)"
    and "(131,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      native_replay_at E pu pr au ar root {}"
  by (simp_all only: replay_reading_at_body[OF material quotation]
    closed_replay_reading_at_body[OF material quotation] replay_source_on_values[OF presented])

theorem replay_reading_compatible_presentations:
  assumes first: "artifact_value_presents C c" "complete_data_quoted_at C r p" "replay_context_presents z p"
    and second: "artifact_value_presents D d" "complete_data_quoted_at D s q" "replay_context_presents z q"
  shows "(130,Pair_Term c p)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      (130,Pair_Term d q)\<in>positive_meaning replay_reading_system"
    and "(131,Pair_Term c p)\<in>positive_meaning replay_reading_system \<longleftrightarrow>
      (131,Pair_Term d q)\<in>positive_meaning replay_reading_system"
  by (simp_all only: replay_reading_at_context[OF first] replay_reading_at_context[OF second])

theorem replay_reading_total:
  assumes replay: "native_replay_at E pu pr au ar root H"
  shows "\<exists>c t. artifact_value_presents (term_syntax t) c \<and>
    complete_data_quoted_at (term_syntax t) [] t \<and> replay_value_presents E pu pr au ar root t \<and>
    replay_quoted_body_presents (((E,((pu,pr),(au,ar))),root),H) (Pair_Term c t) \<and>
    (130,Pair_Term c t)\<in>positive_meaning replay_reading_system \<and>
    ((131,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow> H={})"
proof -
  let ?z="((E,((pu,pr),(au,ar))),root)"
  obtain t b where present: "replay_with_reading_presents ((?z,H),b) t"
    and formed: "term_formed t" "self_contained_term t"
    using native_replay_presentation_total[OF replay] by (simp only: fst_conv snd_conv; blast)
  have context_value: "replay_context_presents ?z t" using present by simp
  have quotation: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed])
  obtain c where material: "artifact_value_presents (term_syntax t) c"
    using artifact_value_presents_total[OF term_syntax_formed[OF formed(1)]] by blast
  have body: "quoted_body_presents t (Pair_Term c t)"
    using material quotation by (auto simp: quoted_body_at_pair)
  have body_record: "replay_quoted_body_presents (?z,H) (Pair_Term c t)"
    using present body by (auto simp: composed_presentation_def)
  have conditional: "(130,Pair_Term c t)\<in>positive_meaning replay_reading_system"
    using replay by (simp only: replay_reading_at_context(1)[OF material quotation context_value]
      fst_conv snd_conv; blast)
  have empty_boundary: "native_replay_at E pu pr au ar root {} \<longleftrightarrow> H={}"
  proof
    assume empty: "native_replay_at E pu pr au ar root {}"
    show "H={}" by (rule native_replay_assumptions_unique[OF replay empty])
  next
    assume "H={}"
    with replay show "native_replay_at E pu pr au ar root {}" by simp
  qed
  have closed: "(131,Pair_Term c t)\<in>positive_meaning replay_reading_system \<longleftrightarrow> H={}"
    using empty_boundary
    by (simp only: replay_reading_at_context(2)[OF material quotation context_value] fst_conv snd_conv)
  show ?thesis by (rule exI[of _ c], rule exI[of _ t])
    (use material quotation context_value body_record conditional closed in simp)
qed

text \<open>
  Projection leaves the exact assertion boundary private while deriving it
  from the complete replay context. The closed-source entry matches that
  boundary against the empty collection. Two constrained-reading instances
  then check complete quotations of the corresponding source classes.

  The four clauses use only the existing replay and quotation readers.
  Every term is covered by their admission equations. The class domains
  are the independent native replay relations; the generic class proofs
  supply totality, recovery, and compatibility with the same actual body.

  Different complete artifacts and body terms may present the same replay
  context. Invariance requires each artifact to quote its own supplied body.
  A source artifact and an unrelated body do not become compatible merely
  because that body presents a related subject.
\<close>

end
