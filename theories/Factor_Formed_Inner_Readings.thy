theory Factor_Formed_Inner_Readings
  imports Factor_Indexed_Readings Factor_Demanded_Graph_Readings
begin

section \<open>A formed body reads through formed bodies\<close>

text \<open>
  Rule (a) of DECISIONS.md, task 482's entry: a formed body's premise, its environment's formation,
  holds in every reading it calls on that environment, so each inner reading is called through a
  formed body and checks nothing (@{text Established_Premises}: the check made where its premise is
  established). The formed bodies of the proof-node readings, the definition readings and the call
  readings still checked it inside: the proof-node readings through the guarded site-citation, table,
  application and site-link readings and the term readings under them, and every term and pattern
  reading through the targets of its citations, whose filter checks the formation of each artifact
  a citation reaches. The bodies below call formed bodies only; each is equal to the original under
  the formation its caller establishes, and no existing constant changes its definition.
\<close>

lemma fimage_agree:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> f x=g x"
  shows "fimage f A=fimage g A"
  by (rule fimage_cong) (simp_all add: assms)

lemma ffUnion_fimage_agree:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> f x=g x"
  shows "ffUnion (fimage f A)=ffUnion (fimage g A)"
  by (simp only: fimage_agree[OF assms])

lemma ffilter_agree:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> P x=Q x"
  shows "ffilter P A=ffilter Q A"
  using assms by (auto intro!: fset_eqI)

section \<open>The targets of a formed environment's citations\<close>

text \<open>
  An artifact of a formed environment is formed, so the target a citation reaches is formed exactly
  when its address belongs to the artifact's carrier, and a whole artifact always is.
\<close>

fun finite_citation_targets_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> finite_exact_target fset" where
  "finite_citation_targets_formed E u (Local a)=fimage (\<lambda>C. Finite_Anchor C a)
    (ffilter (\<lambda>C. a |\<in>| finite_carrier (finite_structure C)) (finite_artifacts_at E u))"
| "finite_citation_targets_formed E u (External k a)=fimage (\<lambda>C. Finite_Anchor C a)
    (ffilter (\<lambda>C. a |\<in>| finite_carrier (finite_structure C)) (finite_bound_artifacts E u k))"
| "finite_citation_targets_formed E u Local_Whole=fimage Finite_Whole (finite_artifacts_at E u)"
| "finite_citation_targets_formed E u (External_Whole k)=fimage Finite_Whole (finite_bound_artifacts E u k)"

lemma formed_bound_artifact:
  assumes formed: "finite_environment_formed E" and member: "C |\<in>| finite_bound_artifacts E u k"
  shows "finite_exact_formed C"
proof -
  obtain v where "C |\<in>| finite_artifacts_at E v"
    using member by (auto simp: finite_bound_artifacts_member)
  then show ?thesis by (rule formed_environment_artifact[OF formed])
qed

lemma finite_citation_targets_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_citation_targets E u=finite_citation_targets_formed E u"
proof
  fix c
  have local: "\<And>C. C |\<in>| finite_artifacts_at E u \<Longrightarrow> finite_exact_formed C"
    by (rule formed_environment_artifact[OF formed])
  have bound: "\<And>C k. C |\<in>| finite_bound_artifacts E u k \<Longrightarrow> finite_exact_formed C"
    by (rule formed_bound_artifact[OF formed])
  show "finite_citation_targets E u c=finite_citation_targets_formed E u c"
  proof (cases c)
    case (Local a)
    have "ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (finite_artifacts_at E u)=
        ffilter (\<lambda>C. a |\<in>| finite_carrier (finite_structure C)) (finite_artifacts_at E u)"
      by (rule ffilter_agree) (simp add: local)
    then show ?thesis by (simp only: Local finite_citation_targets.simps finite_citation_targets_formed.simps)
  next
    case (External k a)
    have "ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (finite_bound_artifacts E u k)=
        ffilter (\<lambda>C. a |\<in>| finite_carrier (finite_structure C)) (finite_bound_artifacts E u k)"
      by (rule ffilter_agree) (simp add: bound)
    then show ?thesis by (simp only: External finite_citation_targets.simps finite_citation_targets_formed.simps)
  next
    case Local_Whole
    have "ffilter finite_exact_formed (finite_artifacts_at E u)=finite_artifacts_at E u"
      by (rule fset_eqI) (auto simp: local)
    then show ?thesis by (simp only: Local_Whole finite_citation_targets.simps finite_citation_targets_formed.simps)
  next
    case (External_Whole k)
    have "ffilter finite_exact_formed (finite_bound_artifacts E u k)=finite_bound_artifacts E u k"
      by (rule fset_eqI) (auto simp: bound)
    then show ?thesis by (simp only: External_Whole finite_citation_targets.simps finite_citation_targets_formed.simps)
  qed
qed

section \<open>The readings of a use, stated over the targets of its citations\<close>

text \<open>
  The readings of a use through its artifacts' readings (@{text Factor_Indexed_Readings}) read the
  environment in two places only: the locations of a call's citations, already formation-free, and the
  targets of a term's citations. They are stated once over the reader of those targets; supplied with
  @{const finite_citation_targets} they are the existing readings, and supplied with the formed targets
  they check nothing of the environment.
\<close>

definition targeted_target_readings ::
  "(citation \<Rightarrow> finite_exact_target fset) \<Rightarrow> artifact_reading \<Rightarrow> local_address \<Rightarrow>
    finite_factor_term finite_syntax_reading fset" where
  "targeted_target_readings tg R r=ffUnion (fimage (\<lambda>(c,I).
    if finite_citation_slots c={||} then {||}
    else fimage (\<lambda>T. (Finite_Target T,I,finite_citation_slots c)) (tg c))
      (read_citation_candidates R r))"

fun targeted_term_readings ::
  "nat \<Rightarrow> (citation \<Rightarrow> finite_exact_target fset) \<Rightarrow> artifact_reading fset \<Rightarrow> local_address \<Rightarrow>
    finite_factor_term finite_syntax_reading fset" where
  "targeted_term_readings 0 tg As r={||}"
| "targeted_term_readings (Suc n) tg As r=ffUnion (fimage (\<lambda>R.
    targeted_target_readings tg R r |\<union>| read_payload_readings R r |\<union>|
    read_record_readings R r Finite_Pair {||} (targeted_term_readings n tg As)) As)"

definition targeted_pattern_constants where
  "targeted_pattern_constants tg As V r=ffUnion (fimage (finite_pattern_leaf V) (targeted_term_readings 1 tg As r))"

fun targeted_pattern_readings ::
  "nat \<Rightarrow> (citation \<Rightarrow> finite_exact_target fset) \<Rightarrow> artifact_reading fset \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address finite_term_pattern finite_syntax_reading fset" where
  "targeted_pattern_readings 0 tg As V r={||}"
| "targeted_pattern_readings (Suc n) tg As V r=targeted_pattern_constants tg As V r |\<union>|
    ffUnion (fimage (\<lambda>R. read_variable_readings R V r |\<union>|
      read_record_readings R r Finite_Pattern_Pair V (targeted_pattern_readings n tg As V)) As)"

definition targeted_sized_pattern_readings where
  "targeted_sized_pattern_readings tg As V r=ffUnion (fimage (\<lambda>R.
    targeted_pattern_readings (reading_size R) tg As V r) As)"

definition targeted_prospective_call_readings where
  "targeted_prospective_call_readings tg E u As V r=read_call_readings E u As V r (targeted_sized_pattern_readings tg As V)"

fun targeted_pattern_vector_readings where
  "targeted_pattern_vector_readings tg As V []={|([],{||},{||})|}"
| "targeted_pattern_vector_readings tg As V (r#rs)=ffUnion (fimage (\<lambda>(p,J0,W0).
    ffUnion (fimage (\<lambda>(ps,J,W).
      if J0 |\<inter>| J={||} \<and> (J0 |\<union>| J) |\<inter>| (W0 |\<union>| W)={||}
      then {|(p#ps,J0 |\<union>| J,W0 |\<union>| W)|} else {||})
        (targeted_pattern_vector_readings tg As V rs))) (targeted_sized_pattern_readings tg As V r))"

definition targeted_pattern_record_readings where
  "targeted_pattern_record_readings tg As V r n=ffUnion (fimage (\<lambda>R. ffUnion (fimage (\<lambda>(ports,roots).
    finite_frame_readings V r ports (targeted_pattern_vector_readings tg As V roots))
      (read_record_candidates R r n))) As)"

definition targeted_material_readings where
  "targeted_material_readings tg As V r=ffUnion (fimage (\<lambda>(ps,I,K).
    fimage (\<lambda>M. (M,I,K)) (finite_material_from_fields ps)) (targeted_pattern_record_readings tg As V r 5))"

definition targeted_premise_readings where
  "targeted_premise_readings tg E u As V r=
    fimage (\<lambda>(c,I,K). (Inl c,I,K)) (targeted_prospective_call_readings tg E u As V r) |\<union>|
    fimage (\<lambda>(M,I,K). (Inr M,I,K)) (targeted_material_readings tg As V r)"

definition targeted_premise_family_readings where
  "targeted_premise_family_readings tg E u As V r=
    fimage (\<lambda>F. (finite_left_sockets F,finite_right_sockets F))
      (read_family_readings As r (\<lambda>a. finite_reading_values (targeted_premise_readings tg E u As V a)))"

definition targeted_schema_body_readings where
  "targeted_schema_body_readings tg E u As R r ps b c m =
    ffUnion (fimage (\<lambda>V. ffUnion (fimage (\<lambda>(p,I,K).
      ffUnion (fimage (\<lambda>(Q,M).
        let S=\<lparr>finite_schema_conclusion=p,finite_schema_premises=Q,finite_schema_materials=M\<rparr> in
        if V=finite_schema_variables S \<and>
          finsert r (fset_of_list ps) |\<inter>| (finsert b V |\<union>| I |\<union>| {|m|})={||} \<and>
          finsert b V |\<inter>| I={||} \<and> b\<noteq>m \<and> m |\<notin>| I
        then {|S|} else {||}) (targeted_premise_family_readings tg E u As V m)))
      (targeted_sized_pattern_readings tg As V c))) (read_binder_scope_candidates R b))"

definition targeted_schema_readings where
  "targeted_schema_readings tg E u As r=ffUnion (fimage (\<lambda>R.
    read_three_field_record R r (targeted_schema_body_readings tg E u As R r)) As)"

definition targeted_scoped_record where
  "targeted_scoped_record tg As R r ps b q=ffUnion (fimage (\<lambda>V.
    ffilter (\<lambda>(p,I,K). finite_pattern_variables p=V)
      (finite_join_readings (\<lambda>(_::unit) p. p) {||} r ps {|((),finsert b V,{||})|}
        (targeted_sized_pattern_readings tg As V q))) (read_binder_scope_candidates R b))"

definition targeted_scoped_pattern_readings where
  "targeted_scoped_pattern_readings tg As r=ffUnion (fimage (\<lambda>R.
    read_two_field_record R r (targeted_scoped_record tg As R r)) As)"

definition targeted_definition_body_readings where
  "targeted_definition_body_readings tg E u As r ps i m =
    ffUnion (fimage (\<lambda>(p,I,K).
      if finsert r (fset_of_list ps) |\<inter>| (I |\<union>| {|m|})={||} \<and> m |\<notin>| I
      then fimage (Pair p) (read_family_readings As m (targeted_schema_readings tg E u As)) else {||})
        (targeted_scoped_pattern_readings tg As i))"

definition targeted_definition_readings where
  "targeted_definition_readings tg E u As r=ffUnion (fimage (\<lambda>R.
    read_two_field_record R r (targeted_definition_body_readings tg E u As r)) As)"

subsection \<open>Over the environment's own targets they are the existing readings\<close>

lemma read_target_readings_targeted:
  "read_target_readings E u R r=targeted_target_readings (finite_citation_targets E u) R r"
  by (simp only: read_target_readings_def targeted_target_readings_def)

lemma read_term_readings_targeted:
  "read_term_readings n E u As=targeted_term_readings n (finite_citation_targets E u) As"
proof (induction n)
  case 0 show ?case by (rule ext) (simp only: read_term_readings.simps targeted_term_readings.simps)
next
  case (Suc n) show ?case
    by (rule ext) (simp only: read_term_readings.simps targeted_term_readings.simps
        read_target_readings_targeted Suc.IH)
qed

lemma read_pattern_constants_targeted:
  "read_pattern_constants E u As V r=targeted_pattern_constants (finite_citation_targets E u) As V r"
  by (simp only: read_pattern_constants_def targeted_pattern_constants_def read_term_readings_targeted)

lemma read_pattern_readings_targeted:
  "read_pattern_readings n E u As V=targeted_pattern_readings n (finite_citation_targets E u) As V"
proof (induction n)
  case 0 show ?case by (rule ext) (simp only: read_pattern_readings.simps targeted_pattern_readings.simps)
next
  case (Suc n) show ?case
    by (rule ext) (simp only: read_pattern_readings.simps targeted_pattern_readings.simps
        read_pattern_constants_targeted Suc.IH)
qed

lemma read_sized_pattern_readings_targeted:
  "read_sized_pattern_readings E u As V=targeted_sized_pattern_readings (finite_citation_targets E u) As V"
  by (rule ext) (simp only: read_sized_pattern_readings_def targeted_sized_pattern_readings_def
      read_pattern_readings_targeted)

lemma read_prospective_call_readings_targeted:
  "read_prospective_call_readings E u As V r=
    targeted_prospective_call_readings (finite_citation_targets E u) E u As V r"
  by (simp only: read_prospective_call_readings_def targeted_prospective_call_readings_def
      read_sized_pattern_readings_targeted)

lemma read_pattern_vector_readings_targeted:
  "read_pattern_vector_readings E u As V rs=targeted_pattern_vector_readings (finite_citation_targets E u) As V rs"
  by (induction rs) (simp_all only: read_pattern_vector_readings.simps targeted_pattern_vector_readings.simps
      read_sized_pattern_readings_targeted)

lemma read_pattern_record_readings_targeted:
  "read_pattern_record_readings E u As V r n=targeted_pattern_record_readings (finite_citation_targets E u) As V r n"
  by (simp only: read_pattern_record_readings_def targeted_pattern_record_readings_def
      read_pattern_vector_readings_targeted)

lemma read_material_readings_targeted:
  "read_material_readings E u As V r=targeted_material_readings (finite_citation_targets E u) As V r"
  by (simp only: read_material_readings_def targeted_material_readings_def read_pattern_record_readings_targeted)

lemma read_premise_readings_targeted:
  "read_premise_readings E u As V r=targeted_premise_readings (finite_citation_targets E u) E u As V r"
  by (simp only: read_premise_readings_def targeted_premise_readings_def
      read_prospective_call_readings_targeted read_material_readings_targeted)

lemma read_premise_family_readings_targeted:
  "read_premise_family_readings E u As V r=targeted_premise_family_readings (finite_citation_targets E u) E u As V r"
  by (simp only: read_premise_family_readings_def targeted_premise_family_readings_def
      read_premise_readings_targeted)

lemma read_schema_body_readings_targeted:
  "read_schema_body_readings E u As R r=targeted_schema_body_readings (finite_citation_targets E u) E u As R r"
  by (intro ext) (simp only: read_schema_body_readings_def targeted_schema_body_readings_def
      read_premise_family_readings_targeted read_sized_pattern_readings_targeted)

lemma read_schema_readings_targeted:
  "read_schema_readings E u As=targeted_schema_readings (finite_citation_targets E u) E u As"
  by (rule ext) (simp only: read_schema_readings_def targeted_schema_readings_def read_schema_body_readings_targeted)

lemma read_scoped_record_targeted:
  "read_scoped_record E u As R r=targeted_scoped_record (finite_citation_targets E u) As R r"
  by (intro ext) (simp only: read_scoped_record_def targeted_scoped_record_def read_sized_pattern_readings_targeted)

lemma read_scoped_pattern_readings_targeted:
  "read_scoped_pattern_readings E u As r=targeted_scoped_pattern_readings (finite_citation_targets E u) As r"
  by (simp only: read_scoped_pattern_readings_def targeted_scoped_pattern_readings_def read_scoped_record_targeted)

lemma read_definition_body_readings_targeted:
  "read_definition_body_readings E u As r=targeted_definition_body_readings (finite_citation_targets E u) E u As r"
  by (intro ext) (simp only: read_definition_body_readings_def targeted_definition_body_readings_def
      read_scoped_pattern_readings_targeted read_schema_readings_targeted)

lemma read_definition_readings_targeted:
  "read_definition_readings E u As r=targeted_definition_readings (finite_citation_targets E u) E u As r"
  by (simp only: read_definition_readings_def targeted_definition_readings_def read_definition_body_readings_targeted)

section \<open>The definition readings read through formed bodies\<close>

text \<open>
  A package's definition reading at a formed environment reads its schemas, patterns, premises,
  materials and calls through the formed targets: no formation of the environment or of an artifact
  a citation reaches is checked inside.
\<close>

definition finite_native_definition_readings_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u finite_native_definition fset" where
  "finite_native_definition_readings_inner E u r=
    targeted_definition_readings (finite_citation_targets_formed E u) E u (artifact_readings_at E u) r"

theorem finite_native_definition_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_definition_readings_formed E=finite_native_definition_readings_inner E"
  by (intro ext) (simp only: finite_native_definition_readings_formed_read_code read_definition_readings_targeted
      finite_citation_targets_formed_exact[OF formed] finite_native_definition_readings_inner_def)

corollary finite_native_definition_readings_inner_entry:
  "finite_native_definition_readings E=
    (if finite_environment_formed E then finite_native_definition_readings_inner E else (\<lambda>u r. {||}))"
  by (cases "finite_environment_formed E")
    (simp_all add: fun_eq_iff finite_native_definition_readings_formed_once_code
      finite_native_definition_readings_inner_exact[symmetric])

section \<open>The term readings and the call readings of an application\<close>

definition finite_term_readings_inner ::
  "nat \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    finite_factor_term finite_syntax_reading fset" where
  "finite_term_readings_inner n E u r=
    targeted_term_readings n (finite_citation_targets_formed E u) (artifact_readings_at E u) r"

theorem finite_term_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_term_readings_formed n E=finite_term_readings_inner n E"
  by (intro ext) (simp only: finite_term_readings_formed_read_code read_term_readings_targeted
      finite_citation_targets_formed_exact[OF formed] finite_term_readings_inner_def)

definition finite_term_readings_carrier_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> finite_factor_term finite_syntax_reading fset" where
  "finite_term_readings_carrier_inner E u r=ffUnion (fimage (\<lambda>C.
    finite_term_readings_inner (fcard (finite_carrier (finite_structure C))) E u r) (finite_artifacts_at E u))"

theorem finite_term_readings_carrier_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_term_readings E=finite_term_readings_carrier_inner E"
  by (intro ext) (simp only: finite_term_readings_def finite_term_readings_carrier_inner_def
      finite_term_readings_formed_exact[OF formed] finite_term_readings_inner_exact[OF formed])

definition finite_application_readings_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> finite_factor_term) finite_syntax_reading fset" where
  "finite_application_readings_inner E u r=
    finite_call_readings_formed E u {||} r (finite_term_readings_carrier_inner E u)"

theorem finite_application_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_application_readings E=finite_application_readings_inner E"
  by (intro ext) (simp only: finite_application_readings_def finite_call_readings_formed_exact[OF formed]
      finite_term_readings_carrier_inner_exact[OF formed] finite_application_readings_inner_def)

text \<open>
  The application readings are an instance of the first notion of @{text Established_Premises} at their
  entry: the check hoisted over the call readings' and the term readings' own (#494's follow-up 4).
\<close>

lemma finite_application_readings_checked_premise:
  "checked_premise finite_application_readings finite_environment_formed finite_application_readings_inner
    (\<lambda>E u r. {||})"
  by unfold_locales
    (simp_all add: finite_application_readings_inner_exact fun_eq_iff finite_application_readings_def
      finite_call_readings_def)

declare finite_application_readings_def[code del]

lemma finite_application_readings_inner_code [code]:
  "finite_application_readings E=(if finite_environment_formed E
    then finite_application_readings_inner E else (\<lambda>u r. {||}))"
  by (rule checked_premise.checked_at_entry[OF finite_application_readings_checked_premise])

section \<open>The proof-node readings read through formed bodies\<close>

definition finite_site_citation_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site finite_syntax_reading fset" where
  "finite_site_citation_readings_formed E u r=
    ffUnion (fimage (\<lambda>C. finite_location_readings_formed E u C r) (finite_artifacts_at E u))"

theorem finite_site_citation_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_site_citation_readings E=finite_site_citation_readings_formed E"
proof (intro ext)
  fix u r
  show "finite_site_citation_readings E u r=finite_site_citation_readings_formed E u r"
    unfolding finite_site_citation_readings_def finite_site_citation_readings_formed_def if_P[OF formed]
    by (rule ffUnion_fimage_agree, rule finite_location_readings_formed_exact[OF formed
        formed_environment_artifact[OF formed]])
qed

definition finite_native_table_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    (local_address \<Rightarrow> ('k \<times> 'v) finite_syntax_reading fset) \<Rightarrow>
    ('k \<times> 'v) fset finite_syntax_reading fset" where
  "finite_native_table_readings_formed E u r reads=ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>M.
      finite_native_table_body r M (finite_socket_rows M reads))
      (finite_family_body_candidates C r))) (finite_artifacts_at E u))"

theorem finite_native_table_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_table_readings E u r reads=finite_native_table_readings_formed E u r reads"
  unfolding finite_native_table_readings_def finite_native_table_readings_formed_def if_P[OF formed]
  by (rule ffUnion_fimage_agree, simp only: finite_family_body_candidates_exact[OF formed_environment_object[OF formed]])

definition finite_binding_table_readings_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> finite_factor_term) fset finite_syntax_reading fset" where
  "finite_binding_table_readings_inner E u r=finite_native_table_readings_formed E u r (finite_application_readings_inner E u)"

theorem finite_binding_table_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_binding_table_readings E=finite_binding_table_readings_inner E"
  by (intro ext) (simp only: finite_binding_table_readings_def finite_application_readings_inner_exact[OF formed]
      finite_native_table_readings_formed_exact[OF formed] finite_binding_table_readings_inner_def)

definition finite_site_link_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) finite_syntax_reading fset" where
  "finite_site_link_readings_formed E u r=finite_call_readings_formed E u {||} r (finite_site_citation_readings_formed E u)"

theorem finite_site_link_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_site_link_readings E=finite_site_link_readings_formed E"
  by (intro ext) (simp only: finite_site_link_readings_def finite_call_readings_formed_exact[OF formed]
      finite_site_citation_readings_formed_exact[OF formed] finite_site_link_readings_formed_def)

definition finite_discharge_table_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) fset finite_syntax_reading fset" where
  "finite_discharge_table_readings_formed E u r=finite_native_table_readings_formed E u r (finite_site_link_readings_formed E u)"

theorem finite_discharge_table_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_discharge_table_readings E=finite_discharge_table_readings_formed E"
  by (intro ext) (simp only: finite_discharge_table_readings_def finite_site_link_readings_formed_exact[OF formed]
      finite_native_table_readings_formed_exact[OF formed] finite_discharge_table_readings_formed_def)

definition finite_proof_inference_readings_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    local_address list \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_inference_readings_formed E u r ps c b p =
    ffUnion (fimage (\<lambda>(d,C,A). ffUnion (fimage (\<lambda>(V,B,L).
      ffUnion (fimage (\<lambda>(D,J,W).
        let I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J);
            K=A |\<union>| L |\<union>| W in
        if finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||} \<and>
          C |\<inter>| B={||} \<and> C |\<inter>| J={||} \<and> B |\<inter>| J={||} \<and>
          I |\<inter>| K={||}
        then {|((Finite_Inference d V,D),I,K)|} else {||})
        (finite_discharge_table_readings_formed E u p))) (finite_binding_table_readings_inner E u b)))
      (finite_site_citation_readings_formed E u c))"

theorem finite_proof_inference_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_proof_inference_readings E=finite_proof_inference_readings_formed E"
  by (intro ext) (simp only: finite_proof_inference_readings_def finite_proof_inference_readings_formed_def
      finite_site_citation_readings_formed_exact[OF formed] finite_binding_table_readings_inner_exact[OF formed]
      finite_discharge_table_readings_formed_exact[OF formed])

definition finite_proof_node_readings_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_node_readings_inner E u r=ffUnion (fimage (\<lambda>C.
      (if ([],[]) |\<in>| finite_record_body_candidates C r 0
       then {|((Finite_Assertion,{||}),{|r|},{||})|} else {||}) |\<union>|
      finite_three_field_record_formed C r (finite_proof_inference_readings_formed E u r))
      (finite_artifacts_at E u))"

theorem finite_proof_node_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_proof_node_readings_formed E=finite_proof_node_readings_inner E"
proof (intro ext)
  fix u r
  have each: "(if ([],[]) |\<in>| finite_record_candidates C r 0
       then {|((Finite_Assertion,{||}),{|r|},{||})|} else {||}) |\<union>|
      finite_three_field_record C r (finite_proof_inference_readings E u r)=
    (if ([],[]) |\<in>| finite_record_body_candidates C r 0
       then {|((Finite_Assertion,{||}),{|r|},{||})|} else {||}) |\<union>|
      finite_three_field_record_formed C r (finite_proof_inference_readings_formed E u r)"
    if C: "C |\<in>| finite_artifacts_at E u" for C
  proof -
    have object: "finite_object_formed C" by (rule formed_environment_object[OF formed C])
    show ?thesis
      by (simp only: finite_record_candidates_formed_once_code object if_True
          finite_three_field_record_formed_exact[OF object] finite_proof_inference_readings_formed_exact[OF formed])
  qed
  show "finite_proof_node_readings_formed E u r=finite_proof_node_readings_inner E u r"
    unfolding finite_proof_node_readings_formed_def finite_proof_node_readings_inner_def
    by (rule ffUnion_fimage_agree, rule each)
qed

definition finite_native_node_slots_inner ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow>
    ('u definition_site,'u definition_site) finite_schema_graph_node \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) fset \<Rightarrow> local_address fset" where
  "finite_native_node_slots_inner E n N D=finite_reading_slots
    (ffilter (\<lambda>((M,F),I,K). M=N \<and> F=D) (finite_proof_node_readings_inner E (fst n) (snd n)))"

theorem finite_native_node_slots_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_node_slots_formed E=finite_native_node_slots_inner E"
  by (intro ext) (simp only: finite_native_node_slots_formed_def finite_native_node_slots_inner_def
      finite_proof_node_readings_inner_exact[OF formed])

section \<open>The entries that establish formation read the formed bodies\<close>

text \<open>
  The proof-node readings, the graph's demands and the recovered graph check the environment's formation
  at their entry; each code equation below is that check with the bodies under it read through formed
  bodies, the entry's value equal to the original on every environment.
\<close>

declare finite_proof_node_readings_def[code del]

lemma finite_proof_node_readings_inner_code [code]:
  "finite_proof_node_readings E=(if finite_environment_formed E
    then finite_proof_node_readings_inner E else (\<lambda>u r. {||}))"
  by (cases "finite_environment_formed E")
    (simp_all only: finite_proof_node_readings_formed_guard finite_proof_node_readings_inner_exact if_True if_False)

declare finite_native_graph_demands_formed_once_code[code del]

lemma finite_native_graph_demands_inner_code [code]:
  "finite_native_graph_demands E G=(if finite_environment_formed E then ffUnion (fimage (\<lambda>(n,N).
      fimage (Pair (fst n)) (finite_native_node_slots_inner E n N (finite_graph_premises G n)))
        (finite_graph_inferences G))
    else {||})"
  by (cases "finite_environment_formed E")
    (simp_all only: finite_native_graph_demands_formed_once_code finite_native_node_slots_inner_exact if_True if_False)

declare finite_recovered_graph_demanded_code[code del]

lemma finite_recovered_graph_inner_code [code]:
  "finite_recovered_graph E root=(let R=(if finite_environment_formed E
       then snd (the (finite_demanded_readings (\<lambda>n. finite_proof_node_readings_inner E (fst n) (snd n))
         finite_proof_children {|root|}))
       else {||}) in
     \<lparr>finite_graph_inferences=fimage (\<lambda>(n,(N,D),I,K). (n,N)) R,
      finite_graph_discharges=ffUnion (fimage (\<lambda>(n,(N,D),I,K). fimage (\<lambda>(s,m). ((n,s),m)) D) R)\<rparr>)"
proof (cases "finite_environment_formed E")
  case True
  have "finite_proof_site_reading_formed E=(\<lambda>n. finite_proof_node_readings_inner E (fst n) (snd n))"
    by (rule ext) (simp only: finite_proof_site_reading_formed_def finite_proof_node_readings_inner_exact[OF True])
  then show ?thesis by (simp only: finite_recovered_graph_demanded_code)
next
  case False
  then show ?thesis by (simp only: finite_recovered_graph_demanded_code if_False)
qed

text \<open>
  Every formed body the recording reaches now reads through formed bodies: the proof-node readings
  through the formed site-citation, table, application and site-link readings, the application's term
  readings and every pattern reading of a definition through the formed targets. The definition readings'
  guarded entry is a root of the seeded state and keeps its code equation; its formed body's reading
  through formed bodies is @{const finite_native_definition_readings_inner}, for its callers to take.
\<close>

end
