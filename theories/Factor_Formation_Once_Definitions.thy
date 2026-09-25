theory Factor_Formation_Once_Definitions
  imports Factor_Formation_Once_Readings Factor_Executable_Judgment_Retention
begin

section \<open>Formed environments read definitions, schemas and calls once\<close>

lemma formed_environment_object:
  "finite_environment_formed E \<Longrightarrow> C |\<in>| finite_artifacts_at E u \<Longrightarrow> finite_object_formed C"
  by (rule exact_formed_object[OF formed_environment_artifact])

definition finite_family_body_at where
  "finite_family_body_at C r M \<longleftrightarrow> r |\<in>| finite_carrier (finite_structure C) \<and>
    finite_headed_incidence (finite_structure C) r=M \<and> finite_relation_functional M \<and>
    r |\<notin>| fimage fst M \<and>
    fBall (fimage fst M) (\<lambda>p. finite_headed_incidence (finite_structure C) p={||}) \<and>
    finite_data_empty_on C (finsert r (fimage fst M))"

lemma finite_family_at_body:
  "finite_family_at C r M \<longleftrightarrow> finite_object_formed C \<and> finite_family_body_at C r M"
  by (simp only: finite_family_at_def finite_family_body_at_def)

definition finite_family_body_candidates where
  "finite_family_body_candidates C r=(let H=finite_headed_incidence (finite_structure C) r in
    if finite_family_body_at C r H then {|H|} else {||})"

lemma finite_family_body_candidates_exact:
  "finite_object_formed C \<Longrightarrow> finite_family_candidates C r=finite_family_body_candidates C r"
  by (simp only: finite_family_candidates_def finite_family_body_candidates_def finite_family_at_body simp_thms)

definition finite_binder_scope_body_candidates where
  "finite_binder_scope_body_candidates C b=(let V=fimage fst (finite_headed_incidence (finite_structure C) b) in
    if finite_family_body_at C b (fimage (\<lambda>a. (a,a)) V) then {|V|} else {||})"

lemma finite_binder_scope_body_candidates_exact:
  "finite_object_formed C \<Longrightarrow> finite_binder_scope_candidates C b=finite_binder_scope_body_candidates C b"
  by (simp only: finite_binder_scope_candidates_def finite_binder_scope_body_candidates_def
    finite_binder_scope_at_def finite_family_at_body simp_thms)

definition finite_three_field_record_formed where
  "finite_three_field_record_formed C r F=ffUnion (fimage
    (\<lambda>(ps,xs). finite_three_fields xs (F ps)) (finite_record_body_candidates C r 3))"

lemma finite_three_field_record_formed_exact:
  "finite_object_formed C \<Longrightarrow> finite_three_field_record C r F=finite_three_field_record_formed C r F"
  by (simp only: finite_three_field_record_def finite_three_field_record_formed_def finite_record_body_candidates_exact)

section \<open>Located citations of formed artifacts need only their carriers\<close>

fun finite_citation_locations_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_citation_locations_formed E u (Local a) =
    (if fBex (finite_artifacts_at E u) (\<lambda>C. a |\<in>| finite_carrier (finite_structure C))
     then {|(u,a)|} else {||})"
| "finite_citation_locations_formed E u (External k a) =
    fimage (\<lambda>((v,l),w). (w,a)) (ffilter (\<lambda>((v,l),w). v=u \<and> l=k \<and>
      fBex (finite_artifacts_at E w) (\<lambda>C. a |\<in>| finite_carrier (finite_structure C)))
      (finite_environment_bindings E))"
| "finite_citation_locations_formed E u Local_Whole = {||}"
| "finite_citation_locations_formed E u (External_Whole k) = {||}"

lemma finite_formed_anchor_member:
  assumes formed: "finite_environment_formed E"
  shows "fBex (finite_artifacts_at E w) (\<lambda>C. finite_target_formed (Finite_Anchor C a)) \<longleftrightarrow>
    fBex (finite_artifacts_at E w) (\<lambda>C. a |\<in>| finite_carrier (finite_structure C))"
  using formed_environment_artifact[OF formed] by (auto simp: Bex_def)

lemma finite_citation_locations_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_citation_locations E u c=finite_citation_locations_formed E u c"
  by (cases c) (simp_all only: finite_citation_locations.simps finite_citation_locations_formed.simps
    finite_formed_anchor_member[OF formed])

definition finite_location_readings_formed where
  "finite_location_readings_formed E u C r=ffUnion (fimage (\<lambda>(c,I).
    fimage (\<lambda>d. (d,I,finite_citation_slots c)) (finite_citation_locations_formed E u c))
      (finite_citation_candidates_formed C r))"

lemma finite_location_readings_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_exact_formed C \<Longrightarrow>
    finite_location_readings E u C r=finite_location_readings_formed E u C r"
  by (simp only: finite_location_readings_def finite_location_readings_formed_def
    finite_citation_candidates_formed_exact finite_citation_locations_formed_exact)

section \<open>Families, calls, patterns and records under one formation premise\<close>

definition finite_family_readings_formed where
  "finite_family_readings_formed E u r reads=ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (\<lambda>M. finite_socket_readings M reads) (finite_family_body_candidates C r)))
      (finite_artifacts_at E u))"

lemma finite_family_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_family_readings E u r reads=finite_family_readings_formed E u r reads"
proof -
  have each: "ffUnion (fimage (\<lambda>M. finite_socket_readings M reads) (finite_family_candidates C r))=
      ffUnion (fimage (\<lambda>M. finite_socket_readings M reads) (finite_family_body_candidates C r))"
    if "C |\<in>| finite_artifacts_at E u" for C
    by (simp only: finite_family_body_candidates_exact[OF formed_environment_object[OF formed that]])
  show ?thesis
    by (simp only: finite_family_readings_def finite_family_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

definition finite_pattern_readings_carrier_formed where
  "finite_pattern_readings_carrier_formed E u V r=ffUnion (fimage (\<lambda>C.
    finite_pattern_readings_formed (fcard (finite_carrier (finite_structure C))) E u V r) (finite_artifacts_at E u))"

lemma finite_pattern_readings_carrier_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_pattern_readings E u V=finite_pattern_readings_carrier_formed E u V"
  by (rule ext) (simp only: finite_pattern_readings_def finite_pattern_readings_carrier_formed_def
    finite_pattern_readings_formed_exact)

definition finite_call_readings_formed where
  "finite_call_readings_formed E u V r reads=ffUnion (fimage (\<lambda>C. finite_two_field_record_formed C r (\<lambda>ps c a.
      finite_join_readings Pair V r ps (finite_location_readings_formed E u C c) (reads a)))
      (finite_artifacts_at E u))"

lemma finite_call_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_call_readings E u V r reads=finite_call_readings_formed E u V r reads"
proof -
  have each: "finite_two_field_record C r (\<lambda>ps c a.
        finite_join_readings Pair V r ps (finite_location_readings E u C c) (reads a))=
      finite_two_field_record_formed C r (\<lambda>ps c a.
        finite_join_readings Pair V r ps (finite_location_readings_formed E u C c) (reads a))"
    if member: "C |\<in>| finite_artifacts_at E u" for C
  proof -
    have exact: "finite_exact_formed C" by (rule formed_environment_artifact[OF formed member])
    show ?thesis
      by (simp only: finite_two_field_record_formed_exact[OF exact_formed_object[OF exact]]
        finite_location_readings_formed_exact[OF formed exact])
  qed
  show ?thesis
    by (simp only: finite_call_readings_def finite_call_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

definition finite_prospective_call_readings_formed where
  "finite_prospective_call_readings_formed E u V r=
    finite_call_readings_formed E u V r (finite_pattern_readings_carrier_formed E u V)"

lemma finite_prospective_call_readings_formed_exact:
  "finite_environment_formed E \<Longrightarrow>
    finite_prospective_call_readings E u V r=finite_prospective_call_readings_formed E u V r"
  by (simp only: finite_prospective_call_readings_def finite_prospective_call_readings_formed_def
    finite_call_readings_formed_exact finite_pattern_readings_carrier_formed_exact)

fun finite_pattern_vector_readings_formed where
  "finite_pattern_vector_readings_formed E u V []={|([],{||},{||})|}"
| "finite_pattern_vector_readings_formed E u V (r#rs)=ffUnion (fimage (\<lambda>(p,A,B).
    ffUnion (fimage (\<lambda>(ps,J,W).
      if A |\<inter>| J={||} \<and> (A |\<union>| J) |\<inter>| (B |\<union>| W)={||}
      then {|(p#ps,A |\<union>| J,B |\<union>| W)|} else {||})
        (finite_pattern_vector_readings_formed E u V rs))) (finite_pattern_readings_carrier_formed E u V r))"

lemma finite_pattern_vector_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_pattern_vector_readings E u V rs=finite_pattern_vector_readings_formed E u V rs"
  by (induction rs) (simp_all only: finite_pattern_vector_readings.simps finite_pattern_vector_readings_formed.simps
    finite_pattern_readings_carrier_formed_exact[OF formed] formed if_True)

definition finite_pattern_record_readings_formed where
  "finite_pattern_record_readings_formed E u V r n=ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>(ports,roots).
      finite_frame_readings V r ports (finite_pattern_vector_readings_formed E u V roots))
        (finite_record_body_candidates C r n))) (finite_artifacts_at E u))"

lemma finite_pattern_record_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_pattern_record_readings E u V r n=finite_pattern_record_readings_formed E u V r n"
proof -
  have each: "ffUnion (fimage (\<lambda>(ports,roots).
        finite_frame_readings V r ports (finite_pattern_vector_readings E u V roots)) (finite_record_candidates C r n))=
      ffUnion (fimage (\<lambda>(ports,roots).
        finite_frame_readings V r ports (finite_pattern_vector_readings_formed E u V roots)) (finite_record_body_candidates C r n))"
    if "C |\<in>| finite_artifacts_at E u" for C
    by (simp only: finite_record_body_candidates_exact[OF formed_environment_object[OF formed that]]
      finite_pattern_vector_readings_formed_exact[OF formed])
  show ?thesis
    by (simp only: finite_pattern_record_readings_def finite_pattern_record_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

definition finite_native_material_readings_formed where
  "finite_native_material_readings_formed E u V r=ffUnion (fimage (\<lambda>(ps,I,K).
    fimage (\<lambda>M. (M,I,K)) (finite_material_from_fields ps)) (finite_pattern_record_readings_formed E u V r 5))"

lemma finite_native_material_readings_formed_exact:
  "finite_environment_formed E \<Longrightarrow>
    finite_native_material_readings E u V r=finite_native_material_readings_formed E u V r"
  by (simp only: finite_native_material_readings_def finite_native_material_readings_formed_def
    finite_pattern_record_readings_formed_exact)

section \<open>Schemas and definitions consume the formed readings\<close>

definition finite_native_premise_readings_formed where
  "finite_native_premise_readings_formed E u V r=
    fimage (\<lambda>(c,I,K). (Inl c,I,K)) (finite_prospective_call_readings_formed E u V r) |\<union>|
    fimage (\<lambda>(M,I,K). (Inr M,I,K)) (finite_native_material_readings_formed E u V r)"

definition finite_native_premise_family_readings_formed where
  "finite_native_premise_family_readings_formed E u V r=
    fimage (\<lambda>F. (finite_left_sockets F,finite_right_sockets F))
      (finite_family_readings_formed E u r (\<lambda>a. finite_reading_values (finite_native_premise_readings_formed E u V a)))"

lemma finite_native_premise_family_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_premise_family_readings E u V r=finite_native_premise_family_readings_formed E u V r"
proof -
  have premise_readings: "finite_native_premise_readings E u V=finite_native_premise_readings_formed E u V"
    by (rule ext) (simp only: finite_native_premise_readings_def finite_native_premise_readings_formed_def
      finite_prospective_call_readings_formed_exact[OF formed] finite_native_material_readings_formed_exact[OF formed])
  show ?thesis
    by (simp only: finite_native_premise_family_readings_def finite_native_premise_family_readings_formed_def
      premise_readings finite_family_readings_formed_exact[OF formed])
qed

definition finite_schema_body_readings_formed where
  "finite_schema_body_readings_formed E u C r ps b c m =
    ffUnion (fimage (\<lambda>V. ffUnion (fimage (\<lambda>(p,I,K).
      ffUnion (fimage (\<lambda>(Q,A).
        let S=\<lparr>finite_schema_conclusion=p,finite_schema_premises=Q,finite_schema_materials=A\<rparr> in
        if V=finite_schema_variables S \<and>
          finsert r (fset_of_list ps) |\<inter>| (finsert b V |\<union>| I |\<union>| {|m|})={||} \<and>
          finsert b V |\<inter>| I={||} \<and> b\<noteq>m \<and> m |\<notin>| I
        then {|S|} else {||}) (finite_native_premise_family_readings_formed E u V m)))
      (finite_pattern_readings_carrier_formed E u V c))) (finite_binder_scope_body_candidates C b))"

lemma finite_schema_body_readings_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_object_formed C \<Longrightarrow>
    finite_schema_body_readings E u C r ps b c m=finite_schema_body_readings_formed E u C r ps b c m"
  by (simp only: finite_schema_body_readings_def finite_schema_body_readings_formed_def
    finite_binder_scope_body_candidates_exact finite_pattern_readings_carrier_formed_exact
    finite_native_premise_family_readings_formed_exact)

definition finite_native_schema_readings_formed where
  "finite_native_schema_readings_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_three_field_record_formed C r (finite_schema_body_readings_formed E u C r)) (finite_artifacts_at E u))"

lemma finite_native_schema_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_schema_readings E u r=finite_native_schema_readings_formed E u r"
proof -
  have each: "finite_three_field_record C r (finite_schema_body_readings E u C r)=
      finite_three_field_record_formed C r (finite_schema_body_readings_formed E u C r)"
    if "C |\<in>| finite_artifacts_at E u" for C
  proof -
    have object: "finite_object_formed C" by (rule formed_environment_object[OF formed that])
    have body: "finite_schema_body_readings E u C r=finite_schema_body_readings_formed E u C r"
      by (intro ext) (rule finite_schema_body_readings_formed_exact[OF formed object])
    show ?thesis by (simp only: finite_three_field_record_formed_exact[OF object] body)
  qed
  show ?thesis
    by (simp only: finite_native_schema_readings_def finite_native_schema_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

definition finite_scoped_record_formed where
  "finite_scoped_record_formed E u C r ps b q=ffUnion (fimage (\<lambda>V.
    ffilter (\<lambda>(p,I,K). finite_pattern_variables p=V)
      (finite_join_readings (\<lambda>(_::unit) p. p) {||} r ps {|((),finsert b V,{||})|}
        (finite_pattern_readings_carrier_formed E u V q))) (finite_binder_scope_body_candidates C b))"

lemma finite_scoped_record_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_object_formed C \<Longrightarrow>
    finite_scoped_record E u C r ps b q=finite_scoped_record_formed E u C r ps b q"
  by (simp only: finite_scoped_record_def finite_scoped_record_formed_def
    finite_binder_scope_body_candidates_exact finite_pattern_readings_carrier_formed_exact)

definition finite_scoped_pattern_readings_formed where
  "finite_scoped_pattern_readings_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_two_field_record_formed C r (finite_scoped_record_formed E u C r)) (finite_artifacts_at E u))"

lemma finite_scoped_pattern_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_scoped_pattern_readings E u r=finite_scoped_pattern_readings_formed E u r"
proof -
  have each: "finite_two_field_record C r (finite_scoped_record E u C r)=
      finite_two_field_record_formed C r (finite_scoped_record_formed E u C r)"
    if "C |\<in>| finite_artifacts_at E u" for C
  proof -
    have object: "finite_object_formed C" by (rule formed_environment_object[OF formed that])
    have scoped: "finite_scoped_record E u C r=finite_scoped_record_formed E u C r"
      by (intro ext) (rule finite_scoped_record_formed_exact[OF formed object])
    show ?thesis by (simp only: finite_two_field_record_formed_exact[OF object] scoped)
  qed
  show ?thesis
    by (simp only: finite_scoped_pattern_readings_def finite_scoped_pattern_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

definition finite_definition_body_readings_formed where
  "finite_definition_body_readings_formed E u r ps i m =
    ffUnion (fimage (\<lambda>(p,I,K).
      if finsert r (fset_of_list ps) |\<inter>| (I |\<union>| {|m|})={||} \<and> m |\<notin>| I
      then fimage (Pair p) (finite_family_readings_formed E u m (finite_native_schema_readings_formed E u)) else {||})
        (finite_scoped_pattern_readings_formed E u i))"

lemma finite_definition_body_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_definition_body_readings E u r ps i m=finite_definition_body_readings_formed E u r ps i m"
proof -
  have schemas: "finite_native_schema_readings E u=finite_native_schema_readings_formed E u"
    by (rule ext) (rule finite_native_schema_readings_formed_exact[OF formed])
  show ?thesis
    by (simp only: finite_definition_body_readings_def finite_definition_body_readings_formed_def
      finite_native_schema_family_readings_def schemas finite_family_readings_formed_exact[OF formed]
      finite_scoped_pattern_readings_formed_exact[OF formed])
qed

definition finite_native_definition_readings_formed where
  "finite_native_definition_readings_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_two_field_record_formed C r (finite_definition_body_readings_formed E u r)) (finite_artifacts_at E u))"

lemma finite_native_definition_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_definition_readings E u r=finite_native_definition_readings_formed E u r"
proof -
  have body: "finite_definition_body_readings E u r=finite_definition_body_readings_formed E u r"
    by (intro ext) (rule finite_definition_body_readings_formed_exact[OF formed])
  have each: "finite_two_field_record C r (finite_definition_body_readings E u r)=
      finite_two_field_record_formed C r (finite_definition_body_readings_formed E u r)"
    if "C |\<in>| finite_artifacts_at E u" for C
    by (simp only: finite_two_field_record_formed_exact[OF formed_environment_object[OF formed that]] body)
  show ?thesis
    by (simp only: finite_native_definition_readings_def finite_native_definition_readings_formed_def formed if_True)
      (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
qed

section \<open>Every guarded entry checks formation once\<close>

declare finite_family_readings_def[code del] finite_call_readings_def[code del]
  finite_pattern_record_readings_def[code del] finite_pattern_vector_readings.simps[code del]
  finite_native_schema_readings_def[code del] finite_scoped_pattern_readings_def[code del]
  finite_native_definition_readings_def[code del] finite_native_package_formed_def[code del]
  finite_native_definition_rows_def[code del]

text \<open>
  Each guarded entry is an instance of the first notion of @{text Established_Premises}: its premise,
  the environment's formation, is checked at the entry, its body is the formation-free reading and
  its refusal the reading's own empty value. Exactness is the @{text "_formed_exact"} fact above, the
  refusal is read from the definition, and the code equation is the check hoisted through the
  application to the remaining arguments, keeping the statement the seeded state presents.
\<close>

lemma finite_family_readings_checked_premise:
  "checked_premise finite_family_readings finite_environment_formed finite_family_readings_formed
    (\<lambda>E u r reads. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_family_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_family_readings_def 2 if_False)
qed

lemma finite_family_readings_formed_once_code [code]:
  "finite_family_readings E u r reads=(if finite_environment_formed E
    then finite_family_readings_formed E u r reads else {||})"
  by (rule checked_premise.checked_through[OF finite_family_readings_checked_premise, where t="\<lambda>f. f u r reads"])

lemma finite_call_readings_checked_premise:
  "checked_premise finite_call_readings finite_environment_formed finite_call_readings_formed
    (\<lambda>E u V r reads. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_call_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_call_readings_def 2 if_False)
qed

lemma finite_call_readings_formed_once_code [code]:
  "finite_call_readings E u V r reads=(if finite_environment_formed E
    then finite_call_readings_formed E u V r reads else {||})"
  by (rule checked_premise.checked_through[OF finite_call_readings_checked_premise, where t="\<lambda>f. f u V r reads"])

lemma finite_pattern_record_readings_checked_premise:
  "checked_premise finite_pattern_record_readings finite_environment_formed finite_pattern_record_readings_formed
    (\<lambda>E u V r n. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_pattern_record_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_pattern_record_readings_def 2 if_False)
qed

lemma finite_pattern_record_readings_formed_once_code [code]:
  "finite_pattern_record_readings E u V r n=(if finite_environment_formed E
    then finite_pattern_record_readings_formed E u V r n else {||})"
  by (rule checked_premise.checked_through[OF finite_pattern_record_readings_checked_premise, where t="\<lambda>f. f u V r n"])

lemma finite_pattern_vector_readings_checked_premise:
  "checked_premise finite_pattern_vector_readings finite_environment_formed finite_pattern_vector_readings_formed
    (\<lambda>E u V rs. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_pattern_vector_readings_formed_exact[OF 1])
next
  case (2 E)
  have none: "finite_pattern_readings E u V q={||}" for u V q
    by (simp add: finite_pattern_readings_def
      checked_premise.refused[OF finite_pattern_readings_bounded_checked_premise 2]
      checked_union[where P=False, simplified])
  have each: "finite_pattern_vector_readings E u V rs={||}" for u V rs
    by (cases rs) (simp_all add: 2 none)
  show ?case by (intro ext) (rule each)
qed

lemma finite_pattern_vector_readings_formed_once_code [code]:
  "finite_pattern_vector_readings E u V rs=(if finite_environment_formed E
    then finite_pattern_vector_readings_formed E u V rs else {||})"
  by (rule checked_premise.checked_through[OF finite_pattern_vector_readings_checked_premise, where t="\<lambda>f. f u V rs"])

lemma finite_native_schema_readings_checked_premise:
  "checked_premise finite_native_schema_readings finite_environment_formed finite_native_schema_readings_formed
    (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_native_schema_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_native_schema_readings_def 2 if_False)
qed

lemma finite_native_schema_readings_formed_once_code [code]:
  "finite_native_schema_readings E u r=(if finite_environment_formed E
    then finite_native_schema_readings_formed E u r else {||})"
  by (rule checked_premise.checked_through[OF finite_native_schema_readings_checked_premise, where t="\<lambda>f. f u r"])

lemma finite_scoped_pattern_readings_checked_premise:
  "checked_premise finite_scoped_pattern_readings finite_environment_formed finite_scoped_pattern_readings_formed
    (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_scoped_pattern_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_scoped_pattern_readings_def 2 if_False)
qed

lemma finite_scoped_pattern_readings_formed_once_code [code]:
  "finite_scoped_pattern_readings E u r=(if finite_environment_formed E
    then finite_scoped_pattern_readings_formed E u r else {||})"
  by (rule checked_premise.checked_through[OF finite_scoped_pattern_readings_checked_premise, where t="\<lambda>f. f u r"])

lemma finite_native_definition_readings_checked_premise:
  "checked_premise finite_native_definition_readings finite_environment_formed
    finite_native_definition_readings_formed (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_native_definition_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_native_definition_readings_def 2 if_False)
qed

lemma finite_native_definition_readings_formed_once_code [code]:
  "finite_native_definition_readings E u r=(if finite_environment_formed E
    then finite_native_definition_readings_formed E u r else {||})"
  by (rule checked_premise.checked_through[OF finite_native_definition_readings_checked_premise, where t="\<lambda>f. f u r"])

text \<open>
  The rows of an environment read a definition at every position: the check hoisted through each
  reading (@{thm [source] checked_premise.checked_through}) and out of the union over the positions
  (@{thm [source] checked_union}).
\<close>

lemma finite_native_definition_rows_formed_definitions_code [code]:
  "finite_native_definition_rows E=(if finite_environment_formed E then ffUnion (fimage (\<lambda>d.
      fimage (Pair d) (finite_native_definition_readings_formed E (fst d) (snd d))) (finite_environment_positions E))
    else {||})"
proof -
  have each: "fimage (Pair d) (finite_native_definition_readings E (fst d) (snd d))=
      (if finite_environment_formed E then fimage (Pair d) (finite_native_definition_readings_formed E (fst d) (snd d))
       else {||})" for d
    by (simp only: checked_premise.checked_through[OF finite_native_definition_readings_checked_premise,
      where t="\<lambda>f. fimage (Pair d) (f (fst d) (snd d))"] fimage_fempty)
  show ?thesis by (simp only: finite_native_definition_rows_def each checked_union)
qed

lemma finite_native_package_formed_checked_premise:
  "checked_premise finite_native_package_formed finite_environment_formed
    (\<lambda>E roots. fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||}))
    (\<lambda>E roots. False)"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case
    by (intro ext) (simp only: finite_native_package_formed_def
      finite_native_definition_readings_formed_exact[OF 1] 1 simp_thms)
next
  case (2 E)
  show ?case by (intro ext) (simp only: finite_native_package_formed_def 2 simp_thms)
qed

lemma finite_native_package_formed_once_code [code]:
  "finite_native_package_formed E roots \<longleftrightarrow> finite_environment_formed E \<and>
    fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||})"
  by (simp only: checked_premise.checked_through[OF finite_native_package_formed_checked_premise,
      where t="\<lambda>f. f roots"] if_bool_eq_conj simp_thms) blast

section \<open>A package's demanded slots are read from the formed bodies\<close>

text \<open>
  The slots a package demands are read at every definition site, through its interface, its clause
  family, each clause's record, binder scope, conclusion and premise family: each of those readings
  checks the environment's formation at its entry and every artifact's at each record it reads. The
  demands establish the environment's formation once, at their entry, and read the formation-free
  bodies of all of them, an instance of the first notion of @{text Established_Premises}. Outside the
  premise every reading of a definition's slots is empty, so the demands are the root requests' slots.
\<close>

definition finite_family_endpoints_formed where
  "finite_family_endpoints_formed E u r=ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (fimage snd) (finite_family_body_candidates C r))) (finite_artifacts_at E u))"

lemma finite_family_endpoints_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_family_endpoints E u r=finite_family_endpoints_formed E u r"
  unfolding finite_family_endpoints_def finite_family_endpoints_formed_def
  by (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl])
    (simp only: finite_family_body_candidates_exact[OF formed_environment_object[OF formed]])

lemma finite_native_premise_readings_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_native_premise_readings E u V=finite_native_premise_readings_formed E u V"
  by (rule ext) (simp only: finite_native_premise_readings_def finite_native_premise_readings_formed_def
    finite_prospective_call_readings_formed_exact finite_native_material_readings_formed_exact)

definition finite_native_premise_family_slots_formed where
  "finite_native_premise_family_slots_formed E u V r=ffUnion (fimage (\<lambda>a.
    finite_reading_slots (finite_native_premise_readings_formed E u V a)) (finite_family_endpoints_formed E u r))"

definition finite_native_schema_slots_formed where
  "finite_native_schema_slots_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_three_field_record_formed C r (\<lambda>ps b c m. ffUnion (fimage (\<lambda>V.
      finite_reading_slots (finite_pattern_readings_carrier_formed E u V c) |\<union>|
      finite_native_premise_family_slots_formed E u V m) (finite_binder_scope_body_candidates C b))))
    (finite_artifacts_at E u))"

definition finite_native_definition_slots_formed where
  "finite_native_definition_slots_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_two_field_record_formed C r (\<lambda>ps i m.
      finite_reading_slots (finite_scoped_pattern_readings_formed E u i) |\<union>|
      ffUnion (fimage (finite_native_schema_slots_formed E u) (finite_family_endpoints_formed E u m))))
    (finite_artifacts_at E u))"

lemma finite_native_definition_slots_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_definition_slots E u r=finite_native_definition_slots_formed E u r"
proof -
  have pattern: "finite_pattern_slots E v V c=finite_reading_slots (finite_pattern_readings_carrier_formed E v V c)"
    for v V c by (simp only: finite_pattern_slots_def finite_pattern_readings_carrier_formed_exact[OF formed])
  have premise_slots: "finite_native_premise_slots E v V=
      (\<lambda>a. finite_reading_slots (finite_native_premise_readings_formed E v V a))" for v V
    by (rule ext) (simp only: finite_native_premise_slots_def finite_native_premise_readings_formed_exact[OF formed])
  have premise: "finite_native_premise_family_slots E v V m=finite_native_premise_family_slots_formed E v V m"
    for v V m by (simp only: finite_native_premise_family_slots_def finite_native_premise_family_slots_formed_def
      premise_slots finite_family_endpoints_formed_exact[OF formed])
  have schema: "finite_native_schema_slots E v s=finite_native_schema_slots_formed E v s" for v s
    unfolding finite_native_schema_slots_def finite_native_schema_slots_formed_def
  proof (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl])
    fix C assume member: "C |\<in>| finite_artifacts_at E v"
    have object: "finite_object_formed C" by (rule formed_environment_object[OF formed member])
    show "finite_three_field_record C s (\<lambda>ps b c m. ffUnion (fimage (\<lambda>V.
        finite_pattern_slots E v V c |\<union>| finite_native_premise_family_slots E v V m)
        (finite_binder_scope_candidates C b)))=
      finite_three_field_record_formed C s (\<lambda>ps b c m. ffUnion (fimage (\<lambda>V.
        finite_reading_slots (finite_pattern_readings_carrier_formed E v V c) |\<union>|
        finite_native_premise_family_slots_formed E v V m) (finite_binder_scope_body_candidates C b)))"
      by (simp only: finite_three_field_record_formed_exact[OF object]
        finite_binder_scope_body_candidates_exact[OF object] pattern premise)
  qed
  have schema_readings: "finite_native_schema_slots E v=finite_native_schema_slots_formed E v" for v
    by (rule ext) (rule schema)
  have family: "finite_native_schema_family_slots E v m=
      ffUnion (fimage (finite_native_schema_slots_formed E v) (finite_family_endpoints_formed E v m))" for v m
    by (simp only: finite_native_schema_family_slots_def finite_family_endpoints_formed_exact[OF formed]
      schema_readings)
  show ?thesis
    unfolding finite_native_definition_slots_def finite_native_definition_slots_formed_def
  proof (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl])
    fix C assume member: "C |\<in>| finite_artifacts_at E u"
    have object: "finite_object_formed C" by (rule formed_environment_object[OF formed member])
    show "finite_two_field_record C r (\<lambda>ps i m.
        finite_scoped_pattern_slots E u i |\<union>| finite_native_schema_family_slots E u m)=
      finite_two_field_record_formed C r (\<lambda>ps i m.
        finite_reading_slots (finite_scoped_pattern_readings_formed E u i) |\<union>|
        ffUnion (fimage (finite_native_schema_slots_formed E u) (finite_family_endpoints_formed E u m)))"
      by (simp only: finite_two_field_record_formed_exact[OF object] finite_scoped_pattern_slots_def
        finite_scoped_pattern_readings_formed_exact[OF formed] family)
  qed
qed

lemma finite_native_definition_slots_unformed:
  assumes unformed: "\<not> finite_environment_formed E"
  shows "finite_native_definition_slots E u r={||}"
proof -
  have none: "finite_reading_slots {||}={||}"
    by (simp add: finite_reading_slots_def fset_eq_iff ffUnion.rep_eq)
  have pattern: "finite_pattern_slots E v V c={||}" for v V c
    by (simp add: finite_pattern_slots_def finite_pattern_readings_def none
      checked_premise.refused[OF finite_pattern_readings_bounded_checked_premise unformed]
      checked_union[where P=False, simplified])
  have scoped: "finite_scoped_pattern_slots E v i={||}" for v i
    by (simp add: finite_scoped_pattern_slots_def none
      checked_premise.refused[OF finite_scoped_pattern_readings_checked_premise unformed])
  have premise: "finite_native_premise_slots E v V a={||}" for v V a
    by (simp add: finite_native_premise_slots_def finite_native_premise_readings_def
      finite_prospective_call_readings_def finite_native_material_readings_def none
      checked_premise.refused[OF finite_call_readings_checked_premise unformed]
      checked_premise.refused[OF finite_pattern_record_readings_checked_premise unformed])
  have premise_family: "finite_native_premise_family_slots E v V m={||}" for v V m
    by (simp add: finite_native_premise_family_slots_def premise fset_eq_iff ffUnion.rep_eq fimage.rep_eq)
  have schema: "finite_native_schema_slots E v s={||}" for v s
    by (auto simp: fset_eq_iff finite_native_schema_slots_step pattern premise_family)
  have family: "finite_native_schema_family_slots E v m={||}" for v m
    by (simp add: finite_native_schema_family_slots_def schema fset_eq_iff ffUnion.rep_eq fimage.rep_eq)
  show ?thesis by (auto simp: fset_eq_iff finite_native_definition_slots_step scoped family)
qed

definition finite_native_package_demands_formed where
  "finite_native_package_demands_formed E u r=finite_requested_slots E (finite_native_root_requests E u r) |\<union>|
    ffUnion (fimage (\<lambda>(v,a). fimage (Pair v) (finite_native_definition_slots_formed E v a))
      (finite_native_package_sites E u r))"

lemma finite_native_package_demands_checked_premise:
  "checked_premise finite_native_package_demands finite_environment_formed finite_native_package_demands_formed
    (\<lambda>E u r. finite_requested_slots E (finite_native_root_requests E u r))"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (simp only: finite_native_package_demands_def finite_native_package_demands_formed_def
    finite_native_definition_slots_formed_exact[OF 1])
next
  case (2 E)
  show ?case
    by (intro ext) (auto simp: finite_native_package_demands_def finite_native_definition_slots_unformed[OF 2]
      fset_eq_iff ffUnion.rep_eq fimage.rep_eq split: prod.splits)
qed

lemma finite_native_package_demands_formed_once_code [code]:
  "finite_native_package_demands E u r=(if finite_environment_formed E
    then finite_native_package_demands_formed E u r
    else finite_requested_slots E (finite_native_root_requests E u r))"
  by (rule checked_premise.checked_through[OF finite_native_package_demands_checked_premise, where t="\<lambda>f. f u r"])

section \<open>An environment reads the package sites once for its sources and its demands\<close>

text \<open>
  A package's least environment, and a judgment's, read the package sites for their sources and again
  inside their demands. The demands are stated over a supplied family of sites, equal to the original at
  the package's own sites by @{thm [source] finite_native_package_demands_formed_once_code}, and each
  environment reads the sites once and passes them to both (HOL's @{text Let}).
\<close>

definition finite_native_package_demands_over where
  "finite_native_package_demands_over E u r S=(if finite_environment_formed E
    then finite_requested_slots E (finite_native_root_requests E u r) |\<union>|
      ffUnion (fimage (\<lambda>(v,a). fimage (Pair v) (finite_native_definition_slots_formed E v a)) S)
    else finite_requested_slots E (finite_native_root_requests E u r))"

lemma finite_native_package_demands_over_sites:
  "finite_native_package_demands E u r=finite_native_package_demands_over E u r (finite_native_package_sites E u r)"
  by (simp only: finite_native_package_demands_formed_once_code finite_native_package_demands_over_def
    finite_native_package_demands_formed_def)

declare finite_native_package_environment_def[code del]

lemma finite_native_package_environment_shared_code [code]:
  "finite_native_package_environment E u r=(let S=finite_native_package_sites E u r in
    finite_read_environment E (finsert u (fimage fst S)) (finite_native_package_demands_over E u r S))"
  by (simp only: finite_native_package_environment_def finite_native_package_sources_def
    finite_native_package_demands_over_sites Let_def)

section \<open>An application's demanded slots are read from the formed bodies\<close>

text \<open>
  An application's slots are read through the call readings, which check the environment's formation at
  their entry, and through the term readings of its argument, which check it again at each artifact of
  the use. The demands check it once, at their entry (@{text Established_Premises}); outside the premise
  the call readings are empty, so the demands are.
\<close>

definition finite_term_readings_carrier_formed where
  "finite_term_readings_carrier_formed E u r=ffUnion (fimage (\<lambda>C.
    finite_term_readings_formed (fcard (finite_carrier (finite_structure C))) E u r) (finite_artifacts_at E u))"

lemma finite_term_readings_carrier_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_term_readings E u=finite_term_readings_carrier_formed E u"
  by (rule ext) (simp only: finite_term_readings_def finite_term_readings_carrier_formed_def
    finite_term_readings_formed_exact)

definition finite_native_application_demands_formed where
  "finite_native_application_demands_formed E u r=fimage (Pair u)
    (finite_reading_slots (finite_call_readings_formed E u {||} r (finite_term_readings_carrier_formed E u)))"

lemma finite_native_application_demands_checked_premise:
  "checked_premise finite_native_application_demands finite_environment_formed
    finite_native_application_demands_formed (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (simp only: finite_native_application_demands_def
    finite_native_application_demands_formed_def finite_application_readings_def
    finite_call_readings_formed_exact[OF 1] finite_term_readings_carrier_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (simp add: finite_native_application_demands_def finite_application_readings_def
    finite_call_readings_def 2 finite_reading_slots_def fset_eq_iff ffUnion.rep_eq)
qed

lemma finite_native_application_demands_formed_once_code [code]:
  "finite_native_application_demands E u r=(if finite_environment_formed E
    then finite_native_application_demands_formed E u r else {||})"
  by (rule checked_premise.checked_through[OF finite_native_application_demands_checked_premise, where t="\<lambda>f. f u r"])

declare finite_native_judgment_environment_def[code del]

lemma finite_native_judgment_environment_shared_code [code]:
  "finite_native_judgment_environment E pu pr au ar=(let S=finite_native_package_sites E pu pr in
    finite_read_environment E (finsert pu (fimage fst S) |\<union>| {|au|})
      (finite_native_package_demands_over E pu pr S |\<union>| finite_native_application_demands E au ar))"
  by (simp only: finite_native_judgment_environment_def finite_native_judgment_sources_def
    finite_native_judgment_demands_def finite_native_package_sources_def finite_native_package_demands_over_sites Let_def)

text \<open>
  A formed environment has exactly formed artifacts, so their record, family,
  binder-scope and citation candidates, and the carriers of located citations,
  are read from the formation-free bodies of the same conditions. Definition,
  schema, scoped pattern, premise, material, call and vector readings therefore
  consume one another's formation-free bodies, and each guarded entry checks
  environment formation once. Unformed environments keep every original empty
  result, and formed environments every original reading and its order.
\<close>

end
