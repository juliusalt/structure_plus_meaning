theory Factor_Formation_Once_Definitions
  imports Factor_Formation_Once_Readings
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
  finite_native_definition_rows_formed_once_code[code del]

lemma finite_family_readings_formed_once_code [code]:
  "finite_family_readings E u r reads=(if finite_environment_formed E
    then finite_family_readings_formed E u r reads else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_family_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_family_readings_def if_False)
qed

lemma finite_call_readings_formed_once_code [code]:
  "finite_call_readings E u V r reads=(if finite_environment_formed E
    then finite_call_readings_formed E u V r reads else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_call_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_call_readings_def if_False)
qed

lemma finite_pattern_record_readings_formed_once_code [code]:
  "finite_pattern_record_readings E u V r n=(if finite_environment_formed E
    then finite_pattern_record_readings_formed E u V r n else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_pattern_record_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_pattern_record_readings_def if_False)
qed

lemma finite_pattern_vector_readings_formed_once_code [code]:
  "finite_pattern_vector_readings E u V rs=(if finite_environment_formed E
    then finite_pattern_vector_readings_formed E u V rs else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_pattern_vector_readings_formed_exact[OF True] if_True)
next
  case False
  have bounded: "finite_pattern_readings_bounded n E u V q={||}" for n q
    by (cases n) (simp_all add: False)
  have none: "finite_pattern_readings E u V q={||}" for q
    by (auto simp: finite_pattern_readings_def bounded fset_eq_iff ffUnion.rep_eq fimage.rep_eq)
  show ?thesis by (cases rs) (simp_all add: False none)
qed

lemma finite_native_schema_readings_formed_once_code [code]:
  "finite_native_schema_readings E u r=(if finite_environment_formed E
    then finite_native_schema_readings_formed E u r else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_native_schema_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_native_schema_readings_def if_False)
qed

lemma finite_scoped_pattern_readings_formed_once_code [code]:
  "finite_scoped_pattern_readings E u r=(if finite_environment_formed E
    then finite_scoped_pattern_readings_formed E u r else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_scoped_pattern_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_scoped_pattern_readings_def if_False)
qed

lemma finite_native_definition_readings_formed_once_code [code]:
  "finite_native_definition_readings E u r=(if finite_environment_formed E
    then finite_native_definition_readings_formed E u r else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis by (simp only: finite_native_definition_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis by (simp only: finite_native_definition_readings_def if_False)
qed

lemma finite_native_definition_rows_formed_definitions_code [code]:
  "finite_native_definition_rows E=(if finite_environment_formed E then ffUnion (fimage (\<lambda>d.
      fimage (Pair d) (finite_native_definition_readings_formed E (fst d) (snd d))) (finite_environment_positions E))
    else {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis
    by (simp only: finite_native_definition_rows_def finite_native_definition_readings_formed_exact[OF True] if_True)
next
  case False
  then show ?thesis
    by (auto simp: finite_native_definition_rows_def finite_native_definition_readings_def
      fset_eq_iff ffUnion.rep_eq fimage.rep_eq)
qed

lemma finite_native_package_formed_once_code [code]:
  "finite_native_package_formed E roots \<longleftrightarrow> finite_environment_formed E \<and>
    fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||})"
proof (cases "finite_environment_formed E")
  case True
  then show ?thesis
    by (simp only: finite_native_package_formed_def finite_native_definition_readings_formed_exact[OF True])
next
  case False
  then show ?thesis by (simp only: finite_native_package_formed_def simp_thms)
qed

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
