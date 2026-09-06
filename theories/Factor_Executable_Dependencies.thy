theory Factor_Executable_Dependencies
  imports Factor_Executable_Packages RRA_Executable_Retention Factor_Package_Dependencies
begin

section \<open>Slots are projected from complete syntax readings\<close>

definition finite_reading_slots :: "'a finite_syntax_reading fset \<Rightarrow> local_address fset" where
  "finite_reading_slots F = ffUnion (fimage (\<lambda>(q,I,K). K) F)"

lemma finite_reading_slots_member:
  "k |\<in>| finite_reading_slots F \<longleftrightarrow> (\<exists>q I K. (q,I,K) |\<in>| F \<and> k |\<in>| K)"
  by (simp only: finite_reading_slots_def finite_union_image_member split_paired_Ex prod.case; blast)

lemma finite_reading_slots_correct:
  assumes correct: "\<And>q I K. (q,I,K) |\<in>| F \<longleftrightarrow> R (D q) (fset I) (fset K)"
    and complete: "\<And>q I K. R q I K \<Longrightarrow> \<exists>p J A. (p,J,A) |\<in>| F \<and> fset A=K"
  shows "fset (finite_reading_slots F) = {k. \<exists>q I K. R q I K \<and> k \<in> K}"
proof (rule set_eqI)
  fix k
  show "k \<in> fset (finite_reading_slots F) \<longleftrightarrow> k \<in> {k. \<exists>q I K. R q I K \<and> k \<in> K}"
  proof
    assume "k \<in> fset (finite_reading_slots F)"
    then obtain q I K where member: "(q,I,K) |\<in>| F" and slot: "k |\<in>| K"
      by (simp only: finite_reading_slots_member; blast)
    have read: "R (D q) (fset I) (fset K)" using correct[of q I K] member by blast
    show "k \<in> {k. \<exists>q I K. R q I K \<and> k \<in> K}" using read slot by blast
  next
    assume "k \<in> {k. \<exists>q I K. R q I K \<and> k \<in> K}"
    then obtain q I K where read: "R q I K" and slot: "k \<in> K" by blast
    obtain p J A where member: "(p,J,A) |\<in>| F" and represented: "fset A=K"
      using complete[OF read] by blast
    show "k \<in> fset (finite_reading_slots F)"
      using member represented slot by (simp only: finite_reading_slots_member; blast)
  qed
qed

definition finite_pattern_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_pattern_slots E u V r = finite_reading_slots (finite_pattern_readings E u V r)"

lemma finite_pattern_slots_correct:
  "fset (finite_pattern_slots E u V r) = pattern_slots (decode_finite_environment E) u (fset V) r"
  unfolding finite_pattern_slots_def pattern_slots_def
proof (rule finite_reading_slots_correct[where D=decode_finite_pattern])
  show "(q,I,K) |\<in>| finite_pattern_readings E u V r \<longleftrightarrow>
      pattern_quoted_at (decode_finite_environment E) u (fset V) r (decode_finite_pattern q) (fset I) (fset K)" for q I K
    by (rule finite_pattern_readings_correct)
  fix q I K assume read: "pattern_quoted_at (decode_finite_environment E) u (fset V) r q I K"
  show "\<exists>p J A. (p,J,A) |\<in>| finite_pattern_readings E u V r \<and> fset A=K"
    using finite_pattern_readings_complete[OF read] by blast
qed

definition finite_scoped_pattern_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_scoped_pattern_slots E u r = finite_reading_slots (finite_scoped_pattern_readings E u r)"

lemma finite_scoped_pattern_slots_correct:
  "fset (finite_scoped_pattern_slots E u r) = scoped_pattern_slots (decode_finite_environment E) u r"
  unfolding finite_scoped_pattern_slots_def scoped_pattern_slots_def
proof (rule finite_reading_slots_correct[where D=decode_finite_pattern])
  show "(q,I,K) |\<in>| finite_scoped_pattern_readings E u r \<longleftrightarrow>
      scoped_pattern_at (decode_finite_environment E) u r (decode_finite_pattern q) (fset I) (fset K)" for q I K
    by (rule finite_scoped_pattern_readings_correct)
  fix q I K assume read: "scoped_pattern_at (decode_finite_environment E) u r q I K"
  show "\<exists>p J A. (p,J,A) |\<in>| finite_scoped_pattern_readings E u r \<and> fset A=K"
    using finite_scoped_pattern_readings_complete[OF read] by blast
qed

definition finite_prospective_call_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_prospective_call_slots E u V r = finite_reading_slots (finite_prospective_call_readings E u V r)"

lemma finite_prospective_call_slots_correct:
  "fset (finite_prospective_call_slots E u V r) = prospective_call_slots (decode_finite_environment E) u (fset V) r"
proof -
  have projected: "fset (finite_reading_slots (finite_prospective_call_readings E u V r)) =
      {k. \<exists>q I K. prospective_call_at (decode_finite_environment E) u (fset V) r (fst q) (snd q) I K \<and> k \<in> K}"
  proof (rule finite_reading_slots_correct[where D=decode_finite_call_pattern])
    show "(q,I,K) |\<in>| finite_prospective_call_readings E u V r \<longleftrightarrow>
        prospective_call_at (decode_finite_environment E) u (fset V) r
          (fst (decode_finite_call_pattern q)) (snd (decode_finite_call_pattern q)) (fset I) (fset K)" for q I K
      by (cases q) (simp add: finite_prospective_call_readings_correct decode_finite_call_pattern_def)
    fix q I K assume read: "prospective_call_at (decode_finite_environment E) u (fset V) r (fst q) (snd q) I K"
    show "\<exists>p J A. (p,J,A) |\<in>| finite_prospective_call_readings E u V r \<and> fset A=K"
      using finite_prospective_call_readings_complete[OF read] by blast
  qed
  show ?thesis by (simp only: finite_prospective_call_slots_def projected prospective_call_slots_def
      split_paired_Ex fst_conv snd_conv)
qed

definition finite_native_premise_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_premise_slots E u V r = finite_reading_slots (finite_native_premise_readings E u V r)"

lemma finite_native_premise_slots_correct:
  "fset (finite_native_premise_slots E u V r) = native_premise_slots (decode_finite_environment E) u (fset V) r"
  unfolding finite_native_premise_slots_def native_premise_slots_def
proof (rule finite_reading_slots_correct[where D=decode_finite_native_premise])
  show "(q,I,K) |\<in>| finite_native_premise_readings E u V r \<longleftrightarrow>
      native_premise_at (decode_finite_environment E) u (fset V) r
        (decode_finite_native_premise q) (fset I) (fset K)" for q I K
    by (rule finite_native_premise_readings_correct)
  fix q I K assume read: "native_premise_at (decode_finite_environment E) u (fset V) r q I K"
  show "\<exists>p J A. (p,J,A) |\<in>| finite_native_premise_readings E u V r \<and> fset A=K"
    using finite_native_premise_readings_complete[OF read] by blast
qed

section \<open>Record and family traversal preserves partial dependency reads\<close>

definition finite_family_endpoints ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_family_endpoints E u r = ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (fimage snd) (finite_family_candidates C r))) (finite_artifacts_at E u))"

lemma finite_family_endpoints_member:
  "a |\<in>| finite_family_endpoints E u r \<longleftrightarrow>
    (\<exists>C M s. C |\<in>| finite_artifacts_at E u \<and> M |\<in>| finite_family_candidates C r \<and> (s,a) |\<in>| M)"
  by (simp only: finite_family_endpoints_def finite_union_image_member finite_image_member
      split_paired_Ex snd_conv; blast)

lemma finite_family_endpoints_correct:
  "fset (finite_family_endpoints E u r) = family_endpoints (decode_finite_environment E) u r"
proof (rule set_eqI)
  fix a
  show "a \<in> fset (finite_family_endpoints E u r) \<longleftrightarrow>
      a \<in> family_endpoints (decode_finite_environment E) u r"
  proof
    assume "a \<in> fset (finite_family_endpoints E u r)"
    then obtain C M s where source: "C |\<in>| finite_artifacts_at E u"
      and family: "M |\<in>| finite_family_candidates C r" and endpoint: "(s,a) |\<in>| M"
      by (simp only: finite_family_endpoints_member; blast)
    have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
      using source by (simp add: finite_artifacts_at_member)
    have read: "family_at (decode_finite_object C) r (fset M)"
      using family by (simp add: finite_family_candidates_correct)
    show "a \<in> family_endpoints (decode_finite_environment E) u r"
      using art read endpoint by (simp only: family_endpoints_def mem_Collect_eq rel_ran_def; blast)
  next
    assume "a \<in> family_endpoints (decode_finite_environment E) u r"
    then obtain R M s where art: "artifact_at (decode_finite_environment E) u R"
      and read: "family_at R r M" and endpoint: "(s,a) \<in> M"
      by (simp only: family_endpoints_def mem_Collect_eq rel_ran_def; blast)
    obtain C where source: "C |\<in>| finite_artifacts_at E u" and decoded: "decode_finite_object C=R"
      using art by (simp only: finite_artifacts_at_complete Bex_def; blast)
    have family: "family_at (decode_finite_object C) r M" using read decoded by simp
    obtain F where member: "F |\<in>| finite_family_candidates C r" and represented: "fset F=M"
      using finite_family_candidates_complete[OF family] by blast
    show "a \<in> fset (finite_family_endpoints E u r)"
      unfolding finite_family_endpoints_member
      apply (rule exI[of _ C], rule exI[of _ F], rule exI[of _ s])
      using source member represented endpoint by simp
  qed
qed

definition finite_prospective_family_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_prospective_family_slots E u V r =
    ffUnion (fimage (finite_prospective_call_slots E u V) (finite_family_endpoints E u r))"

lemma finite_prospective_family_slots_correct:
  "fset (finite_prospective_family_slots E u V r) = prospective_family_slots (decode_finite_environment E) u (fset V) r"
  by (auto simp: finite_prospective_family_slots_def finite_union_image_member finite_prospective_call_slots_correct
      finite_family_endpoints_correct prospective_family_slots_def)

definition finite_native_premise_family_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_premise_family_slots E u V r =
    ffUnion (fimage (finite_native_premise_slots E u V) (finite_family_endpoints E u r))"

lemma finite_native_premise_family_slots_correct:
  "fset (finite_native_premise_family_slots E u V r) = native_premise_family_slots (decode_finite_environment E) u (fset V) r"
  by (auto simp: finite_native_premise_family_slots_def finite_union_image_member finite_native_premise_slots_correct
      finite_family_endpoints_correct native_premise_family_slots_def)

definition finite_native_schema_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_schema_slots E u r = ffUnion (fimage (\<lambda>C.
    finite_three_field_record C r (\<lambda>ps b c m. ffUnion (fimage (\<lambda>V.
      finite_pattern_slots E u V c |\<union>| finite_native_premise_family_slots E u V m)
      (finite_binder_scope_candidates C b)))) (finite_artifacts_at E u))"

lemma finite_native_schema_slots_step:
  "k |\<in>| finite_native_schema_slots E u r \<longleftrightarrow>
    (\<exists>C ps b c m V. C |\<in>| finite_artifacts_at E u \<and>
      record_at (decode_finite_object C) r ps [b,c,m] \<and>
      V |\<in>| finite_binder_scope_candidates C b \<and>
      k |\<in>| finite_pattern_slots E u V c |\<union>| finite_native_premise_family_slots E u V m)"
  by (auto simp: finite_native_schema_slots_def finite_union_image_member finite_three_field_record_member)

theorem finite_native_schema_slots_correct:
  "fset (finite_native_schema_slots E u r) = native_schema_slots (decode_finite_environment E) u r"
proof (rule set_eqI)
  fix k
  show "k \<in> fset (finite_native_schema_slots E u r) \<longleftrightarrow>
      k \<in> native_schema_slots (decode_finite_environment E) u r"
  proof
    assume "k \<in> fset (finite_native_schema_slots E u r)"
    then obtain C ps b c m V where source: "C |\<in>| finite_artifacts_at E u"
      and rec: "record_at (decode_finite_object C) r ps [b,c,m]"
      and scope: "V |\<in>| finite_binder_scope_candidates C b"
      and slot: "k |\<in>| finite_pattern_slots E u V c |\<union>| finite_native_premise_family_slots E u V m"
      by (simp only: finite_native_schema_slots_step; blast)
    have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
      using source by (simp add: finite_artifacts_at_member)
    have scope_read: "binder_scope_at (decode_finite_object C) b (fset V)"
      using scope by (simp add: finite_binder_scope_candidates_correct)
    have demanded: "k \<in> pattern_slots (decode_finite_environment E) u (fset V) c \<union>
        native_premise_family_slots (decode_finite_environment E) u (fset V) m"
      using slot by (simp add: finite_pattern_slots_correct finite_native_premise_family_slots_correct)
    show "k \<in> native_schema_slots (decode_finite_environment E) u r"
      unfolding native_schema_slots_def mem_Collect_eq
      apply (rule exI[of _ "decode_finite_object C"], rule exI[of _ ps])
      apply (rule exI[of _ b], rule exI[of _ c], rule exI[of _ m], rule exI[of _ "fset V"])
      using art rec scope_read demanded by simp
  next
    assume "k \<in> native_schema_slots (decode_finite_environment E) u r"
    then obtain R ps b c m V where art: "artifact_at (decode_finite_environment E) u R"
      and rec: "record_at R r ps [b,c,m]" and scope: "binder_scope_at R b V"
      and slot: "k \<in> pattern_slots (decode_finite_environment E) u V c \<union>
        native_premise_family_slots (decode_finite_environment E) u V m"
      by (simp only: native_schema_slots_def mem_Collect_eq; blast)
    obtain C where source: "C |\<in>| finite_artifacts_at E u" and decoded: "decode_finite_object C=R"
      using art by (simp only: finite_artifacts_at_complete Bex_def; blast)
    have scope_read: "binder_scope_at (decode_finite_object C) b V" using scope decoded by simp
    obtain F where member: "F |\<in>| finite_binder_scope_candidates C b" and represented: "fset F=V"
      using finite_binder_scope_candidates_complete[OF scope_read] by blast
    have demanded: "k |\<in>| finite_pattern_slots E u F c |\<union>| finite_native_premise_family_slots E u F m"
      using slot represented by (simp add: finite_pattern_slots_correct finite_native_premise_family_slots_correct)
    show "k \<in> fset (finite_native_schema_slots E u r)"
      unfolding finite_native_schema_slots_step
      apply (rule exI[of _ C], rule exI[of _ ps])
      apply (rule exI[of _ b], rule exI[of _ c], rule exI[of _ m], rule exI[of _ F])
      using source rec decoded member demanded by simp
  qed
qed

definition finite_native_schema_family_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_schema_family_slots E u r =
    ffUnion (fimage (finite_native_schema_slots E u) (finite_family_endpoints E u r))"

lemma finite_native_schema_family_slots_correct:
  "fset (finite_native_schema_family_slots E u r) = native_schema_family_slots (decode_finite_environment E) u r"
  by (auto simp: finite_native_schema_family_slots_def finite_union_image_member finite_native_schema_slots_correct
      finite_family_endpoints_correct native_schema_family_slots_def)

definition finite_native_definition_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_definition_slots E u r = ffUnion (fimage (\<lambda>C.
    finite_two_field_record C r (\<lambda>ps i m.
      finite_scoped_pattern_slots E u i |\<union>| finite_native_schema_family_slots E u m))
      (finite_artifacts_at E u))"

lemma finite_native_definition_slots_step:
  "k |\<in>| finite_native_definition_slots E u r \<longleftrightarrow>
    (\<exists>C ps i m. C |\<in>| finite_artifacts_at E u \<and>
      record_at (decode_finite_object C) r ps [i,m] \<and>
      k |\<in>| finite_scoped_pattern_slots E u i |\<union>| finite_native_schema_family_slots E u m)"
  by (auto simp: finite_native_definition_slots_def finite_union_image_member finite_two_field_record_member)

theorem finite_native_definition_slots_correct:
  "fset (finite_native_definition_slots E u r) = native_definition_slots (decode_finite_environment E) u r"
proof (rule set_eqI)
  fix k
  show "k \<in> fset (finite_native_definition_slots E u r) \<longleftrightarrow>
      k \<in> native_definition_slots (decode_finite_environment E) u r"
  proof
    assume "k \<in> fset (finite_native_definition_slots E u r)"
    then obtain C ps i m where source: "C |\<in>| finite_artifacts_at E u"
      and rec: "record_at (decode_finite_object C) r ps [i,m]"
      and slot: "k |\<in>| finite_scoped_pattern_slots E u i |\<union>| finite_native_schema_family_slots E u m"
      by (simp only: finite_native_definition_slots_step; blast)
    have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
      using source by (simp add: finite_artifacts_at_member)
    have demanded: "k \<in> scoped_pattern_slots (decode_finite_environment E) u i \<union>
        native_schema_family_slots (decode_finite_environment E) u m"
      using slot by (simp add: finite_scoped_pattern_slots_correct finite_native_schema_family_slots_correct)
    show "k \<in> native_definition_slots (decode_finite_environment E) u r"
      unfolding native_definition_slots_def mem_Collect_eq
      apply (rule exI[of _ "decode_finite_object C"], rule exI[of _ ps], rule exI[of _ i], rule exI[of _ m])
      using art rec demanded by simp
  next
    assume "k \<in> native_definition_slots (decode_finite_environment E) u r"
    then obtain R ps i m where art: "artifact_at (decode_finite_environment E) u R"
      and rec: "record_at R r ps [i,m]"
      and slot: "k \<in> scoped_pattern_slots (decode_finite_environment E) u i \<union>
        native_schema_family_slots (decode_finite_environment E) u m"
      by (simp only: native_definition_slots_def mem_Collect_eq; blast)
    obtain C where source: "C |\<in>| finite_artifacts_at E u" and decoded: "decode_finite_object C=R"
      using art by (simp only: finite_artifacts_at_complete Bex_def; blast)
    have demanded: "k |\<in>| finite_scoped_pattern_slots E u i |\<union>| finite_native_schema_family_slots E u m"
      using slot by (simp add: finite_scoped_pattern_slots_correct finite_native_schema_family_slots_correct)
    show "k \<in> fset (finite_native_definition_slots E u r)"
      unfolding finite_native_definition_slots_step
      apply (rule exI[of _ C], rule exI[of _ ps], rule exI[of _ i], rule exI[of _ m])
      using source rec decoded demanded by simp
  qed
qed

section \<open>The package's own root family determines its retained boundary\<close>

definition finite_native_package_roots ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site fset" where
  "finite_native_package_roots E u r =
    ffUnion (fimage (fimage snd) (finite_native_root_family_readings E u r))"

lemma finite_native_package_roots_member:
  "d |\<in>| finite_native_package_roots E u r \<longleftrightarrow>
    (\<exists>Q s. Q |\<in>| finite_native_root_family_readings E u r \<and> (s,d) |\<in>| Q)"
  by (cases d; simp only: finite_native_package_roots_def finite_union_image_member finite_image_member
      split_paired_Ex snd_conv; blast)

lemma finite_native_package_roots_correct:
  "fset (finite_native_package_roots E u r) = native_package_roots (decode_finite_environment E) u r"
proof (rule set_eqI)
  fix d
  show "d \<in> fset (finite_native_package_roots E u r) \<longleftrightarrow>
      d \<in> native_package_roots (decode_finite_environment E) u r"
  proof
    assume "d \<in> fset (finite_native_package_roots E u r)"
    then obtain Q s where member: "Q |\<in>| finite_native_root_family_readings E u r"
      and endpoint: "(s,d) |\<in>| Q" by (simp only: finite_native_package_roots_member; blast)
    have family: "native_root_family_at (decode_finite_environment E) u r (fset Q)"
      using member by (simp add: finite_native_root_family_readings_correct)
    show "d \<in> native_package_roots (decode_finite_environment E) u r"
      using family endpoint by (simp only: native_package_roots_def mem_Collect_eq rel_ran_def; blast)
  next
    assume "d \<in> native_package_roots (decode_finite_environment E) u r"
    then obtain Q s where family: "native_root_family_at (decode_finite_environment E) u r Q"
      and endpoint: "(s,d) \<in> Q" by (simp only: native_package_roots_def mem_Collect_eq rel_ran_def; blast)
    obtain F where member: "F |\<in>| finite_native_root_family_readings E u r" and represented: "fset F=Q"
      using finite_native_root_family_readings_complete[OF family] by blast
    show "d \<in> fset (finite_native_package_roots E u r)"
      unfolding finite_native_package_roots_member
      apply (rule exI[of _ F], rule exI[of _ s])
      using member represented endpoint by simp
  qed
qed

definition finite_native_package_sites ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site fset" where
  "finite_native_package_sites E u r = finite_native_definition_sites E (finite_native_package_roots E u r)"

lemma finite_native_package_sites_correct:
  "fset (finite_native_package_sites E u r) = native_package_sites (decode_finite_environment E) u r"
  by (simp add: finite_native_package_sites_def native_package_sites_def
      finite_native_definition_sites_correct finite_native_package_roots_correct)

definition finite_native_package_sources ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u fset" where
  "finite_native_package_sources E u r = finsert u (fimage fst (finite_native_package_sites E u r))"

lemma finite_native_package_sources_correct:
  "fset (finite_native_package_sources E u r) = native_package_sources (decode_finite_environment E) u r"
  by (simp add: finite_native_package_sources_def native_package_sources_def fimage.rep_eq
      finite_native_package_sites_correct)

definition finite_native_root_requests ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_root_requests E u r = fimage (Pair u) (finite_family_endpoints E u r)"

lemma finite_native_root_requests_correct:
  "fset (finite_native_root_requests E u r) = native_root_requests (decode_finite_environment E) u r"
  by (auto simp: finite_native_root_requests_def native_root_requests_def fimage.rep_eq finite_family_endpoints_correct)

definition finite_native_package_demands ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_package_demands E u r = finite_requested_slots E (finite_native_root_requests E u r) |\<union>|
    ffUnion (fimage (\<lambda>(v,a). fimage (Pair v) (finite_native_definition_slots E v a))
      (finite_native_package_sites E u r))"

theorem finite_native_package_demands_correct:
  "fset (finite_native_package_demands E u r) = native_package_demands (decode_finite_environment E) u r"
  by (auto simp: finite_native_package_demands_def native_package_demands_def finite_requested_slots_correct
      finite_native_root_requests_correct finite_native_package_sites_correct finite_native_definition_slots_correct
      fimage.rep_eq ffUnion.rep_eq split: prod.splits; force)

definition finite_native_package_environment ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u finite_artifact_environment" where
  "finite_native_package_environment E u r =
    finite_read_environment E (finite_native_package_sources E u r) (finite_native_package_demands E u r)"

theorem finite_native_package_environment_correct:
  "decode_finite_environment (finite_native_package_environment E u r) =
    native_package_environment (decode_finite_environment E) u r"
  by (simp add: finite_native_package_environment_def native_package_environment_def
      finite_read_environment_correct finite_native_package_sources_correct finite_native_package_demands_correct)

export_code finite_pattern_slots finite_scoped_pattern_slots finite_prospective_call_slots
  finite_native_premise_slots finite_prospective_family_slots finite_native_definition_slots
  finite_native_package_sources finite_native_package_demands finite_native_package_environment checking SML

text \<open>
  The grammar itself determines the slots needed by a package. The computation
  follows actual family endpoints, record fields, and binder scopes, retaining
  every slot read within them. It preserves partial dependency reads even when
  an enclosing schema or definition fails its complete formation conditions.
  The root citation family and definition dependencies determine all source
  uses. These boundaries and the resulting retained environment equal their
  mathematical definitions on every finite input.
\<close>

end
