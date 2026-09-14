theory RRA_Finite_Environment_Preservation
  imports RRA_Finite_Inclusion RRA_Executable_Retention
begin

section \<open>Compare every artifact and outgoing binding at the retained uses\<close>

definition finite_environment_agrees_on where
  "finite_environment_agrees_on E F U \<longleftrightarrow>
    ffilter (\<lambda>(u,A). u |\<in>| U) (finite_environment_artifacts E)=
      ffilter (\<lambda>(u,A). u |\<in>| U) (finite_environment_artifacts F) \<and>
    ffilter (\<lambda>((u,k),v). u |\<in>| U) (finite_environment_bindings E)=
      ffilter (\<lambda>((u,k),v). u |\<in>| U) (finite_environment_bindings F)"

lemma finite_environment_agrees_on_rows:
  "finite_environment_agrees_on E F U \<longleftrightarrow>
    (\<forall>u\<in>fset U. \<forall>A. ((u,A) |\<in>| finite_environment_artifacts E \<longleftrightarrow>
      (u,A) |\<in>| finite_environment_artifacts F)) \<and>
    (\<forall>u\<in>fset U. \<forall>k v. (((u,k),v) |\<in>| finite_environment_bindings E \<longleftrightarrow>
      ((u,k),v) |\<in>| finite_environment_bindings F))"
  by (auto simp: finite_environment_agrees_on_def fset_inject[symmetric] set_eq_iff; blast)

theorem finite_environment_agrees_on_correct:
  "finite_environment_agrees_on E F U \<longleftrightarrow>
    (\<forall>u\<in>fset U. \<forall>A. artifact_at (decode_finite_environment E) u A \<longleftrightarrow>
      artifact_at (decode_finite_environment F) u A) \<and>
    (\<forall>u\<in>fset U. \<forall>k v. binds_slot (decode_finite_environment E) u k v \<longleftrightarrow>
      binds_slot (decode_finite_environment F) u k v)"
proof -
  have artifacts: "(\<forall>u\<in>fset U. \<forall>A. ((u,A) |\<in>| finite_environment_artifacts E \<longleftrightarrow>
      (u,A) |\<in>| finite_environment_artifacts F)) \<longleftrightarrow>
      (\<forall>u\<in>fset U. \<forall>A. artifact_at (decode_finite_environment E) u A \<longleftrightarrow>
        artifact_at (decode_finite_environment F) u A)"
  proof
    assume rows: "\<forall>u\<in>fset U. \<forall>A. ((u,A) |\<in>| finite_environment_artifacts E \<longleftrightarrow>
      (u,A) |\<in>| finite_environment_artifacts F)"
    show "\<forall>u\<in>fset U. \<forall>A. artifact_at (decode_finite_environment E) u A \<longleftrightarrow>
        artifact_at (decode_finite_environment F) u A"
    proof (intro ballI allI)
      fix u A assume member: "u\<in>fset U"
      show "artifact_at (decode_finite_environment E) u A \<longleftrightarrow>
          artifact_at (decode_finite_environment F) u A"
        using rows[rule_format, OF member] by auto
    qed
  next
    assume actual: "\<forall>u\<in>fset U. \<forall>A. artifact_at (decode_finite_environment E) u A \<longleftrightarrow>
        artifact_at (decode_finite_environment F) u A"
    show "\<forall>u\<in>fset U. \<forall>A. ((u,A) |\<in>| finite_environment_artifacts E \<longleftrightarrow>
      (u,A) |\<in>| finite_environment_artifacts F)"
    proof (intro ballI allI)
      fix u A assume member: "u\<in>fset U"
      have entry: "artifact_at (decode_finite_environment E) u (decode_finite_object A) \<longleftrightarrow>
          artifact_at (decode_finite_environment F) u (decode_finite_object A)"
        by (rule actual[rule_format, OF member])
      show "(u,A) |\<in>| finite_environment_artifacts E \<longleftrightarrow>
          (u,A) |\<in>| finite_environment_artifacts F"
        using entry by auto
    qed
  qed
  show ?thesis by (simp only: finite_environment_agrees_on_rows artifacts binds_slot_def
    decode_finite_environment_fields)
qed

export_code finite_environment_agrees_on checking SML

lemma finite_environment_agrees_on_trans:
  assumes "finite_environment_agrees_on E F U" "finite_environment_agrees_on F G V" "U |\<subseteq>| V"
  shows "finite_environment_agrees_on E G U"
  using assms by (auto simp: finite_environment_agrees_on_rows less_eq_fset.rep_eq; blast)

end
