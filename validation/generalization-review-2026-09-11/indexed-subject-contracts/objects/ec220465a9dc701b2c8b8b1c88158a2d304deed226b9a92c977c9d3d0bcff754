theory Factor_Generation_Programs
  imports Factor_Program_Scopes RRA_Generation
begin

section \<open>A generation payload can retain an exact complete program scope\<close>

definition generation_program_scope ::
  "generation_core \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option native_system \<Rightarrow> bool" where
  "generation_program_scope G E u r P \<longleftrightarrow> generation_formed G \<and>
    (\<exists>C q. generation_payload G=Whole_Artifact C \<and> program_scope_quoted_at C q E u r P)"

lemma generation_program_scope_from_payload:
  assumes "generation_formed G" "generation_payload G=Whole_Artifact C"
    "program_scope_quoted_at C q E u r P"
  shows "generation_program_scope G E u r P"
  using assms unfolding generation_program_scope_def by blast

theorem generation_program_scope_unique:
  assumes first: "generation_program_scope G E u r P" and second: "generation_program_scope H F v s Q"
    and payload: "generation_payload G=generation_payload H"
  shows "E=F \<and> u=v \<and> r=s \<and> P=Q"
proof -
  obtain C q where left: "generation_payload G=Whole_Artifact C" "program_scope_quoted_at C q E u r P"
    using first unfolding generation_program_scope_def by blast
  obtain D a where right: "generation_payload H=Whole_Artifact D" "program_scope_quoted_at D a F v s Q"
    using second unfolding generation_program_scope_def by blast
  have same: "C=D" using left(1) right(1) payload by simp
  have other: "program_scope_quoted_at C a F v s Q" using right(2) same by simp
  show ?thesis using program_scope_whole_unique[OF left(2) other] by blast
qed

lemma generation_program_scope_closed:
  assumes scope: "generation_program_scope G E u r P"
  shows "generation_formed G \<and> closed_native_package_at E u r P \<and>
    native_package_environment E u r=E"
  using scope program_scope_is_minimal
  unfolding generation_program_scope_def program_scope_quoted_at_def by blast

theorem generation_program_scope_payload_transfer:
  assumes scope: "generation_program_scope G E u r P" and formed: "generation_formed H"
    and payload: "generation_payload H=generation_payload G"
  shows "generation_program_scope H E u r P"
  using assms unfolding generation_program_scope_def by simp

theorem generation_program_scope_future_application:
  assumes scope: "generation_program_scope G E pu pr P" and formed: "environment_formed F"
    and included: "environment_included E F" and app: "native_application_at F au ar d t I K"
  shows "native_package_at F pu pr P"
    and "native_package_environment F pu pr=E"
    and "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    and "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof -
  obtain C q where quote: "program_scope_quoted_at C q E pu pr P"
    using scope unfolding generation_program_scope_def by blast
  show "native_package_at F pu pr P" "native_package_environment F pu pr=E"
    "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule program_scope_future_application[OF quote formed included app])+
qed

text \<open>
  This profile recovers a complete minimal program scope from the generation's
  whole-artifact payload. The complete quotation determines its own root.
  The environment, selected program site, and derived program are unique;
  changing an enclosing generation presentation cannot rebind that scope.

  A different formed core with the identical payload recovers the same program,
  while keeping its own locus, history, and cause. This fact neither identifies
  the two cores nor validates either cause. Formation, construction permission,
  currentness, and amendment acceptance remain separate judgments.
\<close>

end
