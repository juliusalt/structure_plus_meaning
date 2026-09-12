theory Factor_Current_Programs
  imports Factor_Generation_Programs Factor_Current_Scopes
begin

section \<open>The exact currentness frame determines the selected program scope\<close>

definition current_program_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_target \<Rightarrow> exact_target \<Rightarrow>
    generation_core \<Rightarrow> exact_target \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option native_system \<Rightarrow> bool" where
  "current_program_scope_quoted_at C q A l G p E u r P \<longleftrightarrow>
    generation_program_scope G E u r P \<and>
    (\<exists>H pu pr au ar F v root. current_scope_quoted_at C q H pu pr au ar A F v root l G p)"

theorem current_program_scope_with_frame:
  assumes frame: "current_scope_quoted_at C q H pu pr au ar A F v root l G p"
  shows "current_program_scope_quoted_at C q A l G p E u r P \<longleftrightarrow>
    generation_program_scope G E u r P"
  using frame unfolding current_program_scope_quoted_at_def by blast

theorem current_program_scope_unique:
  assumes first: "current_program_scope_quoted_at C q A l G p E u r P"
    and second: "current_program_scope_quoted_at C q B m H z F v s Q"
  shows "A=B \<and> l=m \<and> G=H \<and> p=z \<and> E=F \<and> u=v \<and> r=s \<and> P=Q"
proof -
  obtain D pu pr au ar N w root where left:
    "generation_program_scope G E u r P" "current_scope_quoted_at C q D pu pr au ar A N w root l G p"
    using first unfolding current_program_scope_quoted_at_def by blast
  obtain D' qu qr bu br N' w' root' where right:
    "generation_program_scope H F v s Q" "current_scope_quoted_at C q D' qu qr bu br B N' w' root' m H z"
    using second unfolding current_program_scope_quoted_at_def by blast
  have subject: "A=B \<and> l=m \<and> G=H \<and> p=z"
    using current_scope_quoted_unique[OF left(2) right(2)] by blast
  have payload: "generation_payload G=generation_payload H" using subject by simp
  show ?thesis using subject generation_program_scope_unique[OF left(1) right(1) payload] by blast
qed

theorem current_program_scope_quoted_total:
  fixes H F :: "local_address option artifact_environment"
  assumes current: "native_current H pu pr au ar A F v root l G p"
    and scope: "generation_program_scope G E u r P"
  shows "\<exists>C. current_program_scope_quoted_at C [] A l G p E u r P \<and>
    current_scope_quoted_at C [] (native_judgment_environment H pu pr au ar) pu pr au ar A F v root l G p"
proof -
  obtain C where frame:
    "current_scope_quoted_at C [] (native_judgment_environment H pu pr au ar) pu pr au ar A F v root l G p"
    using current_scope_quoted_total[OF current] by blast
  show ?thesis using frame scope current_program_scope_with_frame[OF frame] by blast
qed

theorem current_program_scope_future_application:
  assumes current: "current_program_scope_quoted_at C q A l G p E pu pr P"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "native_package_at F pu pr P"
    and "native_package_environment F pu pr=E"
    and "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    and "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof -
  have scope: "generation_program_scope G E pu pr P"
    using current by (simp add: current_program_scope_quoted_at_def)
  show "native_package_at F pu pr P" "native_package_environment F pu pr=E"
    "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule generation_program_scope_future_application[OF scope formed included app])+
qed

text \<open>
  The existing currentness frame records the complete adoption and publication
  scopes. Its selected generation now supplies the complete program scope
  through its payload. No additional stored fields are introduced. The actual
  frame uniquely determines authority, locus, generation, purpose, program
  environment, selected site, and derived program.

  Currentness can be recorded for every existing judgment whose generation has
  this payload profile. Future applications in an extension of that exact
  program environment retain its formation and truth. The program that judged
  adoption and the program selected by the generation remain separate. This
  join does not require that they coincide or validate the generation's cause.
\<close>

end
