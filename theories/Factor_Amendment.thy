theory Factor_Amendment
  imports Factor_Amendment_Values Factor_Current_Entries Factor_Definition_Closure
begin

section \<open>Amendment permission respects every complete presentation\<close>

definition amendment_permission_invariant ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "amendment_permission_invariant P d \<longleftrightarrow>
    (\<forall>E pu pr au ar F v root G c t w. amendment_value_presents E pu pr au ar F v root G c t \<longrightarrow>
      amendment_value_presents E pu pr au ar F v root G c w \<longrightarrow>
      (schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d w) \<and>
      ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,w)\<in>positive_meaning P))"

lemma amendment_permission_invariantD:
  assumes invariant: "amendment_permission_invariant P d"
    and first: "amendment_value_presents E pu pr au ar F v root G c t"
    and second: "amendment_value_presents E pu pr au ar F v root G c w"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d w"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,w)\<in>positive_meaning P"
  using invariant[unfolded amendment_permission_invariant_def, rule_format, OF first second] by auto

lemma amendment_permission_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
  shows "amendment_permission_invariant Q e\<longleftrightarrow>amendment_permission_invariant P d"
  by (simp add: amendment_permission_invariant_def boundary meaning)

definition factor_accepts ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "factor_accepts P d E pu pr au ar F v root G c \<longleftrightarrow>
    amendment_permission_invariant P d \<and>
    (\<exists>t. amendment_value_presents E pu pr au ar F v root G c t \<and> (d,t)\<in>positive_meaning P)"

lemma factor_acceptance_formed:
  assumes permitted: "factor_accepts P d E pu pr au ar F v root G c"
  shows "schema_system_formed P \<and> environment_formed E \<and> environment_formed F \<and>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    (v,root)\<in>environment_positions F \<and> generation_formed G \<and> target_formed c"
proof -
  obtain t where present: "amendment_value_presents E pu pr au ar F v root G c t"
    and truth: "(d,t)\<in>positive_meaning P"
    using permitted unfolding factor_accepts_def by blast
  have program: "schema_system_formed P"
    using positive_meaning_formed[OF truth] by (simp add: schema_call_formed_def)
  show ?thesis using program amendment_value_presents_formed[OF present] by blast
qed

theorem factor_acceptance_at_presentation:
  assumes invariant: "amendment_permission_invariant P d"
    and present: "amendment_value_presents E pu pr au ar F v root G c t"
  shows "factor_accepts P d E pu pr au ar F v root G c\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof
  assume "factor_accepts P d E pu pr au ar F v root G c"
  then obtain w where other: "amendment_value_presents E pu pr au ar F v root G c w"
    "(d,w)\<in>positive_meaning P" unfolding factor_accepts_def by blast
  show "(d,t)\<in>positive_meaning P"
    using amendment_permission_invariantD(2)[OF invariant other(1) present] other(2) by blast
next
  assume "(d,t)\<in>positive_meaning P"
  then show "factor_accepts P d E pu pr au ar F v root G c"
    using invariant present unfolding factor_accepts_def by blast
qed

theorem factor_acceptance_every_presentation:
  "factor_accepts P d E pu pr au ar F v root G c\<longleftrightarrow>
    environment_formed E \<and> (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    environment_formed F \<and> (v,root)\<in>environment_positions F \<and>
    generation_formed G \<and> target_formed c \<and> amendment_permission_invariant P d \<and>
    (\<forall>t. amendment_value_presents E pu pr au ar F v root G c t \<longrightarrow> (d,t)\<in>positive_meaning P)"
proof
  assume accepted: "factor_accepts P d E pu pr au ar F v root G c"
  have invariant: "amendment_permission_invariant P d" using accepted by (simp add: factor_accepts_def)
  have every: "\<forall>t. amendment_value_presents E pu pr au ar F v root G c t \<longrightarrow> (d,t)\<in>positive_meaning P"
    using accepted factor_acceptance_at_presentation[OF invariant] by blast
  show "environment_formed E \<and> (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    environment_formed F \<and> (v,root)\<in>environment_positions F \<and>
    generation_formed G \<and> target_formed c \<and> amendment_permission_invariant P d \<and>
    (\<forall>t. amendment_value_presents E pu pr au ar F v root G c t \<longrightarrow> (d,t)\<in>positive_meaning P)"
    using factor_acceptance_formed[OF accepted] invariant every by blast
next
  assume parts: "environment_formed E \<and> (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    environment_formed F \<and> (v,root)\<in>environment_positions F \<and>
    generation_formed G \<and> target_formed c \<and> amendment_permission_invariant P d \<and>
    (\<forall>t. amendment_value_presents E pu pr au ar F v root G c t \<longrightarrow> (d,t)\<in>positive_meaning P)"
  obtain t where present: "amendment_value_presents E pu pr au ar F v root G c t"
    using amendment_value_presents_total parts by blast
  show "factor_accepts P d E pu pr au ar F v root G c"
    using parts present unfolding factor_accepts_def by blast
qed

section \<open>The actual current frame fixes the program and acceptance entry\<close>

definition current_accepts_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "current_accepts_at C q F au ar H c \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d D qu qr bu br N v root t I K.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      current_frame_quoted_at C q D qu qr bu br N v root \<and>
      environment_formed F \<and> environment_included E F \<and>
      native_application_at F au ar d t I K \<and> amendment_permission_invariant P d \<and>
      amendment_value_presents D qu qr bu br N v root H c t \<and> (d,t)\<in>positive_meaning P)"

theorem current_acceptance_with_reads:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v root"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "current_accepts_at C q F au ar H c\<longleftrightarrow>
    amendment_permission_invariant P d \<and>
    amendment_value_presents D qu qr bu br N v root H c t \<and> (d,t)\<in>positive_meaning P"
proof
  assume accepted: "current_accepts_at C q F au ar H c"
  obtain A' l' G' p' E' pu' pr' Q e D' qu' qr' bu' br' N' v' root' w J L where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q e"
    "current_frame_quoted_at C q D' qu' qr' bu' br' N' v' root'"
    "native_application_at F au ar e w J L" "amendment_permission_invariant Q e"
    "amendment_value_presents D' qu' qr' bu' br' N' v' root' H c w" "(e,w)\<in>positive_meaning Q"
    using accepted unfolding current_accepts_at_def by blast
  have scope: "P=Q \<and> d=e" using current_entry_scope_unique[OF current other(1)] by blast
  have fields: "D=D' \<and> qu=qu' \<and> qr=qr' \<and> bu=bu' \<and> br=br' \<and> N=N' \<and> v=v' \<and> root=root'"
    by (rule current_frame_quoted_unique[OF frame other(2)])
  have call_term: "t=w" using native_application_unique[OF app other(3)] by blast
  show "amendment_permission_invariant P d \<and>
    amendment_value_presents D qu qr bu br N v root H c t \<and> (d,t)\<in>positive_meaning P"
    using other(4-6) scope fields call_term by simp
next
  assume "amendment_permission_invariant P d \<and>
    amendment_value_presents D qu qr bu br N v root H c t \<and> (d,t)\<in>positive_meaning P"
  then show "current_accepts_at C q F au ar H c"
    using current frame formed included app unfolding current_accepts_at_def by blast
qed

theorem current_acceptance_at_presentation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v root"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
    and invariant: "amendment_permission_invariant P d"
    and present: "amendment_value_presents D qu qr bu br N v root H c t"
  shows "current_accepts_at C q F au ar H c\<longleftrightarrow>factor_accepts P d D qu qr bu br N v root H c"
    and "current_accepts_at C q F au ar H c\<longleftrightarrow>native_positive_holds F pu pr au ar"
proof -
  have decision: "current_accepts_at C q F au ar H c\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (simp only: current_acceptance_with_reads[OF current frame formed included app] invariant present simp_thms)
  show "current_accepts_at C q F au ar H c\<longleftrightarrow>factor_accepts P d D qu qr bu br N v root H c"
    by (simp only: decision factor_acceptance_at_presentation[OF invariant present])
  show "current_accepts_at C q F au ar H c\<longleftrightarrow>native_positive_holds F pu pr au ar"
    by (simp only: decision current_entry_scope_future_application(4)[OF current formed included app])
qed

theorem current_acceptance_requires_selected_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and app: "native_application_at F au ar e t I K"
    and accepted: "current_accepts_at C q F au ar H c"
  shows "e=d"
proof -
  obtain A' l' G' p' E' pu' pr' Q f w J L where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q f"
    "native_application_at F au ar f w J L"
    using accepted unfolding current_accepts_at_def by blast
  have selected: "d=f" using current_entry_scope_unique[OF current other(1)] by blast
  have called: "e=f" using native_application_unique[OF app other(2)] by blast
  show ?thesis using selected called by simp
qed

theorem current_acceptance_program_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and accepted: "current_accepts_at C q F au ar H c"
  shows "environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
    native_positive_holds F pu pr au ar"
proof -
  obtain A' l' G' p' E' pu' pr' Q e t I K where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q e"
    "environment_formed F" "environment_included E' F"
    "native_application_at F au ar e t I K" "(e,t)\<in>positive_meaning Q"
    using accepted unfolding current_accepts_at_def by blast
  have same: "E=E' \<and> P=Q \<and> d=e"
    using current_entry_scope_unique[OF current other(1)] by blast
  have included: "environment_included E F" and app: "native_application_at F au ar d t I K"
    and truth: "(d,t)\<in>positive_meaning P" using other(3-5) same by simp_all
  show ?thesis using other(2) included truth
    current_entry_scope_future_application[OF current other(2) included app] by blast
qed

theorem current_acceptance_subject_unique:
  assumes first: "current_accepts_at C q F au ar G c" and second: "current_accepts_at R s F au ar H k"
  shows "G=H \<and> c=k"
proof -
  obtain E pu pr bu br N v root d t I K where left: "native_application_at F au ar d t I K"
    "amendment_value_presents E pu pr bu br N v root G c t"
    using first unfolding current_accepts_at_def by blast
  obtain D qu qr cu cr M w tail e x J L where right: "native_application_at F au ar e x J L"
    "amendment_value_presents D qu qr cu cr M w tail H k x"
    using second unfolding current_accepts_at_def by blast
  have same: "x=t" using native_application_unique[OF right(1) left(1)] by blast
  have other: "amendment_value_presents D qu qr cu cr M w tail H k t" using right(2) same by simp
  show ?thesis using amendment_value_presents_unique[OF left(2) other] by blast
qed

section \<open>Predecessor locality of the active positive program\<close>

theorem current_entry_dependency_boundary:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "system_definition_closure P {d}\<subseteq>system_definitions P"
    and "finite (system_definition_closure P {d})"
    and "system_definition_closure P {d}=native_definition_sites E {d}"
proof -
  have closed: "closed_native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    using current_entry_scope_closed[OF current] by auto
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have formed: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have roots: "{d}\<subseteq>system_definitions P" using member by simp
  show "system_definition_closure P {d}\<subseteq>system_definitions P"
    "finite (system_definition_closure P {d})"
    by (rule system_definition_closure_boundary[OF formed roots])+
  have native: "native_package_formed E (native_package_roots E pu pr)"
    "P=native_program E (native_package_roots E pu pr)"
    by (rule native_package_projection[OF package])+
  have inside: "{d}\<subseteq>native_definition_sites E (native_package_roots E pu pr)"
    using roots native by (simp add: native_program_definitions[OF native(1)])
  show "system_definition_closure P {d}=native_definition_sites E {d}"
    using native_program_definition_closure[OF inside] native(2) by simp
qed

theorem amendment_permission_dependency_locality:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definition_closure P {d})"
  shows "factor_accepts P d E pu pr au ar F v root G c\<longleftrightarrow>
    factor_accepts Q d E pu pr au ar F v root G c"
proof -
  have boundary: "\<And>t. schema_call_formed P d t\<longleftrightarrow>schema_call_formed Q d t"
    by (rule system_definition_closure_locality(1)[OF formed agree]) simp
  have meaning: "\<And>t. (d,t)\<in>positive_meaning P\<longleftrightarrow>(d,t)\<in>positive_meaning Q"
    by (rule system_definition_closure_locality(2)[OF formed agree]) simp
  show ?thesis by (simp add: factor_accepts_def amendment_permission_invariant_def boundary meaning)
qed

text \<open>
  Raw acceptance invokes only the entry selected by the exact current frame.
  Its positive semantic dependencies follow the predecessor program's actual
  callees and stay within that closed package. The candidate and certificate
  are complete ordinary argument values; neither contributes a rule to this
  invocation. Agreement on the derived closure preserves formation and truth
  for every argument and therefore preserves the permission relation.

  The adoption judgment that establishes currentness has its separately
  recorded program and dependency scope. No equality with the selected program
  is assumed. These results locate the acceptance invocation after currentness
  is established. Certificate completeness, predecessor continuation, explicit
  cross-version interpretation, and successor adoption still require their
  own joined conditions.
\<close>

end
