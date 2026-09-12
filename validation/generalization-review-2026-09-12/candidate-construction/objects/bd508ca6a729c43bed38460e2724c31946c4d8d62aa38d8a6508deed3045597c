theory Factor_Current_Companions
  imports Factor_Current_Entries Factor_Native_Authority
begin

section \<open>The recorded adoption call determines its exact policy\<close>

definition current_frame_policy ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option native_system \<Rightarrow>
    local_address option definition_site \<Rightarrow> bool" where
  "current_frame_policy C q E pu pr P d \<longleftrightarrow>
    (\<exists>F au ar N v root t I K.
      current_frame_quoted_at C q F pu pr au ar N v root \<and>
      native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
      E=native_package_environment F pu pr)"

theorem current_frame_policy_with_reads:
  assumes frame: "current_frame_quoted_at C q F pu pr au ar N v root"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d t I K"
  shows "current_frame_policy C q E qu qr Q e \<longleftrightarrow>
    E=native_package_environment F pu pr \<and> qu=pu \<and> qr=pr \<and> Q=P \<and> e=d"
proof
  assume "current_frame_policy C q E qu qr Q e"
  then obtain H bu br M w s x J L where other:
    "current_frame_quoted_at C q H qu qr bu br M w s"
    "native_package_at H qu qr Q" "native_application_at H bu br e x J L"
    "E=native_package_environment H qu qr"
    unfolding current_frame_policy_def by blast
  have same: "F=H \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    using current_frame_quoted_unique[OF frame other(1)] by blast
  have read: "native_package_at F pu pr Q" "native_application_at F au ar e x J L"
    using other(2,3) same by simp_all
  have program: "Q=P" by (rule native_package_unique[OF read(1) package])
  have entry: "e=d" using native_application_unique[OF read(2) app] by blast
  show "E=native_package_environment F pu pr \<and> qu=pu \<and> qr=pr \<and> Q=P \<and> e=d"
    using other(4) same program entry by simp
next
  assume "E=native_package_environment F pu pr \<and> qu=pu \<and> qr=pr \<and> Q=P \<and> e=d"
  then show "current_frame_policy C q E qu qr Q e"
    using frame package app unfolding current_frame_policy_def by blast
qed

theorem current_frame_policy_unique:
  assumes first: "current_frame_policy C q E pu pr P d"
    and second: "current_frame_policy C q F qu qr Q e"
  shows "E=F \<and> pu=qu \<and> pr=qr \<and> P=Q \<and> d=e"
proof -
  obtain H au ar N v root t I K where read:
    "current_frame_quoted_at C q H pu pr au ar N v root"
    "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    "E=native_package_environment H pu pr"
    using first unfolding current_frame_policy_def by blast
  have fields: "F=native_package_environment H pu pr \<and> qu=pu \<and> qr=pr \<and> Q=P \<and> e=d"
    using second by (simp only: current_frame_policy_with_reads[OF read(1-3)])
  show ?thesis using fields read(4) by auto
qed

lemma current_scope_has_policy:
  assumes scope: "current_scope_quoted_at C q F pu pr au ar A N v root l G p"
  shows "\<exists>P d. current_frame_policy C q (native_package_environment F pu pr) pu pr P d"
proof -
  obtain P d t I K where read: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    using scope unfolding current_scope_quoted_at_def native_current_def native_adoption_judgment_at_def by blast
  have frame: "current_frame_quoted_at C q F pu pr au ar N v root"
    using scope by (simp add: current_scope_quoted_at_def)
  show ?thesis using frame read unfolding current_frame_policy_def by blast
qed

theorem current_frame_policy_adoption:
  assumes scope: "current_scope_quoted_at C q F pu pr au ar A N v root l G p"
    and policy: "current_frame_policy C q E qu qr Q e"
  shows "factor_adopts Q e A G p"
proof -
  obtain P d t I K where read: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and admitted: "adoption_permission_invariant P d" "adoption_value_presents A G p t"
      "(d,t)\<in>positive_meaning P"
    using scope unfolding current_scope_quoted_at_def native_current_def native_adoption_judgment_at_def by blast
  have frame: "current_frame_quoted_at C q F pu pr au ar N v root"
    using scope by (simp add: current_scope_quoted_at_def)
  have same: "Q=P \<and> e=d"
    using policy by (auto simp only: current_frame_policy_with_reads[OF frame read])
  show ?thesis using admitted same unfolding factor_adopts_def by blast
qed

section \<open>The frame determines its actual published snapshot\<close>

definition current_snapshot_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> selection_snapshot \<Rightarrow> bool" where
  "current_snapshot_at C q S \<longleftrightarrow>
    (\<exists>E pu pr au ar N v root V.
      current_frame_quoted_at C q E pu pr au ar N v root \<and>
      publication_environment_closed N v root V \<and> S=publication_snapshot V)"

theorem current_snapshot_with_publication:
  assumes frame: "current_frame_quoted_at C q E pu pr au ar N v root"
    and publication: "publication_environment_closed N v root V"
  shows "current_snapshot_at C q S\<longleftrightarrow>S=publication_snapshot V"
proof
  assume "current_snapshot_at C q S"
  then obtain F qu qr bu br M w tail W where other:
    "current_frame_quoted_at C q F qu qr bu br M w tail"
    "publication_environment_closed M w tail W" "S=publication_snapshot W"
    unfolding current_snapshot_at_def by blast
  have same: "N=M \<and> v=w \<and> root=tail"
    using current_frame_quoted_unique[OF frame other(1)] by blast
  have reads: "publication_at N v root W" "publication_at N v root V"
    using other(2) publication same by (auto simp: publication_environment_closed_def)
  have "W=V" by (rule publication_at_unique[OF reads])
  then show "S=publication_snapshot V" using other(3) by simp
next
  assume "S=publication_snapshot V"
  then show "current_snapshot_at C q S" using frame publication unfolding current_snapshot_at_def by blast
qed

lemma current_snapshot_unique:
  assumes first: "current_snapshot_at C q S" and second: "current_snapshot_at C q T"
  shows "S=T"
proof -
  obtain E pu pr au ar N v root V where read:
    "current_frame_quoted_at C q E pu pr au ar N v root"
    "publication_environment_closed N v root V"
    using first unfolding current_snapshot_at_def by blast
  have same: "S=publication_snapshot V" "T=publication_snapshot V"
    using first second by (simp_all only: current_snapshot_with_publication[OF read])
  show ?thesis using same by simp
qed

theorem current_entry_snapshot_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "\<exists>S. current_snapshot_at C q S \<and> snapshot_formed S \<and> snapshot_lookup S l=Some G"
proof -
  obtain F qu qr au ar N v root where scope:
    "current_scope_quoted_at C q F qu qr au ar A N v root l G p"
    using current_entry_scope_frame[OF current] by blast
  obtain V where publication: "publication_environment_closed N v root V"
    and selected: "snapshot_lookup (publication_snapshot V) l=Some G"
    using scope unfolding current_scope_quoted_at_def native_current_def by blast
  have frame: "current_frame_quoted_at C q F qu qr au ar N v root"
    using scope by (simp add: current_scope_quoted_at_def)
  have read: "publication_at N v root V" using publication by (simp add: publication_environment_closed_def)
  have formed: "snapshot_formed (publication_snapshot V)"
    using publication_at_formed[OF read] by (simp add: publication_formed_def)
  show ?thesis using frame publication formed selected unfolding current_snapshot_at_def by blast
qed

theorem current_entry_selected_snapshot:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and snapshot: "current_snapshot_at C q S"
  shows "snapshot_formed S \<and> snapshot_lookup S l=Some G"
proof -
  obtain T where actual: "current_snapshot_at C q T" "snapshot_formed T" "snapshot_lookup T l=Some G"
    using current_entry_snapshot_total[OF current] by blast
  have same: "S=T" by (rule current_snapshot_unique[OF snapshot actual(1)])
  show ?thesis using actual(2,3) same by simp
qed

section \<open>Companion purposes retain the same adoption policy and publication\<close>

definition current_companion ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_companion C q D r \<longleftrightarrow>
    (\<exists>E pu pr au ar F qu qr bu br A N v root l G p z.
      current_scope_quoted_at C q E pu pr au ar A N v root l G p \<and>
      current_scope_quoted_at D r F qu qr bu br A N v root l G z) \<and>
    (\<exists>E pu pr P d. current_frame_policy C q E pu pr P d \<and>
      current_frame_policy D r E pu pr P d)"

lemma current_companion_symmetric:
  "current_companion C q D r \<longleftrightarrow>current_companion D r C q"
  unfolding current_companion_def by blast

lemma current_companion_reflexive:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "current_companion C q C q"
proof -
  obtain F qu qr au ar N v root where scope:
    "current_scope_quoted_at C q F qu qr au ar A N v root l G p"
    using current_entry_scope_frame[OF current] by blast
  show ?thesis using scope current_scope_has_policy[OF scope] unfolding current_companion_def by blast
qed

theorem current_companion_policy:
  assumes companion: "current_companion C q D r"
    and policy: "current_frame_policy C q E pu pr P d"
  shows "current_frame_policy D r E pu pr P d"
proof -
  obtain F qu qr Q e where both: "current_frame_policy C q F qu qr Q e"
    "current_frame_policy D r F qu qr Q e"
    using companion unfolding current_companion_def by blast
  have same: "E=F \<and> pu=qu \<and> pr=qr \<and> P=Q \<and> d=e"
    by (rule current_frame_policy_unique[OF policy both(1)])
  show ?thesis using both(2) same by simp
qed

theorem current_companion_subject:
  assumes companion: "current_companion C q D r"
    and current: "current_scope_quoted_at C q E pu pr au ar A N v root l G p"
  shows "\<exists>F qu qr bu br z. current_scope_quoted_at D r F qu qr bu br A N v root l G z"
proof -
  obtain E' pu' pr' au' ar' F qu qr bu br A' N' v' root' l' G' p' z where both:
    "current_scope_quoted_at C q E' pu' pr' au' ar' A' N' v' root' l' G' p'"
    "current_scope_quoted_at D r F qu qr bu br A' N' v' root' l' G' z"
    using companion unfolding current_companion_def by blast
  have same: "A=A' \<and> N=N' \<and> v=v' \<and> root=root' \<and> l=l' \<and> G=G'"
    using current_scope_quoted_unique[OF current both(1)] by blast
  show ?thesis using both(2) same by blast
qed

theorem current_companion_program:
  assumes companion: "current_companion C q D r"
    and first: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and second: "current_entry_scope_quoted_at D r B m H z F qu qr Q e"
  shows "A=B \<and> l=m \<and> G=H \<and> E=F \<and> pu=qu \<and> pr=qr \<and> P=Q"
proof -
  obtain J xu xr au ar N v root where left:
    "current_scope_quoted_at C q J xu xr au ar A N v root l G p"
    using current_entry_scope_frame[OF first] by blast
  obtain K yu yr bu br w where right:
    "current_scope_quoted_at D r K yu yr bu br A N v root l G w"
    using current_companion_subject[OF companion left] by blast
  obtain L zu zr cu cr M a tail where actual:
    "current_scope_quoted_at D r L zu zr cu cr B M a tail m H z"
    using current_entry_scope_frame[OF second] by blast
  have subject: "A=B \<and> l=m \<and> G=H"
    using current_scope_quoted_unique[OF right actual] by blast
  have scopes: "generation_program_scope G E pu pr P" "generation_program_scope H F qu qr Q"
    using first second by (auto simp: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  have payload: "generation_payload G=generation_payload H" using subject by simp
  show ?thesis using subject generation_program_scope_unique[OF scopes payload] by blast
qed

theorem companion_requires_original_adoption:
  assumes companion: "current_companion C q D r"
    and policy: "current_frame_policy C q E pu pr P d"
    and selected: "current_scope_quoted_at D r F qu qr au ar A N v root l G p"
  shows "factor_adopts P d A G p"
  by (rule current_frame_policy_adoption[OF selected current_companion_policy[OF companion policy]])

section \<open>Every permitted companion purpose has an actual current frame\<close>

theorem current_companion_construction:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "current_scope_quoted_at C q F qu qr au ar A N v root l G p"
    and package: "native_package_at F qu qr Q"
    and app: "native_application_at F au ar h t I K"
    and entry: "purpose_entry z e" and member: "e\<in>system_definitions P"
    and allowed: "factor_adopts Q h A G z"
  shows "\<exists>D. current_entry_scope_quoted_at D [] A l G z E pu pr P e \<and>
    current_companion C q D []"
proof -
  obtain x where present: "adoption_value_presents A G z x" and truth: "(h,x)\<in>positive_meaning Q"
    using allowed unfolding factor_adopts_def by blast
  have invariant: "adoption_permission_invariant Q h" using allowed by (simp add: factor_adopts_def)
  have hm: "h\<in>system_definitions Q" using schema_call_formed_target[OF positive_meaning_formed[OF truth]] by blast
  obtain H bu J L where future: "native_package_at H qu qr Q" "native_application_at H bu [] h x J L"
    "native_package_environment H qu qr=native_package_environment F qu qr"
    "native_adoption_judgment_at H qu qr bu [] A G z"
    using native_adoption_application_total[OF package hm invariant present] allowed by blast
  have old: "native_current F qu qr au ar A N v root l G p"
    using scope by (simp add: current_scope_quoted_at_def)
  have adopted: "native_current H qu qr bu [] A N v root l G z"
    using old future(4) unfolding native_current_def by blast
  have program: "generation_program_scope G E pu pr P"
    using current by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  obtain D where new:
    "current_program_scope_quoted_at D [] A l G z E pu pr P"
    "current_scope_quoted_at D [] (native_judgment_environment H qu qr bu []) qu qr bu [] A N v root l G z"
    using current_program_scope_quoted_total[OF adopted program] by blast
  have selected: "current_entry_scope_quoted_at D [] A l G z E pu pr P e"
    using new(1) entry member by (simp add: current_entry_scope_quoted_at_def)
  have old_frame: "current_frame_quoted_at C q F qu qr au ar N v root"
    using scope by (simp add: current_scope_quoted_at_def)
  have old_policy: "current_frame_policy C q (native_package_environment F qu qr) qu qr Q h"
    by (simp only: current_frame_policy_with_reads[OF old_frame package app] simp_thms)
  have new_frame: "current_frame_quoted_at D [] (native_judgment_environment H qu qr bu []) qu qr bu [] N v root"
    using new(2) by (simp add: current_scope_quoted_at_def)
  have kept: "native_package_at (native_judgment_environment H qu qr bu []) qu qr Q"
    "native_application_at (native_judgment_environment H qu qr bu []) bu [] h x J L"
    using native_judgment_environment_recovers(1,2)[OF future(1,2)] by blast+
  have fixed: "native_package_environment (native_judgment_environment H qu qr bu []) qu qr=
      native_package_environment F qu qr"
    using native_judgment_program_environment[OF future(1,2)] future(3) by simp
  have new_policy: "current_frame_policy D [] (native_package_environment F qu qr) qu qr Q h"
    using current_frame_policy_with_reads[OF new_frame kept] fixed by simp
  have companion: "current_companion C q D []"
    using scope new(2) old_policy new_policy unfolding current_companion_def by blast
  show ?thesis using selected companion by blast
qed

text \<open>
  A companion selection uses the same authority, generation, and exact closed
  publication, with a possibly different purpose. Its adoption is judged at
  the same entry of the same complete adoption-program scope. Equality of
  root artifacts or of program values alone is insufficient. The policy and
  selected program are derived from the existing frames; no extra subject
  fields are stored.

  Every companion purpose permitted by that actual adoption policy has a
  current frame retaining the original selected program. The two selected
  entries may differ. The relation gives no new amendment permission and does
  not allow the companion to replace the original acceptance entry.
\<close>

end
