theory Factor_Current_Scopes
  imports Factor_Current_Values Factor_Authority_Scopes Factor_Publication_Scopes
begin

section \<open>Currentness records two complete scopes and derives its subject\<close>

definition current_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "current_scope_quoted_at C q E pu pr au ar A F v root l G p \<longleftrightarrow>
    current_frame_quoted_at C q E pu pr au ar F v root \<and>
    E=native_judgment_environment E pu pr au ar \<and> native_current E pu pr au ar A F v root l G p"

theorem current_scope_quoted_unique:
  assumes first: "current_scope_quoted_at C q E pu pr au ar A F v root l G p"
    and second: "current_scope_quoted_at C q D qu qr bu br B N w s m H z"
  shows "E=D \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> A=B \<and>
    F=N \<and> v=w \<and> root=s \<and> l=m \<and> G=H \<and> p=z"
proof -
  have left: "current_frame_quoted_at C q E pu pr au ar F v root" "native_current E pu pr au ar A F v root l G p"
    using first by (auto simp: current_scope_quoted_at_def)
  have right: "current_frame_quoted_at C q D qu qr bu br N w s" "native_current D qu qr bu br B N w s m H z"
    using second by (auto simp: current_scope_quoted_at_def)
  have scope: "E=D \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> F=N \<and> v=w \<and> root=s"
    by (rule current_frame_quoted_unique[OF left(1) right(1)])
  have other: "native_current E pu pr au ar B F v root m H z" using right(2) scope by simp
  have adopted: "native_adoption_judgment_at E pu pr au ar A G p" "native_adoption_judgment_at E pu pr au ar B H z"
    using left(2) other by (auto simp: native_current_def)
  have subject: "A=B \<and> G=H \<and> p=z" by (rule native_adoption_subject_unique[OF adopted])
  have loci: "l=m" using native_current_locus[OF left(2)] native_current_locus[OF other] subject by simp
  show ?thesis using scope subject loci by blast
qed

lemma current_scope_boundaries:
  assumes quote: "current_scope_quoted_at C q E pu pr au ar A F v root l G p"
  shows "native_judgment_environment E pu pr au ar=E" and "publication_environment F v root=F"
proof -
  show "native_judgment_environment E pu pr au ar=E" using quote by (simp add: current_scope_quoted_at_def)
  obtain P where pub: "publication_environment_closed F v root P"
    using quote unfolding current_scope_quoted_at_def native_current_def by blast
  show "publication_environment F v root=F" by (rule publication_closed_environment_fixed[OF pub])
qed

lemma current_scope_quoted_formed:
  assumes quote: "current_scope_quoted_at C q E pu pr au ar A F v root l G p"
  shows "exact_formed C \<and> environment_formed E \<and> environment_formed F \<and>
    target_formed A \<and> generation_formed G \<and> target_formed p \<and> generation_locus G=l"
proof -
  have frame: "current_frame_quoted_at C q E pu pr au ar F v root"
    and current: "native_current E pu pr au ar A F v root l G p"
    using quote by (auto simp: current_scope_quoted_at_def)
  have adopted: "native_adoption_judgment_at E pu pr au ar A G p" using current by (simp add: native_current_def)
  show ?thesis using current_frame_quoted_formed[OF frame] native_adoption_formed[OF adopted]
    native_current_locus[OF current] by blast
qed

theorem current_scope_quoted_total:
  fixes E F :: "local_address option artifact_environment"
  assumes current: "native_current E pu pr au ar A F v root l G p"
  shows "\<exists>C. current_scope_quoted_at C [] (native_judgment_environment E pu pr au ar) pu pr au ar A F v root l G p"
proof -
  have adopted: "native_adoption_judgment_at E pu pr au ar A G p" using current by (simp add: native_current_def)
  obtain P d t I K where read: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using adopted unfolding native_adoption_judgment_at_def by blast
  let ?H="native_judgment_environment E pu pr au ar"
  have kept: "native_package_at ?H pu pr P" "native_application_at ?H au ar d t I K" "environment_formed ?H"
    using native_judgment_environment_recovers[OF read] by blast+
  have sites: "(pu,pr)\<in>environment_positions ?H" "(au,ar)\<in>environment_positions ?H"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain Q where closed_pub: "publication_environment_closed F v root Q" using current unfolding native_current_def by blast
  have pub: "publication_at F v root Q" using closed_pub by (simp add: publication_environment_closed_def)
  have ff: "environment_formed F"
    using closed_pub by (simp add: publication_environment_closed_def environment_closed_def)
  obtain R where anchor: "artifact_at F v R" "anchor_formed (R,root)" using publication_at_has_anchor[OF pub] by blast
  have pub_site: "(v,root)\<in>environment_positions F" using anchor by (auto simp: anchor_formed_def)
  obtain C where frame: "current_frame_quoted_at C [] ?H pu pr au ar F v root"
    using current_frame_quoted_total[OF kept(3) sites ff pub_site] by blast
  have fixed: "?H=native_judgment_environment ?H pu pr au ar"
    using native_judgment_environment_idempotent[OF read] by simp
  have retained: "native_current ?H pu pr au ar A F v root l G p"
    using current by (simp only: native_current_def native_adoption_judgment_restriction[OF read])
  show ?thesis using frame fixed retained unfolding current_scope_quoted_at_def by blast
qed

theorem current_scope_quoted_in_environment:
  assumes quote: "current_scope_quoted_at C q E pu pr au ar A F v root l G p"
    and formed: "environment_formed H" and source: "artifact_at H u C"
  shows "\<exists>t. current_frame_value_presents E pu pr au ar F v root t \<and>
    term_quoted_at H u q t (rra_carrier (object_structure C)) {}"
  using quote unfolding current_scope_quoted_at_def
  by (meson current_frame_quoted_in_environment[OF _ formed source])

text \<open>
  A currentness record stores the complete minimal adoption judgment scope and
  the exact closed publication scope. The actual call determines authority,
  generation, and purpose; the selected generation determines the locus.
  These derived fields are not stored again. Equal exact quotation targets fix
  both scopes, every selected site, and the entire currentness subject.

  Every native currentness judgment has such a finite record, retaining its
  original publication scope and the complete minimal program-and-call scope.
  The quotation is readable in any formed enclosing environment without an
  external slot. The ordinary program still supplies adoption. This record is
  inspectable material for higher policies, not an amendment authorization.
\<close>

end
