theory Factor_Replay_Scopes
  imports Factor_Replay_Values Factor_Replay
begin

section \<open>A replay record retains exactly the scope checked by replay\<close>

definition replay_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site \<Rightarrow>
    (local_address option definition_site \<times> (local_address option definition_site \<times> factor_term)) set \<Rightarrow> bool" where
  "replay_scope_quoted_at C q E pu pr au ar root H \<longleftrightarrow>
    replay_value_quoted_at C q E pu pr au ar root \<and> native_replay_at E pu pr au ar root H"

theorem replay_scope_whole_unique:
  assumes first: "replay_scope_quoted_at C q E pu pr au ar root H"
    and second: "replay_scope_quoted_at C r F qu qr bu br other J"
  shows "q=r \<and> E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> root=other \<and> H=J"
proof -
  have left: "replay_value_quoted_at C q E pu pr au ar root" "native_replay_at E pu pr au ar root H"
    using first by (auto simp: replay_scope_quoted_at_def)
  have right: "replay_value_quoted_at C r F qu qr bu br other" "native_replay_at F qu qr bu br other J"
    using second by (auto simp: replay_scope_quoted_at_def)
  have same: "q=r \<and> E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> root=other"
    by (rule replay_value_whole_unique[OF left(1) right(1)])
  have other: "native_replay_at E pu pr au ar root J" using right(2) same by simp
  show ?thesis using same native_replay_assumptions_unique[OF left(2) other] by blast
qed

lemma native_replay_sites:
  assumes replay: "native_replay_at E pu pr au ar root H"
  shows "environment_formed E" "(pu,pr)\<in>environment_positions E"
    "(au,ar)\<in>environment_positions E" "root\<in>environment_positions E"
proof -
  obtain P d t I K G where read: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "native_schema_graph_at E root G"
    using replay unfolding native_replay_at_def by blast
  show "environment_formed E" by (rule native_schema_graph_environment[OF read(3)])
  show "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    by (rule native_judgment_positions[OF read(1,2)])+
  have root: "root\<in>schema_graph_nodes G"
    using read(3) by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  show "root\<in>environment_positions E"
    by (rule subsetD[OF native_schema_graph_positions[OF read(3)] root])
qed

theorem replay_scope_quoted_total:
  fixes E :: "local_address option artifact_environment"
  assumes replay: "native_replay_at E pu pr au ar root H"
  shows "\<exists>C. replay_scope_quoted_at C [] E pu pr au ar root H"
  using replay_value_quoted_total[OF native_replay_sites[OF replay]] replay
  unfolding replay_scope_quoted_at_def by blast

lemma replay_scope_closed_sound:
  assumes scope: "replay_scope_quoted_at C q E pu pr au ar root {}"
  shows "native_positive_holds E pu pr au ar"
proof -
  have replay: "native_replay_at E pu pr au ar root {}"
    using scope by (simp add: replay_scope_quoted_at_def)
  show ?thesis by (rule native_replay_closed_sound[OF replay])
qed

lemma replay_scope_formed:
  assumes scope: "replay_scope_quoted_at C q E pu pr au ar root H"
  shows "exact_formed C \<and> environment_formed E"
proof -
  have data: "replay_value_quoted_at C q E pu pr au ar root"
    using scope by (simp add: replay_scope_quoted_at_def)
  show ?thesis using replay_value_quoted_formed[OF data] by blast
qed

theorem replay_scope_quoted_in_environment:
  assumes quote: "replay_scope_quoted_at C q E pu pr au ar root H"
    and formed: "environment_formed F" and source: "artifact_at F u C"
  shows "\<exists>t. replay_value_presents E pu pr au ar root t \<and>
    term_quoted_at F u q t (rra_carrier (object_structure C)) {}"
  using quote unfolding replay_scope_quoted_at_def
  by (meson replay_value_quoted_in_environment[OF _ formed source])

theorem positive_judgment_has_recorded_replay:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and truth: "native_positive_holds E pu pr au ar"
  shows "\<exists>C F root. replay_scope_quoted_at C [] F pu pr au ar root {} \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment F pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  obtain F root where kept: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and replay: "native_replay_at F pu pr au ar root {}"
    and exact: "native_package_environment F pu pr=native_package_environment E pu pr"
      "native_judgment_environment F pu pr au ar=native_judgment_environment E pu pr au ar"
    using native_replay_exact_call_adequate[OF package app] truth by blast
  obtain C where recorded: "replay_scope_quoted_at C [] F pu pr au ar root {}"
    using replay_scope_quoted_total[OF replay] by blast
  show ?thesis using kept recorded exact by blast
qed

text \<open>
  The record retains the original closed replay environment, including every
  demanded program, call, and proof binding. A whole-artifact quotation fixes
  that scope, all three sites, and the exact identified assumption boundary.
  It is readable in a formed enclosing environment without external slots.

  Every native replay has such a finite record. Every positive call has one
  with its original program and complete minimal judgment scope preserved.
  Retention and quotation cannot change derivation validity, discharge an
  assumption, select an authority, or supply amendment permission.
\<close>

end
