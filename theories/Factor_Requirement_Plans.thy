theory Factor_Requirement_Plans
  imports Factor_Admission_Sequences Factor_Requirement_Installation
begin

section \<open>The generated entry requires every original goal on the same subject\<close>

definition requirement_sockets :: "nat list \<Rightarrow> (nat\<times>nat) set" where
  "requirement_sockets ds=set (zip [0..<length ds] ds)"

lemma requirement_sockets_finite [simp]: "finite (requirement_sockets ds)"
  by (simp add: requirement_sockets_def)

lemma requirement_sockets_functional [simp]: "single_valued (requirement_sockets ds)"
  unfolding requirement_sockets_def by (rule single_valued_zip) simp

lemma requirement_sockets_range [simp]: "rel_ran (requirement_sockets ds)=set ds"
  unfolding requirement_sockets_def by (rule zip_range) simp

lemma requirement_sockets_all:
  "(\<forall>(s,d)\<in>requirement_sockets ds. F d) \<longleftrightarrow> (\<forall>d\<in>set ds. F d)"
  using requirement_sockets_range[of ds] by (auto simp: rel_ran_def; force)

definition required_admission_system where
  "required_admission_system P ds k cs=
    install_requirement_guard (install_admission_plan P cs) k (requirement_sockets ds)"

lemma required_admission_entry [simp]:
  "k\<in>system_definitions (required_admission_system P ds k cs)"
  by (simp add: required_admission_system_def install_requirement_guard_def)

theorem required_admission_installed:
  assumes source: "admission_source P n"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
    and sequence: "admission_sequence gs n=(ds,k,cs)"
  shows "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    "k\<notin>system_definitions P"
proof -
  let ?Q="install_admission_plan P cs"
  have built: "admission_source ?Q k \<and> admission_extension P ?Q \<and>
    list_all2 (\<lambda>g d. d\<in>system_definitions ?Q \<and>
      (\<forall>t. (d,t)\<in>positive_meaning ?Q \<longleftrightarrow>
        admission_goal_holds (positive_meaning P) g t)) gs ds"
    by (rule admission_sequence_installed[OF source supported sequence])
  have current: "admission_source ?Q k" and extension: "admission_extension P ?Q"
    and correspondence: "list_all2 (\<lambda>g d. d\<in>system_definitions ?Q \<and>
      (\<forall>t. (d,t)\<in>positive_meaning ?Q \<longleftrightarrow>
        admission_goal_holds (positive_meaning P) g t)) gs ds"
    using built by blast+
  have members: "set ds\<subseteq>system_definitions ?Q"
    using correspondence by (induction rule: list_all2_induct) auto
  have exact: "(\<forall>d\<in>set ds. (d,t)\<in>positive_meaning ?Q) \<longleftrightarrow>
      (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)" for t
    using correspondence by (induction rule: list_all2_induct) auto
  interpret guard: requirement_guard_extension ?Q k "requirement_sockets ds"
    by (rule requirement_guard_extension.intro)
      (use current members in \<open>auto simp: admission_source_def\<close>)
  have advanced: "admission_source (required_admission_system P ds k cs) (Suc k)"
    and last: "admission_extension ?Q (required_admission_system P ds k cs)"
    using admission_fresh_extension[OF current guard.guarded_formed
      [unfolded install_requirement_guard_def]]
    by (simp_all only: required_admission_system_def install_requirement_guard_def)
  show "admission_source (required_admission_system P ds k cs) (Suc k)" by (rule advanced)
  show "admission_extension P (required_admission_system P ds k cs)"
    by (rule admission_extension_trans[OF extension last])
  show "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    by (simp only: required_admission_system_def guard.guarded_meaning requirement_sockets_all exact)
  show "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    by (simp only: required_admission_system_def guard.guarded_call)
  show "k\<notin>system_definitions P"
    using current admission_extension_definitions[OF extension] by (auto simp: admission_source_def)
qed

corollary required_admission_failed_goal:
  assumes "admission_source P n"
    "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
    "admission_sequence gs n=(ds,k,cs)" "g\<in>set gs"
    "\<not>admission_goal_holds (positive_meaning P) g t"
  shows "(k,t)\<notin>positive_meaning (required_admission_system P ds k cs)"
  using required_admission_installed(3)[OF assms(1-3)] assms(4,5) by blast

text \<open>
  The independently supplied goals determine all installed component entries
  and every requirement socket. An empty goal family still requires a formed
  subject. A missing component, an invalid allocation boundary, or a false
  requirement cannot be discharged by the resulting guard itself.

  This theorem establishes the installation contract during bootstrap. Native
  planning must compute the sequence under its separate all-input contract;
  the goal-to-subject meaning and the problem's complete requirement boundary
  remain the client's obligations.
\<close>

end
