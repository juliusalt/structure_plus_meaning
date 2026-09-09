theory Factor_Permission_Families
  imports Factor_Permission_Invariance Factor_Permission_Presentations
    Factor_Construction_Invariance Factor_Authority Factor_Continuation Factor_Amendment Factor_Site_Permission
begin

section \<open>All five original permission conditions instantiate the same contract\<close>

theorem construction_invariant_as_presented:
  "construction_permission_invariant P d \<longleftrightarrow>
    presented_program_invariant construction_account_presents P d"
  by (simp only: construction_permission_observations presented_program_observations)

theorem adoption_invariant_as_presented:
  "adoption_permission_invariant P d \<longleftrightarrow>
    presented_program_invariant adoption_context_presents P d"
  by (simp only: adoption_permission_invariant_def presented_program_invariant_iff
    split_paired_All adoption_context_fields)

theorem continuation_invariant_as_presented:
  "continuation_permission_invariant P d \<longleftrightarrow>
    presented_program_invariant continuation_context_presents P d"
  by (simp only: continuation_permission_invariant_def presented_program_invariant_iff
    split_paired_All continuation_context_fields)

theorem amendment_invariant_as_presented:
  "amendment_permission_invariant P d \<longleftrightarrow>
    presented_program_invariant amendment_context_presents P d"
  by (simp only: amendment_permission_invariant_def presented_program_invariant_iff
    split_paired_All amendment_context_fields)

theorem site_invariant_as_presented:
  "site_permission_invariant P d \<longleftrightarrow>
    presented_program_invariant site_context_presents P d"
  by (simp only: site_permission_invariant_def presented_program_invariant_iff
    split_paired_All fst_conv snd_conv)

section \<open>Unsettled conditions remain attached to the original code and complete subject\<close>

theorem adoption_permission_residual_exact:
  assumes known: "K\<subseteq>{c. observation_condition c}"
  shows "adoption_permission_invariant P d \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (program_invariance_obligations (presentation_transport adoption_context_presents adoption_context_presents) P d))
      \<subseteq>{c. observation_condition c}"
  by (simp only: adoption_invariant_as_presented presented_program_invariance_residual[OF known])

theorem continuation_permission_residual_exact:
  assumes known: "K\<subseteq>{c. observation_condition c}"
  shows "continuation_permission_invariant P d \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (program_invariance_obligations (presentation_transport continuation_context_presents continuation_context_presents) P d))
      \<subseteq>{c. observation_condition c}"
  by (simp only: continuation_invariant_as_presented presented_program_invariance_residual[OF known])

theorem amendment_permission_residual_exact:
  assumes known: "K\<subseteq>{c. observation_condition c}"
  shows "amendment_permission_invariant P d \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (program_invariance_obligations (presentation_transport amendment_context_presents amendment_context_presents) P d))
      \<subseteq>{c. observation_condition c}"
  by (simp only: amendment_invariant_as_presented presented_program_invariance_residual[OF known])

theorem site_permission_residual_exact:
  assumes known: "K\<subseteq>{c. observation_condition c}"
  shows "site_permission_invariant P d \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (program_invariance_obligations (presentation_transport site_context_presents site_context_presents) P d))
      \<subseteq>{c. observation_condition c}"
  by (simp only: site_invariant_as_presented presented_program_invariance_residual[OF known])

text \<open>
  The equations preserve all five original definitions, including construction's
  valid assembly and coordinate boundary. The shared contract changes no
  permission, program, subject, or presentation class. Its general factorization,
  program transport, saturation, and exact residual laws now apply to each case.

  Each family retains its own complete subject. The common condition does not
  identify construction inputs with predecessors or semantic dependencies,
  adoption with publication, a submitted certificate with its validity, or a
  claimed after snapshot with a successful transaction.
\<close>

end
