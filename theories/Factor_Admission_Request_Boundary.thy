theory Factor_Admission_Request_Boundary
  imports Factor_Requirement_Plan_Realization
begin

section \<open>The actual source determines support and the allocation boundary\<close>

definition admission_source_floor :: "nat set \<Rightarrow> nat" where
  "admission_source_floor D=(if D={} then 0 else Suc (Max D))"

lemma admission_source_floor_exact:
  assumes finite: "finite D"
  shows "admission_source_floor D\<le>n \<longleftrightarrow> (\<forall>d\<in>D. d<n)"
proof (cases "D={}")
  case True
  then show ?thesis by (simp add: admission_source_floor_def)
next
  case False
  show ?thesis using Max_less_iff[OF finite False, of n]
    by (simp add: admission_source_floor_def False Suc_le_eq)
qed

lemma admission_source_at_floor:
  assumes formed: "schema_system_formed P"
  shows "admission_source P n \<longleftrightarrow> admission_source_floor (system_definitions P)\<le>n"
  using admission_source_floor_exact[OF system_definitions_finite[OF formed], of n]
  by (simp only: admission_source_def formed; blast)

definition admission_request_supported where
  "admission_request_supported D gs n \<longleftrightarrow>
    admission_source_floor D\<le>n \<and> (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>D)"

definition checked_admission_sequence where
  "checked_admission_sequence D gs n=
    (if admission_request_supported D gs n then Some (admission_sequence gs n) else None)"

theorem checked_admission_sequence_installed:
  assumes formed: "schema_system_formed P"
    and checked: "checked_admission_sequence (system_definitions P) gs n=Some (ds,k,cs)"
  shows "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    "k\<notin>system_definitions P"
proof -
  have source: "admission_source P n"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
    and sequence: "admission_sequence gs n=(ds,k,cs)"
    using checked by (auto simp: checked_admission_sequence_def admission_request_supported_def
      admission_source_at_floor[OF formed] split: if_splits)
  show "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    "k\<notin>system_definitions P"
    by (rule required_admission_installed[OF source supported sequence])+
qed

text \<open>
  The source boundary is the complete definition domain of the actual formed
  program. It is fixed before the request. Neither successful planning nor
  the newly generated guard can excuse an unsupported leaf or a colliding
  allocation counter. The empty source has floor zero, and an empty request
  still retains the source's allocation condition.

  Native request admission must implement this same relation with the actual
  source domain. Supplying an unrelated allowed-site list or a host predicate
  would not instantiate the contract above.
\<close>

end
