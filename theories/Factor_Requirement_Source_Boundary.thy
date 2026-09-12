theory Factor_Requirement_Source_Boundary
  imports Finite_Requirement_Artifact_Admission
begin

section \<open>A source-domain check does not identify the source's meaning\<close>

lemma equal_source_domains_same_plan_admission:
  assumes "system_definitions P=system_definitions Q"
  shows "requirement_artifact_system (system_definitions P) gs n=
    requirement_artifact_system (system_definitions Q) gs n"
  using assms by simp

definition requirement_source_example :: "bool \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "requirement_source_example b=\<lparr>system_interfaces={(0,data_x)},
    system_clauses=(if b then {((0,0),requirement_guard_schema {})} else {})\<rparr>"

lemma requirement_source_example_formed [simp]: "schema_system_formed (requirement_source_example b)"
  by (auto simp: requirement_source_example_def schema_system_formed_def
    requirement_guard_formed single_valued_def system_definitions_def rel_dom_def)

lemma requirement_source_example_domain [simp]:
  "system_definitions (requirement_source_example b)={0}"
  by (auto simp: requirement_source_example_def system_definitions_def rel_dom_def)

lemma requirement_source_example_call:
  "schema_call_formed (requirement_source_example b) 0 t \<longleftrightarrow> term_formed t"
  by (simp only: schema_call_formed_def requirement_source_example_formed)
    (simp add: requirement_source_example_def)

theorem requirement_source_example_meaning:
  "(0,t)\<in>positive_meaning (requirement_source_example b) \<longleftrightarrow> b \<and> term_formed t"
proof (cases b)
  case False
  have empty: "positive_meaning (requirement_source_example False)={}"
    by (subst positive_meaning_unfold)
      (auto simp: schema_consequences_def admitted_schema_instance_def requirement_source_example_def)
  show ?thesis by (simp only: False empty; simp)
next
  case True
  interpret guard: requirement_guard_profile "requirement_source_example True" 0 "{}"
  proof (rule requirement_guard_profile.intro[OF requirement_source_example_formed])
    show "((0,c),S)\<in>system_clauses (requirement_source_example True) \<longleftrightarrow>
      c=0 \<and> S=requirement_guard_schema {}" for c S
      by (simp add: requirement_source_example_def)
    show "schema_call_formed (requirement_source_example True) 0 t \<longleftrightarrow> term_formed t" for t
      by (rule requirement_source_example_call)
  qed
  show ?thesis by (simp only: True guard.exact; simp)
qed

lemma requirement_source_example_plan:
  "checked_admission_sequence (system_definitions (requirement_source_example b)) [Existing_Admission 0] 1
    =Some ([0],1,[])"
  by (simp add: checked_admission_sequence_def admission_request_supported_def admission_source_floor_def)

theorem requirement_source_example_installed:
  "(1,t)\<in>positive_meaning (required_admission_system (requirement_source_example b) [0] 1 [])
    \<longleftrightarrow> b \<and> term_formed t"
  using checked_admission_sequence_installed(3)[OF requirement_source_example_formed[where b=b]
    requirement_source_example_plan[where b=b], where t=t]
  by (auto simp: requirement_source_example_meaning)

theorem equal_source_domains_different_installed_meanings:
  "system_definitions (requirement_source_example True)=system_definitions (requirement_source_example False)"
  "requirement_artifact_system (system_definitions (requirement_source_example True)) [Existing_Admission 0] 1=
    requirement_artifact_system (system_definitions (requirement_source_example False)) [Existing_Admission 0] 1"
  "(1,Payload_Term [])\<in>positive_meaning (required_admission_system (requirement_source_example True) [0] 1 [])"
  "(1,Payload_Term [])\<notin>positive_meaning (required_admission_system (requirement_source_example False) [0] 1 [])"
proof -
  show "system_definitions (requirement_source_example True)=system_definitions (requirement_source_example False)"
    by simp
  show "requirement_artifact_system (system_definitions (requirement_source_example True)) [Existing_Admission 0] 1=
    requirement_artifact_system (system_definitions (requirement_source_example False)) [Existing_Admission 0] 1"
    by simp
  show "(1,Payload_Term [])\<in>positive_meaning (required_admission_system (requirement_source_example True) [0] 1 [])"
    using requirement_source_example_installed[where b=True and t="Payload_Term []"]
    by (simp add: octets_formed_def)
  show "(1,Payload_Term [])\<notin>positive_meaning (required_admission_system (requirement_source_example False) [0] 1 [])"
    using requirement_source_example_installed[where b=False and t="Payload_Term []"] by simp
qed

definition requirement_source_boundary_report where
  "requirement_source_boundary_report b=(
    sorted_list_of_set (system_definitions (requirement_source_example b)),
    checked_admission_sequence (system_definitions (requirement_source_example b)) [Existing_Admission 0] 1,
    finite_requirement_artifact_admitted (system_definitions (requirement_source_example b)) [Existing_Admission 0] 1
      (finite_requirement_candidate [Existing_Admission 0] 1 ([0],1,[])),
    (1,Payload_Term [])\<in>positive_meaning (required_admission_system (requirement_source_example b) [0] 1 []))"

lemma requirement_source_boundary_report_code [code]:
  "requirement_source_boundary_report b=([0],Some ([0],1,[]),True,b)"
proof -
  have finite: "finite (system_definitions (requirement_source_example b))" by simp
  have candidate: "finite_requirement_artifact_admitted (system_definitions (requirement_source_example b))
      [Existing_Admission 0] 1 (finite_requirement_candidate [Existing_Admission 0] 1 ([0],1,[]))"
    by (simp only: finite_requirement_candidate_exact[OF finite] requirement_source_example_plan; simp)
  show ?thesis by (simp only: requirement_source_boundary_report_def candidate requirement_source_example_plan
    requirement_source_example_installed; simp add: octets_formed_def)
qed

export_code requirement_source_boundary_report integer_of_nat
  in SML module_name Requirement_Source_Boundary file_prefix requirement_source_boundary

text \<open>
  The two complete ordinary programs have the same source domain and admit
  the same construction blueprint, yet their installed guards have different
  meanings on the same actual subject. This is consistent with the local
  blueprint contract, which is relative to the separately supplied source.

  A complete development account must therefore retain the actual source
  program and its resulting installation in addition to the source domain.
  The present blueprint generation does not yet provide that complete join.
\<close>

end
