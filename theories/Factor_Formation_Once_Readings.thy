theory Factor_Formation_Once_Readings
  imports Factor_Executable_Packages
    Factor_Executable_Quotation
    Factor_Executable_Patterns
    Factor_Finite_Prepared_Data_Readings
    Established_Premises
begin

section \<open>Formation premises are established once for a traversal\<close>

text \<open>
  The establishing facts of the first notion of DECISIONS.md, "The in-place refinements apply two
  notions": a formed environment has formed artifacts, read from its component statement
  (@{thm [source] finite_environment_formed_components}), and a formed artifact is a formed object. They
  stand here, beside their uses, until a landing changes @{text RRA_Finite_Environments}, where they
  would be stated with the environment's formation.
\<close>

lemma formed_environment_artifact:
  assumes formed: "finite_environment_formed E" and member: "C |\<in>| finite_artifacts_at E u"
  shows "finite_exact_formed C"
proof -
  obtain v where row: "(v,C) |\<in>| finite_environment_artifacts E"
    using member by (auto simp: finite_artifacts_at_def)
  have artifacts: "\<forall>v R. (v,R) |\<in>| finite_environment_artifacts E \<longrightarrow> finite_exact_formed R"
    using formed by (simp add: finite_environment_formed_components)
  show ?thesis by (rule artifacts[rule_format, OF row])
qed

lemma exact_formed_object: "finite_exact_formed C \<Longrightarrow> finite_object_formed C"
  by (simp add: finite_exact_formed_def)

definition finite_citation_candidates_formed where
  "finite_citation_candidates_formed C r=(if r |\<in>| finite_carrier (finite_structure C) \<and> finite_data_empty_on C {|r|}
    then ffilter (\<lambda>(c,I). finite_raw_citation_at C r c I) (finite_citation_choices C r) else {||})"

lemma finite_citation_candidates_formed_exact:
  "finite_exact_formed C \<Longrightarrow> finite_citation_candidates C r=finite_citation_candidates_formed C r"
  by (auto simp: finite_citation_candidates_def finite_citation_candidates_formed_def finite_citation_at_def fset_eq_iff)

declare finite_citation_candidates_def[code del]

lemma finite_citation_candidates_checked_premise:
  "checked_premise finite_citation_candidates finite_exact_formed finite_citation_candidates_formed (\<lambda>C r. {||})"
proof (unfold_locales, goal_cases)
  case (1 C)
  show ?case by (rule ext) (rule finite_citation_candidates_formed_exact[OF 1])
next
  case (2 C)
  show ?case
    using 2 by (intro ext) (auto simp: finite_citation_candidates_def finite_citation_at_def fset_eq_iff)
qed

lemma finite_citation_candidates_formed_once_code [code]:
  "finite_citation_candidates C r=(if finite_exact_formed C then finite_citation_candidates_formed C r else {||})"
  by (rule checked_premise.checked_through[OF finite_citation_candidates_checked_premise, where t="\<lambda>f. f r"])

definition finite_two_field_record_formed where
  "finite_two_field_record_formed C r F=ffUnion (fimage (\<lambda>(ps,xs).
    case xs of [l,q] \<Rightarrow> F ps l q | _ \<Rightarrow> {||}) (finite_record_body_candidates C r 2))"

lemma finite_two_field_record_formed_exact:
  "finite_object_formed C \<Longrightarrow> finite_two_field_record C r F=finite_two_field_record_formed C r F"
  by (simp only: finite_two_field_record_def finite_two_field_record_formed_def finite_record_body_candidates_exact)

definition finite_record_readings_formed where
  "finite_record_readings_formed C r f V reads=finite_two_field_record_formed C r
    (\<lambda>ps l q. finite_join_readings f V r ps (reads l) (reads q))"

lemma finite_record_readings_formed_exact:
  "finite_object_formed C \<Longrightarrow> finite_record_readings C r f V reads=finite_record_readings_formed C r f V reads"
  by (simp only: finite_record_readings_def finite_record_readings_formed_def finite_two_field_record_formed_exact)

definition finite_target_readings_formed where
  "finite_target_readings_formed E u C r=ffUnion (fimage (\<lambda>(c,I).
    if finite_citation_slots c={||} then {||}
    else fimage (\<lambda>T. (Finite_Target T,I,finite_citation_slots c)) (finite_citation_targets E u c))
      (finite_citation_candidates_formed C r))"

lemma finite_target_readings_formed_exact:
  "finite_exact_formed C \<Longrightarrow> finite_target_readings E u C r=finite_target_readings_formed E u C r"
  by (simp only: finite_target_readings_def finite_target_readings_formed_def finite_citation_candidates_formed_exact)

definition finite_variable_readings_formed where
  "finite_variable_readings_formed C V r=ffUnion (fimage (finite_variable_leaf V) (finite_citation_candidates_formed C r))"

lemma finite_variable_readings_formed_exact:
  "finite_exact_formed C \<Longrightarrow> finite_variable_readings C V r=finite_variable_readings_formed C V r"
  by (simp only: finite_variable_readings_def finite_variable_readings_formed_def finite_citation_candidates_formed_exact)


fun finite_term_readings_formed ::
  "nat \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    finite_factor_term finite_syntax_reading fset" where
  "finite_term_readings_formed 0 E u r={||}"
| "finite_term_readings_formed (Suc n) E u r=ffUnion (fimage (\<lambda>C.
      finite_target_readings_formed E u C r |\<union>| finite_payload_body_readings C r |\<union>|
      finite_record_readings_formed C r Finite_Pair {||} (finite_term_readings_formed n E u))
        (finite_artifacts_at E u))"

lemma finite_term_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_term_readings_bounded n E u=finite_term_readings_formed n E u"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  show ?case
  proof (rule ext)
    fix r
    have each: "finite_target_readings E u C r |\<union>| finite_payload_readings C r |\<union>|
        finite_record_readings C r Finite_Pair {||} (finite_term_readings_bounded n E u)=
      finite_target_readings_formed E u C r |\<union>| finite_payload_body_readings C r |\<union>|
        finite_record_readings_formed C r Finite_Pair {||} (finite_term_readings_formed n E u)"
      if "C |\<in>| finite_artifacts_at E u" for C
    proof -
      have exact: "finite_exact_formed C" by (rule formed_environment_artifact[OF formed that])
      show ?thesis
        by (simp only: Suc.IH finite_target_readings_formed_exact[OF exact]
          finite_payload_body_readings_exact[OF exact_formed_object[OF exact]]
          finite_record_readings_formed_exact[OF exact_formed_object[OF exact]])
    qed
    show "finite_term_readings_bounded (Suc n) E u r=finite_term_readings_formed (Suc n) E u r"
      by (simp only: finite_term_readings_bounded.simps finite_term_readings_formed.simps formed if_True)
        (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl], rule each)
  qed
qed

declare finite_term_readings_bounded.simps[code del]

text \<open>
  The premise is on the second argument, so the instance is stated for the constant applied to the
  bound, and its code equation at the environment's arity.
\<close>

lemma finite_term_readings_bounded_checked_premise:
  "checked_premise (finite_term_readings_bounded n) finite_environment_formed (finite_term_readings_formed n)
    (\<lambda>E u r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (rule ext) (rule finite_term_readings_formed_exact[OF 1])
next
  case (2 E)
  show ?case by (intro ext) (cases n; simp add: 2)
qed

lemma finite_term_readings_bounded_formed_once_code [code]:
  "finite_term_readings_bounded n E u r=(if finite_environment_formed E
    then finite_term_readings_formed n E u r else {||})"
  by (rule checked_premise.checked_through[OF finite_term_readings_bounded_checked_premise, where t="\<lambda>f. f u r"])

definition finite_pattern_constants_formed where
  "finite_pattern_constants_formed E u V r=ffUnion (fimage (finite_pattern_leaf V) (finite_term_readings_formed 1 E u r))"

lemma finite_pattern_constants_formed_exact:
  "finite_environment_formed E \<Longrightarrow> finite_pattern_constants E u V r=finite_pattern_constants_formed E u V r"
  by (simp only: finite_pattern_constants_def finite_pattern_constants_formed_def finite_term_readings_formed_exact)

fun finite_pattern_readings_formed ::
  "nat \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address finite_term_pattern finite_syntax_reading fset" where
  "finite_pattern_readings_formed 0 E u V r={||}"
| "finite_pattern_readings_formed (Suc n) E u V r=finite_pattern_constants_formed E u V r |\<union>|
      ffUnion (fimage (\<lambda>C. finite_variable_readings_formed C V r |\<union>|
        finite_record_readings_formed C r Finite_Pattern_Pair V (finite_pattern_readings_formed n E u V))
          (finite_artifacts_at E u))"

lemma finite_pattern_readings_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_pattern_readings_bounded n E u V=finite_pattern_readings_formed n E u V"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  show ?case
  proof (rule ext)
    fix r
    have each: "finite_variable_readings C V r |\<union>|
        finite_record_readings C r Finite_Pattern_Pair V (finite_pattern_readings_bounded n E u V)=
      finite_variable_readings_formed C V r |\<union>|
        finite_record_readings_formed C r Finite_Pattern_Pair V (finite_pattern_readings_formed n E u V)"
      if "C |\<in>| finite_artifacts_at E u" for C
    proof -
      have exact: "finite_exact_formed C" by (rule formed_environment_artifact[OF formed that])
      show ?thesis
        by (simp only: Suc.IH finite_variable_readings_formed_exact[OF exact]
          finite_record_readings_formed_exact[OF exact_formed_object[OF exact]])
    qed
    show "finite_pattern_readings_bounded (Suc n) E u V r=finite_pattern_readings_formed (Suc n) E u V r"
      by (simp only: finite_pattern_readings_bounded.simps finite_pattern_readings_formed.simps formed if_True
          finite_pattern_constants_formed_exact[OF formed])
        (rule arg_cong[where f="\<lambda>X. finite_pattern_constants_formed E u V r |\<union>| ffUnion X"],
         rule fimage_cong[OF refl], rule each)
  qed
qed

declare finite_pattern_readings_bounded.simps[code del]

lemma finite_pattern_readings_bounded_checked_premise:
  "checked_premise (finite_pattern_readings_bounded n) finite_environment_formed (finite_pattern_readings_formed n)
    (\<lambda>E u V r. {||})"
proof (unfold_locales, goal_cases)
  case (1 E)
  show ?case by (intro ext) (rule finite_pattern_readings_formed_exact[OF 1, THEN fun_cong])
next
  case (2 E)
  show ?case by (intro ext) (cases n; simp add: 2)
qed

lemma finite_pattern_readings_bounded_formed_once_code [code]:
  "finite_pattern_readings_bounded n E u V r=(if finite_environment_formed E
    then finite_pattern_readings_formed n E u V r else {||})"
  by (rule checked_premise.checked_through[OF finite_pattern_readings_bounded_checked_premise, where t="\<lambda>f. f u V r"])

text \<open>
  A formed environment has formed artifacts. Its bounded term and pattern
  readings therefore consume the formation-free bodies of record candidates,
  citation choices, payload leaves and variable leaves, and check environment
  formation once at entry. Each code equation is the check of an instance of the first notion of
  @{text Established_Premises} hoisted through the application to the remaining arguments
  (@{thm [source] checked_premise.checked_through}). It keeps the statement's full arity: the seeded
  state presents the code equations in effect of its roots, so the arity rule's form would change
  its words. Unformed inputs keep
  every original empty result; formed inputs keep every original traversal and its order.
\<close>

end
