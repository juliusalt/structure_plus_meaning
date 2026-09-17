theory Factor_Formation_Once_Readings
  imports Factor_Executable_Packages
    Factor_Executable_Quotation
    Factor_Executable_Patterns
    Factor_Finite_Prepared_Data_Readings
begin

section \<open>Formation premises are established once for a traversal\<close>

lemma formed_environment_artifact:
  "finite_environment_formed E \<Longrightarrow> C |\<in>| finite_artifacts_at E u \<Longrightarrow> finite_exact_formed C"
  by (auto simp: finite_environment_formed_def finite_artifacts_at_def)

lemma exact_formed_object: "finite_exact_formed C \<Longrightarrow> finite_object_formed C"
  by (simp add: finite_exact_formed_def)

definition finite_citation_candidates_formed where
  "finite_citation_candidates_formed C r=(if r |\<in>| finite_carrier (finite_structure C) \<and> finite_data_empty_on C {|r|}
    then ffilter (\<lambda>(c,I). finite_raw_citation_at C r c I) (finite_citation_choices C r) else {||})"

lemma finite_citation_candidates_formed_exact:
  "finite_exact_formed C \<Longrightarrow> finite_citation_candidates C r=finite_citation_candidates_formed C r"
  by (auto simp: finite_citation_candidates_def finite_citation_candidates_formed_def finite_citation_at_def fset_eq_iff)

declare finite_citation_candidates_def[code del]

lemma finite_citation_candidates_formed_once_code [code]:
  "finite_citation_candidates C r=(if finite_exact_formed C then finite_citation_candidates_formed C r else {||})"
  by (auto simp: finite_citation_candidates_def finite_citation_candidates_formed_def finite_citation_at_def fset_eq_iff)

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

declare finite_native_definition_rows_def[code del]

lemma finite_native_definition_rows_formed_once_code [code]:
  "finite_native_definition_rows E=(if finite_environment_formed E then ffUnion (fimage (\<lambda>d.
      fimage (Pair d) (ffUnion (fimage (\<lambda>C. finite_two_field_record C (snd d)
        (finite_definition_body_readings E (fst d) (snd d))) (finite_artifacts_at E (fst d)))))
      (finite_environment_positions E)) else {||})"
  by (auto simp: finite_native_definition_rows_def finite_native_definition_readings_def fset_eq_iff
    ffUnion.rep_eq fimage.rep_eq)

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

lemma finite_term_readings_bounded_formed_once_code [code]:
  "finite_term_readings_bounded n E u r=(if finite_environment_formed E
    then finite_term_readings_formed n E u r else {||})"
  by (cases "finite_environment_formed E"; cases n) (simp_all add: finite_term_readings_formed_exact)

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

lemma finite_pattern_readings_bounded_formed_once_code [code]:
  "finite_pattern_readings_bounded n E u V r=(if finite_environment_formed E
    then finite_pattern_readings_formed n E u V r else {||})"
  by (cases "finite_environment_formed E"; cases n) (simp_all add: finite_pattern_readings_formed_exact)

text \<open>
  A formed environment has formed artifacts. Its bounded term and pattern
  readings therefore consume the formation-free bodies of record candidates,
  citation choices, payload leaves and variable leaves, and check environment
  formation once at entry. Citation choices share one object formation per root,
  and definition rows establish environment formation once for all positions.
  Unformed inputs keep every original empty result; formed inputs keep every
  original traversal and its order.
\<close>

end
