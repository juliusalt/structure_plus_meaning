theory Filtered_Native_Questions
  imports Factor_Finite_Development_Questions Finite_Singleton_Selection Native_Path_Stores
    Factor_Finite_Payload_Literals
begin

section \<open>One reusable native question for computed predicates on actual subjects\<close>

text \<open>
  A decision whose candidates are actual subjects and whose original condition is computed
  on each of them is one question: the candidates are the indices of the subject list and
  the single facet is the indices the condition holds at. Admission then establishes the
  condition at every admitted index, so a use instantiates this contract with its own
  subjects and condition instead of restating the correspondence. Nothing here supplies an
  observation, a satisfaction row or a preference among the admitted candidates: the
  condition is evaluated on the actual subject, and several candidates may satisfy it.
\<close>

definition filtered_development_indices where
  "filtered_development_indices subjects condition=
    map finite_development_index (filter (\<lambda>i. condition (subjects!i)) [0..<length subjects])"

definition filtered_development_question where
  "filtered_development_question subjects condition=finite_development_question
    (map finite_development_index [0..<length subjects])
    [filtered_development_indices subjects condition]"

lemma filtered_development_indices_exact:
  "finite_development_index i\<in>set (filtered_development_indices subjects condition)
    \<longleftrightarrow> i<length subjects \<and> condition (subjects!i)"
  by (auto simp: filtered_development_indices_def)

theorem filtered_development_admission:
  assumes question: "filtered_development_question subjects condition=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  shows "i<length subjects \<and> condition (subjects!i)"
proof -
  have inside: "finite_development_index i\<in>set (filtered_development_indices subjects condition)"
    by (rule finite_development_original_conditions[OF question[unfolded filtered_development_question_def]
      admission selected]) simp
  then show ?thesis by (simp only: filtered_development_indices_exact)
qed

text \<open>
  A subject list the condition holds nowhere on supplies an empty facet, and an empty
  subject list supplies no candidate; the question construction refuses both, so no
  admission is obtained from an empty original scope.
\<close>

lemma filtered_development_question_refuses_empty_subjects:
  "filtered_development_question [] condition=None"
  by (simp add: filtered_development_question_def finite_development_question_def finite_subject_question_def)

lemma filtered_development_unsatisfied_facet:
  assumes "\<forall>i<length subjects. \<not>condition (subjects!i)"
  shows "filtered_development_indices subjects condition=[]"
  using assms by (simp add: filtered_development_indices_def)

section \<open>Reusable consumers retain the original native admission\<close>

definition native_admitted_subjects where
  "native_admitted_subjects subjects question report=(case question of None \<Rightarrow> None
    | Some Q \<Rightarrow> map_option (\<lambda>accepted. map (nth subjects)
      (filter (\<lambda>i. finite_development_index i\<in>set accepted) [0..<length subjects]))
        (native_development_admission Q report))"

lemma native_admitted_subjects_fields:
  assumes result: "native_admitted_subjects subjects question report=Some xs" and member: "x\<in>set xs"
  obtains Q accepted i where "question=Some Q" "native_development_admission Q report=Some accepted"
    "i<length subjects" "finite_development_index i\<in>set accepted" "x=subjects!i"
  using result member by (auto simp: native_admitted_subjects_def split: option.splits)

definition native_admitted_choice where
  "native_admitted_choice subjects question report=(case native_admitted_subjects subjects question report of
    None \<Rightarrow> None | Some xs \<Rightarrow> list_singleton_option xs)"

lemma native_admitted_choice_fields:
  assumes chosen: "native_admitted_choice subjects question report=Some x"
  obtains Q accepted i where "question=Some Q" "native_development_admission Q report=Some accepted"
    "i<length subjects" "finite_development_index i\<in>set accepted" "x=subjects!i"
proof -
  obtain xs where result: "native_admitted_subjects subjects question report=Some xs" and member: "x\<in>set xs"
    using chosen by (auto simp: native_admitted_choice_def list_singleton_option_some split: option.splits)
  show thesis by (rule native_admitted_subjects_fields[OF result member]) (rule that; assumption)
qed

theorem filtered_admitted_choice_condition:
  assumes chosen: "native_admitted_choice subjects (filtered_development_question subjects condition) report=Some x"
  shows "condition x"
  by (rule native_admitted_choice_fields[OF chosen])
    (use filtered_development_admission in blast)

text \<open>
  An executed packet already carries its admission, so its admitted subjects are read from
  that admission instead of admitting the same report a second time; they are the admitted
  subjects of the packet's own report.
\<close>

definition native_packet_subjects where
  "native_packet_subjects subjects packet=(case packet of (Q,report,admission) \<Rightarrow>
    map_option (\<lambda>accepted. map (nth subjects)
      (filter (\<lambda>i. finite_development_index i\<in>set accepted) [0..<length subjects])) admission)"

lemma native_packet_subjects_admitted:
  "native_packet_subjects subjects (native_development_packet Q)=
    native_admitted_subjects subjects (Some Q) (construct_native_development Q)"
  by (simp add: native_packet_subjects_def native_development_packet_def native_admitted_subjects_def Let_def)

theorem filtered_admitted_subjects_condition:
  assumes admitted: "native_admitted_subjects subjects (filtered_development_question subjects condition) report=Some xs"
    and member: "x\<in>set xs"
  shows "x\<in>set subjects \<and> condition x"
proof (rule native_admitted_subjects_fields[OF admitted member])
  fix Q accepted i
  assume question: "filtered_development_question subjects condition=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and bound: "i<length subjects" and index: "finite_development_index i\<in>set accepted"
    and chosen: "x=subjects!i"
  have "condition (subjects!i)" using filtered_development_admission[OF question admission index] by simp
  then show "x\<in>set subjects \<and> condition x" using nth_mem[OF bound] by (simp add: chosen)
qed

section \<open>The same question over paths of its subjects' keys\<close>

text \<open>
  A candidate is the path of its subject's key, a list of shapes, and not a position in the subject list
  written as a payload of digits: the scope and the facets state paths, so the question reads no octet but
  the empty payload that ends a list and the bits' shapes. The key is a parameter; a use supplies the key its
  subjects have, and asks of it only that it be injective on them. The question is stated for a list of
  facets, each the paths of the subjects its condition holds of; the one-facet question is its instance.
  An admitted subject is read back as a subject whose path is accepted, never by an index.
\<close>

definition keyed_development_candidates :: "('s \<Rightarrow> bool list) \<Rightarrow> 's list \<Rightarrow> finite_factor_term list" where
  "keyed_development_candidates key subjects=map (\<lambda>s. finite_path (key s)) subjects"

definition keyed_development_facet ::
    "('s \<Rightarrow> bool list) \<Rightarrow> 's list \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> finite_factor_term list" where
  "keyed_development_facet key subjects condition=map (\<lambda>s. finite_path (key s)) (filter condition subjects)"

definition keyed_faceted_question where
  "keyed_faceted_question key subjects facets observe=finite_development_question
    (keyed_development_candidates key subjects)
    (map (\<lambda>f. keyed_development_facet key subjects (\<lambda>s. observe s f)) facets)"

definition keyed_development_question where
  "keyed_development_question key subjects condition=keyed_faceted_question key subjects [()] (\<lambda>s f. condition s)"

lemma keyed_development_candidates_length [simp]:
  "length (keyed_development_candidates key subjects)=length subjects"
  by (simp add: keyed_development_candidates_def)

lemma keyed_development_facet_exact:
  assumes injective: "inj_on key (set subjects)" and member: "s\<in>set subjects"
  shows "finite_path (key s)\<in>set (keyed_development_facet key subjects condition) \<longleftrightarrow> condition s"
proof
  assume "finite_path (key s)\<in>set (keyed_development_facet key subjects condition)"
  then obtain t where t: "t\<in>set subjects" "condition t" and path: "finite_path (key s)=finite_path (key t)"
    by (auto simp: keyed_development_facet_def)
  have "key s=key t" using path by (simp only: inj_eq[OF finite_path_injective])
  then have "s=t" by (rule inj_onD[OF injective _ member t(1)])
  then show "condition s" using t(2) by simp
next
  assume "condition s"
  then show "finite_path (key s)\<in>set (keyed_development_facet key subjects condition)"
    using member by (simp add: keyed_development_facet_def)
qed

lemma keyed_faceted_question_refuses_empty_subjects: "keyed_faceted_question key [] facets observe=None"
  by (simp add: keyed_faceted_question_def keyed_development_candidates_def finite_development_question_def
    finite_subject_question_def)

lemma keyed_faceted_question_refuses_no_facets: "keyed_faceted_question key subjects [] observe=None"
  by (simp add: keyed_faceted_question_def finite_development_question_def finite_subject_question_def)

lemma keyed_development_question_refuses_empty_subjects: "keyed_development_question key [] condition=None"
  by (simp only: keyed_development_question_def keyed_faceted_question_refuses_empty_subjects)

theorem keyed_faceted_facet:
  assumes question: "keyed_faceted_question key subjects facets observe=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted" and facet: "f\<in>set facets"
  shows "\<exists>s\<in>set subjects. x=finite_path (key s) \<and> observe s f"
proof -
  have "x\<in>set (keyed_development_facet key subjects (\<lambda>s. observe s f))"
    by (rule finite_development_original_conditions[OF question[unfolded keyed_faceted_question_def]
      admission selected]) (use facet in auto)
  then show ?thesis by (auto simp: keyed_development_facet_def)
qed

theorem keyed_faceted_admission_at:
  assumes injective: "inj_on key (set subjects)"
    and question: "keyed_faceted_question key subjects facets observe=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_path (key s)\<in>set accepted" and member: "s\<in>set subjects"
    and facet: "f\<in>set facets"
  shows "observe s f"
proof -
  have "finite_path (key s)\<in>set (keyed_development_facet key subjects (\<lambda>s. observe s f))"
    by (rule finite_development_original_conditions[OF question[unfolded keyed_faceted_question_def]
      admission selected]) (use facet in auto)
  then show ?thesis by (simp only: keyed_development_facet_exact[OF injective member])
qed

theorem keyed_faceted_admission:
  assumes injective: "inj_on key (set subjects)"
    and question: "keyed_faceted_question key subjects facets observe=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted"
  obtains s where "s\<in>set subjects" "x=finite_path (key s)" "\<forall>f\<in>set facets. observe s f"
proof -
  have nonempty: "facets\<noteq>[]"
  proof
    assume "facets=[]"
    with question show False by (simp add: keyed_faceted_question_refuses_no_facets)
  qed
  then obtain f0 where f0: "f0\<in>set facets" by (cases facets) auto
  obtain s where member: "s\<in>set subjects" and path: "x=finite_path (key s)"
    using keyed_faceted_facet[OF question admission selected f0] by blast
  have "\<forall>f\<in>set facets. observe s f"
    using keyed_faceted_admission_at[OF injective question admission selected[unfolded path] member] by blast
  then show thesis by (rule that[OF member path])
qed

theorem keyed_development_admission:
  assumes question: "keyed_development_question key subjects condition=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted"
  obtains s where "s\<in>set subjects" "x=finite_path (key s)" "condition s"
  using keyed_faceted_facet[OF question[unfolded keyed_development_question_def] admission selected] by auto

definition keyed_admitted_subjects where
  "keyed_admitted_subjects key subjects question report=(case question of None \<Rightarrow> None
    | Some Q \<Rightarrow> map_option (\<lambda>accepted. filter (\<lambda>s. finite_path (key s)\<in>set accepted) subjects)
        (native_development_admission Q report))"

lemma keyed_admitted_subjects_fields:
  assumes result: "keyed_admitted_subjects key subjects question report=Some xs" and member: "x\<in>set xs"
  obtains Q accepted where "question=Some Q" "native_development_admission Q report=Some accepted"
    "x\<in>set subjects" "finite_path (key x)\<in>set accepted"
  using result member by (auto simp: keyed_admitted_subjects_def split: option.splits)

definition keyed_admitted_choice where
  "keyed_admitted_choice key subjects question report=(case keyed_admitted_subjects key subjects question report of
    None \<Rightarrow> None | Some xs \<Rightarrow> list_singleton_option xs)"

lemma keyed_admitted_choice_fields:
  assumes chosen: "keyed_admitted_choice key subjects question report=Some x"
  obtains Q accepted where "question=Some Q" "native_development_admission Q report=Some accepted"
    "x\<in>set subjects" "finite_path (key x)\<in>set accepted"
proof -
  obtain xs where result: "keyed_admitted_subjects key subjects question report=Some xs" and member: "x\<in>set xs"
    using chosen by (auto simp: keyed_admitted_choice_def list_singleton_option_some split: option.splits)
  show thesis by (rule keyed_admitted_subjects_fields[OF result member]) (rule that; assumption)
qed

definition keyed_packet_subjects where
  "keyed_packet_subjects key subjects packet=(case packet of (Q,report,admission) \<Rightarrow>
    map_option (\<lambda>accepted. filter (\<lambda>s. finite_path (key s)\<in>set accepted) subjects) admission)"

lemma keyed_packet_subjects_admitted:
  "keyed_packet_subjects key subjects (native_development_packet Q)=
    keyed_admitted_subjects key subjects (Some Q) (construct_native_development Q)"
  by (simp add: keyed_packet_subjects_def native_development_packet_def keyed_admitted_subjects_def Let_def)

theorem keyed_admitted_subjects_condition:
  assumes injective: "inj_on key (set subjects)"
    and admitted: "keyed_admitted_subjects key subjects (keyed_faceted_question key subjects facets observe) report=Some xs"
    and member: "x\<in>set xs" and facet: "f\<in>set facets"
  shows "x\<in>set subjects \<and> observe x f"
proof (rule keyed_admitted_subjects_fields[OF admitted member])
  fix Q accepted
  assume question: "keyed_faceted_question key subjects facets observe=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and inside: "x\<in>set subjects" and path: "finite_path (key x)\<in>set accepted"
  show "x\<in>set subjects \<and> observe x f"
    using inside keyed_faceted_admission_at[OF injective question admission path inside facet] by blast
qed

theorem keyed_admitted_choice_condition:
  assumes injective: "inj_on key (set subjects)"
    and chosen: "keyed_admitted_choice key subjects (keyed_faceted_question key subjects facets observe) report=Some x"
    and facet: "f\<in>set facets"
  shows "observe x f"
proof (rule keyed_admitted_choice_fields[OF chosen])
  fix Q accepted
  assume question: "keyed_faceted_question key subjects facets observe=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and inside: "x\<in>set subjects" and path: "finite_path (key x)\<in>set accepted"
  show "observe x f" by (rule keyed_faceted_admission_at[OF injective question admission path inside facet])
qed

section \<open>The keyed question's clauses read no octet but the empty payload\<close>

text \<open>
  The payloads a program states literally are the octets it reads as structure. The clauses the keyed
  question adds, one scope clause per candidate and one ground clause per facet row, state exactly the
  empty payload: the paths are shapes, and the empty payload ends every list and pairs a row with the
  empty subject.
\<close>

lemma finite_path_payloads:
  "v |\<in>| finite_pattern_payloads (finite_exact_term_pattern (finite_path bs) :: local_address finite_term_pattern)
    \<longleftrightarrow> v=[]"
  by (induction bs) (auto simp: finite_path_def finite_bit_def)

lemma finite_scope_rule_payloads:
  "v |\<in>| finite_schema_payloads (finite_scope_rule y) \<longleftrightarrow>
    v |\<in>| finite_pattern_payloads (finite_exact_term_pattern y :: local_address finite_term_pattern)"
  by (auto simp: finite_scope_rule_def finite_schema_payloads_def ffUnion.rep_eq fimage.rep_eq)

lemma finite_ground_rule_payloads:
  "v |\<in>| finite_schema_payloads (finite_ground_rule t) \<longleftrightarrow>
    v |\<in>| finite_pattern_payloads (finite_exact_term_pattern t :: local_address finite_term_pattern)"
  by (auto simp: finite_ground_rule_def finite_schema_payloads_def ffUnion.rep_eq fimage.rep_eq)

theorem keyed_scope_clause_payloads:
  assumes clause: "(c,S) |\<in>| finite_scope_clauses (keyed_development_candidates key subjects)"
  shows "v |\<in>| finite_schema_payloads S \<longleftrightarrow> v=[]"
proof -
  obtain i where i: "i<length subjects"
    and rule: "S=finite_scope_rule (keyed_development_candidates key subjects!i)"
    using clause by (auto simp: finite_scope_clauses_def fset_of_list.rep_eq keyed_development_candidates_length)
  have "S=finite_scope_rule (finite_path (key (subjects!i)))"
    using i rule by (simp add: keyed_development_candidates_def)
  then show ?thesis by (simp only: finite_scope_rule_payloads finite_path_payloads)
qed

theorem keyed_facet_clause_payloads:
  assumes clause: "(c,S) |\<in>| finite_ground_clauses (finite_development_rows (keyed_development_facet key subjects condition))"
  shows "v |\<in>| finite_schema_payloads S \<longleftrightarrow> v=[]"
proof -
  let ?ys="filter condition subjects"
  obtain i where i: "i<length ?ys"
    and rule: "S=finite_ground_rule (finite_development_rows (keyed_development_facet key subjects condition)!i)"
    using clause by (auto simp: finite_ground_clauses_def fset_of_list.rep_eq finite_development_rows_def
      keyed_development_facet_def)
  have "S=finite_ground_rule (Finite_Pair (Finite_Payload []) (finite_path (key (?ys!i))))"
    using i rule by (simp add: finite_development_rows_def keyed_development_facet_def)
  then show ?thesis by (auto simp: finite_ground_rule_payloads finite_path_payloads)
qed

corollary keyed_question_clause_leaves:
  assumes "(c,S) |\<in>| finite_scope_clauses (keyed_development_candidates key subjects) \<or>
    (c,S) |\<in>| finite_ground_clauses (finite_development_rows (keyed_development_facet key subjects condition))"
  shows "Payload_Term v\<in>schema_leaves (decode_finite_schema S) \<longleftrightarrow> v=[]"
proof -
  have "v |\<in>| finite_schema_payloads S \<longleftrightarrow> v=[]"
  proof (cases "(c,S) |\<in>| finite_scope_clauses (keyed_development_candidates key subjects)")
    case True
    then show ?thesis by (rule keyed_scope_clause_payloads)
  next
    case False
    then have "(c,S) |\<in>| finite_ground_clauses
        (finite_development_rows (keyed_development_facet key subjects condition))"
      using assms False by (iprover elim: disjE notE)
    then show ?thesis by (rule keyed_facet_clause_payloads)
  qed
  then show ?thesis by (simp only: finite_schema_payloads_exact)
qed

end
