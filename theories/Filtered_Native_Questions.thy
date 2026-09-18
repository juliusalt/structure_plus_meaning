theory Filtered_Native_Questions
  imports Factor_Finite_Development_Questions Finite_Singleton_Selection
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
  by (simp add: filtered_development_question_def finite_development_question_def)

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

end
