theory Factor_Source_Development_Subjects
  imports Factor_Finite_Development_Questions Factor_Finite_Source_Entry_Installation
begin

type_synonym source_development_proposal =
  "local_address option finite_native_system\<times>local_address option definition_site"

record source_development_request =
  source_development_environment :: "local_address option finite_artifact_environment"
  source_development_use :: "local_address option"
  source_development_root :: local_address
  source_development_targets :: "source_development_proposal list"
  source_development_input :: finite_factor_term
  source_development_outputs :: "finite_factor_term list"

definition source_development_proposals :: "source_development_request \<Rightarrow> source_development_proposal list" where
  "source_development_proposals R=concat (map (\<lambda>(Q,e).
    [(Q,e),(Q\<lparr>finite_system_clauses:={||}\<rparr>,e),
      (\<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr>,e),(Q,(None,[]))])
    (source_development_targets R))"

lemma source_development_original_scope:
  "set (source_development_targets R)\<subseteq>set (source_development_proposals R)"
  by (auto simp: source_development_proposals_def split: prod.splits)

definition source_development_indices where
  "source_development_indices R=[0..<length (source_development_proposals R)]"

definition source_development_values where
  "source_development_values R=map finite_development_index (source_development_indices R)"

definition source_development_compatible where
  "source_development_compatible R Q \<longleftrightarrow>
    (\<exists>P. native_package_at (decode_finite_environment (source_development_environment R))
      (source_development_use R) (source_development_root R) (decode_finite_system P) \<and>
      schema_system_formed (decode_finite_system Q) \<and>
      systems_agree_on (decode_finite_system P) (decode_finite_system Q)
        (system_definitions (decode_finite_system P)))"

definition source_development_original_condition :: "source_development_request \<Rightarrow>
    source_development_proposal \<Rightarrow> nat \<Rightarrow> bool" where
  "source_development_original_condition R proposal f=(case proposal of (Q,e) \<Rightarrow>
    if f=0 then source_development_compatible R Q
    else if f=1 then e\<in>system_definitions (decode_finite_system Q)
    else if f=2 then proposal\<in>set (source_development_targets R)
    else if f=3 then (\<exists>actual. finite_development_generated (source_development_values R)=Some actual \<and>
      set (source_development_values R)\<subseteq>set actual)
    else False)"

definition source_development_observation :: "source_development_request \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "source_development_observation R i f=(i<length (source_development_proposals R) \<and>
    (case source_development_proposals R!i of (Q,e) \<Rightarrow>
      if f=0 then finite_source_extension_context (source_development_environment R)
        (source_development_use R) (source_development_root R) Q\<noteq>None
      else if f=1 then e |\<in>| finite_system_definitions Q
      else if f=2 then (Q,e)\<in>set (source_development_targets R)
      else if f=3 then finite_development_scope_complete (source_development_values R)
      else False))"

theorem source_development_observation_exact:
  assumes "i<length (source_development_proposals R)"
  shows "source_development_observation R i f \<longleftrightarrow>
    source_development_original_condition R (source_development_proposals R!i) f"
  using assms by (auto simp: source_development_observation_def source_development_original_condition_def
    source_development_compatible_def finite_source_extension_context_correct[symmetric]
    finite_system_definitions_correct finite_development_scope_complete_def list_all_iff
    split: prod.splits option.splits if_splits)

definition source_development_facet_values where
  "source_development_facet_values R f=map finite_development_index
    (filter (\<lambda>i. source_development_observation R i f) (source_development_indices R))"

lemma source_development_scope_observation:
  "i<length (source_development_proposals R) \<Longrightarrow>
    source_development_observation R i 3=finite_development_scope_complete (source_development_values R)"
  by (simp add: source_development_observation_def split: prod.splits)

lemma source_development_facet_values_shared [code]:
  "source_development_facet_values R f=(if f=3 then
      (if finite_development_scope_complete (source_development_values R) then source_development_values R else [])
    else map finite_development_index
      (filter (\<lambda>i. source_development_observation R i f) (source_development_indices R)))"
proof (cases "f=3")
  case True
  have same: "filter (\<lambda>i. source_development_observation R i 3) (source_development_indices R)=
    filter (\<lambda>_. finite_development_scope_complete (source_development_values R)) (source_development_indices R)"
    by (rule filter_cong[OF refl])
      (use source_development_scope_observation in \<open>auto simp: source_development_indices_def\<close>)
  show ?thesis using same
    by (cases "finite_development_scope_complete (source_development_values R)")
      (simp_all add: True source_development_facet_values_def source_development_values_def)
next
  case False
  then show ?thesis by (simp only: source_development_facet_values_def if_False)
qed

lemma source_development_facet_values_exact:
  assumes "i<length (source_development_proposals R)"
  shows "finite_development_index i\<in>set (source_development_facet_values R f) \<longleftrightarrow>
    source_development_original_condition R (source_development_proposals R!i) f"
  using assms by (auto simp: source_development_facet_values_def source_development_indices_def
    source_development_observation_exact)

definition source_development_question where
  "source_development_question R=finite_development_question (source_development_values R)
    (map (source_development_facet_values R) [0,1,2,3])"

theorem source_development_admitted_condition:
  assumes question: "source_development_question R=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and chosen: "finite_development_index i\<in>set accepted"
    and index: "i<length (source_development_proposals R)"
    and facet: "f\<in>set [0,1,2,3]"
  shows "source_development_original_condition R (source_development_proposals R!i) f"
proof -
  have represented: "finite_development_index i\<in>set (source_development_facet_values R f)"
    by (rule finite_development_original_conditions[OF _ admitted chosen])
      (use question facet in \<open>auto simp: source_development_question_def\<close>)
  show ?thesis using represented by (simp only: source_development_facet_values_exact[OF index])
qed

definition source_development_selected_indices where
  "source_development_selected_indices R accepted=filter (\<lambda>i. finite_development_index i\<in>set accepted)
    (source_development_indices R)"

definition source_development_selection where
  "source_development_selection R accepted=(if list_all (\<lambda>x. x\<in>set (source_development_values R)) accepted
    then list_singleton_option (map (nth (source_development_proposals R))
      (source_development_selected_indices R accepted)) else None)"

lemma source_development_selection_member:
  assumes selected: "source_development_selection R accepted=Some proposal"
  obtains i where "i<length (source_development_proposals R)"
    "finite_development_index i\<in>set accepted" "proposal=source_development_proposals R!i"
  using selected by (auto simp: source_development_selection_def list_singleton_option_some
    source_development_selected_indices_def source_development_indices_def split: if_splits)

theorem source_development_selected_conditions:
  assumes question: "source_development_question R=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and selected: "source_development_selection R accepted=Some proposal"
    and facet: "f\<in>set [0,1,2,3]"
  shows "source_development_original_condition R proposal f"
proof -
  obtain i where index: "i<length (source_development_proposals R)"
    and chosen: "finite_development_index i\<in>set accepted"
    and proposal_eq: "proposal=source_development_proposals R!i"
    by (rule source_development_selection_member[OF selected]) blast
  show ?thesis by (simp only: proposal_eq; rule source_development_admitted_condition[OF question admitted chosen index facet])
qed

theorem source_development_selected_original_target:
  assumes "source_development_question R=Some Q"
    "native_development_admission Q report=Some accepted"
    "source_development_selection R accepted=Some (T,e)"
  shows "(T,e)\<in>set (source_development_targets R)"
    "source_development_compatible R T"
    "e |\<in>| finite_system_definitions T"
    "finite_development_scope_complete (source_development_values R)"
  using source_development_selected_conditions[OF assms, of 2]
    source_development_selected_conditions[OF assms, of 0]
    source_development_selected_conditions[OF assms, of 1]
    source_development_selected_conditions[OF assms, of 3]
  by (auto simp: source_development_original_condition_def finite_system_definitions_correct
    finite_development_scope_complete_def list_all_iff split: option.splits)

text \<open>
  The original request contains the entire source, every permitted target
  program and entry, and the subsequent query. Proposals preserve every original
  occurrence and also compute actual changed programs and entries. None of
  these observations is a supplied satisfaction table. Their equation refers
  to source reading, complete old-definition agreement, requested target
  membership, entry membership and actual generated-scope coverage.

  Selection compares the complete target values. Repeated occurrences remain
  in the report; equal targets can determine one value, while distinct adequate
  targets remain ambiguous. The declared target family is an original input,
  not a claim to discover every possible program.
\<close>

end
