theory Development_Recording_Refinements
  imports Development_Bounded_Recording Established_Premises
begin

text \<open>
  The recording's refinement collection (DECISIONS.md, task 482's entry, its (4) R): each refinement of the
  bounded recording is a new constant beside the original with its exactness under the premise the recording
  establishes, and the code equations of the recording's own constants that call it. No library theory imports
  this theory, and no theory a recorded state's definition imports; execution theories do.
\<close>

section \<open>The recording's target formations are made where the payload is made\<close>

text \<open>
  The recording records at locus and payload @{term "Finite_Whole R"}, where R is the payload's complete data
  quotation. @{const finite_construct_formed_cause_generation} checks the formation of both targets, two walks of
  R. Under their formation it is the constructor below, which keeps the check of the cited rows' distinctness: the
  first notion of @{text Established_Premises}, its premise established where R is made.
\<close>

definition finite_construct_quoted_generation :: development_constructor where
  "finite_construct_quoted_generation E l p c rows=(if distinct (map snd rows) then
    map_option (finite_generation_record_body E l p c rows) (keyed_option_map (finite_anchor_artifact E) (map fst rows))
    else None)"

lemma finite_construct_quoted_generation_exact:
  assumes "finite_target_formed l" "finite_target_formed p"
  shows "finite_construct_formed_cause_generation E l p c rows=finite_construct_quoted_generation E l p c rows"
  using assms by (simp add: finite_construct_formed_cause_generation_def finite_construct_quoted_generation_def)

lemma finite_construct_quoted_generation_established:
  "established_premise (\<lambda>(l,p). finite_construct_formed_cause_generation E l p)
    (\<lambda>(l,p). finite_target_formed l \<and> finite_target_formed p) (\<lambda>(l,p). finite_construct_quoted_generation E l p)"
  by (rule established_premise.intro) (auto intro!: ext simp: finite_construct_quoted_generation_exact)

lemma finite_construct_quoted_generation_whole:
  assumes "finite_exact_formed R"
  shows "finite_construct_formed_cause_generation E (Finite_Whole R) (Finite_Whole R) c rows=
    finite_construct_quoted_generation E (Finite_Whole R) (Finite_Whole R) c rows"
  using assms by (simp add: finite_construct_quoted_generation_exact)

text \<open>
  The payload's quotation forms R from the term's formation; the recording's judgment already has it: the
  listing policy's source is constructed only over formed presentations, so a judgment of R is made only of a
  formed R.
\<close>

lemma finite_data_syntax_quotation_formed:
  assumes "term_formed t" "finite_data_syntax t=Some R"
  shows "finite_exact_formed R"
  using complete_data_quotation_formed[OF finite_data_syntax_complete_quotation[OF assms]]
  by (simp add: finite_exact_formed_correct)

lemma development_policy_source_with_formed:
  assumes policy: "development_policy_source_with xs=Some s"
  shows "list_all finite_term_formed xs"
proof -
  obtain d F u where "finite_ground_source xs=Some (d,F,u)"
    using policy by (cases "finite_ground_source xs") (auto simp: development_policy_source_with_def)
  then show ?thesis using finite_ground_source_total by blast
qed

lemma development_bounded_policy_judgment_formed:
  assumes judged: "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some j"
  shows "finite_exact_formed R"
proof -
  obtain d K pu B au root J C where j: "j=(d,K,pu,B,au,root,J,C)" by (metis prod.collapse)
  obtain p A M G I W F0 V where policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and "development_policy_certificate K pu d R=Some p"
    and "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=Some (A,M,root,G,au,I,W,B)"
    and "finite_bounded_judgment_quote B pu [] au [] R=Some (J,F0,V,C)"
    and "replay_policy_condition K pu [] d R J pu [] au []"
    by (rule development_bounded_policy_judgment_result[OF judged[unfolded j]])
  show ?thesis using development_policy_source_with_formed[OF policy] by simp
qed

text \<open>The recording, executed by the constructor that makes neither formation.\<close>

declare development_indexed_generation_def [code del]

lemma development_indexed_generation_quoted [code]:
  "development_indexed_generation t H rows=(case finite_data_syntax (decode_finite_term t) of
     None \<Rightarrow> None
   | Some R \<Rightarrow> Option.bind (development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R)
       (\<lambda>(d,K,pu,B,au,root,J,C). finite_construct_quoted_generation H (Finite_Whole R) (Finite_Whole R)
          (Finite_Whole C) rows))"
proof (cases "finite_data_syntax (decode_finite_term t)")
  case None
  then show ?thesis by (simp add: development_indexed_generation_def)
next
  case (Some R)
  note quoted=this
  show ?thesis
  proof (cases "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R")
    case None
    then show ?thesis using quoted by (simp add: development_indexed_generation_def)
  next
    case (Some j)
    have formed: "finite_exact_formed R" by (rule development_bounded_policy_judgment_formed[OF Some])
    show ?thesis using quoted Some
      by (simp add: development_indexed_generation_def finite_construct_quoted_generation_whole[OF formed]
        split: prod.splits)
  qed
qed

end
