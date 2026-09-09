theory Presentation_Development
  imports Inference_Development Presentation_Function_Witnesses
begin

section \<open>The development account transports through complete classes\<close>

theorem inference_closure_presentation:
  assumes seed: "K\<subseteq>D"
    and boundary: "\<And>X. X\<subseteq>D \<Longrightarrow> inference_consequences R X\<subseteq>D"
    and step: "\<And>X. X\<subseteq>D \<Longrightarrow>
      inference_consequences S (presented_set P X)=presented_set P (inference_consequences R X)"
  shows "inference_closure S (presented_set P K)=presented_set P (inference_closure R K)"
proof -
  have source_mono: "mono (\<lambda>X. K\<union>inference_consequences R X)"
    using inference_consequences_mono by (auto simp: mono_def)
  have target_mono: "mono (\<lambda>X. presented_set P K\<union>inference_consequences S X)"
    using inference_consequences_mono by (auto simp: mono_def)
  have closed: "K\<union>inference_consequences R X\<subseteq>D" if "X\<subseteq>D" for X
    using seed boundary[OF that] by blast
  have transport: "presented_set P K\<union>inference_consequences S (presented_set P X)=
      presented_set P (K\<union>inference_consequences R X)" if "X\<subseteq>D" for X
    by (simp only: step[OF that]) (auto simp: presented_set_def)
  show ?thesis unfolding inference_closure_def
    by (rule presented_least_fixed_point_on[OF source_mono target_mono closed transport])
qed

theorem inference_membership_presentation:
  assumes source: "presentation_class P D A"
    and closure: "inference_closure S (presented_set P K)=presented_set P (inference_closure R K)"
    and read: "P a p"
  shows "p\<in>inference_closure S (presented_set P K) \<longleftrightarrow> a\<in>inference_closure R K"
  unfolding closure
proof
  assume "p\<in>presented_set P (inference_closure R K)"
  then obtain b where member: "b\<in>inference_closure R K" and presented: "P b p"
    by (auto simp: presented_set_def)
  have "a=b" by (rule presentation_class.recovery[OF source read presented])
  then show "a\<in>inference_closure R K" using member by simp
next
  assume "a\<in>inference_closure R K"
  then show "p\<in>presented_set P (inference_closure R K)"
    using read by (auto simp: presented_set_def)
qed

theorem inference_residual_occurrences:
  assumes source: "presentation_class P D A"
    and closure: "inference_closure S (presented_set P K)=presented_set P (inference_closure R K)"
    and reads: "\<And>i. i\<in>I \<Longrightarrow> P (h i) (g i)"
  shows "rel_dom (remaining_obligations (inference_closure S (presented_set P K)) (graph_map I g))=
    rel_dom (remaining_obligations (inference_closure R K) (graph_map I h))"
  using inference_membership_presentation[OF source closure] reads
  by (auto simp: rel_dom_def graph_map_member)

section \<open>Existing implementation proposals have explicit remaining conditions\<close>

context presentation_class
begin

theorem literal_copy_method_reduction:
  "exact_obligation_reduction UNIV
    (\<lambda>_::unit. presented_function_contract presents subject admissible
      presents subject admissible id (\<lambda>p q. admissible p \<and> q=p))
    id (\<lambda>_. {((),\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> p=q)})"
  using literal_copy_contract_iff[OF presentation_class_axioms]
  by (simp add: exact_obligation_reduction_def rel_ran_def)

theorem completed_copy_method_reduction:
  "exact_obligation_reduction UNIV
    (\<lambda>_::unit. presented_function_contract presents subject admissible
      presents subject admissible id
      (\<lambda>p r. \<exists>q. (admissible p \<and> q=p) \<and> presentation_transport presents presents q r))
    id (\<lambda>_. {}::(unit\<times>bool) set)"
proof -
  have witness: "presented_function_witness presents subject admissible presents subject admissible id
      (\<lambda>p q. admissible p \<and> q=p)"
    by (rule literal_copy_witness[OF presentation_class_axioms])
  have complete: "presented_function_contract presents subject admissible presents subject admissible id
      (\<lambda>p r. \<exists>q. (admissible p \<and> q=p) \<and> presentation_transport presents presents q r)"
    by (rule presented_function_witness.completion[OF witness])
  show ?thesis using complete by (simp add: exact_obligation_reduction_def)
qed

end

theorem copy_counterexample_remains_an_obligation:
  "remaining_obligations {True}
    {((),\<forall>a::unit. \<forall>p q::bool. True \<longrightarrow> True \<longrightarrow> p=q)}={((),False)}"
  by (auto simp: remaining_obligations_def)

text \<open>
  Exact transport of the actual inference-consequence step transports the
  whole development closure. Complete class recovery then transports every
  membership result and the exact remaining occurrence domain. No candidate
  comparison is allowed to depend silently on a discarded presentation detail.

  Literal copying and copying followed by semantic correspondence enter the
  same reduction account. The existing owned contract gives the former an
  exact uniqueness condition. The proved witness-completion construction
  discharges the latter for every complete class. A class with two forms for
  one subject leaves the copying condition unresolved. Neither proposal
  narrows that independently stated class to make its own test succeed.
\<close>

end
