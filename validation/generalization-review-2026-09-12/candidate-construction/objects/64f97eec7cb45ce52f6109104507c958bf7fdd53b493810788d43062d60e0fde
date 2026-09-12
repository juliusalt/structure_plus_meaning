theory Conjunction_Development
  imports Inference_Development
begin

section \<open>Two independently meaningful methods for finite conjunction\<close>

definition conjunction_premises :: "'a list \<Rightarrow> (nat\<times>'a list) set" where
  "conjunction_premises xs=graph_map {..<length xs} (\<lambda>i. [xs!i])"

lemma conjunction_premises_finite:
  "finite (conjunction_premises xs)"
  by (simp add: conjunction_premises_def graph_map_finite)

lemma conjunction_premises_functional:
  "single_valued (conjunction_premises xs)"
  by (simp add: conjunction_premises_def graph_map_single_valued)

lemma conjunction_premises_values:
  "rel_ran (conjunction_premises xs)=(\<lambda>x. [x]) ` set xs"
  by (auto simp: conjunction_premises_def graph_map_ran image_iff in_set_conv_nth)

lemma conjunction_premises_card:
  "card (conjunction_premises xs)=length xs"
proof -
  have shape: "conjunction_premises xs=(\<lambda>i. (i,[xs!i])) ` {..<length xs}"
    by (auto simp: conjunction_premises_def graph_map_def)
  have injective: "inj_on (\<lambda>i. (i,[xs!i])) {..<length xs}" by (auto simp: inj_on_def)
  show ?thesis by (simp add: shape card_image[OF injective])
qed

definition flat_conjunction_rules :: "'a list \<Rightarrow> (nat\<times>'a list) set \<Rightarrow> bool" where
  "flat_conjunction_rules q H \<longleftrightarrow> H=conjunction_premises q \<or>
    (\<exists>xs a. a\<in>set xs \<and> q=[a] \<and> H={(0,xs)})"

definition binary_conjunction_rules :: "'a list \<Rightarrow> (nat\<times>'a list) set \<Rightarrow> bool" where
  "binary_conjunction_rules q H \<longleftrightarrow>
    (q=[] \<and> H={}) \<or>
    (\<exists>a xs. q=a#xs \<and> H={(0,[a]),(1,xs)}) \<or>
    (\<exists>xs a. a\<in>set xs \<and> q=[a] \<and> H={(0,xs)})"

theorem flat_conjunction_sound:
  "inference_sound (\<lambda>xs. set xs\<subseteq>A) flat_conjunction_rules"
  unfolding inference_sound_def
proof (intro allI impI)
  fix q H
  assume "finite H" "single_valued H"
    and rule: "flat_conjunction_rules q H"
    and support: "rel_ran H\<subseteq>{xs. set xs\<subseteq>A}"
  from rule have "H=conjunction_premises q \<or>
      (\<exists>xs a. a\<in>set xs \<and> q=[a] \<and> H={(0,xs)})"
    by (simp only: flat_conjunction_rules_def)
  then show "set q\<subseteq>A"
  proof
    assume shape: "H=conjunction_premises q"
    have "(\<lambda>a. [a]) ` set q\<subseteq>{xs. set xs\<subseteq>A}"
      using support by (simp only: shape conjunction_premises_values)
    then show ?thesis by auto
  next
    assume "\<exists>xs a. a\<in>set xs \<and> q=[a] \<and> H={(0,xs)}"
    then obtain xs a where atom: "a\<in>set xs" and q: "q=[a]" and H: "H={(0,xs)}"
      by blast
    have member: "xs\<in>rel_ran H" by (simp add: H rel_ran_image)
    have "set xs\<subseteq>A" using subsetD[OF support member] by simp
    then show ?thesis using atom q by auto
  qed
qed

theorem binary_conjunction_sound:
  "inference_sound (\<lambda>xs. set xs\<subseteq>A) binary_conjunction_rules"
  by (auto simp: inference_sound_def binary_conjunction_rules_def rel_ran_image)

lemma flat_conjunction_collect:
  assumes "\<And>a. a\<in>set xs \<Longrightarrow> [a]\<in>inference_closure flat_conjunction_rules K"
  shows "xs\<in>inference_closure flat_conjunction_rules K"
  by (rule inference_closure_step[OF conjunction_premises_finite conjunction_premises_functional])
    (use assms in \<open>auto simp: flat_conjunction_rules_def conjunction_premises_values\<close>)

lemma binary_conjunction_collect:
  assumes "\<And>a. a\<in>set xs \<Longrightarrow> [a]\<in>inference_closure binary_conjunction_rules K"
  shows "xs\<in>inference_closure binary_conjunction_rules K"
  using assms
proof (induction xs)
  case Nil
  show ?case by (rule inference_closure_step[where H="{}"])
    (simp_all add: single_valued_def binary_conjunction_rules_def)
next
  case (Cons a xs)
  have head: "[a]\<in>inference_closure binary_conjunction_rules K" by (rule Cons.prems) simp
  have tail: "xs\<in>inference_closure binary_conjunction_rules K"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case
  proof (rule inference_closure_step[where H="{(0,[a]),(1,xs)}" and R=binary_conjunction_rules])
    show "finite {(0::nat,[a]),(1,xs)}" by simp
    show "single_valued {(0::nat,[a]),(1,xs)}" by (auto simp: single_valued_def)
    show "binary_conjunction_rules (a#xs) {(0,[a]),(1,xs)}"
      by (auto simp: binary_conjunction_rules_def)
    show "rel_ran {(0::nat,[a]),(1,xs)}\<subseteq>inference_closure binary_conjunction_rules K"
      using head tail by (auto simp: rel_ran_image)
  qed
qed

lemma flat_conjunction_project:
  assumes "xs\<in>inference_closure flat_conjunction_rules K" "a\<in>set xs"
  shows "[a]\<in>inference_closure flat_conjunction_rules K"
  by (rule inference_closure_step[where H="{(0,xs)}"])
    (use assms in \<open>auto simp: single_valued_def flat_conjunction_rules_def rel_ran_def\<close>)

lemma binary_conjunction_project:
  assumes "xs\<in>inference_closure binary_conjunction_rules K" "a\<in>set xs"
  shows "[a]\<in>inference_closure binary_conjunction_rules K"
  by (rule inference_closure_step[where H="{(0,xs)}"])
    (use assms in \<open>auto simp: single_valued_def binary_conjunction_rules_def rel_ran_def\<close>)

section \<open>The shared semantic boundary settles both methods\<close>

theorem conjunction_closure_characterization:
  assumes sound: "\<And>A. inference_sound (\<lambda>xs. set xs\<subseteq>A) R"
    and collect: "\<And>xs K. (\<And>a. a\<in>set xs \<Longrightarrow> [a]\<in>inference_closure R K)
      \<Longrightarrow> xs\<in>inference_closure R K"
    and project: "\<And>xs K a. xs\<in>inference_closure R K \<Longrightarrow> a\<in>set xs
      \<Longrightarrow> [a]\<in>inference_closure R K"
  shows "xs\<in>inference_closure R K \<longleftrightarrow> set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
proof
  assume member: "xs\<in>inference_closure R K"
  have seeds: "K\<subseteq>{ys. set ys\<subseteq>(\<Union>ys\<in>K. set ys)}" by blast
  show "set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
    using inference_closure_sound[OF sound seeds] member by blast
next
  assume support: "set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
  show "xs\<in>inference_closure R K"
  proof (rule collect)
    fix a assume "a\<in>set xs"
    then obtain ys where source: "ys\<in>K" "a\<in>set ys" using support by blast
    have seed: "ys\<in>inference_closure R K"
      by (rule subsetD[OF inference_closure_seed source(1)])
    show "[a]\<in>inference_closure R K" by (rule project[OF seed source(2)])
  qed
qed

theorem flat_conjunction_closure:
  "xs\<in>inference_closure flat_conjunction_rules K \<longleftrightarrow>
    set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
  by (rule conjunction_closure_characterization[OF flat_conjunction_sound
    flat_conjunction_collect flat_conjunction_project])

theorem binary_conjunction_closure:
  "xs\<in>inference_closure binary_conjunction_rules K \<longleftrightarrow>
    set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
  by (rule conjunction_closure_characterization[OF binary_conjunction_sound
    binary_conjunction_collect binary_conjunction_project])

theorem conjunction_methods_same_unbounded_capability:
  "inference_refines flat_conjunction_rules binary_conjunction_rules \<and>
    inference_refines binary_conjunction_rules flat_conjunction_rules"
  by (auto simp: inference_refines_def flat_conjunction_closure binary_conjunction_closure)

lemma binary_conjunction_local_bound:
  assumes "binary_conjunction_rules q H"
  shows "card H\<le>2"
  using assms by (auto simp: binary_conjunction_rules_def)

theorem binary_conjunction_bounded_closure:
  "inference_closure (bounded_inferences 2 binary_conjunction_rules) K=
    inference_closure binary_conjunction_rules K"
  by (rule bounded_inferences_complete) (rule binary_conjunction_local_bound)

lemma bounded_flat_conjunction_length:
  assumes "K\<subseteq>{xs. length xs\<le>k}" "1\<le>k"
  shows "inference_closure (bounded_inferences k flat_conjunction_rules) K\<subseteq>
    {xs. length xs\<le>k}"
  by (rule inference_closure_least[OF assms(1)])
    (use assms(2) in \<open>auto simp: inference_consequences_def bounded_inferences_def
      flat_conjunction_rules_def conjunction_premises_card\<close>)

theorem meaningful_depth_improves_bounded_capability:
  "inference_capability 2 (flat_conjunction_rules :: unit list \<Rightarrow> (nat\<times>unit list) set \<Rightarrow> bool)
    \<subset>inference_capability 2 binary_conjunction_rules"
proof -
  have flat: "inference_refines (bounded_inferences 2 flat_conjunction_rules) flat_conjunction_rules"
    by (rule inference_refines_by_inclusion) (simp add: bounded_inferences_def)
  have included: "inference_capability 2 flat_conjunction_rules\<subseteq>
      inference_capability 2 binary_conjunction_rules"
    using flat conjunction_methods_same_unbounded_capability
    by (auto simp: inference_capability_def inference_refines_def binary_conjunction_bounded_closure)
  have produced: "({[()]},[(),(),()])\<in>inference_capability 2 binary_conjunction_rules"
    by (simp add: inference_capability_def binary_conjunction_bounded_closure binary_conjunction_closure)
  have limited: "inference_closure (bounded_inferences 2 flat_conjunction_rules) {[()]}
      \<subseteq>{xs. length xs\<le>2}"
    by (rule bounded_flat_conjunction_length) auto
  have missing: "({[()]},[(),(),()])\<notin>inference_capability 2 flat_conjunction_rules"
    using limited by (auto simp: inference_capability_def)
  show ?thesis using included produced missing by blast
qed

section \<open>Stopping is justified over the entire stated semantic class\<close>

definition conjunction_models :: "'a list set set" where
  "conjunction_models={{xs. set xs\<subseteq>A} |A. True}"

lemma conjunction_model_consequences:
  "model_consequences conjunction_models K={xs. set xs\<subseteq>(\<Union>ys\<in>K. set ys)}"
proof (rule set_eqI)
  fix xs
  show "xs\<in>model_consequences conjunction_models K \<longleftrightarrow>
      xs\<in>{xs. set xs\<subseteq>(\<Union>ys\<in>K. set ys)}"
  proof
    assume member: "xs\<in>model_consequences conjunction_models K"
    have model: "{zs. set zs\<subseteq>(\<Union>ys\<in>K. set ys)}\<in>conjunction_models"
      by (auto simp: conjunction_models_def)
    have support: "K\<subseteq>{zs. set zs\<subseteq>(\<Union>ys\<in>K. set ys)}" by blast
    show "xs\<in>{xs. set xs\<subseteq>(\<Union>ys\<in>K. set ys)}"
      using member model support by (auto simp: model_consequences_def)
  next
    assume "xs\<in>{xs. set xs\<subseteq>(\<Union>ys\<in>K. set ys)}"
    then show "xs\<in>model_consequences conjunction_models K"
      by (auto simp: model_consequences_def conjunction_models_def; blast)
  qed
qed

definition conjunction_methods ::
  "('a list \<Rightarrow> (nat\<times>'a list) set \<Rightarrow> bool) set" where
  "conjunction_methods={R. \<forall>A. inference_sound (\<lambda>xs. set xs\<subseteq>A) R}"

theorem binary_conjunction_complete_candidate:
  "complete_candidate conjunction_methods (inference_capability 2) binary_conjunction_rules"
  apply (rule model_complete_candidate[where M=conjunction_models])
  subgoal
    by (simp add: conjunction_methods_def binary_conjunction_sound)
  subgoal for S T
    by (auto simp: conjunction_methods_def conjunction_models_def)
  subgoal for K
    by (auto simp: binary_conjunction_bounded_closure binary_conjunction_closure conjunction_model_consequences; blast)
  done

theorem conjunction_residual_exact:
  "remaining_obligations (inference_closure (bounded_inferences 2 binary_conjunction_rules) K) H=
    {(i,xs)\<in>H. \<not>set xs\<subseteq>(\<Union>ys\<in>K. set ys)}"
  by (auto simp: remaining_obligations_def binary_conjunction_bounded_closure binary_conjunction_closure)

theorem arbitrary_conjunction_family_complete:
  assumes "\<And>i xs. (i,xs)\<in>H \<Longrightarrow> set xs\<subseteq>A"
  shows "remaining_obligations
    (inference_closure (bounded_inferences 2 binary_conjunction_rules) ((\<lambda>a. [a]) ` A)) H={}"
  using assms by (auto simp: conjunction_residual_exact)

text \<open>
  Finite conjunction is specified for arbitrary element types, arbitrary
  predicates on those elements, and lists of every finite length. Flat
  introduction uses one premise occurrence per list position. Binary
  introduction uses the head and tail; projection supplies the same independent
  element relationship. Repeated elements retain separate introduction sockets.

  Both methods establish exactly the same conditional consequences without a
  local bound. Under two immediate premises, binary introduction retains the
  whole capability while flat introduction does not. The length-three witness
  distinguishes them; the general theorem covers every length.

  Semantic completeness proves that the binary method already covers every
  uniformly sound method for this declared conjunction meaning at that bound.
  This is a stopping proof over an infinite candidate class, not an inference
  from inspecting two examples. It concerns conditional conjunction capability,
  not every possible improvement in proof size, execution cost, other meanings,
  or native presentation. Missing element conditions remain exact residuals.
\<close>

end
