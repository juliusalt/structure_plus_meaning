theory Inference_Embeddings
  imports Inference_Abstraction Finite_Inference_Development
begin

section \<open>An injective value presentation preserves the complete inference account\<close>

lemma map_relation_values_range:
  "rel_ran (map_relation_values f H)=f ` rel_ran H"
  by (auto simp: rel_ran_def)

lemma finite_relation_values_support:
  assumes "inj f"
  shows "rel_ran (map_relation_values f (fset H))\<subseteq>image f (fset X) \<longleftrightarrow>
    fimage snd H |\<subseteq>| X"
  by (simp only: rel_ran_image map_relation_values_range[unfolded rel_ran_image] inj_image_subset_iff[OF assms]
    less_eq_fset.rep_eq fimage.rep_eq rel_ran_image)

definition embedded_inferences where
  "embedded_inferences f R b H \<longleftrightarrow>
    (\<exists>a G. b=f a \<and> finite G \<and> single_valued G \<and> R a G \<and> H=map_relation_values f G)"

theorem embedded_inference_closure:
  assumes injective: "inj f"
  shows "inference_closure (embedded_inferences f R) (f ` K)=f ` inference_closure R K"
proof (rule subset_antisym)
  have reflect: "finite_inference (embedded_inferences f R) (f ` K) b \<Longrightarrow>
    b\<in>f ` inference_closure R K" for b
  proof (induction rule: finite_inference.induct)
    case (seed b)
    then show ?case using inference_closure_seed[of K R] by blast
  next
    case (step H b)
    obtain a G where fields: "b=f a" "finite G" "single_valued G" "R a G"
      "H=map_relation_values f G"
      using step.hyps(3) by (auto simp: embedded_inferences_def)
    have support: "rel_ran G\<subseteq>inference_closure R K"
    proof
      fix x assume member: "x\<in>rel_ran G"
      have "f x\<in>rel_ran H" using member by (simp only: fields(5) map_relation_values_range; blast)
      then have "f x\<in>f ` inference_closure R K" using step.IH by blast
      then show "x\<in>inference_closure R K" using injective by (auto dest: injD)
    qed
    have "a\<in>inference_closure R K"
      by (rule inference_closure_step[OF fields(2-4) support])
    then show ?case by (simp only: fields(1); blast)
  qed
  show "inference_closure (embedded_inferences f R) (f ` K)\<subseteq>f ` inference_closure R K"
  proof
    fix b assume "b\<in>inference_closure (embedded_inferences f R) (f ` K)"
    then show "b\<in>f ` inference_closure R K"
      by (rule finite_inference_complete[THEN reflect])
  qed
next
  show "f ` inference_closure R K\<subseteq>inference_closure (embedded_inferences f R) (f ` K)"
    by (rule inference_closure_projection) (auto simp: embedded_inferences_def)
qed

theorem finite_inference_result_embedding:
  assumes "inj f"
  shows "f ` finite_inference_result F K=
    inference_closure (embedded_inferences f (finite_inference_rules F)) (f ` fset K)"
  by (simp only: finite_inference_result_exact embedded_inference_closure[OF assms])

section \<open>A finite rule table has the same embedding\<close>

definition finite_embedded_inferences ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset \<Rightarrow> ('b\<times>('i\<times>'b) fset) fset" where
  "finite_embedded_inferences f F=fimage (\<lambda>(a,H). (f a,fimage (\<lambda>(i,b). (i,f b)) H)) F"

lemma finite_embedded_premises:
  "fset (fimage (\<lambda>(i,b). (i,f b)) H)=map_relation_values f (fset H)"
  by (auto simp: map_relation_values_def fimage.rep_eq)

theorem finite_embedded_inference_rules:
  assumes formed: "finite_inference_formed F"
  shows "finite_inference_rules (finite_embedded_inferences f F)=embedded_inferences f (finite_inference_rules F)"
proof (intro ext iffI)
  fix b H assume "finite_inference_rules (finite_embedded_inferences f F) b H"
  then obtain a K where member: "(a,K) |\<in>| F" and image: "b=f a"
    and mapped: "H=map_relation_values f (fset K)"
    by (auto simp: finite_inference_rules_def finite_embedded_inferences_def
      map_relation_values_def fimage.rep_eq)
  have functional: "single_valued (fset K)"
    using formed member by (auto simp: finite_inference_formed_def finite_premise_functional_exact)
  show "embedded_inferences f (finite_inference_rules F) b H"
    unfolding embedded_inferences_def
    by (rule exI[of _ a], rule exI[of _ "fset K"])
      (use member image mapped functional in \<open>auto simp: finite_inference_rules_def\<close>)
next
  fix b H assume "embedded_inferences f (finite_inference_rules F) b H"
  then obtain a K where member: "(a,K) |\<in>| F" and image: "b=f a"
    and mapped: "H=map_relation_values f (fset K)"
    by (auto simp: embedded_inferences_def finite_inference_rules_def)
  show "finite_inference_rules (finite_embedded_inferences f F) b H"
    unfolding finite_inference_rules_def
    by (rule exI[of _ "fimage (\<lambda>(i,x). (i,f x)) K"])
      (use member image mapped in \<open>auto simp: finite_embedded_inferences_def
        map_relation_values_def fimage.rep_eq\<close>)
qed

theorem finite_inference_result_renaming:
  assumes injective: "inj f" and formed: "finite_inference_formed F"
  shows "finite_inference_result (finite_embedded_inferences f F) (fimage f K)=f ` finite_inference_result F K"
  by (simp only: finite_inference_result_exact finite_embedded_inference_rules[OF formed]
    embedded_inference_closure[OF injective] fimage.rep_eq)

text \<open>
  The finite table of a renamed subject holds exactly the mapped rules of the original
  table, so the existing terminating evaluator computes the image of the original least
  closure. Formation of the supplied table is what makes the two rule readings agree;
  injectivity is what permits the reflection.
\<close>

text \<open>
  Every premise occurrence and the seed boundary is mapped. Injectivity is
  what permits reflection of a derivation. The result concerns the original
  least closure and uses the existing terminating finite evaluator unchanged.
\<close>

end
