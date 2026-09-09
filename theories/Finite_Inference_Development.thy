theory Finite_Inference_Development
  imports Inference_Development "HOL-Library.While_Combinator"
begin

section \<open>Supplied finite rule tables have a complete evaluation\<close>

definition finite_premise_functional :: "('i\<times>'a) fset \<Rightarrow> bool" where
  "finite_premise_functional H \<longleftrightarrow>
    fBall H (\<lambda>(i,a). fBall H (\<lambda>(j,b). i=j \<longrightarrow> a=b))"

lemma finite_premise_functional_exact:
  "finite_premise_functional H \<longleftrightarrow> single_valued (fset H)"
  by (auto simp: finite_premise_functional_def single_valued_def)

definition finite_inference_formed :: "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> bool" where
  "finite_inference_formed F \<longleftrightarrow> fBall F (\<lambda>(a,H). finite_premise_functional H)"

definition finite_inference_rules ::
  "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a \<Rightarrow> ('i\<times>'a) set \<Rightarrow> bool" where
  "finite_inference_rules F a H \<longleftrightarrow> (\<exists>G. (a,G) |\<in>| F \<and> H=fset G)"

definition finite_inference_round ::
  "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "finite_inference_round F K X=fset K \<union>
    fset (fimage fst (ffilter (\<lambda>(a,H).
      finite_premise_functional H \<and> fset (fimage snd H)\<subseteq>X) F))"

lemma finite_inference_round_exact:
  "finite_inference_round F K X=fset K\<union>inference_consequences (finite_inference_rules F) X"
proof -
  have consequences: "a\<in>inference_consequences (finite_inference_rules F) X \<longleftrightarrow>
      (\<exists>G. (a,G) |\<in>| F \<and> single_valued (fset G) \<and> snd ` fset G\<subseteq>X)" for a
  proof
    assume "a\<in>inference_consequences (finite_inference_rules F) X"
    then show "\<exists>G. (a,G) |\<in>| F \<and> single_valued (fset G) \<and> snd ` fset G\<subseteq>X"
      by (auto simp: inference_consequences_def finite_inference_rules_def rel_ran_image)
  next
    assume "\<exists>G. (a,G) |\<in>| F \<and> single_valued (fset G) \<and> snd ` fset G\<subseteq>X"
    then obtain G where member: "(a,G) |\<in>| F" and formed: "single_valued (fset G)"
      and support: "snd ` fset G\<subseteq>X" by blast
    have rule: "finite_inference_rules F a (fset G)"
      unfolding finite_inference_rules_def by (rule exI[of _ G]) (use member in simp)
    show "a\<in>inference_consequences (finite_inference_rules F) X"
      unfolding inference_consequences_def
      by (rule CollectI, rule exI[of _ "fset G"])
        (use formed support rule in \<open>simp add: rel_ran_image\<close>)
  qed
  show ?thesis
    apply (auto simp: finite_inference_round_def consequences finite_premise_functional_exact
      fimage.rep_eq image_iff split: prod.splits)
    subgoal for x G
      by (drule bspec[where x="(x,G)"]) auto
    done
qed

lemma finite_inference_round_mono:
  "mono (finite_inference_round F K)"
  using inference_consequences_mono
  by (auto simp: mono_def finite_inference_round_exact)

lemma finite_inference_round_bound:
  "finite_inference_round F K X\<subseteq>fset K\<union>fst ` fset F"
  by (auto simp: finite_inference_round_def fimage.rep_eq split: prod.splits)

definition finite_inference_result ::
  "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> 'a set" where
  "finite_inference_result F K=
    while (\<lambda>X. finite_inference_round F K X\<noteq>X) (finite_inference_round F K) {}"

theorem finite_inference_terminates:
  "\<exists>X. while_option (\<lambda>X. finite_inference_round F K X\<noteq>X)
    (finite_inference_round F K) {}=Some X"
  by (rule while_option_finite_subset_Some[OF finite_inference_round_mono,
        where C="fset K\<union>fst ` fset F"])
    (rule finite_inference_round_bound, simp)

theorem finite_inference_result_exact:
  "finite_inference_result F K=inference_closure (finite_inference_rules F) (fset K)"
proof -
  have "lfp (finite_inference_round F K)=finite_inference_result F K"
    unfolding finite_inference_result_def
    by (rule lfp_while[OF finite_inference_round_mono,
          where C="fset K\<union>fst ` fset F"])
      (rule finite_inference_round_bound, simp)
  then show ?thesis by (simp add: inference_closure_def finite_inference_round_exact[abs_def])
qed

definition finite_inference_residual ::
  "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow>
    ('j\<times>'a) fset \<Rightarrow> ('j\<times>'a) fset" where
  "finite_inference_residual F K H=ffilter (\<lambda>(i,a). a\<notin>finite_inference_result F K) H"

theorem finite_inference_residual_exact:
  "fset (finite_inference_residual F K H)=
    remaining_obligations (inference_closure (finite_inference_rules F) (fset K)) (fset H)"
  by (auto simp: finite_inference_residual_def finite_inference_result_exact remaining_obligations_def)

definition finite_inference_evaluation ::
  "('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow>
    ('j\<times>'a) fset \<Rightarrow> ('j\<times>'a) fset \<Rightarrow> bool" where
  "finite_inference_evaluation F K H G \<longleftrightarrow>
    finite_inference_formed F \<and> finite_premise_functional H \<and>
    G=finite_inference_residual F K H"

theorem finite_inference_evaluation_exact:
  "finite_inference_evaluation F K H G \<longleftrightarrow>
    (\<forall>a Q. (a,Q) |\<in>| F \<longrightarrow> single_valued (fset Q)) \<and>
    single_valued (fset H) \<and>
    fset G=remaining_obligations
      (inference_closure (finite_inference_rules F) (fset K)) (fset H)"
  by (auto simp: finite_inference_evaluation_def finite_inference_formed_def
    finite_premise_functional_exact finite_inference_residual_exact[symmetric] fset_inject
    split: prod.splits)

theorem finite_inference_evaluation_sound:
  assumes checked: "finite_inference_evaluation F K H {||}"
    and rules: "inference_sound T (finite_inference_rules F)"
    and known: "fset K\<subseteq>{a. T a}"
  shows "\<forall>i a. (i,a) |\<in>| H \<longrightarrow> T a"
proof -
  have empty: "remaining_obligations
      (inference_closure (finite_inference_rules F) (fset K)) (fset H)={}"
    using checked by (simp add: finite_inference_evaluation_exact)
  have covered: "rel_ran (fset H)\<subseteq>inference_closure (finite_inference_rules F) (fset K)"
    using empty by (simp only: remaining_obligations_empty)
  have valid: "rel_ran (fset H)\<subseteq>{a. T a}"
    by (rule subset_trans[OF covered inference_closure_sound[OF rules known]])
  show ?thesis using valid by (auto simp: rel_ran_def)
qed

theorem malformed_premise_family_is_rejected:
  "\<not>finite_inference_formed
    (fset_of_list [(True,fset_of_list [(0::nat,True),(0,False)])])"
  by (simp add: finite_inference_formed_def finite_premise_functional_def)

theorem a_conjunctive_rule_needs_every_premise:
  defines "F \<equiv> fset_of_list [(True,fset_of_list [(0::nat,False),(1,True)])]"
  shows "True\<notin>finite_inference_result F (fset_of_list [False])"
proof -
  have sound: "inference_sound Not (finite_inference_rules F)"
    by (auto simp: inference_sound_def finite_inference_rules_def F_def rel_ran_def)
  have known: "fset (fset_of_list [False])\<subseteq>{a. Not a}" by simp
  show ?thesis using inference_closure_sound[OF sound known]
    by (auto simp: finite_inference_result_exact)
qed

export_code finite_inference_formed finite_inference_result finite_inference_residual
  finite_inference_evaluation checking SML

text \<open>
  Evaluation checks the whole supplied finite rule table and the complete
  obligation family, then returns exactly the unresolved occurrences. The
  standard least-fixed-point iteration terminates within the finite set of
  supplied seeds and rule conclusions. Its stopping test is actual closure.
  The finite table need not enumerate an independently specified infinite
  method; claiming that additional coverage requires a proof.

  Formation and closure do not validate the semantic truth of a supplied rule.
  The soundness contract and established seed conditions remain necessary for
  semantic discharge. The conjunction counterexample prevents replacing
  multi-premise support by ordinary edge reachability.
\<close>

end
