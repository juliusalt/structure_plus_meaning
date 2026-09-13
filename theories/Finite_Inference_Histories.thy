theory Finite_Inference_Histories
  imports Finite_Inference_Development Finite_Iteration_Histories Finite_Set_Transformations
begin

section \<open>The complete finite closure retains its actual preceding states\<close>

definition finite_inference_next where
  "finite_inference_next F K X=K |\<union>| fimage fst (finite_inference_enabled F (fset X))"

lemma finite_inference_next_correct:
  "fset (finite_inference_next F K X)=finite_inference_round F K (fset X)"
  by (simp add: finite_inference_next_def finite_inference_round_def)

lemma finite_inference_next_mono:
  "X |\<subseteq>| Y \<Longrightarrow> finite_inference_next F K X |\<subseteq>| finite_inference_next F K Y"
  using finite_inference_round_mono[of F K]
  by (auto simp: less_eq_fset.rep_eq finite_inference_next_correct mono_def)

lemma finite_inference_next_fixed:
  "(finite_inference_next F K X=X)=(finite_inference_round F K (fset X)=fset X)"
  by (simp only: finite_inference_next_correct[symmetric] fset_inject)

lemma finite_inference_next_test:
  "(finite_inference_next F K X\<noteq>X)=(finite_inference_round F K (fset X)\<noteq>fset X)"
  by (simp only: finite_inference_next_fixed)

lemma finite_inference_next_projection:
  "map_option fset (while_option (\<lambda>X. finite_inference_next F K X\<noteq>X)
    (finite_inference_next F K) {||})=
    while_option (\<lambda>X. finite_inference_round F K X\<noteq>X) (finite_inference_round F K) {}"
proof -
  have projected: "map_option fset (while_option (\<lambda>X. finite_inference_next F K X\<noteq>X)
      (finite_inference_next F K) {||})=
      while_option (\<lambda>X. finite_inference_round F K X\<noteq>X) (finite_inference_round F K) (fset {||})"
    using while_option_commute[where f=fset and
      b="\<lambda>X. finite_inference_next F K X\<noteq>X" and c="finite_inference_next F K"
      and b'="\<lambda>X. finite_inference_round F K X\<noteq>X" and c'="finite_inference_round F K" and s="{||}"]
    by (simp only: finite_inference_next_test finite_inference_next_correct)
  show ?thesis using projected by simp
qed

definition finite_inference_history where
  "finite_inference_history F K=while_history (\<lambda>X. finite_inference_next F K X\<noteq>X)
    (finite_inference_next F K) {||}"

lemma finite_inference_history_projection:
  "map_option (\<lambda>(A,Xs). fset A) (finite_inference_history F K)=
    while_option (\<lambda>X. finite_inference_round F K X\<noteq>X) (finite_inference_round F K) {}"
proof -
  have composition: "map_option (\<lambda>(A,Xs). fset A) (finite_inference_history F K)=
      map_option fset (map_option fst (finite_inference_history F K))"
    by (simp only: option.map_comp comp_def split_def)
  show ?thesis
    by (subst composition)
      (simp only: finite_inference_history_def while_history_projection finite_inference_next_projection)
qed

theorem finite_inference_history_total:
  "\<exists>A Xs. finite_inference_history F K=Some (A,Xs)"
proof -
  have projected: "\<exists>A. map_option (\<lambda>(A,Xs). fset A) (finite_inference_history F K)=Some A"
    by (simp only: finite_inference_history_projection; rule finite_inference_terminates)
  then show ?thesis by (simp only: map_option_eq_Some split_paired_Ex; blast)
qed

theorem finite_inference_history_correct:
  assumes result: "finite_inference_history F K=Some (A,Xs)"
  shows "fset A=inference_closure (finite_inference_rules F) (fset K)"
    "iteration_prefix (\<lambda>X. finite_inference_next F K X\<noteq>X) (finite_inference_next F K) {||} Xs A"
    "finite_inference_next F K A=A"
proof -
  have projected: "while_option (\<lambda>X. finite_inference_round F K X\<noteq>X)
      (finite_inference_round F K) {}=Some (fset A)"
    using finite_inference_history_projection[of F K] result by simp
  have "finite_inference_result F K=fset A"
    by (simp only: finite_inference_result_def while_def projected option.sel)
  then show "fset A=inference_closure (finite_inference_rules F) (fset K)"
    by (simp only: finite_inference_result_exact)
  show "iteration_prefix (\<lambda>X. finite_inference_next F K X\<noteq>X) (finite_inference_next F K) {||} Xs A"
    "finite_inference_next F K A=A"
    using while_history_correct[OF result[unfolded finite_inference_history_def]] by simp_all
qed

lemma finite_inference_history_bound:
  assumes result: "finite_inference_history F K=Some (A,Xs)"
  shows "fset A\<subseteq>fset K\<union>image fst (fset F)"
    "\<forall>X\<in>set Xs. fset X\<subseteq>fset K\<union>image fst (fset F)"
  using iteration_prefix_invariant[where I="\<lambda>X. fset X\<subseteq>fset K\<union>image fst (fset F)",
    OF _ _ finite_inference_history_correct(2)[OF result]]
    finite_inference_round_bound[of F K]
  by (auto simp: finite_inference_next_correct)

lemma finite_inference_history_states_subset:
  assumes result: "finite_inference_history F K=Some (A,Xs)"
  shows "\<forall>X\<in>set Xs. X |\<subseteq>| A"
proof -
  have fixed: "finite_inference_next F K A=A"
    by (rule finite_inference_history_correct(3)[OF result])
  have step: "finite_inference_next F K X |\<subseteq>| A" if "X |\<subseteq>| A" for X
    using finite_inference_next_mono[OF that, of F K] by (simp only: fixed)
  have initial: "{||} |\<subseteq>| A" by simp
  have stable: "finite_inference_next F K X |\<subseteq>| A"
    if "X |\<subseteq>| A" "finite_inference_next F K X\<noteq>X" for X
    by (rule step[OF that(1)])
  show ?thesis
    using iteration_prefix_invariant[where I="\<lambda>X. X |\<subseteq>| A",
      OF initial stable finite_inference_history_correct(2)[OF result]]
    by blast
qed

definition finite_inference_witnesses where
  "finite_inference_witnesses project F X=
    ffilter (\<lambda>w. project w |\<in>| finite_inference_enabled (fimage project F) (fset X)) F"

lemma finite_inference_witness_member:
  "w |\<in>| finite_inference_witnesses project F X \<longleftrightarrow>
    w |\<in>| F \<and> (case project w of (q,H) \<Rightarrow>
      finite_premise_functional H \<and> fimage snd H |\<subseteq>| X)"
  by (auto simp: finite_inference_witnesses_def finite_inference_enabled_def
    less_eq_fset.rep_eq split: prod.splits; force)

lemma finite_inference_witness_projection:
  "fimage project (finite_inference_witnesses project F X)=
    finite_inference_enabled (fimage project F) (fset X)"
  unfolding finite_inference_witnesses_def
  by (rule finite_image_restriction) (auto simp: finite_inference_enabled_def)

definition finite_inference_witness_review where
  "finite_inference_witness_review project F Hs=map (\<lambda>(X,W).
    (X,W |-| finite_inference_witnesses project F X,
      finite_inference_witnesses project F X |-| W)) Hs"

definition finite_inference_witness_review_holds where
  "finite_inference_witness_review_holds rows=
    list_all (\<lambda>(X,extra,missing). extra={||} \<and> missing={||}) rows"

lemma finite_inference_witness_review_exact:
  "finite_inference_witness_review_holds (finite_inference_witness_review project F Hs) \<longleftrightarrow>
    list_all (\<lambda>(X,W). W=finite_inference_witnesses project F X) Hs"
  by (auto simp: finite_inference_witness_review_def finite_inference_witness_review_holds_def
    finite_differences_empty list_all_iff comp_def split_def intro: order_antisym)

definition finite_inference_labelled_history where
  "finite_inference_labelled_history project F K=map_option (\<lambda>(A,Xs).
    (A,map (\<lambda>X. (X,finite_inference_witnesses project F X)) Xs))
      (finite_inference_history (fimage project F) K)"

lemma finite_inference_labelled_history_conditions:
  "finite_inference_labelled_history project F K=Some (A,Hs) \<longleftrightarrow>
    (\<exists>Xs. finite_inference_history (fimage project F) K=Some (A,Xs) \<and>
      Hs=map (\<lambda>X. (X,finite_inference_witnesses project F X)) Xs)"
  by (auto simp: finite_inference_labelled_history_def split: option.splits prod.splits)

lemma finite_inference_labelled_history_total:
  "\<exists>A Hs. finite_inference_labelled_history project F K=Some (A,Hs)"
  using finite_inference_history_total[of "fimage project F" K]
  by (auto simp: finite_inference_labelled_history_conditions)

definition finite_inference_activation_history where
  "finite_inference_activation_history F K=finite_inference_labelled_history id F K"

definition finite_inference_labelled_history_valid where
  "finite_inference_labelled_history_valid project F K A Hs=(
    iteration_prefix (\<lambda>X. finite_inference_next (fimage project F) K X\<noteq>X)
      (finite_inference_next (fimage project F) K) {||} (map fst Hs) A \<and>
    finite_inference_next (fimage project F) K A=A \<and>
    list_all (\<lambda>(X,W). W=finite_inference_witnesses project F X) Hs)"

theorem finite_inference_labelled_history_valid:
  assumes result: "finite_inference_labelled_history project F K=Some (A,Hs)"
  shows "finite_inference_labelled_history_valid project F K A Hs"
proof -
  obtain Xs where history: "finite_inference_history (fimage project F) K=Some (A,Xs)"
    and labels: "Hs=map (\<lambda>X. (X,finite_inference_witnesses project F X)) Xs"
    using result by (simp only: finite_inference_labelled_history_conditions; blast)
  show ?thesis
    using finite_inference_history_correct(2,3)[OF history]
    by (simp add: finite_inference_labelled_history_valid_def labels comp_def list_all_iff)
qed

export_code finite_inference_history finite_inference_labelled_history finite_inference_activation_history
  finite_inference_witness_review finite_inference_witness_review_holds checking SML

text \<open>
  The retained sequence contains the complete state before every taken step.
  Its final state is the original inference closure. Each attached rule is
  selected from the actual supplied rule table, with its entire premise family.
  An application-level client must retain the original clause and binding
  witnesses as well. A native proof graph still requires its own construction.
\<close>

end
