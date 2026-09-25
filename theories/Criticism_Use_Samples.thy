theory Criticism_Use_Samples
  imports Criticism_Samples Factor_Use_Renaming RRA_Finite_Environment_Construction
    Factor_Finite_Artifact_Enumeration
begin

section \<open>A permutation that sends a list onto a rearrangement of it\<close>

text \<open>
  Two distinct lists over the same elements, of the same length, determine the permutation that sends
  the i-th element of the first to the i-th of the second and is the identity elsewhere: the listed
  rekeying of @{text Finite_List_Rekey} with the argument itself its default. Its inverse is the
  permutation of the two lists exchanged, so it is a bijection.
\<close>

definition listed_permutation :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "listed_permutation xs ys x=listed_rekey xs ys x x"

lemma listed_permutation_at:
  assumes "distinct xs" "distinct ys" "length xs=length ys" "i<length xs"
  shows "listed_permutation xs ys (xs!i)=ys!i"
proof -
  have "listed_permutation xs ys (xs!i)=map (listed_rekey xs ys (xs!i)) xs!i"
    using assms(4) by (simp add: listed_permutation_def)
  then show ?thesis using listed_rekey_properties(2)[OF assms(3,1,2)] by simp
qed

lemma listed_permutation_outside:
  assumes "length xs=length ys" "x\<notin>set xs"
  shows "listed_permutation xs ys x=x"
  using map_of_zip_is_None[OF assms(1), of x] assms(2) by (simp add: listed_permutation_def listed_rekey_def)

lemma listed_permutation_inverse:
  assumes distinct: "distinct xs" "distinct ys" and length: "length xs=length ys" and same: "set xs=set ys"
  shows "listed_permutation ys xs (listed_permutation xs ys x)=x"
proof (cases "x\<in>set xs")
  case True
  then obtain i where i: "i<length xs" "x=xs!i" by (auto simp: in_set_conv_nth)
  have "listed_permutation xs ys x=ys!i" using listed_permutation_at[OF distinct length i(1)] i(2) by simp
  moreover have "listed_permutation ys xs (ys!i)=xs!i"
    using listed_permutation_at[OF distinct(2,1) length[symmetric]] i(1) length by simp
  ultimately show ?thesis using i(2) by simp
next
  case False
  then show ?thesis using same length by (simp add: listed_permutation_outside)
qed

theorem listed_permutation_bij:
  assumes "distinct xs" "distinct ys" "length xs=length ys" "set xs=set ys"
  shows "bij (listed_permutation xs ys)"
  unfolding bij_def
proof
  show "inj (listed_permutation xs ys)"
    by (rule inj_on_inverseI[where g="listed_permutation ys xs"]) (rule listed_permutation_inverse[OF assms])
  show "surj (listed_permutation xs ys)"
    by (rule surjI[where f="listed_permutation ys xs"])
      (rule listed_permutation_inverse[OF assms(2,1) assms(3)[symmetric] assms(4)[symmetric]])
qed

section \<open>The uses of a finite environment, listed\<close>

definition environment_use_list :: "local_address option finite_artifact_environment \<Rightarrow> local_address option list" where
  "environment_use_list C=sorted_list_of_fset (finite_environment_uses C)"

lemma environment_use_list_distinct [simp]: "distinct (environment_use_list C)"
  by (simp add: environment_use_list_def)

lemma environment_use_list_set:
  "set (environment_use_list C)=environment_uses (decode_finite_environment C)"
  by (simp add: environment_use_list_def finite_environment_uses_correct)

section \<open>h1: every use of the environment moved outside it\<close>

text \<open>
  The fresh use map of the environment's uses (@{thm [source] finite_fresh_use_map_exact}) sends a present
  use to a present use behind a prefix of zeros longer than every use it avoids, and None to its
  boundary; the boundary is itself a fresh use, taken by the same map, so None is moved as well. The
  permutation h1 exchanges every use with its image and is the identity elsewhere.
\<close>

definition fresh_boundary :: "local_address option fset \<Rightarrow> local_address option" where
  "fresh_boundary U=finite_fresh_use_map U None (Some [])"

definition fresh_move :: "local_address option fset \<Rightarrow> local_address option \<Rightarrow> local_address option" where
  "fresh_move U=finite_fresh_use_map U (fresh_boundary U)"

lemma fresh_boundary_outside: "fresh_boundary U \<notin> fset U"
proof -
  have "fresh_use_map (fset U) None (Some []) \<notin> insert None (fset U)"
    by (rule fresh_use_map_outside[OF finite_fset])
  then show ?thesis by (simp add: fresh_boundary_def finite_fresh_use_map_exact)
qed

lemma fresh_move_outside: "fresh_move U x \<notin> fset U"
proof (cases x)
  case None
  then show ?thesis using fresh_boundary_outside by (simp add: fresh_move_def)
next
  case (Some a)
  have "fresh_use_map (fset U) (fresh_boundary U) (Some a) \<notin> insert (fresh_boundary U) (fset U)"
    by (rule fresh_use_map_outside[OF finite_fset])
  then show ?thesis by (simp add: fresh_move_def finite_fresh_use_map_exact Some)
qed

lemma fresh_move_inj: "inj (fresh_move U)"
  unfolding fresh_move_def finite_fresh_use_map_exact by (rule fresh_use_map_injective[OF finite_fset])

definition fresh_use_permutation ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address option" where
  "fresh_use_permutation C=(let xs=environment_use_list C; f=fresh_move (fset_of_list xs) in
    listed_permutation (xs@map f xs) (map f xs@xs))"

lemma fresh_use_permutation_parts:
  fixes C defines "xs\<equiv>environment_use_list C" and "f\<equiv>fresh_move (fset_of_list (environment_use_list C))"
  shows "fresh_use_permutation C=listed_permutation (xs@map f xs) (map f xs@xs)"
    and "distinct (xs@map f xs)" and "distinct (map f xs@xs)"
proof -
  have outside: "f x\<notin>set xs" for x
    using fresh_move_outside[of "fset_of_list xs" x] by (simp add: f_def xs_def fset_of_list.rep_eq)
  have mapped: "distinct (map f xs)"
    using inj_on_subset[OF fresh_move_inj subset_UNIV] by (simp add: distinct_map xs_def f_def)
  show "fresh_use_permutation C=listed_permutation (xs@map f xs) (map f xs@xs)"
    by (simp add: fresh_use_permutation_def xs_def f_def Let_def)
  show "distinct (xs@map f xs)" "distinct (map f xs@xs)"
    using mapped outside by (auto simp: xs_def)
qed

theorem fresh_use_permutation_bij: "bij (fresh_use_permutation C)"
  unfolding fresh_use_permutation_parts(1)
  by (rule listed_permutation_bij[OF fresh_use_permutation_parts(2,3)]) auto

theorem fresh_use_permutation_uses:
  assumes use: "u\<in>environment_uses (decode_finite_environment C)"
  shows "fresh_use_permutation C u=fresh_move (fset_of_list (environment_use_list C)) u"
    and "fresh_use_permutation C u\<notin>environment_uses (decode_finite_environment C)"
proof -
  let ?xs="environment_use_list C" and ?f="fresh_move (fset_of_list (environment_use_list C))"
  obtain i where i: "i<length ?xs" "u=?xs!i" using use by (auto simp: environment_use_list_set[symmetric] in_set_conv_nth)
  have "listed_permutation (?xs@map ?f ?xs) (map ?f ?xs@?xs) ((?xs@map ?f ?xs)!i)=(map ?f ?xs@?xs)!i"
    by (rule listed_permutation_at[OF fresh_use_permutation_parts(2,3)]) (use i in auto)
  then show moved: "fresh_use_permutation C u=?f u"
    by (simp add: fresh_use_permutation_parts(1) nth_append i)
  show "fresh_use_permutation C u\<notin>environment_uses (decode_finite_environment C)"
    using fresh_move_outside[of "fset_of_list ?xs" u]
    by (simp add: moved environment_use_list_set[symmetric] fset_of_list.rep_eq)
qed

text \<open>
  On the environment, h1 renames exactly as the fresh use map does
  (@{thm [source] rename_environment_cong}): the abstract route of an injective renaming extended to a
  permutation (@{thm [source] injective_renaming_permutation}) meets this executable one.
\<close>

theorem fresh_use_permutation_renaming:
  assumes formed: "finite_environment_formed C"
  shows "rename_environment (fresh_use_permutation C) (decode_finite_environment C)=
    rename_environment (fresh_use_map (set (environment_use_list C))
      (fresh_boundary (fset_of_list (environment_use_list C)))) (decode_finite_environment C)"
proof -
  have "rename_environment (fresh_use_permutation C) (decode_finite_environment C)=
      rename_environment (fresh_move (fset_of_list (environment_use_list C))) (decode_finite_environment C)"
    by (rule rename_environment_cong[OF formed[unfolded finite_environment_formed_correct]])
      (rule fresh_use_permutation_uses(1))
  then show ?thesis by (simp add: fresh_move_def finite_fresh_use_map_exact fset_of_list.rep_eq)
qed

section \<open>h2: the uses permuted among themselves in the reverse of their listing\<close>

definition reversal_use_permutation ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address option" where
  "reversal_use_permutation C=listed_permutation (environment_use_list C) (rev (environment_use_list C))"

theorem reversal_use_permutation_bij: "bij (reversal_use_permutation C)"
  unfolding reversal_use_permutation_def by (rule listed_permutation_bij) simp_all

theorem reversal_use_permutation_list:
  "map (reversal_use_permutation C) (environment_use_list C)=rev (environment_use_list C)"
  by (rule nth_equalityI) (simp_all add: reversal_use_permutation_def listed_permutation_at)

theorem reversal_use_permutation_uses:
  assumes "u\<in>environment_uses (decode_finite_environment C)"
  shows "reversal_use_permutation C u\<in>environment_uses (decode_finite_environment C)"
proof -
  have "reversal_use_permutation C u\<in>set (map (reversal_use_permutation C) (environment_use_list C))"
    using assms by (simp add: environment_use_list_set)
  then show ?thesis by (simp only: reversal_use_permutation_list set_rev environment_use_list_set)
qed

definition use_permutations ::
    "local_address option finite_artifact_environment \<Rightarrow> (local_address option \<Rightarrow> local_address option) list" where
  "use_permutations C=[fresh_use_permutation C,reversal_use_permutation C]"

lemma use_permutations_bij: "h\<in>set (use_permutations C) \<Longrightarrow> bij h"
  by (auto simp: use_permutations_def fresh_use_permutation_bij reversal_use_permutation_bij)

section \<open>The renamed copy of each argument shape\<close>

text \<open>
  A shape's renamed copy is the shape at the renamed environment, its sites moved by the site action;
  the renamed environment is the finite renaming (@{thm [source] decode_finite_rename_environment}), and
  its presentation is the canonical one of the renamed environment.
\<close>

fun rename_shape :: "(local_address option \<Rightarrow> local_address option) \<Rightarrow> criticism_shape \<Rightarrow> criticism_shape" where
  "rename_shape h Environment_Argument=Environment_Argument"
| "rename_shape h (Site_Argument u r)=Site_Argument (h u) r"
| "rename_shape h (Entry_Argument u r d)=Entry_Argument (h u) r (map_prod h id d)"
| "rename_shape h (Pair_Argument a b)=Pair_Argument (rename_shape h a) (rename_shape h b)"

definition use_pair :: "(local_address option \<Rightarrow> local_address option) \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> criticism_shape \<Rightarrow> finite_factor_term\<times>finite_factor_term" where
  "use_pair h C s=(canonical_argument_value C s,
    canonical_argument_value (finite_rename_environment h C) (rename_shape h s))"

definition use_sample_pairs :: "local_address option finite_artifact_environment \<Rightarrow> criticism_shape list \<Rightarrow>
    (finite_factor_term\<times>finite_factor_term) list" where
  "use_sample_pairs C ss=concat (map (\<lambda>h. map (use_pair h C) ss) (use_permutations C))"

lemma use_sample_pairs_member:
  assumes "(p,q)\<in>set (use_sample_pairs C ss)"
  obtains h s where "h\<in>set (use_permutations C)" "s\<in>set ss" "(p,q)=use_pair h C s"
  using assms by (auto simp: use_sample_pairs_def)

lemma finite_rename_formed:
  assumes "finite_environment_formed C" "inj h"
  shows "finite_environment_formed (finite_rename_environment h C)"
  by (metis assms decode_finite_rename_environment environment_renaming_formed finite_environment_formed_correct)

lemma position_renamed:
  assumes "d\<in>environment_positions E"
  shows "map_prod h id d\<in>environment_positions (rename_environment h E)"
  unfolding environment_positions_renaming by (rule imageI[OF assms])

lemma site_position_renamed:
  assumes "(u,r)\<in>environment_positions E"
  shows "(h u,r)\<in>environment_positions (rename_environment h E)"
  using position_renamed[OF assms, of h] by (simp only: map_prod_simp id_apply)

lemma argument_positions_renamed:
  "argument_positions E s \<Longrightarrow> argument_positions (rename_environment h E) (rename_shape h s)"
proof (induction s)
  case Environment_Argument
  then show ?case by simp
next
  case (Site_Argument u r)
  then show ?case by (simp only: argument_positions.simps rename_shape.simps) (rule site_position_renamed)
next
  case (Entry_Argument u r d)
  then show ?case
    by (simp only: argument_positions.simps rename_shape.simps) (blast intro: site_position_renamed position_renamed)
next
  case (Pair_Argument a b)
  then show ?case by (simp only: argument_positions.simps rename_shape.simps)
qed

lemma use_pair_arguments:
  assumes formed: "finite_environment_formed C"
    and positions: "argument_positions (decode_finite_environment C) s" and permutation: "bij h"
  shows "argument_presents s (decode_finite_environment C) (decode_finite_term (fst (use_pair h C s)))"
    "argument_presents (rename_shape h s) (rename_environment h (decode_finite_environment C))
      (decode_finite_term (snd (use_pair h C s)))"
proof -
  have renamed: "finite_environment_formed (finite_rename_environment h C)"
    by (rule finite_rename_formed[OF formed bij_is_inj[OF permutation]])
  have moved: "argument_positions (decode_finite_environment (finite_rename_environment h C)) (rename_shape h s)"
    using argument_positions_renamed[OF positions] by simp
  show "argument_presents s (decode_finite_environment C) (decode_finite_term (fst (use_pair h C s)))"
    using argument_values_present_one_subject(1)[OF formed positions] by (simp add: use_pair_def)
  show "argument_presents (rename_shape h s) (rename_environment h (decode_finite_environment C))
      (decode_finite_term (snd (use_pair h C s)))"
    using argument_values_present_one_subject(1)[OF renamed moved] by (simp add: use_pair_def)
qed

text \<open>
  Each pair of a term and its renamed copy is a renaming correspondence of its shape's class at the
  permutation, under the action @{text Factor_Use_Renaming} states on that class.
\<close>

theorem use_pair_environment:
  assumes "finite_environment_formed C" "bij h"
  shows "renaming_correspondence environment_value_presents rename_environment h
    (decode_finite_term (fst (use_pair h C Environment_Argument)))
    (decode_finite_term (snd (use_pair h C Environment_Argument)))"
  using use_pair_arguments[OF assms(1) _ assms(2), of Environment_Argument]
  unfolding renaming_correspondence_def by auto

theorem use_pair_site:
  assumes formed: "finite_environment_formed C"
    and site: "(u,r)\<in>environment_positions (decode_finite_environment C)" and permutation: "bij h"
  shows "renaming_correspondence (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
    site_context_renaming h (decode_finite_term (fst (use_pair h C (Site_Argument u r))))
    (decode_finite_term (snd (use_pair h C (Site_Argument u r))))"
  using use_pair_arguments[OF formed _ permutation, of "Site_Argument u r"] site
  unfolding renaming_correspondence_def
  by (intro exI[of _ "(decode_finite_environment C,(u,r))"]) simp

theorem use_pair_entry:
  assumes formed: "finite_environment_formed C"
    and site: "(u,r)\<in>environment_positions (decode_finite_environment C)"
    and entry: "d\<in>environment_positions (decode_finite_environment C)" and permutation: "bij h"
  shows "renaming_correspondence program_entry_presents program_entry_renaming h
    (decode_finite_term (fst (use_pair h C (Entry_Argument u r d))))
    (decode_finite_term (snd (use_pair h C (Entry_Argument u r d))))"
  using use_pair_arguments[OF formed _ permutation, of "Entry_Argument u r d"] site entry
  unfolding renaming_correspondence_def
  by (intro exI[of _ "((decode_finite_environment C,(u,r)),d)"]) simp

theorem use_pair_product:
  assumes "renaming_correspondence R actL h p p'" "renaming_correspondence S actR h q q'"
  shows "renaming_correspondence (factor_pair_presents R S) (product_action actL actR) h
    (Pair_Term p q) (Pair_Term p' q')"
proof -
  obtain a where a: "R a p" "R (actL h a) p'" using assms(1) by (auto simp: renaming_correspondence_def)
  obtain b where b: "S b q" "S (actR h b) q'" using assms(2) by (auto simp: renaming_correspondence_def)
  show ?thesis unfolding renaming_correspondence_def
    by (intro exI[of _ "(a,b)"]) (simp add: a b)
qed

section \<open>The renamed package is not read again\<close>

text \<open>
  A package at a renamed use of the renamed environment is the original package relocated, and its
  meaning at a renamed entry is the original's at the entry, at the same term
  (@{thm [source] native_package_use_renaming}, @{thm [source] native_package_renamed_meaning}). So the
  use sample evaluates the original program at the entry on a term and on its renamed copy.
\<close>

theorem use_sample_renamed_package:
  assumes formed: "environment_formed E" and permutation: "bij h" and package: "native_package_at E u r P"
    and renamed: "native_package_at (rename_environment h E) (h u) r Q"
  shows "(map_prod h id d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  obtain P' where P': "native_package_at E u r P'" "Q=rename_system (map_prod h id) P'"
    using renamed native_package_use_renaming[OF formed permutation] by blast
  have "P'=P" by (rule native_package_unique[OF P'(1) package])
  then show ?thesis
    using native_package_renamed_meaning[OF package bij_is_inj[OF permutation]] P'(2) by simp
qed

section \<open>A recorded row at a use pair refutes the entry's use equivariance\<close>

text \<open>
  A row recorded at a pair standing in a renaming correspondence at a permutation refutes
  @{const renaming_equivariant} of the entry's relation at the class's use action, the clause the
  verification request asks the answer to prove (@{thm [source] criticism_refutes}). Only the row's own
  pair is asked to correspond, so a sample may mix shapes.
\<close>

theorem use_row_refutes:
  assumes presented: "presentation_class R D X" and action: "renaming_action bij act D"
    and forward: "(c,c')\<in>set ps \<Longrightarrow>
      \<exists>h. bij h \<and> renaming_correspondence R act h (decode_finite_term c) (decode_finite_term c')"
    and backward: "(c',c)\<in>set ps \<Longrightarrow>
      \<exists>h. bij h \<and> renaming_correspondence R act h (decode_finite_term c') (decode_finite_term c)"
    and table: "criticism_table P ds ps=Some A" and row: "(c,c',d,w) |\<in>| criticism_record ds ps A"
  shows "\<not>(\<exists>Q. (\<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate R Q t) \<and>
    renaming_equivariant bij act D Q)"
proof -
  have paired: "criticism_paired ps c c'"
    and holds: "(d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P)"
    and fails: "(d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system P)"
    using row by (simp_all add: criticism_record_meaning[OF table])
  have differ: "((d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P)) \<noteq>
      ((d,decode_finite_term c')\<in>positive_meaning (decode_finite_system P))"
    using holds fails by simp
  from paired consider (forward) "(c,c')\<in>set ps" | (backward) "(c',c)\<in>set ps"
    by (auto simp: criticism_paired_def)
  then show ?thesis
  proof cases
    case forward
    then obtain h where h: "bij h" "renaming_correspondence R act h (decode_finite_term c) (decode_finite_term c')"
      using assms(3) by blast
    show ?thesis by (rule criticism_refutes[OF presented action h differ])
  next
    case backward
    then obtain h where h: "bij h" "renaming_correspondence R act h (decode_finite_term c') (decode_finite_term c)"
      using assms(4) by blast
    show ?thesis by (rule criticism_refutes[OF presented action h not_sym[OF differ]])
  qed
qed


corollary use_sample_site_refutes:
  assumes formed: "finite_environment_formed C"
    and sites: "\<forall>s\<in>set ss. \<exists>u r. s=Site_Argument u r \<and> (u,r)\<in>environment_positions (decode_finite_environment C)"
    and table: "criticism_table P ds (use_sample_pairs C ss)=Some A"
    and row: "(c,c',d,w) |\<in>| criticism_record ds (use_sample_pairs C ss) A"
  shows "\<not>(\<exists>Q. (\<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      presented_predicate (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t) Q t) \<and>
    renaming_equivariant bij site_context_renaming site_context_formed Q)"
proof -
  have pairs: "\<exists>h. bij h \<and> renaming_correspondence (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      site_context_renaming h (decode_finite_term p) (decode_finite_term q)"
    if member: "(p,q)\<in>set (use_sample_pairs C ss)" for p q
  proof -
    obtain h s where h: "h\<in>set (use_permutations C)" and s: "s\<in>set ss" and pq: "(p,q)=use_pair h C s"
      using use_sample_pairs_member[OF member] by blast
    obtain u r where site: "s=Site_Argument u r" "(u,r)\<in>environment_positions (decode_finite_environment C)"
      using sites s by blast
    have eq: "use_pair h C (Site_Argument u r)=(p,q)" using pq site(1) by simp
    have "renaming_correspondence (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
        site_context_renaming h (decode_finite_term (fst (use_pair h C (Site_Argument u r))))
        (decode_finite_term (snd (use_pair h C (Site_Argument u r))))"
      by (rule use_pair_site[OF formed site(2) use_permutations_bij[OF h]])
    then show ?thesis using use_permutations_bij[OF h] unfolding eq fst_conv snd_conv by blast
  qed
  show ?thesis
    by (rule use_row_refutes[OF site_presentations.presentation_class_axioms site_context_renaming_action
      pairs pairs table row])
qed

corollary use_sample_entry_refutes:
  assumes formed: "finite_environment_formed C"
    and entries: "\<forall>s\<in>set ss. \<exists>u r d. s=Entry_Argument u r d \<and>
      (u,r)\<in>environment_positions (decode_finite_environment C) \<and> d\<in>environment_positions (decode_finite_environment C)"
    and table: "criticism_table P ds (use_sample_pairs C ss)=Some A"
    and row: "(c,c',d,w) |\<in>| criticism_record ds (use_sample_pairs C ss) A"
  shows "\<not>(\<exists>Q. (\<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      presented_predicate program_entry_presents Q t) \<and>
    renaming_equivariant bij program_entry_renaming program_entry_context_formed Q)"
proof -
  have pairs: "\<exists>h. bij h \<and> renaming_correspondence program_entry_presents program_entry_renaming h
      (decode_finite_term p) (decode_finite_term q)"
    if member: "(p,q)\<in>set (use_sample_pairs C ss)" for p q
  proof -
    obtain h s where h: "h\<in>set (use_permutations C)" and s: "s\<in>set ss" and pq: "(p,q)=use_pair h C s"
      using use_sample_pairs_member[OF member] by blast
    obtain u r e where entry: "s=Entry_Argument u r e" "(u,r)\<in>environment_positions (decode_finite_environment C)"
        "e\<in>environment_positions (decode_finite_environment C)"
      using entries s by blast
    have "renaming_correspondence program_entry_presents program_entry_renaming h
        (decode_finite_term (fst (use_pair h C (Entry_Argument u r e))))
        (decode_finite_term (snd (use_pair h C (Entry_Argument u r e))))"
      by (rule use_pair_entry[OF formed entry(2,3) use_permutations_bij[OF h]])
    moreover have eq: "use_pair h C (Entry_Argument u r e)=(p,q)" using pq entry(1) by simp
    ultimately show ?thesis using use_permutations_bij[OF h] unfolding eq fst_conv snd_conv by blast
  qed
  show ?thesis
    by (rule use_row_refutes[OF program_entry_presentation_class program_entry_renaming_action pairs pairs table row])
qed

section \<open>Controls\<close>

text \<open>
  Two uses, @{term "Some [0]"} and @{term "Some [1]"}, each holding an artifact with one address. One entry
  compares the use of its argument's site with the use literal of @{term "Some [0]"}, the unary word
  that states only the empty payload: it records a row at the site's pair at h1, and at h2, which
  exchanges the two uses. The other compares two uses of a program entry value for equality by a
  repeated variable: no row at either permutation. A one-use environment at None shows None moved.
\<close>

definition use_control_artifact :: finite_exact_artifact where
  "use_control_artifact=finite_enumerated_artifact [[]] [] [] []"

definition use_control_environment :: "local_address option finite_artifact_environment" where
  "use_control_environment=finite_enumerated_environment
    [(Some [0],use_control_artifact),(Some [1],use_control_artifact)] []"

definition use_control_none_environment :: "local_address option finite_artifact_environment" where
  "use_control_none_environment=finite_enumerated_environment [(None,use_control_artifact)] []"

definition use_control_site :: criticism_shape where
  "use_control_site=Site_Argument (Some [0]) []"

definition use_control_entry :: criticism_shape where
  "use_control_entry=Entry_Argument (Some [1]) [] (Some [1],[])"

definition use_control_literal_entry :: "local_address option definition_site" where
  "use_control_literal_entry=(Some [4,3,7],[0])"

definition use_control_equality_entry :: "local_address option definition_site" where
  "use_control_equality_entry=(Some [4,3,7],[1])"

definition use_control_literal :: finite_factor_term where
  "use_control_literal=the (finite_self_contained_term (use_data_term (Some [0])))"

definition use_control_program :: "local_address option finite_native_system" where
  "use_control_program=finite_rule_program
    [(use_control_literal_entry,[([0],finite_native_rule (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (finite_exact_term_pattern use_control_literal) (native_var 1))) [])]),
     (use_control_equality_entry,[([0],finite_native_rule (Finite_Pattern_Pair
        (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
        (Finite_Pattern_Pair (native_var 1) (native_var 3))) [])])]"

definition use_control_pairs :: "(finite_factor_term\<times>finite_factor_term) list" where
  "use_control_pairs=use_sample_pairs use_control_environment [use_control_site,use_control_entry]"

definition use_control_reading :: "unit \<Rightarrow> bool list" where
  "use_control_reading _=(let C=use_control_environment; xs=environment_use_list C;
      h1=fresh_use_permutation C; h2=reversal_use_permutation C;
      ds=[use_control_literal_entry,use_control_equality_entry]; ps=use_control_pairs;
      s1=use_pair h1 C use_control_site; s2=use_pair h2 C use_control_site;
      e1=use_pair h1 C use_control_entry; e2=use_pair h2 C use_control_entry in
    [xs=[Some [0],Some [1]], list_all (\<lambda>u. h1 u\<notin>set xs \<and> h1 (h1 u)=u) xs, map h2 xs=rev xs,
     fresh_use_permutation use_control_none_environment None\<noteq>None]@
    (case criticism_table use_control_program ds ps of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [criticism_record ds ps A=
          {|(fst s1,snd s1,use_control_literal_entry,()),(fst s2,snd s2,use_control_literal_entry,()),
            (snd e2,fst e2,use_control_literal_entry,())|},
        criticism_refuted ds ps A={|use_control_literal_entry|},
        (use_control_equality_entry,fst e1) |\<in>| A,(use_control_equality_entry,snd e1) |\<in>| A,
        (use_control_equality_entry,snd e2) |\<in>| A]))"

text \<open>
  The reading is executed in @{text Factor_Finite_Site_Value_Reader_Controls}, one conjunct of the one
  evaluation of the native evaluator's controls; a library theory runs no evaluation.
\<close>

end
