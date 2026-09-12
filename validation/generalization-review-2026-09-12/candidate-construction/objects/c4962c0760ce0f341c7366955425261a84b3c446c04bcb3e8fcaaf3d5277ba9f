theory Factor_Term_Sequence_Operations
  imports Factor_Term_Sequence_Clauses Factor_Finite_Terms Factor_Coordinate_Values
begin

section \<open>Local constructor equations determine both whole folds\<close>

lemma term_pair_step_exact:
  "(232,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>x z. term_formed x \<and> term_formed z \<and>
      t=collection_join_argument x z (Pair_Term x z))"
proof -
  have valuation: "(232,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
        t=collection_join_argument (h 0) (h 1) (Pair_Term (h 0) (h 1)))"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: term_sequence_clause_family_def term_pair_step_schema_def
        schema_variables_def term_sequence_call)
  show ?thesis
  proof
    assume "(232,t)\<in>positive_meaning term_sequence_system"
    then show "\<exists>x z. term_formed x \<and> term_formed z \<and>
        t=collection_join_argument x z (Pair_Term x z)" by (simp only: valuation; blast)
  next
    assume "\<exists>x z. term_formed x \<and> term_formed z \<and>
        t=collection_join_argument x z (Pair_Term x z)"
    then obtain x z where fields: "term_formed x" "term_formed z"
      "t=collection_join_argument x z (Pair_Term x z)" by blast
    let ?h="\<lambda>i::nat. if i=0 then x else z"
    show "(232,t)\<in>positive_meaning term_sequence_system"
      by (simp only: valuation; rule exI[of _ ?h]) (use fields in auto)
  qed
qed

lemma term_pair_step_at:
  "(232,collection_join_argument x z y)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    term_formed x \<and> term_formed z \<and> y=Pair_Term x z"
  by (auto simp: term_pair_step_exact)

lemma term_count_step_exact:
  "(234,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>x z. term_formed x \<and> term_formed z \<and>
      t=collection_join_argument x z (Pair_Term (Payload_Term []) z))"
proof -
  have valuation: "(234,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
        t=collection_join_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (h 1)))"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: term_sequence_clause_family_def term_count_step_schema_def
        schema_variables_def term_sequence_call octets_formed_def)
  show ?thesis
  proof
    assume "(234,t)\<in>positive_meaning term_sequence_system"
    then show "\<exists>x z. term_formed x \<and> term_formed z \<and>
        t=collection_join_argument x z (Pair_Term (Payload_Term []) z)" by (simp only: valuation; blast)
  next
    assume "\<exists>x z. term_formed x \<and> term_formed z \<and>
        t=collection_join_argument x z (Pair_Term (Payload_Term []) z)"
    then obtain x z where fields: "term_formed x" "term_formed z"
      "t=collection_join_argument x z (Pair_Term (Payload_Term []) z)" by blast
    let ?h="\<lambda>i::nat. if i=0 then x else z"
    show "(234,t)\<in>positive_meaning term_sequence_system"
      by (simp only: valuation; rule exI[of _ ?h]) (use fields in auto)
  qed
qed

lemma term_count_step_at:
  "(234,collection_join_argument x z y)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    term_formed x \<and> term_formed z \<and> y=Pair_Term (Payload_Term []) z"
  by (auto simp: term_count_step_exact)

lemma term_sequence_fold_at_seed:
  assumes seed: "term_formed z"
  shows "(233,collection_join_argument z p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs \<and> q=foldr Pair_Term xs z)"
proof -
  have exact: "(233,collection_join_argument (id z) p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term (map id xs) \<and>
        q=id (foldr Pair_Term xs z))"
    by (rule term_pair_fold.encoded[where E=term_formed and D=term_formed])
      (use seed in \<open>auto simp: term_pair_step_at\<close>)
  show ?thesis using exact by simp
qed

theorem term_sequence_fold_exact:
  "(233,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs) (foldr Pair_Term xs z))"
proof
  assume holds: "(233,t)\<in>positive_meaning term_sequence_system"
  obtain z p q where shape: "t=collection_join_argument z p q" and seed: "term_formed z"
    using term_pair_fold.sound[OF holds] by blast
  obtain xs where fields: "\<forall>x\<in>set xs. term_formed x" "p=data_list_term xs" "q=foldr Pair_Term xs z"
    using holds term_sequence_fold_at_seed[OF seed, of p q] shape by blast
  show "\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs) (foldr Pair_Term xs z)"
    using shape seed fields by blast
next
  assume "\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs) (foldr Pair_Term xs z)"
  then obtain z xs where fields: "term_formed z" "\<forall>x\<in>set xs. term_formed x"
    "t=collection_join_argument z (data_list_term xs) (foldr Pair_Term xs z)" by blast
  show "(233,t)\<in>positive_meaning term_sequence_system"
    using term_sequence_fold_at_seed[OF fields(1)] fields(2,3) by blast
qed

lemma term_sequence_count_at_seed:
  assumes seed: "term_formed z"
  shows "(235,collection_join_argument z p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs \<and>
      q=foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z)"
proof -
  have exact: "(235,collection_join_argument (id z) p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term (map id xs) \<and>
        q=id (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z))"
    by (rule term_count_fold.encoded[where E=term_formed and D=term_formed])
      (use seed in \<open>auto simp: term_count_step_at octets_formed_def\<close>)
  show ?thesis using exact by simp
qed

theorem term_sequence_count_exact:
  "(235,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs)
        (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z))"
proof
  assume holds: "(235,t)\<in>positive_meaning term_sequence_system"
  obtain z p q where shape: "t=collection_join_argument z p q" and seed: "term_formed z"
    using term_count_fold.sound[OF holds] by blast
  obtain xs where fields: "\<forall>x\<in>set xs. term_formed x" "p=data_list_term xs"
    "q=foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z"
    using holds term_sequence_count_at_seed[OF seed, of p q] shape by blast
  show "\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs)
        (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z)"
    using shape seed fields by blast
next
  assume "\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs)
        (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z)"
  then obtain z xs where fields: "term_formed z" "\<forall>x\<in>set xs. term_formed x"
    "t=collection_join_argument z (data_list_term xs)
      (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z)" by blast
  show "(235,t)\<in>positive_meaning term_sequence_system"
    using term_sequence_count_at_seed[OF fields(1)] fields(2,3) by blast
qed

lemma term_sequence_pair_formed:
  "term_formed (foldr Pair_Term xs z) \<longleftrightarrow>
    term_formed z \<and> (\<forall>x\<in>set xs. term_formed x)"
  by (induction xs) auto

lemma term_sequence_count_formed:
  "term_formed (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z) \<longleftrightarrow> term_formed z"
  by (induction xs) (auto simp: octets_formed_def)

lemma term_sequence_pair_boundaries:
  "foldr Pair_Term xs (Payload_Term [])=data_list_term xs"
  "foldr Pair_Term xs (Target_Term (Whole_Artifact empty_artifact))=enumeration_term xs"
  by (induction xs) auto

lemma term_sequence_count_boundaries:
  "foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs (Payload_Term [])=natural_data_term (length xs)"
  "foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs
    (Target_Term (Whole_Artifact empty_artifact))=natural_term (length xs)"
  by (induction xs) auto

lemma term_sequence_list_guard:
  "(233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs)"
proof -
  have seed: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  show ?thesis by (simp only: term_sequence_fold_at_seed[OF seed] term_sequence_pair_boundaries; simp)
qed

lemma term_sequence_length_exact:
  "(235,collection_join_argument (Payload_Term []) p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs \<and> q=natural_data_term (length xs))"
proof -
  have seed: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  show ?thesis by (simp only: term_sequence_count_at_seed[OF seed] term_sequence_count_boundaries)
qed

section \<open>A complete prefix determines the selected position\<close>

lemma term_sequence_prefix:
  "foldr Pair_Term ps (Pair_Term x t)=data_list_term xs \<longleftrightarrow>
    (\<exists>ys. xs=ps@x#ys \<and> t=data_list_term ys)"
  by (induction ps arbitrary: xs) (case_tac xs; auto)+

lemma term_index_calls:
  "(236,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>p n y u v. t=Pair_Term (Pair_Term p n) y \<and>
      (233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system \<and>
      (233,collection_join_argument (Pair_Term y u) v p)\<in>positive_meaning term_sequence_system \<and>
      (235,collection_join_argument (Payload_Term []) v n)\<in>positive_meaning term_sequence_system)"
proof -
  have valuation: "(236,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
        t=Pair_Term (Pair_Term (h 0) (h 1)) (h 2) \<and>
        (233,collection_join_argument (Payload_Term []) (h 0) (h 0))\<in>positive_meaning term_sequence_system \<and>
        (233,collection_join_argument (Pair_Term (h 2) (h 3)) (h 4) (h 0))\<in>positive_meaning term_sequence_system \<and>
        (235,collection_join_argument (Payload_Term []) (h 4) (h 1))\<in>positive_meaning term_sequence_system)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: term_sequence_clause_family_def term_index_schema_def schema_variables_def
        term_sequence_call octets_formed_def)
  show ?thesis
  proof
    assume "(236,t)\<in>positive_meaning term_sequence_system"
    then show "\<exists>p n y u v. t=Pair_Term (Pair_Term p n) y \<and>
        (233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system \<and>
        (233,collection_join_argument (Pair_Term y u) v p)\<in>positive_meaning term_sequence_system \<and>
        (235,collection_join_argument (Payload_Term []) v n)\<in>positive_meaning term_sequence_system"
      by (simp only: valuation; blast)
  next
    assume "\<exists>p n y u v. t=Pair_Term (Pair_Term p n) y \<and>
        (233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system \<and>
        (233,collection_join_argument (Pair_Term y u) v p)\<in>positive_meaning term_sequence_system \<and>
        (235,collection_join_argument (Payload_Term []) v n)\<in>positive_meaning term_sequence_system"
    then obtain p n y u v where parts: "t=Pair_Term (Pair_Term p n) y"
      "(233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system"
      "(233,collection_join_argument (Pair_Term y u) v p)\<in>positive_meaning term_sequence_system"
      "(235,collection_join_argument (Payload_Term []) v n)\<in>positive_meaning term_sequence_system" by blast
    have formed: "term_formed p" "term_formed n" "term_formed y" "term_formed u" "term_formed v"
      using parts(2-4) positive_meaning_formed schema_call_formed_target by fastforce+
    let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then n else if i=2 then y else if i=3 then u else v"
    show "(236,t)\<in>positive_meaning term_sequence_system"
      by (simp only: valuation; rule exI[of _ ?h]) (use parts formed in auto)
  qed
qed

theorem term_sequence_index_exact:
  "(236,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<exists>xs n. (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and>
      t=Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) (xs!n))"
proof
  assume holds: "(236,t)\<in>positive_meaning term_sequence_system"
  obtain p n y u v where parts: "t=Pair_Term (Pair_Term p n) y"
    "(233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system"
    "(233,collection_join_argument (Pair_Term y u) v p)\<in>positive_meaning term_sequence_system"
    "(235,collection_join_argument (Payload_Term []) v n)\<in>positive_meaning term_sequence_system"
    using holds by (simp only: term_index_calls; blast)
  obtain xs where source: "\<forall>x\<in>set xs. term_formed x" "p=data_list_term xs"
    using parts(2) by (simp only: term_sequence_list_guard; blast)
  obtain ps where prefix: "v=data_list_term ps" "p=foldr Pair_Term ps (Pair_Term y u)"
    using parts(3) by (auto simp: term_sequence_fold_exact)
  have index: "n=natural_data_term (length ps)"
    using parts(4) prefix(1) by (auto simp: term_sequence_length_exact data_list_term_injective)
  obtain ys where split: "xs=ps@y#ys" "u=data_list_term ys"
    using prefix(2) source(2) term_sequence_prefix[of ps y u xs] by blast
  show "\<exists>xs n. (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and>
      t=Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) (xs!n)"
    by (rule exI[of _ xs], rule exI[of _ "length ps"])
      (use source parts(1) index split in simp)
next
  assume "\<exists>xs n. (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and>
      t=Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) (xs!n)"
  then obtain xs n where source: "\<forall>x\<in>set xs. term_formed x" and bound: "n<length xs"
    and shape: "t=Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) (xs!n)" by blast
  let ?ps="take n xs"
  let ?ys="drop (Suc n) xs"
  have split: "xs=?ps@(xs!n)#?ys" by (rule id_take_nth_drop[OF bound])
  have formed: "term_formed (xs!n)" "term_formed (data_list_term ?ys)"
    "\<forall>x\<in>set ?ps. term_formed x"
    using source bound set_take_subset[of n xs] set_drop_subset[of "Suc n" xs]
    by (auto simp: data_list_term_formed)
  have rebuilt: "foldr Pair_Term ?ps (Pair_Term (xs!n) (data_list_term ?ys))=data_list_term xs"
    using split by (simp only: term_sequence_prefix) blast
  have guard: "(233,collection_join_argument (Payload_Term []) (data_list_term xs) (data_list_term xs))
      \<in>positive_meaning term_sequence_system"
    using source by (simp only: term_sequence_list_guard; blast)
  have prefix: "(233,collection_join_argument (Pair_Term (xs!n) (data_list_term ?ys))
      (data_list_term ?ps) (data_list_term xs))\<in>positive_meaning term_sequence_system"
  proof -
    have seed: "term_formed (Pair_Term (xs!n) (data_list_term ?ys))" using formed(1,2) by simp
    show ?thesis
      by (simp only: term_sequence_fold_at_seed[OF seed]; rule exI[of _ ?ps])
        (use formed(3) rebuilt in auto)
  qed
  have length: "(235,collection_join_argument (Payload_Term []) (data_list_term ?ps) (natural_data_term n))
      \<in>positive_meaning term_sequence_system"
    using formed(3) bound by (auto simp: term_sequence_length_exact)
  show "(236,t)\<in>positive_meaning term_sequence_system"
    using shape guard prefix length by (simp only: term_index_calls; blast)
qed

corollary term_sequence_index_at:
  "(236,Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) y)
    \<in>positive_meaning term_sequence_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and> y=xs!n"
  by (auto simp: term_sequence_index_exact data_list_term_injective
    dest: injD[OF natural_data_term_injective])

theorem term_sequence_index_encoded:
  assumes formed: "\<forall>x\<in>set xs. term_formed (f x)"
  shows "(236,Pair_Term (Pair_Term (data_list_term (map f xs)) (natural_data_term n)) y)
    \<in>positive_meaning term_sequence_system \<longleftrightarrow> n<length xs \<and> y=f (xs!n)"
  using formed by (auto simp: term_sequence_index_at)

text \<open>
  The two local step equations and their formation closure discharge both
  native traversals through the general fold contract. Position selection
  then uses the ordinary list-prefix equation; it needs no further native
  induction. Its full input guard remains necessary even when the selected
  head occurs first. Every suffix element and the final boundary are checked.

  Selection copies the actual term at the supplied position. Equal terms at
  different positions remain different input occurrences. Neither a missing
  position nor an improper list receives a default value.
\<close>

end
