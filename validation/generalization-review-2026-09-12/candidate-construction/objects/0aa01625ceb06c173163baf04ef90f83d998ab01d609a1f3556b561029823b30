theory Factor_Collection_Correspondence
  imports Factor_Related_Bags Factor_Term_Sequence_Contracts
begin

section \<open>Formation belongs to each actual collection member\<close>

lemma list_all2_formed_readings:
  "list_all2 (\<lambda>a p. R a p \<and> term_formed p) xs ps \<longleftrightarrow>
    list_all2 R xs ps \<and> (\<forall>p\<in>set ps. term_formed p)"
  by (induction xs arbitrary: ps) (case_tac ps; auto)+

lemma finite_collection_formed_readings:
  "finite_collection_presents (\<lambda>a p. R a p \<and> term_formed p) A t \<longleftrightarrow>
    finite_collection_presents R A t \<and> term_formed t"
  by (simp only: finite_collection_presents_def list_all2_formed_readings)
    (metis enumeration_term_formed)

lemma finite_collection_native_retermination:
  "(term_formed q \<and> finite_collection_presents R A q) \<longleftrightarrow>
    (\<exists>p. data_collection_presents R A p \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)
        \<in>positive_meaning term_sequence_system)"
  by (auto simp: finite_collection_retermination composed_presentation_def term_sequence_enumeration_exact
    enumeration_retermination_def data_list_term_formed enumeration_term_formed)

section \<open>The same occurrence comparison crosses a complete terminator change\<close>

definition enumerated_comparison_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "enumerated_comparison_schema reterminate bag=data_rule (Pattern_Pair data_x data_y)
    {(0,reterminate,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) data_z data_x),
     (1,reterminate,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) data_w data_y),
     (2,bag,Pattern_Pair data_z data_w)}"

lemma enumerated_comparison_schema_formed [simp]:
  "schema_formed (enumerated_comparison_schema reterminate bag)"
  by (auto simp: enumerated_comparison_schema_def schema_formed_def single_valued_def)

lemma enumerated_comparison_schema_dependencies [simp]:
  "schema_dependencies (enumerated_comparison_schema reterminate bag)={reterminate,bag}"
  by (simp add: enumerated_comparison_schema_def schema_dependencies_def rel_ran_image)

locale enumerated_comparison_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry reterminate bag :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>{(0,enumerated_comparison_schema reterminate bag)}"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
    and conversion: "\<And>p q. (reterminate,collection_join_argument
      (Target_Term (Whole_Artifact empty_artifact)) p q)\<in>positive_meaning P \<longleftrightarrow>
      term_formed p \<and> enumeration_retermination p q"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 2) (h 0))
        \<in>positive_meaning P \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 3) (h 1))
        \<in>positive_meaning P \<and> (bag,Pair_Term (h 2) (h 3))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family enumerated_comparison_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q u v. t=Pair_Term p q \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)
        \<in>positive_meaning P \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v q)
        \<in>positive_meaning P \<and> (bag,Pair_Term u v)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>p q u v. t=Pair_Term p q \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)
        \<in>positive_meaning P \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v q)
        \<in>positive_meaning P \<and> (bag,Pair_Term u v)\<in>positive_meaning P"
    by (simp only: valuation; blast)
next
  assume "\<exists>p q u v. t=Pair_Term p q \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)
        \<in>positive_meaning P \<and>
      (reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v q)
        \<in>positive_meaning P \<and> (bag,Pair_Term u v)\<in>positive_meaning P"
  then obtain p q u v where shape: "t=Pair_Term p q" and reads:
    "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)\<in>positive_meaning P"
    "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v q)\<in>positive_meaning P"
    "(bag,Pair_Term u v)\<in>positive_meaning P" by blast
  have formed: "term_formed p" "term_formed q" "term_formed u" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(2)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then q else if i=2 then u else v"
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h]) (use shape reads formed in auto)
qed

theorem on_reterminations:
  assumes first: "term_formed u" "enumeration_retermination u p"
    and second: "term_formed v" "enumeration_retermination v q"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
    (bag,Pair_Term u v)\<in>positive_meaning P"
proof -
  have left: "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)\<in>positive_meaning P"
    using first by (simp only: conversion; blast)
  have right: "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v q)\<in>positive_meaning P"
    using second by (simp only: conversion; blast)
  show ?thesis
  proof
    assume "(entry,Pair_Term p q)\<in>positive_meaning P"
    then obtain u' v' where reads:
      "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u' p)\<in>positive_meaning P"
      "(reterminate,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) v' q)\<in>positive_meaning P"
      "(bag,Pair_Term u' v')\<in>positive_meaning P"
      by (simp only: exact factor_term.inject; blast)
    have forms: "enumeration_retermination u' p" "enumeration_retermination v' q"
    proof -
      show "enumeration_retermination u' p" using reads(1) by (simp only: conversion; blast)
      show "enumeration_retermination v' q" using reads(2) by (simp only: conversion; blast)
    qed
    have equal: "u'=u" "v'=v"
      by (rule presentation_class.recovery[OF enumeration_retermination_class forms(1) first(2)],
        rule presentation_class.recovery[OF enumeration_retermination_class forms(2) second(2)])
    show "(bag,Pair_Term u v)\<in>positive_meaning P" using reads(3) equal by simp
  next
    assume holds: "(bag,Pair_Term u v)\<in>positive_meaning P"
    show "(entry,Pair_Term p q)\<in>positive_meaning P"
      by (simp only: exact; rule exI[of _ p], rule exI[of _ q], rule exI[of _ u], rule exI[of _ v])
        (use left right holds in simp)
  qed
qed

theorem comparison_collections:
  assumes first: "finite_collection_presents read A p" "term_formed p"
    and second: "finite_collection_presents read B q" "term_formed q"
    and compare: "\<And>u v. data_collection_presents read A u \<Longrightarrow>
      data_collection_presents read B v \<Longrightarrow>
      (bag,Pair_Term u v)\<in>positive_meaning P \<longleftrightarrow> A=B"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> A=B"
proof -
  have p: "term_formed p \<and> finite_collection_presents read A p" using first by blast
  have q: "term_formed q \<and> finite_collection_presents read B q" using second by blast
  obtain u where left: "data_collection_presents read A u" "term_formed u" "enumeration_retermination u p"
    using p by (simp only: finite_collection_native_retermination term_sequence_enumeration_exact; blast)
  obtain v where right: "data_collection_presents read B v" "term_formed v" "enumeration_retermination v q"
    using q by (simp only: finite_collection_native_retermination term_sequence_enumeration_exact; blast)
  show ?thesis by (simp only: on_reterminations[OF left(2,3) right(2,3)] compare[OF left(1) right(1)])
qed

end

context related_occurrences
begin

theorem comparison_enumerations:
  assumes enumeration: "enumerated_comparison_profile P entry reterminate bag_site"
    and first: "finite_collection_presents read A p" and second: "finite_collection_presents read B q"
    and compare: "\<And>a b u v. read a u \<Longrightarrow> read b v \<Longrightarrow> related u v \<longleftrightarrow> a=b"
  shows "(entry,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> A=B"
proof -
  have formed: "term_formed u" if "read a u" for a u
    using compare[OF that that] comparison_data[of u u] by blast
  have pf: "term_formed p" by (rule finite_collection_presents_formed[OF first]) (use formed in blast)
  have qf: "term_formed q" by (rule finite_collection_presents_formed[OF second]) (use formed in blast)
  show ?thesis
  proof (rule enumerated_comparison_profile.comparison_collections[OF enumeration first pf second qf])
    fix u v assume left: "data_collection_presents read A u" and right: "data_collection_presents read B v"
    show "(bag_site,Pair_Term u v)\<in>positive_meaning P \<longleftrightarrow> A=B"
      by (rule related_occurrences.comparison_collections[OF related_occurrences_axioms left right compare])
  qed
qed

end

text \<open>
  Formation constrains every actual member and the complete terminator. The
  three ordinary premises retain both source enumerations and submit their
  complete rows to the supplied occurrence comparison. The generic rule
  transports that comparison through the already proved native conversion.
  A relation between member presentations remains a separately owned premise;
  changing a terminator alone does not compare reordered collections.
\<close>

end
