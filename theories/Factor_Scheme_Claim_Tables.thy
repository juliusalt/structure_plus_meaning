theory Factor_Scheme_Claim_Tables
  imports Factor_Scheme_Claim_Joins Factor_Proof_Claim_Values Functional_Relation_Lists Factor_Keyed_Row_Admission
begin

section \<open>The temporary table contains the observations of actual symbolic claims\<close>

definition observed_claim_rows ::
  "('s\<times>(local_address option definition_site\<times>local_address term_pattern)) list\<Rightarrow>
    ('s\<times>(local_address option definition_site\<times>factor_term)) list" where
  "observed_claim_rows xs=map (map_prod id (map_prod id pattern_claim_observation)) xs"

lemma observed_claim_rows_set:
  "set (observed_claim_rows xs)=map_relation_values (map_prod id pattern_claim_observation) (set xs)"
  by (auto simp: observed_claim_rows_def map_relation_values_def map_prod_def)

lemma observed_claim_rows_keys:
  "map fst (observed_claim_rows xs)=map fst xs"
  by (simp add: observed_claim_rows_def comp_def map_prod_def case_prod_unfold)

lemma observed_claim_rows_member [simp]:
  "(n,d,pattern_claim_observation p)\<in>set (observed_claim_rows xs) \<longleftrightarrow> (n,d,p)\<in>set xs"
  by (cases d) (auto simp: observed_claim_rows_set map_prod_def)

lemma observed_claim_rows_fibre:
  assumes "distinct (map fst xs)"
  shows "key_values (definition_site_value n) (encoded_positioned_calls (observed_claim_rows xs))=
      [call_instance_value d (pattern_claim_observation p)] \<longleftrightarrow> (n,d,p)\<in>set xs"
  by (simp only: positioned_calls_fibre[of "observed_claim_rows xs", unfolded observed_claim_rows_keys,
    OF assms] observed_claim_rows_member)

lemma observed_claim_table_admission:
  "(21,positioned_call_rows_term (observed_claim_rows xs))\<in>positive_meaning keyed_list_system
    \<longleftrightarrow> formed_key_rows (encoded_positioned_calls (observed_claim_rows xs)) \<and>
      distinct (map fst xs)"
  by (simp only: keyed_list_row_admission positioned_calls_key_order observed_claim_rows_keys)

lemma observed_claim_parent_fibre:
  assumes keys: "distinct (map fst xs)"
  shows "(28,key_fibre_argument (definition_site_value n)
      (positioned_call_rows_term (observed_claim_rows xs))
      (data_list_term [call_instance_value d (pattern_claim_observation p)]))\<in>positive_meaning key_fibre_system
    \<longleftrightarrow> term_formed (definition_site_value n) \<and>
      formed_key_rows (encoded_positioned_calls (observed_claim_rows xs)) \<and> (n,d,p)\<in>set xs"
  by (simp only: key_fibre_lists data_list_term_injective)
    (use observed_claim_rows_fibre[OF keys, where n=n and d=d and p=p] in auto)

section \<open>Every native joined row retains its actual discharge occurrence\<close>

theorem observed_claim_join:
  assumes rows: "formed_key_rows (encoded_positioned_calls (observed_claim_rows xs))"
    and keys: "distinct (map fst xs)"
    and covered: "rel_ran (set ds)\<subseteq>rel_dom (set xs)"
    and source: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
      term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
  shows "(100,keyed_row_join_argument (positioned_call_rows_term (observed_claim_rows xs))
      (discharge_rows_term ds)
      (positioned_call_rows_term (observed_claim_rows (joined_relation_rows (set xs) ds))))
    \<in>positive_meaning keyed_row_join_system"
proof -
  have functional: "single_valued (set xs)" using keys by (simp only: distinct_keys_iff; blast)
  have fibre: "key_values (definition_site_value n) (encoded_positioned_calls (observed_claim_rows xs))=
      [call_instance_value (fst (rel_value (set xs) n))
        (pattern_claim_observation (snd (rel_value (set xs) n)))]"
    if row: "(s,n)\<in>set ds" for s n
  proof -
    have key: "n\<in>rel_dom (set xs)" using covered rel_ranI[OF row] by blast
    obtain q where actual: "(n,q)\<in>set xs" using key by (auto simp: rel_dom_def)
    have selected: "rel_value (set xs) n=q" by (rule rel_value_eq[OF functional actual])
    have entry: "(n,fst (rel_value (set xs) n),snd (rel_value (set xs) n))\<in>set xs"
      using actual by (simp only: selected prod.collapse)
    show ?thesis by (simp only: observed_claim_rows_fibre[OF keys]; rule entry)
  qed
  have inputs: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
      term_formed (definition_site_value s) \<and> term_formed (definition_site_value n) \<and>
      self_contained_term (definition_site_value n) \<and>
      key_values (definition_site_value n) (encoded_positioned_calls (observed_claim_rows xs))=
        [call_instance_value (fst (rel_value (set xs) n))
          (pattern_claim_observation (snd (rel_value (set xs) n)))]"
    using source fibre by auto
  have constructed: "keyed_row_join (positioned_call_rows_term (observed_claim_rows xs))
      (map (\<lambda>(s,n). (definition_site_value s,definition_site_value n)) ds)
      (map (\<lambda>(s,n). (definition_site_value s,
        call_instance_value (fst (rel_value (set xs) n))
          (pattern_claim_observation (snd (rel_value (set xs) n))))) ds)"
    by (rule keyed_row_join_row_values[where key=definition_site_value and target=definition_site_value
      and f="\<lambda>s n. rel_value (set xs) n"
      and val="\<lambda>q. call_instance_value (fst q) (pattern_claim_observation (snd q))", OF rows inputs])
  have joined: "keyed_row_join (positioned_call_rows_term (observed_claim_rows xs))
      (encoded_discharge_rows ds)
      (encoded_positioned_calls (observed_claim_rows (joined_relation_rows (set xs) ds)))"
    using constructed
    by (simp add: observed_claim_rows_def joined_relation_rows_def map_prod_def comp_def case_prod_unfold)
  show ?thesis by (rule keyed_row_join_complete[OF pair_list_term_formed[OF rows] joined])
qed

theorem observed_claim_join_output:
  assumes rows: "formed_key_rows (encoded_positioned_calls (observed_claim_rows xs))"
    and keys: "distinct (map fst xs)"
    and covered: "rel_ran (set ds)\<subseteq>rel_dom (set xs)"
    and source: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
      term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
  shows "(100,keyed_row_join_argument (positioned_call_rows_term (observed_claim_rows xs))
      (discharge_rows_term ds) z)\<in>positive_meaning keyed_row_join_system \<longleftrightarrow>
    z=positioned_call_rows_term (observed_claim_rows (joined_relation_rows (set xs) ds))"
proof
  let ?js="positioned_call_rows_term (observed_claim_rows xs)"
  let ?qs="encoded_positioned_calls (observed_claim_rows (joined_relation_rows (set xs) ds))"
  assume admitted: "(100,keyed_row_join_argument ?js (discharge_rows_term ds) z)
    \<in>positive_meaning keyed_row_join_system"
  obtain qs where joined_output: "z=pair_list_term qs" "keyed_row_join ?js (encoded_discharge_rows ds) qs"
    using keyed_row_join_sound[OF admitted] by (auto simp only: factor_term.inject pair_list_term_injective)
  have canonical: "keyed_row_join ?js (encoded_discharge_rows ds) ?qs"
    using observed_claim_join[OF rows keys covered source]
    by (simp only: keyed_row_join_lists; blast)
  have same: "qs=?qs" by (rule keyed_row_join_output_unique[OF joined_output(2) canonical])
  show "z=positioned_call_rows_term (observed_claim_rows (joined_relation_rows (set xs) ds))"
    by (simp only: joined_output(1) same)
next
  assume "z=positioned_call_rows_term (observed_claim_rows (joined_relation_rows (set xs) ds))"
  then show "(100,keyed_row_join_argument (positioned_call_rows_term (observed_claim_rows xs))
      (discharge_rows_term ds) z)\<in>positive_meaning keyed_row_join_system"
    using observed_claim_join[OF rows keys covered source] by simp
qed

text \<open>
  Whole table formation is an explicit hypothesis. The local symbolic judgment
  cannot establish formation of unrelated claims. The native join above copies
  the observed actual claim at every discharge target, retaining all list
  occurrences, while its set is the independent complete relation join.
\<close>

end
