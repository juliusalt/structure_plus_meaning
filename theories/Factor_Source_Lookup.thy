theory Factor_Source_Lookup
  imports Factor_Source_Admission
begin

section \<open>The two ordinary branches retain the same complete context\<close>

lemma source_lookup_valuation:
  "(243,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3) \<and>
      (242,Pair_Term (h 0) (h 1))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 4) (h 0))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 5) (h 2))\<in>positive_meaning source_system \<and>
      (236,Pair_Term (Pair_Term (h 4) (h 5)) (h 3))\<in>positive_meaning source_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3) \<and>
      (242,Pair_Term (h 0) (h 1))\<in>positive_meaning source_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 4) (h 1))\<in>positive_meaning source_system \<and>
      (28,key_fibre_argument (h 2) (h 4) (data_list_term [h 3]))\<in>positive_meaning source_system)"
proof -
  have family: "((243,c),S)\<in>system_clauses source_system \<longleftrightarrow>
      (c=0 \<and> S=source_input_schema) \<or> (c=1 \<and> S=source_base_schema)" for c S
    by (simp only: source_system_clause[of 243, simplified] source_clause_family_def; auto)
  have ordinary: "schema_material_premises S={}"
    if "((243,c),S)\<in>system_clauses source_system" for c S
    using that by (auto simp: family source_input_schema_def source_base_schema_def)
  have calls: "schema_call_formed source_system 243 t \<longleftrightarrow> term_formed t"
    by (simp add: source_system_call)
  let ?Q="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning source_system)"
  have valuation: "(243,t)\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>c S h. ((243,c),S)\<in>system_clauses source_system \<and> ?Q S h)"
    apply (subst ordinary_positive_entry_valuation)
     apply (rule ordinary)
     apply assumption
    apply (simp only: calls)
    done
  have raw: "(243,t)\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>h. ?Q source_input_schema h) \<or> (\<exists>h. ?Q source_base_schema h)"
  proof
    assume holds: "(243,t)\<in>positive_meaning source_system"
    obtain c S h where clause: "((243,c),S)\<in>system_clauses source_system"
      and fields: "\<forall>i\<in>schema_variables S. term_formed (h i)"
        "t=evaluate_pattern h (schema_conclusion S)" "term_formed t"
        "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning source_system"
      using iffD1[OF valuation holds] by blast
    have cases: "S=source_input_schema \<or> S=source_base_schema" using clause by (simp only: family; blast)
    have checked: "?Q S h" using fields by (simp only: calls; blast)
    show "(\<exists>h. ?Q source_input_schema h) \<or> (\<exists>h. ?Q source_base_schema h)"
      using cases checked by blast
  next
    assume "(\<exists>h. ?Q source_input_schema h) \<or> (\<exists>h. ?Q source_base_schema h)"
    then consider (input) h where "?Q source_input_schema h" | (base) h where "?Q source_base_schema h" by blast
    then show "(243,t)\<in>positive_meaning source_system"
    proof cases
      case (input h)
      show ?thesis
        by (rule iffD2[OF valuation],
            rule exI[of _ 0], rule exI[of _ source_input_schema], rule exI[of _ h])
          (use input in \<open>simp only: family calls; blast\<close>)
    next
      case (base h)
      show ?thesis
        by (rule iffD2[OF valuation],
            rule exI[of _ 1], rule exI[of _ source_base_schema], rule exI[of _ h])
          (use base in \<open>simp only: family calls; blast\<close>)
    qed
  qed
  have input: "?Q source_input_schema h \<longleftrightarrow>
      (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3) \<and>
      (242,Pair_Term (h 0) (h 1))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 4) (h 0))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 5) (h 2))\<in>positive_meaning source_system \<and>
      (236,Pair_Term (Pair_Term (h 4) (h 5)) (h 3))\<in>positive_meaning source_system" for h
    by (auto simp: source_input_schema_def schema_variables_def)
  have base: "?Q source_base_schema h \<longleftrightarrow>
      (\<forall>i\<in>{0,1,2,3,4}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3) \<and>
      (242,Pair_Term (h 0) (h 1))\<in>positive_meaning source_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 4) (h 1))\<in>positive_meaning source_system \<and>
      (28,key_fibre_argument (h 2) (h 4) (data_list_term [h 3]))\<in>positive_meaning source_system" for h
    by (auto simp: source_base_schema_def schema_variables_def)
  show ?thesis by (simp only: raw input base)
qed

lemma source_lookup_calls:
  "(243,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>x b j v. t=Pair_Term (Pair_Term (Pair_Term x b) j) v \<and>
      (242,Pair_Term x b)\<in>positive_meaning source_system \<and>
      ((\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system) \<or>
       ((1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system))))"
proof
  assume "(243,t)\<in>positive_meaning source_system"
  then show "\<exists>x b j v. t=Pair_Term (Pair_Term (Pair_Term x b) j) v \<and>
      (242,Pair_Term x b)\<in>positive_meaning source_system \<and>
      ((\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system) \<or>
       ((1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system)))"
    by (simp only: source_lookup_valuation; blast)
next
  assume "\<exists>x b j v. t=Pair_Term (Pair_Term (Pair_Term x b) j) v \<and>
      (242,Pair_Term x b)\<in>positive_meaning source_system \<and>
      ((\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system) \<or>
       ((1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system)))"
  then obtain x b j v where shape: "t=Pair_Term (Pair_Term (Pair_Term x b) j) v"
    and "context": "(242,Pair_Term x b)\<in>positive_meaning source_system" and choice:
      "(\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system) \<or>
       ((1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system))" by blast
  have outer: "term_formed x" "term_formed b"
    using schema_call_formed_target[OF positive_meaning_formed[OF "context"]] by auto
  from choice show "(243,t)\<in>positive_meaning source_system"
  proof
    assume "\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system"
    then obtain p n where support:
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system"
      "(236,Pair_Term (Pair_Term p n) v)\<in>positive_meaning source_system" by blast
    have formed: "term_formed j" "term_formed v" "term_formed p" "term_formed n"
      using support positive_meaning_formed schema_call_formed_target by fastforce+
    let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then b else if i=2 then j else if i=3 then v else if i=4 then p else n"
    show ?thesis by (simp only: source_lookup_valuation; rule disjI1; rule exI[of _ ?h])
      (use shape "context" outer support formed in auto)
  next
    assume "(1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system)"
    then obtain p where support: "(1,data_list_term [j])\<in>positive_meaning source_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system"
      "(28,key_fibre_argument j p (data_list_term [v]))\<in>positive_meaning source_system" by blast
    have formed: "term_formed j" "term_formed v" "term_formed p"
      using schema_call_formed_target[OF positive_meaning_formed[OF support(3)]] by auto
    let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then b else if i=2 then j else if i=3 then v else p"
    show ?thesis by (simp only: source_lookup_valuation; rule disjI2; rule exI[of _ ?h])
      (use shape "context" outer support formed in auto)
  qed
qed

section \<open>Position lookup and keyed lookup specialize their owning contracts\<close>

lemma source_input_lookup:
  assumes formed: "\<forall>R\<in>set xs. exact_formed R"
  shows "(\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p (artifact_list_term xs))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
      (236,Pair_Term (Pair_Term p n) q)\<in>positive_meaning source_system) \<longleftrightarrow>
    (\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i)))"
proof -
  let ?ts="map (Target_Term \<circ> Whole_Artifact) xs"
  have index: "(236,Pair_Term (Pair_Term (data_list_term ?ts) n) q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
      (\<exists>i. i<length xs \<and> n=natural_data_term i \<and> q=Target_Term (Whole_Artifact (xs!i)))" for n q
  proof
    assume holds: "(236,Pair_Term (Pair_Term (data_list_term ?ts) n) q)\<in>positive_meaning term_sequence_system"
    then obtain ts i where parts: "\<forall>x\<in>set ts. term_formed x" "i<length ts"
      "Pair_Term (Pair_Term (data_list_term ?ts) n) q=Pair_Term (Pair_Term (data_list_term ts) (natural_data_term i)) (ts!i)"
      by (simp only: term_sequence_index_exact; blast)
    have same: "ts=?ts" using parts(3) by (simp add: data_list_term_injective)
    show "\<exists>i. i<length xs \<and> n=natural_data_term i \<and> q=Target_Term (Whole_Artifact (xs!i))"
      by (rule exI[of _ i]) (use parts same in auto)
  next
    assume "\<exists>i. i<length xs \<and> n=natural_data_term i \<and> q=Target_Term (Whole_Artifact (xs!i))"
    then obtain i where parts: "i<length xs" "n=natural_data_term i" "q=Target_Term (Whole_Artifact (xs!i))" by blast
    show "(236,Pair_Term (Pair_Term (data_list_term ?ts) n) q)\<in>positive_meaning term_sequence_system"
      by (simp only: term_sequence_index_exact; rule exI[of _ ?ts], rule exI[of _ i])
        (use formed parts in auto)
  qed
  show ?thesis
  proof
    assume accepted: "\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p (artifact_list_term xs))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
      (236,Pair_Term (Pair_Term p n) q)\<in>positive_meaning source_system"
    then obtain p n where source: "p=data_list_term ?ts"
      and count: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning term_sequence_system"
      and selected: "(236,Pair_Term (Pair_Term p n) q)\<in>positive_meaning term_sequence_system"
      by (simp only: source_component_meanings(5,6) source_inputs_native_at[OF formed]; blast)
    obtain i where parts: "i<length xs" "n=natural_data_term i" "q=Target_Term (Whole_Artifact (xs!i))"
      using selected by (simp only: source index; blast)
    have old_index: "j=natural_term i" using count by (simp only: parts(2) natural_term_native_retermination)
    show "\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i))"
      by (rule exI[of _ i]) (use parts old_index in blast)
  next
    assume "\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i))"
    then obtain i where parts: "i<length xs" "j=natural_term i" "q=Target_Term (Whole_Artifact (xs!i))" by blast
    have count: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (natural_data_term i) j)\<in>positive_meaning term_sequence_system"
      by (simp only: natural_term_native_retermination parts(2))
    have selected: "(236,Pair_Term (Pair_Term (data_list_term ?ts) (natural_data_term i)) q)\<in>positive_meaning term_sequence_system"
      by (simp only: index; rule exI[of _ i]) (use parts in blast)
    show "\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p (artifact_list_term xs))\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
      (236,Pair_Term (Pair_Term p n) q)\<in>positive_meaning source_system"
      by (rule exI[of _ "data_list_term ?ts"], rule exI[of _ "natural_data_term i"])
        (use count selected in \<open>simp only: source_component_meanings(5,6) source_inputs_native_at[OF formed]; simp\<close>)
  qed
qed

lemma source_base_lookup:
  assumes base: "source_base_presents B b" and key: "octets_formed k"
  shows "(\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
      (28,key_fibre_argument (Payload_Term k) p (data_list_term [q]))\<in>positive_meaning source_system) \<longleftrightarrow>
    (\<exists>R. (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
proof -
  have boundary: "\<And>j R. (j,R)\<in>B \<Longrightarrow> term_formed (Payload_Term j) \<and>
      self_contained_term (Payload_Term j) \<and> term_formed ((Target_Term \<circ> Whole_Artifact) R)"
    using base by (auto simp: source_base_fields)
  have lookup: "(28,key_fibre_argument (Payload_Term k) p (data_list_term [q]))\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>R. (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
    if change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system" for p
  proof -
    have table: "data_table_presents payload_value_presents artifact_literal_presents B p"
      by (rule source_base_at_change[OF base]) (use change in \<open>simp only: source_component_meanings(5)\<close>)
    have raw: "data_table_presents (\<lambda>j p. p=Payload_Term j) (\<lambda>R q. q=(Target_Term \<circ> Whole_Artifact) R) B p"
      using table by (simp only: data_table_literal_boundaries; simp)
    show ?thesis using key_fibre_at_literal_table[OF raw payload_term_injective, of k q] key boundary
      by (simp only: source_component_meanings(4); auto)
  qed
  have exists: "\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system"
    using base by (simp only: source_base_native_change source_component_meanings(5); blast)
  show ?thesis using lookup exists by blast
qed

theorem source_lookup_at_context:
  assumes "context": "source_context_presents (xs,B) c"
  shows "(243,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>k R. j=construction_source_term k \<and> construction_source_at xs B k R \<and>
      q=Target_Term (Whole_Artifact R))"
proof -
  obtain b where base: "source_base_presents B b" and shape: "c=Pair_Term (artifact_list_term xs) b"
    and formed: "\<forall>R\<in>set xs. exact_formed R"
    using "context" by (auto simp: factor_pair_presents_def)
  have admitted: "(242,c)\<in>positive_meaning source_system" using "context" by (simp only: source_context_exact; blast)
  have keys: "(k,R)\<in>B \<Longrightarrow> octets_formed k" for k R using base by (auto simp: source_base_fields)
  have base_branch: "((1,data_list_term [j])\<in>positive_meaning source_system \<and>
      (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
        (28,key_fibre_argument j p (data_list_term [q]))\<in>positive_meaning source_system)) \<longleftrightarrow>
      (\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
  proof
    assume accepted: "(1,data_list_term [j])\<in>positive_meaning source_system \<and>
      (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
        (28,key_fibre_argument j p (data_list_term [q]))\<in>positive_meaning source_system)"
    obtain k where key: "octets_formed k" "j=Payload_Term k"
      using accepted by (simp only: source_component_meanings(1) payload_value_recognition; blast)
    have result: "\<exists>R. (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R)"
      using accepted key(2) source_base_lookup[OF base key(1), of q] by blast
    show "\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R)"
      using key(2) result by blast
  next
    assume "\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R)"
    then obtain k R where result: "j=Payload_Term k" "(k,R)\<in>B" "q=Target_Term (Whole_Artifact R)" by blast
    have key: "octets_formed k" by (rule keys[OF result(2)])
    have lookup: "\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
        (28,key_fibre_argument j p (data_list_term [q]))\<in>positive_meaning source_system"
      using source_base_lookup[OF base key, of q] result by blast
    have payload: "(1,data_list_term [j])\<in>positive_meaning source_system"
      using key result(1) by (simp only: source_component_meanings(1) payload_value_recognition; blast)
    show "(1,data_list_term [j])\<in>positive_meaning source_system \<and>
      (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
        (28,key_fibre_argument j p (data_list_term [q]))\<in>positive_meaning source_system)"
      using payload lookup by blast
  qed
  let ?alternatives="\<lambda>x b j q.
      (\<exists>p n. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
        (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) n j)\<in>positive_meaning source_system \<and>
        (236,Pair_Term (Pair_Term p n) q)\<in>positive_meaning source_system) \<or>
      ((1,data_list_term [j])\<in>positive_meaning source_system \<and>
        (\<exists>p. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning source_system \<and>
          (28,key_fibre_argument j p (data_list_term [q]))\<in>positive_meaning source_system))"
  have raw: "(243,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system \<longleftrightarrow>
      ?alternatives (artifact_list_term xs) b j q"
  proof
    assume holds: "(243,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system"
    obtain x b' k v where fields: "Pair_Term (Pair_Term c j) q=Pair_Term (Pair_Term (Pair_Term x b') k) v"
      and child: "?alternatives x b' k v"
      using holds by (simp only: source_lookup_calls; blast)
    have same: "x=artifact_list_term xs" "b'=b" "k=j" "v=q"
      using fields by (simp_all add: shape)
    show "?alternatives (artifact_list_term xs) b j q" using child by (simp only: same)
  next
    assume child: "?alternatives (artifact_list_term xs) b j q"
    show "(243,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system"
      by (simp only: source_lookup_calls; rule exI[of _ "artifact_list_term xs"],
          rule exI[of _ b], rule exI[of _ j], rule exI[of _ q])
        (use child admitted in \<open>simp only: shape; simp\<close>)
  qed
  have branches: "(243,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i))) \<or>
      (\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
    by (simp only: raw source_input_lookup[OF formed] base_branch)
  show ?thesis
  proof (simp only: branches, rule iffI)
    assume "(\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i))) \<or>
      (\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
    then show "\<exists>k R. j=construction_source_term k \<and> construction_source_at xs B k R \<and>
        q=Target_Term (Whole_Artifact R)"
      by (auto; metis construction_source_at.simps construction_source_term.simps)
  next
    assume "\<exists>k R. j=construction_source_term k \<and> construction_source_at xs B k R \<and>
        q=Target_Term (Whole_Artifact R)"
    then obtain k R where parts: "j=construction_source_term k" "construction_source_at xs B k R"
      "q=Target_Term (Whole_Artifact R)" by blast
    show "(\<exists>i. i<length xs \<and> j=natural_term i \<and> q=Target_Term (Whole_Artifact (xs!i))) \<or>
      (\<exists>k R. j=Payload_Term k \<and> (k,R)\<in>B \<and> q=Target_Term (Whole_Artifact R))"
      using parts by (cases k) auto
  qed
qed

section \<open>The whole query determines exactly its existing source value\<close>

lemma source_lookup_output:
  assumes query: "source_query_presents z p"
  shows "(243,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
    artifact_literal_presents (source_query_value z) q"
proof -
  obtain xs B j c where "context": "source_context_presents (xs,B) c" and member: "\<exists>R. construction_source_at xs B j R"
    and shape: "z=((xs,B),j)" "p=Pair_Term c (construction_source_term j)"
    using query by (cases z; cases "fst z") (auto simp: source_query_presents_def factor_pair_presents_def)
  have sf: "construction_sources_formed xs B" using source_contexts.subject_boundary[OF "context"] by simp
  obtain R where source: "construction_source_at xs B j R" using member by blast
  have "value": "construction_source_value xs B j=R" "exact_formed R"
    using construction_source_value_at[OF sf source] by auto
  have unique: "construction_source_at xs B j S \<Longrightarrow> S=R" for S
    using construction_source_value_at(1)[OF sf] "value"(1) by blast
  have calls: "(243,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>k S. construction_source_term j=construction_source_term k \<and>
        construction_source_at xs B k S \<and> q=Target_Term (Whole_Artifact S))"
    by (simp only: shape(2) source_lookup_at_context[OF "context"])
  have result: "(243,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
      q=Target_Term (Whole_Artifact R)"
  proof
    assume "(243,Pair_Term p q)\<in>positive_meaning source_system"
    then obtain k S where index: "construction_source_term j=construction_source_term k"
      and origin: "construction_source_at xs B k S" and literal: "q=Target_Term (Whole_Artifact S)"
      by (simp only: calls; blast)
    have same: "j=k" using index by (simp only: construction_source_term_exact)
    have subject: "S=R" by (rule unique) (use origin same in simp)
    show "q=Target_Term (Whole_Artifact R)" using literal subject by simp
  next
    assume expected: "q=Target_Term (Whole_Artifact R)"
    have support: "\<exists>k S. construction_source_term j=construction_source_term k \<and>
        construction_source_at xs B k S \<and> q=Target_Term (Whole_Artifact S)"
      by (rule exI[of _ j], rule exI[of _ R]) (use source expected in simp)
    show "(243,Pair_Term p q)\<in>positive_meaning source_system" by (rule iffD2[OF calls support])
  qed
  show ?thesis using "value" by (simp only: result shape(1); simp)
qed

lemma source_lookup_query_boundary:
  assumes "(243,t)\<in>positive_meaning source_system"
  shows "\<exists>z p q. t=Pair_Term p q \<and> source_query_presents z p"
proof -
  obtain x b j q where shape: "t=Pair_Term (Pair_Term (Pair_Term x b) j) q"
    and admitted: "(242,Pair_Term x b)\<in>positive_meaning source_system"
    using assms by (simp only: source_lookup_calls; blast)
  obtain C where "context": "source_context_presents C (Pair_Term x b)"
    using admitted by (simp only: source_context_exact; blast)
  obtain xs B where C: "C=(xs,B)" by (cases C) auto
  obtain k R where selected: "j=construction_source_term k" "construction_source_at xs B k R"
    using assms source_lookup_at_context[OF "context"[unfolded C], of j q] shape by blast
  have query: "source_query_presents ((xs,B),k) (Pair_Term (Pair_Term x b) j)"
    using "context" selected by (simp only: source_query_at C; blast)
  show ?thesis using shape query by blast
qed

theorem source_lookup_exact:
  "(243,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>z p q. t=Pair_Term p q \<and> source_query_presents z p \<and>
      artifact_literal_presents (source_query_value z) q)"
  using source_lookup_query_boundary source_lookup_output by blast

lemma source_query_native_class:
  "presentation_class source_query_presents source_query_domain
    (\<lambda>p. \<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system)"
proof -
  have boundary: "(\<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system) \<longleftrightarrow>
      (\<exists>z. source_query_presents z p)" for p
  proof
    assume "\<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system"
    then obtain q where holds: "(243,Pair_Term p q)\<in>positive_meaning source_system" by blast
    show "\<exists>z. source_query_presents z p" using source_lookup_query_boundary[OF holds] by auto
  next
    assume "\<exists>z. source_query_presents z p"
    then obtain z where query: "source_query_presents z p" by blast
    have formed: "exact_formed (source_query_value z)"
      by (rule source_query_value_formed[OF source_queries.subject_boundary[OF query]])
    have holds: "(243,Pair_Term p (Target_Term (Whole_Artifact (source_query_value z))))\<in>positive_meaning source_system"
      using source_lookup_output[OF query, of "Target_Term (Whole_Artifact (source_query_value z))"] formed by simp
    show "\<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system" using holds by blast
  qed
  show ?thesis using source_query_presentation_class by (simp only: boundary)
qed

lemma source_lookup_presented:
  "(243,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
    presented_relation source_query_presents artifact_literal_presents (\<lambda>z R. R=source_query_value z) p q"
  by (auto simp: source_lookup_exact presented_relation_def)

interpretation source_lookup_reading: presented_function_contract
  source_query_presents source_query_domain "\<lambda>p. \<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system"
  artifact_literal_presents exact_formed "\<lambda>p. (237,p)\<in>positive_meaning source_system" source_query_value
  "\<lambda>p q. (243,Pair_Term p q)\<in>positive_meaning source_system"
  using source_query_native_class artifact_literal_native_class source_lookup_presented source_query_value_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def; blast)

text \<open>
  Source selection composes actual bounded position lookup or complete-table
  key lookup with the common source admission contract. The result is the
  existing source value on its actual domain, never a list or relation default.
  The complete class exports totality and invariance for every admitted query.
  Whole-table order may vary; input order and repeated positions remain part
  of the query subject.
\<close>

end
