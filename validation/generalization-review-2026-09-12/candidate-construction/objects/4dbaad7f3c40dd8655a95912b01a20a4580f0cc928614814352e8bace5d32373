theory Factor_Construction_Comparison
  imports Factor_Collection_Correspondence Factor_Construction_Contracts Factor_List_Profiles
begin

section \<open>Complete account comparison uses actual component calls\<close>

definition construction_selection_comparison_schema :: "(nat,nat,nat) factor_schema" where
  "construction_selection_comparison_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
      (Pattern_Pair data_x (Pattern_Pair data_y data_w)))
    {(0,256,Pattern_Pair data_z data_w)}"

definition construction_comparison_schema :: "(nat,nat,nat) factor_schema" where
  "construction_comparison_schema=data_rule
    (Pattern_Pair
      (foldr Pattern_Pair [data_x,data_y,data_z,data_w,Pattern_Variable 4]
        (Pattern_Target (Whole_Artifact empty_artifact)))
      (foldr Pattern_Pair [data_x,Pattern_Variable 5,Pattern_Variable 6,Pattern_Variable 7,Pattern_Variable 4]
        (Pattern_Target (Whole_Artifact empty_artifact))))
    {(0,250,foldr Pattern_Pair [data_x,data_y,data_z,data_w,Pattern_Variable 4]
        (Pattern_Target (Whole_Artifact empty_artifact))),
     (1,250,foldr Pattern_Pair [data_x,Pattern_Variable 5,Pattern_Variable 6,Pattern_Variable 7,Pattern_Variable 4]
        (Pattern_Target (Whole_Artifact empty_artifact))),
     (2,256,Pattern_Pair data_y (Pattern_Variable 5)),
     (3,260,Pattern_Pair data_z (Pattern_Variable 6)),
     (4,256,Pattern_Pair data_w (Pattern_Variable 7))}"

definition construction_comparison_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "construction_comparison_clause_family d=(if d=251 then {(0,data_rule data_x {})}
    else if d=252 then list_profile_clauses 251 252
    else if d=253 then {(0,data_rule (Pattern_Pair data_x data_x) {})}
    else if d=254 then related_selection_clauses 251 252 253 254
    else if d=255 then related_bag_clauses 254 255
    else if d=256 then {(0,enumerated_comparison_schema 233 255)}
    else if d=257 then {(0,construction_selection_comparison_schema)}
    else if d=258 then related_selection_clauses 251 252 257 258
    else if d=259 then related_bag_clauses 258 259
    else if d=260 then {(0,enumerated_comparison_schema 233 259)}
    else if d=261 then {(0,construction_comparison_schema)} else {})"

lemmas construction_comparison_schema_defs = construction_selection_comparison_schema_def
  construction_comparison_schema_def enumerated_comparison_schema_def list_profile_clauses_def
  data_list_nil_schema_def list_step_schema_def related_selection_clauses_def
  related_selection_here_schema_def selection_later_schema_def related_bag_clauses_def
  bag_nil_schema_def bag_step_schema_def

definition construction_comparison_group_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_comparison_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{251,252,253,254,255,256,257,258,259,260,261}},
    system_clauses={((d,c),S). d\<in>{251,252,253,254,255,256,257,258,259,260,261} \<and>
      (c,S)\<in>construction_comparison_clause_family d}\<rparr>"

lemma construction_comparison_group_definitions [simp]:
  "system_definitions construction_comparison_group_system={251,252,253,254,255,256,257,258,259,260,261}"
  by (auto simp: construction_comparison_group_system_def system_definitions_def rel_dom_def)

lemma construction_comparison_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces construction_comparison_group_system \<longleftrightarrow>
    d\<in>system_definitions construction_comparison_group_system \<and> p=Pattern_Variable 0"
  by (simp only: construction_comparison_group_definitions; auto simp: construction_comparison_group_system_def)

lemma construction_comparison_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses construction_comparison_group_system \<longleftrightarrow>
    d\<in>system_definitions construction_comparison_group_system \<and>
    (c,S)\<in>construction_comparison_clause_family d"
  by (simp only: construction_comparison_group_definitions; auto simp: construction_comparison_group_system_def)

lemma construction_comparison_group_formed_over:
  "schema_system_formed_over {233,250} construction_comparison_group_system"
proof -
  have finite: "finite (construction_comparison_clause_family d)" for d
    by (simp add: construction_comparison_clause_family_def construction_comparison_schema_defs)
  have functional: "single_valued (construction_comparison_clause_family d)" for d
    by (auto simp: construction_comparison_clause_family_def construction_comparison_schema_defs
      single_valued_def split: if_splits)
  have schemas: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{233,250}\<union>system_definitions construction_comparison_group_system"
    if "(c,S)\<in>construction_comparison_clause_family d" for c S d
    using that by (auto simp: construction_comparison_clause_family_def construction_comparison_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def split: if_splits)
  show ?thesis
    by (rule schema_system_formed_over_families[where D="system_definitions construction_comparison_group_system"
        and p="\<lambda>_. Pattern_Variable 0" and C=construction_comparison_clause_family])
      (use finite functional schemas in
        \<open>simp_all only: construction_comparison_group_definitions; auto simp: construction_comparison_group_system_def\<close>)+
qed

lemma construction_comparison_external_dependencies:
  "system_external_dependencies construction_comparison_group_system={233,250}"
proof -
  have bounded: "system_external_dependencies construction_comparison_group_system\<subseteq>{233,250}"
    by (rule system_external_dependencies_boundary[OF construction_comparison_group_formed_over])
  have reached: "e\<in>system_external_dependencies construction_comparison_group_system"
    if "((d,c),S)\<in>system_clauses construction_comparison_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions construction_comparison_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses construction_comparison_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3) by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have conversion: "233\<in>system_external_dependencies construction_comparison_group_system"
    by (rule reached[where d=256 and c=0 and S="enumerated_comparison_schema 233 255"])
      (auto simp: construction_comparison_clause_family_def)
  have admission: "250\<in>system_external_dependencies construction_comparison_group_system"
    by (rule reached[where d=261 and c=0 and S=construction_comparison_schema])
      (auto simp: construction_comparison_clause_family_def construction_comparison_schema_def
        schema_dependencies_def rel_ran_image)
  show ?thesis using bounded conversion admission by blast
qed

definition construction_comparison_base_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_comparison_base_system=rooted_system construction_admission_system
    (system_external_dependencies construction_comparison_group_system)"

lemma construction_comparison_base_formed [simp]: "schema_system_formed construction_comparison_base_system"
  unfolding construction_comparison_base_system_def by (rule rooted_system_formed[OF construction_admission_system_formed])

lemma construction_comparison_base_subdomain:
  "system_definitions construction_comparison_base_system\<subseteq>system_definitions construction_admission_system"
  unfolding construction_comparison_base_system_def by (rule rooted_system_subdomain)

lemma construction_comparison_base_bound:
  "system_definitions construction_comparison_base_system\<subseteq>{..250}"
proof -
  have parent: "system_definitions construction_admission_base_system\<subseteq>{..244}"
    using construction_admission_base_subdomain by (auto dest: subsetD)
  have domain: "system_definitions construction_admission_system\<subseteq>{..250}"
    using parent by (auto dest: subsetD)
  show ?thesis by (rule subset_trans[OF construction_comparison_base_subdomain domain])
qed

lemma construction_comparison_base_roots:
  "{233,250}\<subseteq>system_definitions construction_comparison_base_system"
proof -
  have roots: "{233,250}\<subseteq>system_definitions construction_admission_system"
    using construction_admission_base_roots by auto
  show ?thesis unfolding construction_comparison_base_system_def construction_comparison_external_dependencies
    by (rule rooted_system_roots[OF construction_admission_system_formed roots])
qed

lemma construction_comparison_base_least:
  assumes "{233,250}\<subseteq>U" "system_dependency_closed construction_admission_system U"
  shows "system_definitions construction_comparison_base_system\<subseteq>U"
proof -
  have roots: "{233,250}\<subseteq>system_definitions construction_admission_system"
    using construction_admission_base_roots by auto
  show ?thesis unfolding construction_comparison_base_system_def construction_comparison_external_dependencies
    by (rule rooted_system_least[OF construction_admission_system_formed roots assms])
qed

lemma construction_comparison_base_call:
  "schema_call_formed construction_comparison_base_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_comparison_base_system \<and> term_formed t"
  unfolding construction_comparison_base_system_def
  by (rule rooted_system_variable_calls[OF construction_admission_system_formed construction_admission_call])

interpretation construction_comparison_group:
  positive_definition_group construction_comparison_base_system construction_comparison_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF construction_comparison_group_formed_over construction_comparison_base_roots]
      construction_comparison_base_bound in \<open>auto dest: subsetD\<close>)

definition construction_comparison_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_comparison_system=system_union construction_comparison_base_system construction_comparison_group_system"

lemma construction_comparison_system_formed [simp]: "schema_system_formed construction_comparison_system"
  using construction_comparison_group.formed by (simp only: construction_comparison_system_def)

lemma construction_comparison_system_definitions [simp]:
  "system_definitions construction_comparison_system=
    system_definitions construction_comparison_base_system\<union>system_definitions construction_comparison_group_system"
  by (simp add: construction_comparison_system_def)

lemma construction_comparison_definition_bound:
  "system_definitions construction_comparison_system\<subseteq>{..261}"
  using construction_comparison_base_bound by (auto dest: subsetD)

lemma construction_comparison_call:
  "schema_call_formed construction_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_comparison_system \<and> term_formed t"
  unfolding construction_comparison_system_def
  by (rule construction_comparison_group.variable_calls[OF construction_comparison_base_call construction_comparison_group_interfaces])

lemma construction_comparison_clause:
  assumes "d\<in>system_definitions construction_comparison_group_system"
  shows "((d,c),S)\<in>system_clauses construction_comparison_system \<longleftrightarrow>
    (c,S)\<in>construction_comparison_clause_family d"
  using construction_comparison_group.group_clauses[OF assms] assms by (simp add: construction_comparison_system_def)

lemma construction_comparison_previous_meaning:
  assumes "d\<in>{233,250}"
  shows "(d,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning construction_admission_system"
proof -
  have member: "d\<in>system_definitions construction_comparison_base_system"
    using construction_comparison_base_roots assms by blast
  show ?thesis using construction_comparison_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF construction_admission_system_formed member[unfolded construction_comparison_base_system_def], of t]
    by (simp only: construction_comparison_system_def construction_comparison_base_system_def; blast)
qed

lemma construction_comparison_components:
  "(233,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
  "(250,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> (\<exists>a. construction_account_presents a t)"
  by (simp_all add: construction_comparison_previous_meaning construction_admission_components construction_admission_exact)

section \<open>Literal terms and related rows instantiate the same occurrence proof\<close>

lemma construction_comparison_value:
  "(251,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> term_formed t"
proof -
  have equation: "(251,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=h 0)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: construction_comparison_clause construction_comparison_clause_family_def schema_variables_def construction_comparison_call)
  show ?thesis by (simp only: equation; rule iffI) (blast, rule exI[of _ "\<lambda>_. t"], simp)
qed

lemma construction_comparison_literal:
  "(253,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    (\<exists>p. term_formed p \<and> t=Pair_Term p p)"
proof -
  have equation: "(253,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=Pair_Term (h 0) (h 0))"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: construction_comparison_clause construction_comparison_clause_family_def schema_variables_def construction_comparison_call)
  show ?thesis
  proof (simp only: equation; rule iffI)
    assume "\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=Pair_Term (h 0) (h 0)"
    then show "\<exists>p. term_formed p \<and> t=Pair_Term p p" by blast
  next
    assume "\<exists>p. term_formed p \<and> t=Pair_Term p p"
    then obtain p where parts: "term_formed p" "t=Pair_Term p p" by blast
    show "\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=Pair_Term (h 0) (h 0)"
      by (rule exI[of _ "\<lambda>_. p"]) (use parts in simp)
  qed
qed

interpretation construction_comparison_lists: list_profile construction_comparison_system 251 252
  by (unfold_locales)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def construction_comparison_call)

interpretation construction_literal_bags: related_occurrences construction_comparison_system 251 252 253 254 255 "\<lambda>_. True"
  by (unfold_locales)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def construction_comparison_call
      construction_comparison_value construction_comparison_lists.exact construction_comparison_literal)

interpretation construction_selection_bags: related_occurrences construction_comparison_system 251 252 257 258 259 "\<lambda>_. True"
  by (unfold_locales)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def construction_comparison_call
      construction_comparison_value construction_comparison_lists.exact
      dest: positive_meaning_formed schema_call_formed_target)

interpretation construction_literal_enumerations: enumerated_comparison_profile construction_comparison_system 256 233 255
  by (unfold_locales)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def construction_comparison_call
      construction_comparison_components term_sequence_enumeration_exact)

interpretation construction_selection_enumerations: enumerated_comparison_profile construction_comparison_system 260 233 259
  by (unfold_locales)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def construction_comparison_call
      construction_comparison_components term_sequence_enumeration_exact)

lemma construction_literal_collections:
  assumes first: "finite_collection_presents (\<lambda>a p. p=f a) A p"
    and second: "finite_collection_presents (\<lambda>a p. p=f a) B q"
    and formed: "term_formed p" "term_formed q" and injective: "inj f"
  shows "(256,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> A=B"
proof -
  let ?read="\<lambda>a p. p=f a \<and> term_formed p"
  have left: "finite_collection_presents ?read A p" and right: "finite_collection_presents ?read B q"
    using first second formed by (simp_all only: finite_collection_formed_readings)
  have comparison: "(253,Pair_Term u v)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> a=b"
    if "?read a u" "?read b v" for a b u v
    using that injective by (auto simp: construction_comparison_literal dest: injD)
  show ?thesis
    by (rule construction_literal_bags.comparison_enumerations[
      OF construction_literal_enumerations.enumerated_comparison_profile_axioms left right comparison])
qed

lemma construction_literal_tables:
  assumes first: "finite_table_presents K (\<lambda>a p. p=V a) A p"
    and second: "finite_table_presents K (\<lambda>a p. p=V a) B q"
    and formed: "term_formed p" "term_formed q" and keys: "inj K" and value_encoding: "inj V"
  shows "(256,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> A=B"
proof -
  let ?f="\<lambda>z. Pair_Term (K (fst z)) (V (snd z))"
  have row: "table_entry_presents K (\<lambda>a p. p=V a)=(\<lambda>z p. p=?f z)"
    by (intro ext) (auto simp: table_entry_presents_def)
  have injective: "inj ?f" using keys value_encoding by (auto simp: inj_on_def)
  show ?thesis by (rule construction_literal_collections[OF _ _ formed injective])
    (use first second in \<open>auto simp: finite_table_presents_def row\<close>)
qed

lemma construction_selection_comparison_pair:
  "(257,Pair_Term (Pair_Term k (Pair_Term j a)) (Pair_Term l (Pair_Term i b)))
      \<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    k=l \<and> j=i \<and> term_formed k \<and> term_formed j \<and>
      (256,Pair_Term a b)\<in>positive_meaning construction_comparison_system"
proof -
  have equation: "(257,z)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>n\<in>{0,1,2,3}. term_formed (h n)) \<and>
        z=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2)))
          (Pair_Term (h 0) (Pair_Term (h 1) (h 3))) \<and>
        (256,Pair_Term (h 2) (h 3))\<in>positive_meaning construction_comparison_system)" for z
    by (subst ordinary_positive_entry_valuation)
      (auto simp: construction_comparison_clause construction_comparison_clause_family_def
        construction_selection_comparison_schema_def schema_variables_def construction_comparison_call)
  have formed: "term_formed a \<and> term_formed b"
    if "(256,Pair_Term a b)\<in>positive_meaning construction_comparison_system"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show ?thesis
  proof (simp only: equation; rule iffI)
    show "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>n\<in>{0,1,2,3}. term_formed (h n)) \<and>
        Pair_Term (Pair_Term k (Pair_Term j a)) (Pair_Term l (Pair_Term i b))=
          Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (Pair_Term (h 0) (Pair_Term (h 1) (h 3))) \<and>
        (256,Pair_Term (h 2) (h 3))\<in>positive_meaning construction_comparison_system \<Longrightarrow>
      k=l \<and> j=i \<and> term_formed k \<and> term_formed j \<and>
        (256,Pair_Term a b)\<in>positive_meaning construction_comparison_system" by auto
    assume parts: "k=l \<and> j=i \<and> term_formed k \<and> term_formed j \<and>
      (256,Pair_Term a b)\<in>positive_meaning construction_comparison_system"
    show "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>n\<in>{0,1,2,3}. term_formed (h n)) \<and>
        Pair_Term (Pair_Term k (Pair_Term j a)) (Pair_Term l (Pair_Term i b))=
          Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (Pair_Term (h 0) (Pair_Term (h 1) (h 3))) \<and>
        (256,Pair_Term (h 2) (h 3))\<in>positive_meaning construction_comparison_system"
      by (rule exI[of _ "\<lambda>n::nat. if n=0 then k else if n=1 then j else if n=2 then a else b"])
        (use parts formed in auto)
  qed
qed

lemma construction_selection_rows:
  assumes first: "table_entry_presents Payload_Term construction_selection_presents z p" "term_formed p"
    and second: "table_entry_presents Payload_Term construction_selection_presents w q" "term_formed q"
  shows "(257,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> z=w"
proof -
  obtain a where left: "finite_set_presents Payload_Term (snd (snd z)) a"
    "p=Pair_Term (Payload_Term (fst z)) (Pair_Term (construction_source_term (fst (snd z))) a)"
    using first(1) by (auto simp: table_entry_presents_def construction_selection_presents_def)
  obtain b where right: "finite_set_presents Payload_Term (snd (snd w)) b"
    "q=Pair_Term (Payload_Term (fst w)) (Pair_Term (construction_source_term (fst (snd w))) b)"
    using second(1) by (auto simp: table_entry_presents_def construction_selection_presents_def)
  have fields: "term_formed (Payload_Term (fst z))" "term_formed (construction_source_term (fst (snd z)))"
    "term_formed a" "term_formed b" using first(2) second(2) left(2) right(2) by auto
  have atoms: "(256,Pair_Term a b)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      snd (snd z)=snd (snd w)"
    by (rule construction_literal_collections[OF left(1)[unfolded finite_set_presents_def]
      right(1)[unfolded finite_set_presents_def] fields(3,4) payload_term_injective])
  show ?thesis by (simp only: left(2) right(2) construction_selection_comparison_pair fields atoms
      factor_term.inject construction_source_term_exact; cases z; cases w; auto)
qed

lemma construction_selection_tables:
  assumes first: "finite_table_presents Payload_Term construction_selection_presents A p" "term_formed p"
    and second: "finite_table_presents Payload_Term construction_selection_presents B q" "term_formed q"
  shows "(260,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> A=B"
proof -
  let ?read="\<lambda>z t. table_entry_presents Payload_Term construction_selection_presents z t \<and> term_formed t"
  have left: "finite_collection_presents ?read A p" and right: "finite_collection_presents ?read B q"
    using first second by (auto simp: finite_collection_formed_readings finite_table_presents_def)
  have compare: "(257,Pair_Term u v)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> a=b"
    if "?read a u" "?read b v" for a b u v
    by (rule construction_selection_rows) (use that in auto)
  show ?thesis by (rule construction_selection_bags.comparison_enumerations[
    OF construction_selection_enumerations.enumerated_comparison_profile_axioms left right compare])
qed

section \<open>The native relation is exactly complete account correspondence\<close>

lemma construction_comparison_valuation:
  "(261,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (enumeration_term [h 0,h 1,h 2,h 3,h 4]) (enumeration_term [h 0,h 5,h 6,h 7,h 4]) \<and>
      (250,enumeration_term [h 0,h 1,h 2,h 3,h 4])\<in>positive_meaning construction_comparison_system \<and>
      (250,enumeration_term [h 0,h 5,h 6,h 7,h 4])\<in>positive_meaning construction_comparison_system \<and>
      (256,Pair_Term (h 1) (h 5))\<in>positive_meaning construction_comparison_system \<and>
      (260,Pair_Term (h 2) (h 6))\<in>positive_meaning construction_comparison_system \<and>
      (256,Pair_Term (h 3) (h 7))\<in>positive_meaning construction_comparison_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_comparison_clause construction_comparison_clause_family_def
      construction_comparison_schema_def schema_variables_def construction_comparison_call)

lemma construction_comparison_at_forms:
  "(261,Pair_Term (enumeration_term [x,b,s,orig,y]) (enumeration_term [x',b',s',orig',y']))
      \<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    x=x' \<and> y=y' \<and>
    (250,enumeration_term [x,b,s,orig,y])\<in>positive_meaning construction_comparison_system \<and>
    (250,enumeration_term [x',b',s',orig',y'])\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term b b')\<in>positive_meaning construction_comparison_system \<and>
    (260,Pair_Term s s')\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term orig orig')\<in>positive_meaning construction_comparison_system"
proof (rule iffI)
  assume "(261,Pair_Term (enumeration_term [x,b,s,orig,y]) (enumeration_term [x',b',s',orig',y']))
      \<in>positive_meaning construction_comparison_system"
  then show "x=x' \<and> y=y' \<and>
    (250,enumeration_term [x,b,s,orig,y])\<in>positive_meaning construction_comparison_system \<and>
    (250,enumeration_term [x',b',s',orig',y'])\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term b b')\<in>positive_meaning construction_comparison_system \<and>
    (260,Pair_Term s s')\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term orig orig')\<in>positive_meaning construction_comparison_system"
    by (auto simp: construction_comparison_valuation enumeration_term_injective)
next
  assume parts: "x=x' \<and> y=y' \<and>
    (250,enumeration_term [x,b,s,orig,y])\<in>positive_meaning construction_comparison_system \<and>
    (250,enumeration_term [x',b',s',orig',y'])\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term b b')\<in>positive_meaning construction_comparison_system \<and>
    (260,Pair_Term s s')\<in>positive_meaning construction_comparison_system \<and>
    (256,Pair_Term orig orig')\<in>positive_meaning construction_comparison_system"
  have first: "(250,enumeration_term [x,b,s,orig,y])\<in>positive_meaning construction_comparison_system"
    and second: "(250,enumeration_term [x',b',s',orig',y'])\<in>positive_meaning construction_comparison_system"
    using parts by blast+
  have first_formed: "term_formed (enumeration_term [x,b,s,orig,y])"
    using schema_call_formed_target[OF positive_meaning_formed[OF first]] by blast
  have second_formed: "term_formed (enumeration_term [x',b',s',orig',y'])"
    using schema_call_formed_target[OF positive_meaning_formed[OF second]] by blast
  have formed: "term_formed x" "term_formed b" "term_formed s" "term_formed orig" "term_formed y"
    "term_formed b'" "term_formed s'" "term_formed orig'"
    using first_formed second_formed by (auto simp: enumeration_term_formed)
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then b else if i=2 then s else if i=3 then orig
    else if i=4 then y else if i=5 then b' else if i=6 then s' else orig'"
  show "(261,Pair_Term (enumeration_term [x,b,s,orig,y]) (enumeration_term [x',b',s',orig',y']))
      \<in>positive_meaning construction_comparison_system"
    by (simp only: construction_comparison_valuation; rule exI[of _ ?h]) (use parts formed in auto)
qed

theorem construction_comparison_on_accounts:
  assumes first: "construction_account_presents a p" and second: "construction_account_presents b q"
  shows "(261,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> a=b"
proof -
  obtain xs B W where a: "a=((xs,B),W)" by (cases a; cases "fst a") auto
  obtain ys C X where b: "b=((ys,C),X)" by (cases b; cases "fst b") auto
  let ?R="construction_account_output a" and ?S="construction_account_output b"
  obtain bp sp orig_p where left:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) B bp"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections W) sp"
    "finite_table_presents construction_atom_term (\<lambda>v u. u=Payload_Term v) (construction_origins W) orig_p"
    "p=enumeration_term [artifact_list_term xs,bp,sp,orig_p,Target_Term (Whole_Artifact ?R)]"
    using first by (auto simp: construction_account_presents_def construction_claim_presents_def a)
  obtain bq sq orig_q where right:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) C bq"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections X) sq"
    "finite_table_presents construction_atom_term (\<lambda>v u. u=Payload_Term v) (construction_origins X) orig_q"
    "q=enumeration_term [artifact_list_term ys,bq,sq,orig_q,Target_Term (Whole_Artifact ?S)]"
    using second by (auto simp: construction_account_presents_def construction_claim_presents_def b)
  have pf: "term_formed bp" "term_formed sp" "term_formed orig_p"
    using construction_account_formed[OF first] left(4) by (auto simp: enumeration_term_formed)
  have qf: "term_formed bq" "term_formed sq" "term_formed orig_q"
    using construction_account_formed[OF second] right(4) by (auto simp: enumeration_term_formed)
  have literal: "inj (\<lambda>T. Target_Term (Whole_Artifact T))" by (auto simp: inj_on_def)
  have bases: "(256,Pair_Term bp bq)\<in>positive_meaning construction_comparison_system \<longleftrightarrow> B=C"
    by (rule construction_literal_tables[OF left(1) right(1) pf(1) qf(1) payload_term_injective literal])
  have selections: "(260,Pair_Term sp sq)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      construction_selections W=construction_selections X"
    by (rule construction_selection_tables[OF left(2) pf(2) right(2) qf(2)])
  have origins: "(256,Pair_Term orig_p orig_q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
      construction_origins W=construction_origins X"
    by (rule construction_literal_tables[OF left(3) right(3) pf(3) qf(3) construction_atom_term_injective payload_term_injective])
  have admitted: "(250,p)\<in>positive_meaning construction_comparison_system"
    "(250,q)\<in>positive_meaning construction_comparison_system"
  proof -
    show "(250,p)\<in>positive_meaning construction_comparison_system"
      by (simp only: construction_comparison_components; rule exI[of _ a]) (rule first)
    show "(250,q)\<in>positive_meaning construction_comparison_system"
      by (simp only: construction_comparison_components; rule exI[of _ b]) (rule second)
  qed
  have witness: "W=X \<longleftrightarrow> construction_selections W=construction_selections X \<and>
      construction_origins W=construction_origins X" by (cases W; cases X) auto
  show ?thesis
    by (simp only: left(4) right(4) construction_comparison_at_forms
        admitted[unfolded left(4) right(4)] bases selections origins artifact_list_term_exact factor_term.inject;
      use witness in \<open>auto simp: a b\<close>)
qed

theorem construction_comparison_exact:
  "(261,t)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)"
proof
  assume holds: "(261,t)\<in>positive_meaning construction_comparison_system"
  obtain p q where shape: "t=Pair_Term p q" and admitted:
    "(250,p)\<in>positive_meaning construction_comparison_system" "(250,q)\<in>positive_meaning construction_comparison_system"
    using holds by (simp only: construction_comparison_valuation; blast)
  obtain a b where read: "construction_account_presents a p" "construction_account_presents b q"
    using admitted by (auto simp: construction_comparison_components)
  have same: "a=b" using holds by (simp only: shape construction_comparison_on_accounts[OF read])
  have left: "construction_account_presents b p" using read(1) same by simp
  have related: "presentation_transport construction_account_presents construction_account_presents p q"
    unfolding presentation_transport_def by (rule exI[of _ b]) (rule conjI[OF left read(2)])
  show "\<exists>p q. t=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q"
    by (rule exI[of _ p], rule exI[of _ q]) (rule conjI[OF shape related])
next
  assume "\<exists>p q. t=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q"
  then obtain p q a where shape: "t=Pair_Term p q" and read: "construction_account_presents a p" "construction_account_presents a q"
    by (auto simp: presentation_transport_def)
  show "(261,t)\<in>positive_meaning construction_comparison_system"
    by (simp only: shape construction_comparison_on_accounts[OF read]; simp)
qed

corollary construction_comparison_at_pair:
  "(261,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    presentation_transport construction_account_presents construction_account_presents p q"
  by (auto simp: construction_comparison_exact)

interpretation construction_correspondence: presented_function_contract
  construction_account_presents construction_account_domain "\<lambda>p. \<exists>a. construction_account_presents a p"
  construction_account_presents construction_account_domain "\<lambda>p. \<exists>a. construction_account_presents a p" id
  "\<lambda>p q. (261,Pair_Term p q)\<in>positive_meaning construction_comparison_system"
  using construction_account_presentation_class
  by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def construction_comparison_at_pair
    presentation_transport_def presented_relation_def)

theorem construction_comparison_preserves_whole_account:
  assumes first: "construction_account_presents a p"
  shows "(261,Pair_Term p q)\<in>positive_meaning construction_comparison_system \<longleftrightarrow>
    construction_account_presents a q"
  using construction_correspondence.output[OF first, of q] by simp

theorem construction_comparison_rejects_invalid_side:
  assumes "\<not>(\<exists>a. construction_account_presents a p) \<or> \<not>(\<exists>a. construction_account_presents a q)"
  shows "(261,Pair_Term p q)\<notin>positive_meaning construction_comparison_system"
  using assms by (auto simp: construction_comparison_at_pair presentation_transport_def)

section \<open>One native program precedes every future pair of presentations\<close>

theorem native_construction_correspondence:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu Q k.
    closed_native_package_at C cu [] Q \<and> native_package_environment C cu []=C \<and>
    k\<in>system_definitions Q \<and> (\<forall>z. schema_call_formed Q k z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (k,z)\<in>positive_meaning Q \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q where compiled:
    "inj_on g (system_definitions construction_comparison_system)"
    "closed_native_package_at C cu [] Q" "native_package_environment C cu []=C"
    "system_alpha_variant (rename_system g construction_comparison_system) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning construction_comparison_system"
    using program_compilation_total[OF construction_comparison_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have member: "261\<in>system_definitions construction_comparison_system" by simp
  have target: "g 261\<in>system_definitions Q"
    using member compiled(4) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have call: "schema_call_formed Q (g 261) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF construction_comparison_system_formed
      compiled(1,4) member] construction_comparison_call; simp)
  have meaning: "(g 261,z)\<in>positive_meaning Q \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) member compiled(5)] construction_comparison_exact)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q], rule exI[of _ "g 261"])
    (use compiled(2,3) target call meaning in blast)
qed

text \<open>
  Eleven definitions contain sixteen ordinary clauses over the least closure
  of the two actual external entries: complete retermination and construction
  admission. Both submitted accounts are admitted in full. Literal occurrence
  matching compares base and origin rows, including exact artifact values.
  Related occurrence matching compares every selection row through its exact
  key, source coordinate, and complete selected-atom collection.

  The two ordered input lists and exact outputs are shared literal fields.
  The proved equation covers every raw argument and every permitted ordering
  inside all three unordered fields. It yields the complete identity function
  contract on accounts, including every compatible output presentation.
  Missing or malformed unused material is rejected by whole-account admission.
  The fixed native reference is obtained from these ordinary clauses before
  any supplied policy or future account is considered.
\<close>

end
