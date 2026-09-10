theory Factor_Observation_Equations
  imports Factor_Observation_Clauses
begin

section \<open>Each finite call equation retains the entire binding boundary\<close>

lemma observation_member_valuation:
  "(303,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=(Pair_Term (h 0) (h 1)) \<and> ((5,(Pair_Term (h 1) (Pair_Term (h 0) (h 2))))\<in>positive_meaning observation_system))"
proof -
  have family: "((303,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 303" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_member_calls:
  "(303,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and>
      t=(Pair_Term v0 v1) \<and> ((5,(Pair_Term v1 (Pair_Term v0 v2)))\<in>positive_meaning observation_system))"
proof
  assume "(303,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and>
      t=(Pair_Term v0 v1) \<and> ((5,(Pair_Term v1 (Pair_Term v0 v2)))\<in>positive_meaning observation_system)"
    by (simp only: observation_member_valuation) blast
next
  assume "\<exists>v0 v1 v2. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and>
      t=(Pair_Term v0 v1) \<and> ((5,(Pair_Term v1 (Pair_Term v0 v2)))\<in>positive_meaning observation_system)"
  then obtain v0 v1 v2 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2" "t=(Pair_Term v0 v1)" "(5,(Pair_Term v1 (Pair_Term v0 v2)))\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else v2"
  show "(303,t)\<in>positive_meaning observation_system"
    by (simp only: observation_member_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_absent_valuation:
  "(304,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=(Pair_Term (h 0) (h 1)) \<and> ((2,(h 1))\<in>positive_meaning observation_system \<and> (132,(Pair_Term (h 1) (h 0)))\<in>positive_meaning observation_system))"
proof -
  have family: "((304,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 304" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_absent_calls:
  "(304,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (132,(Pair_Term v1 v0))\<in>positive_meaning observation_system))"
proof
  assume "(304,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (132,(Pair_Term v1 v0))\<in>positive_meaning observation_system)"
    by (simp only: observation_absent_valuation) blast
next
  assume "\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (132,(Pair_Term v1 v0))\<in>positive_meaning observation_system)"
  then obtain v0 v1 where parts: "term_formed v0 \<and> term_formed v1" "t=(Pair_Term v0 v1)" "(2,v1)\<in>positive_meaning observation_system \<and> (132,(Pair_Term v1 v0))\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else v1"
  show "(304,t)\<in>positive_meaning observation_system"
    by (simp only: observation_absent_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_context_valuation:
  "(295,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=(Pair_Term (h 0) (h 1)) \<and> ((4,(h 0))\<in>positive_meaning observation_system \<and> (2,(h 1))\<in>positive_meaning observation_system))"
proof -
  have family: "((295,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 295" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_context_calls:
  "(295,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((4,v0)\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system))"
proof
  assume "(295,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((4,v0)\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system)"
    by (simp only: observation_context_valuation) blast
next
  assume "\<exists>v0 v1. term_formed v0 \<and> term_formed v1 \<and>
      t=(Pair_Term v0 v1) \<and> ((4,v0)\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system)"
  then obtain v0 v1 where parts: "term_formed v0 \<and> term_formed v1" "t=(Pair_Term v0 v1)" "(4,v0)\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else v1"
  show "(295,t)\<in>positive_meaning observation_system"
    by (simp only: observation_context_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_keep_valuation:
  "(296,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=(Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (h 1) (h 3)))) \<and> ((303,(Pair_Term (h 0) (h 2)))\<in>positive_meaning observation_system \<and> (2,(h 1))\<in>positive_meaning observation_system \<and> (2,(h 3))\<in>positive_meaning observation_system))"
proof -
  have family: "((296,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 296" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_keep_calls:
  "(296,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v1 v3))) \<and> ((303,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system))"
proof
  assume "(296,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v1 v3))) \<and> ((303,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system)"
    by (simp only: observation_keep_valuation) blast
next
  assume "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v1 v3))) \<and> ((303,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system)"
  then obtain v0 v1 v2 v3 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3" "t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v1 v3)))" "(303,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else if i=2 then v2 else v3"
  show "(296,t)\<in>positive_meaning observation_system"
    by (simp only: observation_keep_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_omit_valuation:
  "(297,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and> term_formed (h 4) \<and>
      t=(Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (h 3) (h 4)))) \<and> (((4,(h 0))\<in>positive_meaning observation_system \<and> (3,(Pair_Term (h 1) (h 3)))\<in>positive_meaning observation_system \<and> (2,(h 2))\<in>positive_meaning observation_system \<and> (2,(h 4))\<in>positive_meaning observation_system) \<or> ((304,(Pair_Term (h 0) (h 2)))\<in>positive_meaning observation_system \<and> (2,(h 1))\<in>positive_meaning observation_system \<and> (2,(h 3))\<in>positive_meaning observation_system \<and> (2,(h 4))\<in>positive_meaning observation_system)))"
proof -
  have family: "((297,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 297" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call ex_disj_distrib conj_disj_distribL conj_disj_distribR)
qed

lemma observation_omit_calls:
  "(297,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2 v3 v4. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v3 v4))) \<and> (((4,v0)\<in>positive_meaning observation_system \<and> (3,(Pair_Term v1 v3))\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system) \<or> ((304,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system)))"
proof
  assume "(297,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2 v3 v4. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v3 v4))) \<and> (((4,v0)\<in>positive_meaning observation_system \<and> (3,(Pair_Term v1 v3))\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system) \<or> ((304,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system))"
    by (simp only: observation_omit_valuation) blast
next
  assume "\<exists>v0 v1 v2 v3 v4. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and>
      t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v3 v4))) \<and> (((4,v0)\<in>positive_meaning observation_system \<and> (3,(Pair_Term v1 v3))\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system) \<or> ((304,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system))"
  then obtain v0 v1 v2 v3 v4 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4" "t=(Pair_Term (Pair_Term v0 v1) (Pair_Term v2 (Pair_Term v3 v4)))" "((4,v0)\<in>positive_meaning observation_system \<and> (3,(Pair_Term v1 v3))\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system) \<or> ((304,(Pair_Term v0 v2))\<in>positive_meaning observation_system \<and> (2,v1)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system \<and> (2,v4)\<in>positive_meaning observation_system)" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else if i=2 then v2 else if i=3 then v3 else v4"
  show "(297,t)\<in>positive_meaning observation_system"
    by (simp only: observation_omit_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_pair_valuation:
  "(299,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=(Pair_Term (h 0) (Pair_Term (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) (Pair_Term (h 1) (h 3)))) \<and> ((2,(h 1))\<in>positive_meaning observation_system \<and> (2,(h 2))\<in>positive_meaning observation_system \<and> (2,(h 3))\<in>positive_meaning observation_system))"
proof -
  have family: "((299,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 299" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_pair_calls:
  "(299,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term (Pair_Term v1 (Pair_Term v2 v3)) (Pair_Term v1 v3))) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system))"
proof
  assume "(299,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term (Pair_Term v1 (Pair_Term v2 v3)) (Pair_Term v1 v3))) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system)"
    by (simp only: observation_pair_valuation) blast
next
  assume "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term (Pair_Term v1 (Pair_Term v2 v3)) (Pair_Term v1 v3))) \<and> ((2,v1)\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system)"
  then obtain v0 v1 v2 v3 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3" "t=(Pair_Term v0 (Pair_Term (Pair_Term v1 (Pair_Term v2 v3)) (Pair_Term v1 v3)))" "(2,v1)\<in>positive_meaning observation_system \<and> (2,v2)\<in>positive_meaning observation_system \<and> (2,v3)\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else if i=2 then v2 else v3"
  show "(299,t)\<in>positive_meaning observation_system"
    by (simp only: observation_pair_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_profile_valuation:
  "(301,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=(Pair_Term (h 0) (Pair_Term (h 1) (h 2))) \<and> ((298,(Pair_Term (h 0) (Pair_Term (h 1) (h 3))))\<in>positive_meaning observation_system \<and> (300,(Pair_Term (h 0) (Pair_Term (h 3) (h 2))))\<in>positive_meaning observation_system))"
proof -
  have family: "((301,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 301" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_profile_calls:
  "(301,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term v1 v2)) \<and> ((298,(Pair_Term v0 (Pair_Term v1 v3)))\<in>positive_meaning observation_system \<and> (300,(Pair_Term v0 (Pair_Term v3 v2)))\<in>positive_meaning observation_system))"
proof
  assume "(301,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term v1 v2)) \<and> ((298,(Pair_Term v0 (Pair_Term v1 v3)))\<in>positive_meaning observation_system \<and> (300,(Pair_Term v0 (Pair_Term v3 v2)))\<in>positive_meaning observation_system)"
    by (simp only: observation_profile_valuation) blast
next
  assume "\<exists>v0 v1 v2 v3. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and>
      t=(Pair_Term v0 (Pair_Term v1 v2)) \<and> ((298,(Pair_Term v0 (Pair_Term v1 v3)))\<in>positive_meaning observation_system \<and> (300,(Pair_Term v0 (Pair_Term v3 v2)))\<in>positive_meaning observation_system)"
  then obtain v0 v1 v2 v3 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3" "t=(Pair_Term v0 (Pair_Term v1 v2))" "(298,(Pair_Term v0 (Pair_Term v1 v3)))\<in>positive_meaning observation_system \<and> (300,(Pair_Term v0 (Pair_Term v3 v2)))\<in>positive_meaning observation_system" by blast
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else if i=2 then v2 else v3"
  show "(301,t)\<in>positive_meaning observation_system"
    by (simp only: observation_profile_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

lemma observation_losses_valuation:
  "(306,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and> term_formed (h 4) \<and> term_formed (h 5) \<and> term_formed (h 6) \<and>
      t=(Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (Pair_Term (h 3) (h 4))) \<and> ((301,(Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 3) (h 5))))\<in>positive_meaning observation_system \<and> (301,(Pair_Term (Pair_Term (h 0) (h 2)) (Pair_Term (h 3) (h 6))))\<in>positive_meaning observation_system \<and> (305,(Pair_Term (h 6) (Pair_Term (h 5) (h 4))))\<in>positive_meaning observation_system))"
proof -
  have family: "((306,c),S)\<in>system_clauses observation_system \<longleftrightarrow> (c,S)\<in>observation_clause_family 306" for c S
    by (rule observation_clause) simp
  show ?thesis
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family observation_clause_family_def observation_schema_defs
        schema_variables_def observation_call)
qed

lemma observation_losses_calls:
  "(306,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>v0 v1 v2 v3 v4 v5 v6. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and> term_formed v5 \<and> term_formed v6 \<and>
      t=(Pair_Term (Pair_Term v0 (Pair_Term v1 v2)) (Pair_Term v3 v4)) \<and> ((301,(Pair_Term (Pair_Term v0 v1) (Pair_Term v3 v5)))\<in>positive_meaning observation_system \<and> (301,(Pair_Term (Pair_Term v0 v2) (Pair_Term v3 v6)))\<in>positive_meaning observation_system \<and> (305,(Pair_Term v6 (Pair_Term v5 v4)))\<in>positive_meaning observation_system))"
proof
  assume "(306,t)\<in>positive_meaning observation_system"
  then show "\<exists>v0 v1 v2 v3 v4 v5 v6. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and> term_formed v5 \<and> term_formed v6 \<and>
      t=(Pair_Term (Pair_Term v0 (Pair_Term v1 v2)) (Pair_Term v3 v4)) \<and> ((301,(Pair_Term (Pair_Term v0 v1) (Pair_Term v3 v5)))\<in>positive_meaning observation_system \<and> (301,(Pair_Term (Pair_Term v0 v2) (Pair_Term v3 v6)))\<in>positive_meaning observation_system \<and> (305,(Pair_Term v6 (Pair_Term v5 v4)))\<in>positive_meaning observation_system)"
    apply (simp only: observation_losses_valuation)
    apply (elim exE)
    subgoal for h
      by (intro exI[of _ "h 0"] exI[of _ "h 1"] exI[of _ "h 2"]
        exI[of _ "h 3"] exI[of _ "h 4"] exI[of _ "h 5"] exI[of _ "h 6"]) assumption
    done
next
  assume "\<exists>v0 v1 v2 v3 v4 v5 v6. term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and> term_formed v5 \<and> term_formed v6 \<and>
      t=(Pair_Term (Pair_Term v0 (Pair_Term v1 v2)) (Pair_Term v3 v4)) \<and> ((301,(Pair_Term (Pair_Term v0 v1) (Pair_Term v3 v5)))\<in>positive_meaning observation_system \<and> (301,(Pair_Term (Pair_Term v0 v2) (Pair_Term v3 v6)))\<in>positive_meaning observation_system \<and> (305,(Pair_Term v6 (Pair_Term v5 v4)))\<in>positive_meaning observation_system)"
  then obtain v0 v1 v2 v3 v4 v5 v6 where parts: "term_formed v0 \<and> term_formed v1 \<and> term_formed v2 \<and> term_formed v3 \<and> term_formed v4 \<and> term_formed v5 \<and> term_formed v6" "t=(Pair_Term (Pair_Term v0 (Pair_Term v1 v2)) (Pair_Term v3 v4))" "(301,(Pair_Term (Pair_Term v0 v1) (Pair_Term v3 v5)))\<in>positive_meaning observation_system \<and> (301,(Pair_Term (Pair_Term v0 v2) (Pair_Term v3 v6)))\<in>positive_meaning observation_system \<and> (305,(Pair_Term v6 (Pair_Term v5 v4)))\<in>positive_meaning observation_system" by (elim exE) (rule that; blast)
  let ?h="\<lambda>i::nat. if i=0 then v0 else if i=1 then v1 else if i=2 then v2 else if i=3 then v3 else if i=4 then v4 else if i=5 then v5 else v6"
  show "(306,t)\<in>positive_meaning observation_system"
    by (simp only: observation_losses_valuation; rule exI[of _ ?h]) (use parts in auto)
qed

end
