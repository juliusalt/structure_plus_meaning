theory Factor_Construction_Accounts
  imports Factor_Selection_Tables
begin

section \<open>A complete construction account has the original primitive basis\<close>

type_synonym construction_account = "construction_source_context\<times>addressed_construction"

abbreviation construction_account_output :: "construction_account \<Rightarrow> exact_artifact" where
  "construction_account_output a \<equiv>
    assembly_output (construction_assembly (fst (fst a)) (snd (fst a)) (snd a))"

abbreviation construction_account_domain :: "construction_account \<Rightarrow> bool" where
  "construction_account_domain a \<equiv>
    source_constructs (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a) \<and>
    construction_coordinates_formed (snd (fst a)) (snd a)"

definition construction_account_presents :: "construction_account \<Rightarrow> factor_term \<Rightarrow> bool" where
  "construction_account_presents a p \<longleftrightarrow> construction_account_domain a \<and>
    construction_claim_presents (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a) p"

lemma construction_account_presentation_class:
  "presentation_class construction_account_presents construction_account_domain
    (\<lambda>p. \<exists>a. construction_account_presents a p)"
proof (unfold_locales)
  fix a p assume "construction_account_presents a p"
  then show "construction_account_domain a" by (simp only: construction_account_presents_def; blast)
next
  fix a p assume "construction_account_presents a p"
  then show "\<exists>a. construction_account_presents a p" by blast
next
  fix a assume domain: "construction_account_domain a"
  have present: "construction_claim_presents (fst (fst a)) (snd (fst a)) (snd a)
      (construction_account_output a)
      (construction_claim_term (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a))"
    by (rule construction_claim_term_presents) (use domain in blast)
  show "\<exists>p. construction_account_presents a p"
    using present domain by (auto simp: construction_account_presents_def)
next
  fix p assume "\<exists>a. construction_account_presents a p"
  then show "\<exists>a. construction_account_presents a p" .
next
  fix a b p assume first: "construction_account_presents a p" and second: "construction_account_presents b p"
  have first_read: "construction_claim_presents (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a) p"
    and second_read: "construction_claim_presents (fst (fst b)) (snd (fst b)) (snd b) (construction_account_output b) p"
    using first second by (simp only: construction_account_presents_def; blast)+
  have "fst (fst a)=fst (fst b) \<and> snd (fst a)=snd (fst b) \<and> snd a=snd b"
    using construction_claim_presents_unique[OF first_read second_read] by blast
  then show "a=b" by (cases a; cases b) auto
qed

interpretation construction_accounts: presentation_class construction_account_presents construction_account_domain
  "\<lambda>p. \<exists>a. construction_account_presents a p"
  by (rule construction_account_presentation_class)

lemma construction_account_formed:
  assumes "construction_account_presents a p"
  shows "term_formed p"
  using assms by (auto simp: construction_account_presents_def intro: construction_claim_presents_formed)


lemma construction_account_fields:
  assumes "construction_account_presents a p"
  shows "\<exists>b s orig. p=enumeration_term [artifact_list_term (fst (fst a)),b,s,orig,
    Target_Term (Whole_Artifact (construction_account_output a))]"
  using assms by (auto simp: construction_account_presents_def construction_claim_presents_def)

lemma construction_account_at_claim:
  assumes present: "construction_claim_presents xs B W R p"
  shows "construction_account_presents ((xs,B),W) p \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W"
proof
  assume read: "construction_account_presents ((xs,B),W) p"
  have actual: "construction_claim_presents xs B W (assembly_output (construction_assembly xs B W)) p"
    and domain: "source_constructs xs B W (assembly_output (construction_assembly xs B W))"
      "construction_coordinates_formed B W"
    using read by (auto simp: construction_account_presents_def)
  have same: "R=assembly_output (construction_assembly xs B W)"
    using construction_claim_presents_unique[OF present actual] by blast
  show "source_constructs xs B W R \<and> construction_coordinates_formed B W" using domain by (simp only: same)
next
  assume built: "source_constructs xs B W R \<and> construction_coordinates_formed B W"
  have same: "R=assembly_output (construction_assembly xs B W)"
    using built by (simp only: source_constructs_iff_K2; blast)
  show "construction_account_presents ((xs,B),W) p"
    using built present by (simp add: construction_account_presents_def same)
qed

lemma construction_accounts_exact:
  "(\<exists>a. construction_account_presents a p) \<longleftrightarrow>
    (\<exists>xs B W R. source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
      construction_claim_presents xs B W R p)"
  using construction_account_at_claim by (auto simp: construction_account_presents_def; blast)

section \<open>The complete origin table crosses the same terminator boundary\<close>

lemma construction_origin_retermination:
  "composed_presentation (origin_table_presents payload_value_presents) enumeration_retermination Q p \<longleftrightarrow>
    (\<forall>z\<in>Q. octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z)) \<and> octets_formed (snd z)) \<and>
    finite_table_presents construction_atom_term (\<lambda>a q. q=Payload_Term a) Q p"
proof -
  have keys: "factor_pair_presents payload_value_presents payload_value_presents=
      (\<lambda>z p. (octets_formed (fst z) \<and> octets_formed (snd z)) \<and> p=construction_atom_term z)"
    by (intro ext) (auto simp: factor_pair_presents_def construction_atom_term_def)
  show ?thesis by (simp only: keys reterminated_literal_table_boundaries; blast)
qed

lemma construction_origin_native_retermination:
  "(\<exists>u. origin_table_presents payload_value_presents Q u \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)
        \<in>positive_meaning term_sequence_system) \<longleftrightarrow>
    (\<forall>z\<in>Q. octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z)) \<and> octets_formed (snd z)) \<and>
    finite_table_presents construction_atom_term (\<lambda>a q. q=Payload_Term a) Q p"
proof -
  have formed: "origin_table_presents payload_value_presents Q u \<Longrightarrow> term_formed u" for u
    using origin_table_value_formed[of payload_value_presents Q u] by auto
  show ?thesis using formed
    by (auto simp: term_sequence_enumeration_exact construction_origin_retermination[symmetric]
      composed_presentation_def)
qed

lemma construction_claim_context_fields:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and present: "construction_claim_presents xs B W R p"
  shows "\<exists>b s orig. p=enumeration_term [artifact_list_term xs,b,s,orig,Target_Term (Whole_Artifact R)] \<and>
    selection_context_presents ((xs,B),construction_selections W) (Pair_Term (Pair_Term (artifact_list_term xs) b) s) \<and>
    finite_table_presents construction_atom_term (\<lambda>a q. q=Payload_Term a) (construction_origins W) orig"
proof -
  obtain b s orig where shape: "p=enumeration_term [artifact_list_term xs,b,s,orig,Target_Term (Whole_Artifact R)]"
    and base: "finite_table_presents Payload_Term (\<lambda>T q. q=Target_Term (Whole_Artifact T)) B b"
    and selected: "finite_table_presents Payload_Term construction_selection_presents (construction_selections W) s"
    and origins: "finite_table_presents construction_atom_term (\<lambda>a q. q=Payload_Term a) (construction_origins W) orig"
    using present by (auto simp: construction_claim_presents_def)
  have domain: "selection_context_domain ((xs,B),construction_selections W)"
    using built coords by (simp only: selection_context_construction_boundary; auto simp: source_constructs_def)
  have "context": "source_context_presents (xs,B) (Pair_Term (artifact_list_term xs) b)"
    using domain base by (simp only: source_context_fields fst_conv snd_conv; blast)
  have table: "selection_table_presents (xs,B) (construction_selections W) s"
    using selection_table_fields[where C="(xs,B)" and Q="construction_selections W" and p=s]
      domain selected by (simp only: fst_conv snd_conv; blast)
  show ?thesis using shape "context" table origins by (auto simp: selection_context_at)
qed

text \<open>
  The account is exactly the supplied source context and construction witness.
  Its pieces and output are derived. The complete claim relation already
  proves coverage and recovery for every permitted enumeration; those owned
  facts establish this class without choosing a preferred presentation.

  Origin retermination relates the entire supplied origin table to its data
  presentation. It admits all formed table rows. Assembly admission remains
  responsible for the distinct condition that these rows form the complete
  origin map for the actual selected pieces and claimed output.
\<close>

end
