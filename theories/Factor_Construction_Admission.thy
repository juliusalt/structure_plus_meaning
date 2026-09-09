theory Factor_Construction_Admission
  imports Factor_Construction_Accounts
begin

section \<open>A complete assembly test consumes any mapped piece witness\<close>

lemma selected_pieces_assembly_test:
  assumes selected: "selection_context_presents z s"
    and origins: "origin_table_presents payload_value_presents QO orig"
    and result: "artifact_value_presents R r"
  shows "(\<exists>p. (249,Pair_Term s p)\<in>positive_meaning construction_admission_system \<and>
      (230,Pair_Term (Pair_Term p orig) r)\<in>positive_meaning assembly_checking_system) \<longleftrightarrow>
    assembly_relation \<lparr>piece_graph=selection_context_value z\<rparr> QO R"
proof -
  have check: "(230,Pair_Term (Pair_Term p orig) r)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      assembly_relation \<lparr>piece_graph=P\<rparr> QO R"
    if "data_table_presents payload_value_presents artifact_value_presents P p" for P p
    by (rule assembly_report_at_presentations[OF _ origins result])
      (use that in \<open>simp add: piece_family_presents_def\<close>)
  show ?thesis by (simp only: selected_piece_tables.predicate_transfer[OF check]
    selection_contexts.predicate_at[OF selected])
qed

section \<open>The native claim calls the existing complete component operations\<close>

lemma construction_admission_valuation:
  "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=enumeration_term [h 0,h 1,h 2,h 3,h 4] \<and>
      (249,Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 5))\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 6) (h 3))
        \<in>positive_meaning construction_admission_system \<and>
      (10,Pair_Term (h 4) (h 7))\<in>positive_meaning construction_admission_system \<and>
      (230,Pair_Term (Pair_Term (h 5) (h 6)) (h 7))\<in>positive_meaning construction_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_admission_clause construction_admission_clause_family_def
      construction_admission_schema_def schema_variables_def construction_admission_call)

lemma construction_admission_calls:
  "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>x b s orig y p q r. t=enumeration_term [x,b,s,orig,y] \<and>
      (249,Pair_Term (Pair_Term (Pair_Term x b) s) p)\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)
        \<in>positive_meaning term_sequence_system \<and>
      (10,Pair_Term y r)\<in>positive_meaning artifact_projection_system \<and>
      (230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system)"
proof
  assume "(250,t)\<in>positive_meaning construction_admission_system"
  then show "\<exists>x b s orig y p q r. t=enumeration_term [x,b,s,orig,y] \<and>
      (249,Pair_Term (Pair_Term (Pair_Term x b) s) p)\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)
        \<in>positive_meaning term_sequence_system \<and>
      (10,Pair_Term y r)\<in>positive_meaning artifact_projection_system \<and>
      (230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system"
    by (simp only: construction_admission_valuation construction_admission_components; blast)
next
  assume "\<exists>x b s orig y p q r. t=enumeration_term [x,b,s,orig,y] \<and>
      (249,Pair_Term (Pair_Term (Pair_Term x b) s) p)\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)
        \<in>positive_meaning term_sequence_system \<and>
      (10,Pair_Term y r)\<in>positive_meaning artifact_projection_system \<and>
      (230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system"
  then obtain x b s orig y p q r where shape: "t=enumeration_term [x,b,s,orig,y]"
    and calls: "(249,Pair_Term (Pair_Term (Pair_Term x b) s) p)\<in>positive_meaning construction_admission_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)\<in>positive_meaning term_sequence_system"
      "(10,Pair_Term y r)\<in>positive_meaning artifact_projection_system"
      "(230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed x" "term_formed b" "term_formed s" "term_formed orig"
      "term_formed y" "term_formed p" "term_formed q" "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then b else if i=2 then s else if i=3 then orig
    else if i=4 then y else if i=5 then p else if i=6 then q else r"
  show "(250,t)\<in>positive_meaning construction_admission_system"
    by (simp only: construction_admission_valuation; rule exI[of _ ?h])
      (use shape calls formed in \<open>auto simp: construction_admission_components\<close>)
qed

section \<open>Every accepted raw term recovers a complete valid construction\<close>

lemma construction_admission_sound:
  assumes accepted: "(250,t)\<in>positive_meaning construction_admission_system"
  shows "\<exists>xs B W R. source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_claim_presents xs B W R t"
proof -
  obtain x b s orig y p q r where shape: "t=enumeration_term [x,b,s,orig,y]"
    and calls: "(249,Pair_Term (Pair_Term (Pair_Term x b) s) p)\<in>positive_meaning construction_admission_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)\<in>positive_meaning term_sequence_system"
      "(10,Pair_Term y r)\<in>positive_meaning artifact_projection_system"
      "(230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system"
    using accepted by (simp only: construction_admission_calls; blast)
  obtain z where read: "selection_context_presents z (Pair_Term (Pair_Term x b) s)"
    using selected_piece_tables.input_boundary[OF calls(1)] by blast
  obtain xs B Q where zshape: "z=((xs,B),Q)" by (cases z; cases "fst z") auto
  have "context": "source_context_presents (xs,B) (Pair_Term x b)"
    and selection: "selection_table_presents (xs,B) Q s"
    using read by (simp only: zshape selection_context_at; blast)+
  have inputs: "x=artifact_list_term xs"
    and base: "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) B b"
    using "context" by (auto simp only: source_context_fields factor_term.inject)
  obtain R where target: "y=Target_Term (Whole_Artifact R)" and result: "artifact_value_presents R r"
    using calls(3) by (auto simp only: artifact_projection_exact factor_term.inject)
  obtain QO where origin: "origin_table_presents payload_value_presents QO q"
    using calls(4) by (auto simp: assembly_report_exact assembly_report_presents_def
      assembly_value_presents_def factor_pair_presents_def)
  have old_origin: "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) QO orig"
    using construction_origin_native_retermination[of QO orig] origin calls(2) by blast
  have assembled: "assembly_relation \<lparr>piece_graph=selection_context_value z\<rparr> QO R"
    using calls(1,4) by (simp only: selected_pieces_assembly_test[OF read origin result, symmetric]; blast)
  let ?W="\<lparr>construction_selections=Q,construction_origins=QO\<rparr>"
  have domain: "selection_context_domain ((xs,B),construction_selections ?W)"
    using selection_contexts.subject_boundary[OF read] by (simp add: zshape)
  have selected: "construction_selection_formed xs B ?W" and coords: "construction_coordinates_formed B ?W"
    using domain by (simp only: selection_context_construction_boundary; blast)+
  have pieces: "construction_pieces xs B ?W=\<lparr>piece_graph=selection_context_value z\<rparr>"
    by (simp add: zshape construction_pieces_def case_prod_beta')
  have built: "source_constructs xs B ?W R"
    using selected assembled by (simp add: source_constructs_def pieces)
  have old_selection: "finite_table_presents Payload_Term construction_selection_presents Q s"
    using selection_table_fields[where C="(xs,B)" and Q=Q and p=s] selection by blast
  have claim: "construction_claim_presents xs B ?W R t"
    using base old_selection old_origin
    by (auto simp: shape inputs target construction_claim_presents_def)
  show ?thesis using built coords claim by blast
qed

section \<open>Every complete presentation supplies an accepted native claim\<close>

lemma construction_admission_complete:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and claim: "construction_claim_presents xs B W R t"
  shows "(250,t)\<in>positive_meaning construction_admission_system"
proof -
  obtain b s orig where shape: "t=enumeration_term [artifact_list_term xs,b,s,orig,Target_Term (Whole_Artifact R)]"
    and read: "selection_context_presents ((xs,B),construction_selections W)
      (Pair_Term (Pair_Term (artifact_list_term xs) b) s)"
    and old_origin: "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a)
      (construction_origins W) orig"
    using construction_claim_context_fields[OF built coords claim] by blast
  have addresses: "\<forall>z\<in>construction_origins W.
      octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z)) \<and> octets_formed (snd z)"
    using construction_origin_coordinates[OF built coords] by auto
  obtain q where origin: "origin_table_presents payload_value_presents (construction_origins W) q"
    and fold: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q orig)
      \<in>positive_meaning term_sequence_system"
    using construction_origin_native_retermination[of "construction_origins W" orig] addresses old_origin by blast
  obtain r where result: "artifact_value_presents R r"
    using artifact_presentations.total[OF source_construction_finite(7)[OF built]] by blast
  have projection: "(10,Pair_Term (Target_Term (Whole_Artifact R)) r)\<in>positive_meaning artifact_projection_system"
    using result by (simp only: artifact_projection_at_source)
  have pieces: "construction_pieces xs B W=
      \<lparr>piece_graph=selection_context_value ((xs,B),construction_selections W)\<rparr>"
    by (simp add: construction_pieces_def case_prod_beta')
  have assembled: "assembly_relation
      \<lparr>piece_graph=selection_context_value ((xs,B),construction_selections W)\<rparr>
      (construction_origins W) R"
    using built by (simp only: source_constructs_def pieces; blast)
  obtain p where mapped: "(249,Pair_Term (Pair_Term (Pair_Term (artifact_list_term xs) b) s) p)
      \<in>positive_meaning construction_admission_system"
    and checked: "(230,Pair_Term (Pair_Term p q) r)\<in>positive_meaning assembly_checking_system"
    using assembled by (simp only: selected_pieces_assembly_test[OF read origin result, symmetric]; blast)
  show ?thesis using shape mapped fold projection checked
    by (simp only: construction_admission_calls; blast)
qed

theorem construction_admission_exact:
  "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>a. construction_account_presents a t)"
  using construction_admission_sound construction_admission_complete
    by (simp only: construction_accounts_exact; blast)

theorem construction_admission_native_class:
  "presentation_class construction_account_presents construction_account_domain
    (\<lambda>p. (250,p)\<in>positive_meaning construction_admission_system)"
  using construction_account_presentation_class by (simp only: construction_admission_exact)

theorem construction_admission_at_claim:
  assumes claim: "construction_claim_presents xs B W R t"
  shows "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W"
proof
  assume accepted: "(250,t)\<in>positive_meaning construction_admission_system"
  obtain ys C X S where built: "source_constructs ys C X S" and coords: "construction_coordinates_formed C X"
    and other: "construction_claim_presents ys C X S t"
    using construction_admission_sound[OF accepted] by blast
  show "source_constructs xs B W R \<and> construction_coordinates_formed B W"
    using construction_claim_presents_unique[OF claim other] built coords by blast
next
  assume "source_constructs xs B W R \<and> construction_coordinates_formed B W"
  then show "(250,t)\<in>positive_meaning construction_admission_system"
    by (intro construction_admission_complete[OF _ _ claim]) auto
qed

text \<open>
  Exact admission covers every raw term. An accepted term recovers the entire
  old claim and proves its source selection, coordinate, origin, and output
  conditions. Conversely every complete presentation of every valid claim
  supplies the native calls. No extra witness field or preferred enumeration
  enters the public claim.

  The table-to-assembly step uses the general witness predicate rule. Its
  observation condition is exactly the existing assembly contract. Thus the
  traversal's internal order does not become an obligation for construction
  clients, and source, fragment, and assembly proofs remain owned locally.
\<close>

end
