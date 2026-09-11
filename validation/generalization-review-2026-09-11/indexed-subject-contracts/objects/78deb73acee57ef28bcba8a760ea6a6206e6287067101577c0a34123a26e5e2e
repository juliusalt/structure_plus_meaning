theory Factor_Assembly_Equations
  imports Factor_Assembly_Clauses
begin

section \<open>The combined program preserves each external operation\<close>

lemma assembly_bag_meaning:
  assumes "d\<in>{5,6}"
  shows "(d,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using assembly_previous_meaning[of d t] assembly_components_row_meaning[of d t]
    whole_system_agreement_meaning[OF bag_comparison_system_formed row_values_system_formed
      row_values_bag_agreement, of d t] assms by auto

lemma assembly_append_meaning:
  "(46,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (46,t)\<in>positive_meaning data_append_system"
  using assembly_previous_meaning[of 46 t] assembly_components_row_meaning[of 46 t]
    whole_system_agreement_meaning[OF data_append_system_formed row_values_system_formed
      row_values_append_agreement, of 46 t] by auto

lemma assembly_artifact_meaning:
  "(11,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>R. artifact_value_presents R t)"
  using assembly_previous_meaning[of 11 t] assembly_components_row_meaning[of 11 t]
    whole_system_agreement_meaning[OF artifact_identity_system_formed row_values_system_formed
      row_values_artifact_agreement, of 11 t] by (auto simp: artifact_identity_admission)

lemma assembly_keys_meaning:
  "(51,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (51,t)\<in>positive_meaning row_keys_system"
  using assembly_previous_meaning[of 51 t] assembly_components_row_meaning[of 51 t]
    whole_system_agreement_meaning[OF row_keys_system_formed row_values_system_formed
      row_values_row_keys_agreement, of 51 t] by auto

lemma assembly_values_meaning:
  "(59,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (59,t)\<in>positive_meaning row_values_system"
  using assembly_previous_meaning[of 59 t] assembly_components_row_meaning[of 59 t] by auto

lemma assembly_piece_table_meaning:
  "(213,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>P. piece_family_presents payload_value_presents P t)"
  using assembly_previous_meaning[of 213 t] assembly_components_table_meaning[of 213 t]
    structural_piece_table_exact[of t] by auto

lemma assembly_origin_table_meaning:
  "(216,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q. origin_table_presents payload_value_presents q t)"
  using assembly_previous_meaning[of 216 t] assembly_components_table_meaning[of 216 t]
    structural_origin_table_exact[of t] by auto

lemma assembly_set_meaning:
  "(219,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (219,t)\<in>positive_meaning data_set_comparison_system"
  using assembly_previous_meaning[of 219 t] assembly_components_comparison_meaning[of 219 t] by auto

section \<open>Each local clause is exactly its actual finite family of calls\<close>

lemma assembly_tag_valuation:
  "(220,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1}. term_formed (h i)) \<and>
      t=(context_relation_argument (h 0) (h 1) (Pair_Term (h 0) (h 1))))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: assembly_checking_clause assembly_clause_family_def assembly_tag_schema_def
      schema_variables_def assembly_checking_call)

lemma assembly_tag_calls:
  "(220,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>s a. t=(context_relation_argument (s) (a) (Pair_Term (s) (a))) \<and>
      term_formed s \<and> term_formed a)"
proof
  assume "(220,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>s a. t=(context_relation_argument (s) (a) (Pair_Term (s) (a))) \<and>
      term_formed s \<and> term_formed a)"
    by (simp only: assembly_tag_valuation; blast)
next
  assume "(\<exists>s a. t=(context_relation_argument (s) (a) (Pair_Term (s) (a))) \<and>
      term_formed s \<and> term_formed a)"
  then obtain s a where shape: "t=(context_relation_argument (s) (a) (Pair_Term (s) (a)))"
    and supported: "term_formed s \<and> term_formed a" by blast
  have formed: "term_formed s" "term_formed a"
    using supported by auto
  show "(220,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_tag_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then s else a"])
      (use shape supported formed in auto)
qed

lemma assembly_incidence_valuation:
  "(222,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      t=(context_relation_argument (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (Pair_Term (h 3) (h 4))) (Pair_Term (h 5) (Pair_Term (h 6) (h 7)))) \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (h 1) (h 2)) (h 5)) (Pair_Term (h 0) (h 8))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (h 1) (h 3)) (h 6)) (Pair_Term (h 0) (h 9))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (h 1) (h 4)) (h 7)) (Pair_Term (h 0) (h 10))))\<in>positive_meaning assembly_checking_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: assembly_checking_clause assembly_clause_family_def assembly_incidence_schema_def
      schema_variables_def assembly_checking_call)

lemma assembly_incidence_calls:
  "(222,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q s r p x u v w zr zp zx. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (r) (Pair_Term (p) (x))) (Pair_Term (u) (Pair_Term (v) (w)))) \<and>
      (5,(Pair_Term (Pair_Term (Pair_Term (s) (r)) (u)) (Pair_Term (q) (zr))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (p)) (v)) (Pair_Term (q) (zp))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (x)) (w)) (Pair_Term (q) (zx))))\<in>positive_meaning assembly_checking_system)"
proof
  assume "(222,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>q s r p x u v w zr zp zx. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (r) (Pair_Term (p) (x))) (Pair_Term (u) (Pair_Term (v) (w)))) \<and>
      (5,(Pair_Term (Pair_Term (Pair_Term (s) (r)) (u)) (Pair_Term (q) (zr))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (p)) (v)) (Pair_Term (q) (zp))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (x)) (w)) (Pair_Term (q) (zx))))\<in>positive_meaning assembly_checking_system)"
    by (simp only: assembly_incidence_valuation; blast)
next
  assume "(\<exists>q s r p x u v w zr zp zx. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (r) (Pair_Term (p) (x))) (Pair_Term (u) (Pair_Term (v) (w)))) \<and>
      (5,(Pair_Term (Pair_Term (Pair_Term (s) (r)) (u)) (Pair_Term (q) (zr))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (p)) (v)) (Pair_Term (q) (zp))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (x)) (w)) (Pair_Term (q) (zx))))\<in>positive_meaning assembly_checking_system)"
  then obtain q s r p x u v w zr zp zx where shape: "t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (r) (Pair_Term (p) (x))) (Pair_Term (u) (Pair_Term (v) (w))))"
    and supported: "(5,(Pair_Term (Pair_Term (Pair_Term (s) (r)) (u)) (Pair_Term (q) (zr))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (p)) (v)) (Pair_Term (q) (zp))))\<in>positive_meaning assembly_checking_system \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (s) (x)) (w)) (Pair_Term (q) (zx))))\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed q" "term_formed s" "term_formed r" "term_formed p" "term_formed x" "term_formed u" "term_formed v" "term_formed w" "term_formed zr" "term_formed zp" "term_formed zx"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(222,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_incidence_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then q else if i=1 then s else if i=2 then r else if i=3 then p else if i=4 then x else if i=5 then u else if i=6 then v else if i=7 then w else if i=8 then zr else if i=9 then zp else zx"])
      (use shape supported formed in auto)
qed

lemma assembly_attachment_valuation:
  "(224,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=(context_relation_argument (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)) (Pair_Term (h 4) (h 3))) \<and>
        (5,(Pair_Term (Pair_Term (Pair_Term (h 1) (h 2)) (h 4)) (Pair_Term (h 0) (h 5))))\<in>positive_meaning assembly_checking_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: assembly_checking_clause assembly_clause_family_def assembly_attachment_schema_def
      schema_variables_def assembly_checking_call)

lemma assembly_attachment_calls:
  "(224,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q s a v b z. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (a) (v)) (Pair_Term (b) (v))) \<and>
      term_formed v \<and> (5,(Pair_Term (Pair_Term (Pair_Term (s) (a)) (b)) (Pair_Term (q) (z))))\<in>positive_meaning assembly_checking_system)"
proof
  assume "(224,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>q s a v b z. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (a) (v)) (Pair_Term (b) (v))) \<and>
      term_formed v \<and> (5,(Pair_Term (Pair_Term (Pair_Term (s) (a)) (b)) (Pair_Term (q) (z))))\<in>positive_meaning assembly_checking_system)"
    by (simp only: assembly_attachment_valuation; blast)
next
  assume "(\<exists>q s a v b z. t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (a) (v)) (Pair_Term (b) (v))) \<and>
      term_formed v \<and> (5,(Pair_Term (Pair_Term (Pair_Term (s) (a)) (b)) (Pair_Term (q) (z))))\<in>positive_meaning assembly_checking_system)"
  then obtain q s a v b z where shape: "t=(context_relation_argument (Pair_Term (q) (s)) (Pair_Term (a) (v)) (Pair_Term (b) (v)))"
    and supported: "term_formed v \<and> (5,(Pair_Term (Pair_Term (Pair_Term (s) (a)) (b)) (Pair_Term (q) (z))))\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed q" "term_formed s" "term_formed a" "term_formed v" "term_formed b" "term_formed z"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(224,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_attachment_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then q else if i=1 then s else if i=2 then a else if i=3 then v else if i=4 then b else z"])
      (use shape supported formed in auto)
qed

lemma assembly_piece_valuation:
  "(226,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9}. term_formed (h i)) \<and>
      t=(context_relation_argument (h 0) (Pair_Term (h 1) (artifact_fields_term (h 2) (h 3) (h 4) (h 5))) (artifact_fields_term (h 6) (h 7) (h 8) (h 9))) \<and>
        (221,(context_relation_argument (h 1) (h 2) (h 6)))\<in>positive_meaning assembly_checking_system \<and>
        (223,(context_relation_argument (Pair_Term (h 0) (h 1)) (h 3) (h 7)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (h 0) (h 1)) (h 4) (h 8)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (h 0) (h 1)) (h 5) (h 9)))\<in>positive_meaning assembly_checking_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: assembly_checking_clause assembly_clause_family_def assembly_piece_schema_def
      schema_variables_def assembly_checking_call)

lemma assembly_piece_calls:
  "(226,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q s a e b f ca ce cb cf. t=(context_relation_argument (q) (Pair_Term (s) (artifact_fields_term (a) (e) (b) (f))) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (221,(context_relation_argument (s) (a) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (223,(context_relation_argument (Pair_Term (q) (s)) (e) (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (b) (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (f) (cf)))\<in>positive_meaning assembly_checking_system)"
proof
  assume "(226,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>q s a e b f ca ce cb cf. t=(context_relation_argument (q) (Pair_Term (s) (artifact_fields_term (a) (e) (b) (f))) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (221,(context_relation_argument (s) (a) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (223,(context_relation_argument (Pair_Term (q) (s)) (e) (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (b) (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (f) (cf)))\<in>positive_meaning assembly_checking_system)"
    by (simp only: assembly_piece_valuation; blast)
next
  assume "(\<exists>q s a e b f ca ce cb cf. t=(context_relation_argument (q) (Pair_Term (s) (artifact_fields_term (a) (e) (b) (f))) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (221,(context_relation_argument (s) (a) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (223,(context_relation_argument (Pair_Term (q) (s)) (e) (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (b) (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (f) (cf)))\<in>positive_meaning assembly_checking_system)"
  then obtain q s a e b f ca ce cb cf where shape: "t=(context_relation_argument (q) (Pair_Term (s) (artifact_fields_term (a) (e) (b) (f))) (artifact_fields_term (ca) (ce) (cb) (cf)))"
    and supported: "(221,(context_relation_argument (s) (a) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (223,(context_relation_argument (Pair_Term (q) (s)) (e) (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (b) (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (225,(context_relation_argument (Pair_Term (q) (s)) (f) (cf)))\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed q" "term_formed s" "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed ca" "term_formed ce" "term_formed cb" "term_formed cf"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(226,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_piece_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then q else if i=1 then s else if i=2 then a else if i=3 then e else if i=4 then b else if i=5 then f else if i=6 then ca else if i=7 then ce else if i=8 then cb else cf"])
      (use shape supported formed in auto)
qed

lemma assembly_fields_append_valuation:
  "(228,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11}. term_formed (h i)) \<and>
      t=(collection_join_argument (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (artifact_fields_term (h 4) (h 5) (h 6) (h 7)) (artifact_fields_term (h 8) (h 9) (h 10) (h 11))) \<and>
        (46,(collection_join_argument (h 0) (h 4) (h 8)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (h 1) (h 5) (h 9)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (h 2) (h 6) (h 10)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (h 3) (h 7) (h 11)))\<in>positive_meaning assembly_checking_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: assembly_checking_clause assembly_clause_family_def assembly_fields_append_schema_def
      schema_variables_def assembly_checking_call)

lemma assembly_fields_append_calls:
  "(228,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>a e b f a' e' b' f' ca ce cb cf. t=(collection_join_argument (artifact_fields_term (a) (e) (b) (f)) (artifact_fields_term (a') (e') (b') (f')) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (46,(collection_join_argument (a) (a') (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (e) (e') (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (b) (b') (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (f) (f') (cf)))\<in>positive_meaning assembly_checking_system)"
proof
  assume "(228,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>a e b f a' e' b' f' ca ce cb cf. t=(collection_join_argument (artifact_fields_term (a) (e) (b) (f)) (artifact_fields_term (a') (e') (b') (f')) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (46,(collection_join_argument (a) (a') (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (e) (e') (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (b) (b') (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (f) (f') (cf)))\<in>positive_meaning assembly_checking_system)"
    by (simp only: assembly_fields_append_valuation; blast)
next
  assume "(\<exists>a e b f a' e' b' f' ca ce cb cf. t=(collection_join_argument (artifact_fields_term (a) (e) (b) (f)) (artifact_fields_term (a') (e') (b') (f')) (artifact_fields_term (ca) (ce) (cb) (cf))) \<and>
      (46,(collection_join_argument (a) (a') (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (e) (e') (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (b) (b') (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (f) (f') (cf)))\<in>positive_meaning assembly_checking_system)"
  then obtain a e b f a' e' b' f' ca ce cb cf where shape: "t=(collection_join_argument (artifact_fields_term (a) (e) (b) (f)) (artifact_fields_term (a') (e') (b') (f')) (artifact_fields_term (ca) (ce) (cb) (cf)))"
    and supported: "(46,(collection_join_argument (a) (a') (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (e) (e') (ce)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (b) (b') (cb)))\<in>positive_meaning assembly_checking_system \<and>
        (46,(collection_join_argument (f) (f') (cf)))\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed a'" "term_formed e'" "term_formed b'" "term_formed f'" "term_formed ca" "term_formed ce" "term_formed cb" "term_formed cf"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(228,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_fields_append_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then a' else if i=5 then e' else if i=6 then b' else if i=7 then f' else if i=8 then ca else if i=9 then ce else if i=10 then cb else cf"])
      (use shape supported formed in auto)
qed

lemma assembly_report_valuation:
  "(230,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}. term_formed (h i)) \<and>
      t=(Pair_Term (Pair_Term (h 0) (h 1)) (artifact_fields_term (h 2) (h 3) (h 4) (h 5))) \<and>
        (213,(h 0))\<in>positive_meaning assembly_checking_system \<and>
        (216,(h 1))\<in>positive_meaning assembly_checking_system \<and>
        (11,(artifact_fields_term (h 2) (h 3) (h 4) (h 5)))\<in>positive_meaning assembly_checking_system \<and>
        (227,(context_relation_argument (h 1) (h 0) (h 6)))\<in>positive_meaning assembly_checking_system \<and>
        (229,(collection_join_argument (artifact_fields_term (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term [])) (h 6) (artifact_fields_term (h 7) (h 8) (h 9) (h 10))))\<in>positive_meaning assembly_checking_system \<and>
        (51,(Pair_Term (h 1) (h 11)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (h 11) (h 7)))\<in>positive_meaning assembly_checking_system \<and>
        (59,(Pair_Term (h 1) (h 12)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (h 12) (h 2)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (h 8) (h 3)))\<in>positive_meaning assembly_checking_system \<and>
        (6,(Pair_Term (h 9) (h 4)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (h 10) (h 5)))\<in>positive_meaning assembly_checking_system)"
proof -
  have family: "((230,c),S)\<in>system_clauses assembly_checking_system \<longleftrightarrow>
      c=0 \<and> S=assembly_report_schema" for c S
    by (auto simp: assembly_checking_clause assembly_clause_family_def)
  have ordinary: "schema_material_premises assembly_report_schema={}"
    by (simp add: assembly_report_schema_def)
  have accepts: "schema_call_formed assembly_checking_system 230
      (evaluate_pattern h (schema_conclusion assembly_report_schema))"
    if "\<forall>i\<in>schema_variables assembly_report_schema. term_formed (h i)" for h
    using that by (auto simp: assembly_report_schema_def schema_variables_def assembly_checking_call)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF family ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: assembly_report_schema_def schema_variables_def conj_ac all_conj_distrib imp_conjL)
    done
qed

lemma assembly_report_calls:
  "(230,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>p q a e b f pieces ca ce cb cf keys vals. t=(Pair_Term (Pair_Term (p) (q)) (artifact_fields_term (a) (e) (b) (f))) \<and>
      (213,(p))\<in>positive_meaning assembly_checking_system \<and>
        (216,(q))\<in>positive_meaning assembly_checking_system \<and>
        (11,(artifact_fields_term (a) (e) (b) (f)))\<in>positive_meaning assembly_checking_system \<and>
        (227,(context_relation_argument (q) (p) (pieces)))\<in>positive_meaning assembly_checking_system \<and>
        (229,(collection_join_argument (artifact_fields_term (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term [])) (pieces) (artifact_fields_term (ca) (ce) (cb) (cf))))\<in>positive_meaning assembly_checking_system \<and>
        (51,(Pair_Term (q) (keys)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (keys) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (59,(Pair_Term (q) (vals)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (vals) (a)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (ce) (e)))\<in>positive_meaning assembly_checking_system \<and>
        (6,(Pair_Term (cb) (b)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (cf) (f)))\<in>positive_meaning assembly_checking_system)"
proof
  assume "(230,t)\<in>positive_meaning assembly_checking_system"
  then show "(\<exists>p q a e b f pieces ca ce cb cf keys vals. t=(Pair_Term (Pair_Term (p) (q)) (artifact_fields_term (a) (e) (b) (f))) \<and>
      (213,(p))\<in>positive_meaning assembly_checking_system \<and>
        (216,(q))\<in>positive_meaning assembly_checking_system \<and>
        (11,(artifact_fields_term (a) (e) (b) (f)))\<in>positive_meaning assembly_checking_system \<and>
        (227,(context_relation_argument (q) (p) (pieces)))\<in>positive_meaning assembly_checking_system \<and>
        (229,(collection_join_argument (artifact_fields_term (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term [])) (pieces) (artifact_fields_term (ca) (ce) (cb) (cf))))\<in>positive_meaning assembly_checking_system \<and>
        (51,(Pair_Term (q) (keys)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (keys) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (59,(Pair_Term (q) (vals)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (vals) (a)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (ce) (e)))\<in>positive_meaning assembly_checking_system \<and>
        (6,(Pair_Term (cb) (b)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (cf) (f)))\<in>positive_meaning assembly_checking_system)"
    by (simp only: assembly_report_valuation; blast)
next
  assume "(\<exists>p q a e b f pieces ca ce cb cf keys vals. t=(Pair_Term (Pair_Term (p) (q)) (artifact_fields_term (a) (e) (b) (f))) \<and>
      (213,(p))\<in>positive_meaning assembly_checking_system \<and>
        (216,(q))\<in>positive_meaning assembly_checking_system \<and>
        (11,(artifact_fields_term (a) (e) (b) (f)))\<in>positive_meaning assembly_checking_system \<and>
        (227,(context_relation_argument (q) (p) (pieces)))\<in>positive_meaning assembly_checking_system \<and>
        (229,(collection_join_argument (artifact_fields_term (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term [])) (pieces) (artifact_fields_term (ca) (ce) (cb) (cf))))\<in>positive_meaning assembly_checking_system \<and>
        (51,(Pair_Term (q) (keys)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (keys) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (59,(Pair_Term (q) (vals)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (vals) (a)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (ce) (e)))\<in>positive_meaning assembly_checking_system \<and>
        (6,(Pair_Term (cb) (b)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (cf) (f)))\<in>positive_meaning assembly_checking_system)"
  then obtain p q a e b f pieces ca ce cb cf keys vals where shape: "t=(Pair_Term (Pair_Term (p) (q)) (artifact_fields_term (a) (e) (b) (f)))"
    and supported: "(213,(p))\<in>positive_meaning assembly_checking_system \<and>
        (216,(q))\<in>positive_meaning assembly_checking_system \<and>
        (11,(artifact_fields_term (a) (e) (b) (f)))\<in>positive_meaning assembly_checking_system \<and>
        (227,(context_relation_argument (q) (p) (pieces)))\<in>positive_meaning assembly_checking_system \<and>
        (229,(collection_join_argument (artifact_fields_term (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term [])) (pieces) (artifact_fields_term (ca) (ce) (cb) (cf))))\<in>positive_meaning assembly_checking_system \<and>
        (51,(Pair_Term (q) (keys)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (keys) (ca)))\<in>positive_meaning assembly_checking_system \<and>
        (59,(Pair_Term (q) (vals)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (vals) (a)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (ce) (e)))\<in>positive_meaning assembly_checking_system \<and>
        (6,(Pair_Term (cb) (b)))\<in>positive_meaning assembly_checking_system \<and>
        (219,(Pair_Term (cf) (f)))\<in>positive_meaning assembly_checking_system" by blast
  have formed: "term_formed p" "term_formed q" "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed pieces" "term_formed ca" "term_formed ce" "term_formed cb" "term_formed cf" "term_formed keys" "term_formed vals"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(230,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: assembly_report_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else if i=1 then q else if i=2 then a else if i=3 then e else if i=4 then b else if i=5 then f else if i=6 then pieces else if i=7 then ca else if i=8 then ce else if i=9 then cb else if i=10 then cf else if i=11 then keys else vals"])
      (use shape supported formed in auto)
qed

text \<open>
  The equations retain every actual premise. Selection remainders remain
  private variables, and the attachment step explicitly retains formation of
  the opaque value copied only in its conclusion. The tag step has no callee
  and requires formation of both copied operands. Subsequent semantic
  specializations use these equations and the established traversal profiles.
\<close>

end
