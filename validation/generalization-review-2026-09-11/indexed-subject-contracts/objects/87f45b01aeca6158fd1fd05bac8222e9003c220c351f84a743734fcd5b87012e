theory Factor_Assembly_Transport
  imports Factor_Assembly_Equations Factor_Assembly_Table_Operations Factor_Fragment_Enumerations
begin

section \<open>Each copied coordinate retains its actual piece occurrence\<close>

lemma assembly_tag_at:
  "(220,context_relation_argument s a t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    term_formed s \<and> term_formed a \<and> t=Pair_Term s a"
  by (auto simp: assembly_tag_calls)

theorem assembly_tag_list:
  assumes slot: "octets_formed s" and atoms: "\<forall>a\<in>set A. octets_formed a"
  shows "(221,context_relation_argument (Payload_Term s) (data_list_term (map Payload_Term A)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    t=data_list_term (map (\<lambda>a. address_pair_data (s,a)) A)"
  by (rule assembly_tags.encoded_input)
    (use slot atoms in \<open>auto simp: assembly_tag_at address_pair_data_def\<close>)

section \<open>Incidence and attachments use one admitted origin relation\<close>

lemma assembly_incidence_selected:
  "(222,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q s r p x u v w. t=context_relation_argument (Pair_Term q s)
      (Pair_Term r (Pair_Term p x)) (Pair_Term u (Pair_Term v w)) \<and>
      selected_data_member (Pair_Term (Pair_Term s r) u) q \<and>
      selected_data_member (Pair_Term (Pair_Term s p) v) q \<and>
      selected_data_member (Pair_Term (Pair_Term s x) w) q)"
  by (simp only: assembly_incidence_calls assembly_bag_meaning[of 5, simplified]; blast)

lemma assembly_attachment_selected:
  "(224,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>q s a v b. term_formed v \<and>
      t=context_relation_argument (Pair_Term q s) (Pair_Term a v) (Pair_Term b v) \<and>
      selected_data_member (Pair_Term (Pair_Term s a) b) q)"
  by (simp only: assembly_attachment_calls assembly_bag_meaning[of 5, simplified]; blast)

theorem assembly_incidence_at:
  assumes source: "origin_table_presents payload_value_presents q p"
  shows "(222,context_relation_argument (Pair_Term p (Payload_Term s)) (incidence_data z) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q \<and>
    t=incidence_data (rel_value q (s,fst z),rel_value q (s,fst (snd z)),rel_value q (s,snd (snd z)))"
proof -
  have lookup: "selected_data_member (Pair_Term (Pair_Term (Payload_Term s) (Payload_Term a)) v) p \<longleftrightarrow>
      (s,a)\<in>rel_dom q \<and> v=Payload_Term (rel_value q (s,a))" for a v
    using origin_table_partial_selection[OF source, of "(s,a)" v] by (simp add: address_pair_data_def)
  show ?thesis by (auto simp: assembly_incidence_selected incidence_data_def address_pair_data_def lookup)
qed

theorem assembly_attachment_at:
  assumes source: "origin_table_presents payload_value_presents q p" and datum: "octets_formed (snd z)"
  shows "(224,context_relation_argument (Pair_Term p (Payload_Term s)) (address_pair_data z) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (s,fst z)\<in>rel_dom q \<and> t=address_pair_data (rel_value q (s,fst z),snd z)"
proof -
  have lookup: "selected_data_member (Pair_Term (Pair_Term (Payload_Term s) (Payload_Term (fst z))) v) p \<longleftrightarrow>
      (s,fst z)\<in>rel_dom q \<and> v=Payload_Term (rel_value q (s,fst z))" for v
    using origin_table_partial_selection[OF source, of "(s,fst z)" v] by (simp add: address_pair_data_def)
  show ?thesis using datum by (auto simp: assembly_attachment_selected address_pair_data_def lookup)
qed

theorem assembly_incidence_list:
  assumes source: "origin_table_presents payload_value_presents q p" and slot: "octets_formed s"
  shows "(223,context_relation_argument (Pair_Term p (Payload_Term s)) (data_list_term (map incidence_data E)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<forall>z\<in>set E. (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
    t=data_list_term (map (\<lambda>z. incidence_data
      (rel_value q (s,fst z),rel_value q (s,fst (snd z)),rel_value q (s,snd (snd z)))) E)"
proof (rule assembly_edges.encoded_partial_input)
  show "term_formed (Pair_Term p (Payload_Term s))"
    using origin_table_value_formed[OF source] slot by auto
  show "\<And>x y. x\<in>set E \<Longrightarrow>
      assembly_edges.related (Pair_Term p (Payload_Term s)) (incidence_data x) y \<longleftrightarrow>
      ((s,fst x)\<in>rel_dom q \<and> (s,fst (snd x))\<in>rel_dom q \<and> (s,snd (snd x))\<in>rel_dom q) \<and>
      y=incidence_data (rel_value q (s,fst x),rel_value q (s,fst (snd x)),rel_value q (s,snd (snd x)))"
    by (simp only: assembly_incidence_at[OF source] conj_assoc)
qed

theorem assembly_attachment_list:
  assumes source: "origin_table_presents payload_value_presents q p" and slot: "octets_formed s"
    and data: "\<forall>z\<in>set B. octets_formed (snd z)"
  shows "(225,context_relation_argument (Pair_Term p (Payload_Term s)) (data_list_term (map address_pair_data B)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<forall>z\<in>set B. (s,fst z)\<in>rel_dom q) \<and>
    t=data_list_term (map (\<lambda>z. address_pair_data (rel_value q (s,fst z),snd z)) B)"
proof (rule assembly_attachments.encoded_partial_input)
  show "term_formed (Pair_Term p (Payload_Term s))"
    using origin_table_value_formed[OF source] slot by auto
  show "\<And>x y. x\<in>set B \<Longrightarrow>
      assembly_attachments.related (Pair_Term p (Payload_Term s)) (address_pair_data x) y \<longleftrightarrow>
      (s,fst x)\<in>rel_dom q \<and> y=address_pair_data (rel_value q (s,fst x),snd x)"
    by (rule assembly_attachment_at[OF source]) (use data in auto)
qed

section \<open>One piece contributes all four fields together\<close>

abbreviation assembly_contribution_term ::
  "((octets\<times>local_address)\<times>local_address) set \<Rightarrow> octets \<Rightarrow>
    local_address list \<Rightarrow> (local_address\<times>local_address\<times>local_address) list \<Rightarrow>
    (local_address\<times>octets) list \<Rightarrow> (local_address\<times>octets) list \<Rightarrow> factor_term" where
  "assembly_contribution_term q s A E B F \<equiv> artifact_fields_term
    (data_list_term (map (\<lambda>a. address_pair_data (s,a)) A))
    (data_list_term (map (\<lambda>z. incidence_data
      (rel_value q (s,fst z),rel_value q (s,fst (snd z)),rel_value q (s,snd (snd z)))) E))
    (data_list_term (map (\<lambda>z. address_pair_data (rel_value q (s,fst z),snd z)) B))
    (data_list_term (map (\<lambda>z. address_pair_data (rel_value q (s,fst z),snd z)) F))"

theorem assembly_piece_at:
  assumes source: "origin_table_presents payload_value_presents q p" and slot: "octets_formed s"
    and enumeration: "artifact_enumeration R A E B F"
  shows "(226,context_relation_argument p (Pair_Term (Payload_Term s) (artifact_data_term A E B F)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<forall>z\<in>set E. (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
    (\<forall>z\<in>set B\<union>set F. (s,fst z)\<in>rel_dom q) \<and>
    t=assembly_contribution_term q s A E B F"
proof -
  have atoms: "\<forall>a\<in>set A. octets_formed a"
    and bags: "\<forall>z\<in>set B. octets_formed (snd z)"
    and function_data: "\<forall>z\<in>set F. octets_formed (snd z)"
    using artifact_enumeration_coordinates[OF enumeration] by auto
  show ?thesis
    by (auto simp: assembly_piece_calls artifact_data_term_def assembly_tag_list[OF slot atoms]
      assembly_incidence_list[OF source slot] assembly_attachment_list[OF source slot bags]
      assembly_attachment_list[OF source slot function_data])
qed

theorem assembly_piece_list_at:
  assumes source: "origin_table_presents payload_value_presents q p"
    and enumeration: "piece_family_enumeration P ss A E B F"
    and slots: "\<forall>s\<in>set ss. octets_formed s"
  shows "(227,context_relation_argument p
      (pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<forall>s\<in>set ss.
      (\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
      (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)) \<and>
    t=data_list_term (map (\<lambda>s. assembly_contribution_term q s (A s) (E s) (B s) (F s)) ss)"
proof -
  interpret pieces: enumerated_piece_family P ss A E B F
    by (rule enumerated_piece_family.intro[OF enumeration])
  have formed: "term_formed p" using origin_table_value_formed[OF source] by auto
  have each: "assembly_piece_list.related p
      (Pair_Term (Payload_Term s) (artifact_data_term (A s) (E s) (B s) (F s))) u \<longleftrightarrow>
      ((\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
        (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)) \<and>
      u=assembly_contribution_term q s (A s) (E s) (B s) (F s)"
    if "s\<in>set ss" for s u
    using assembly_piece_at[where s=s and t=u, OF source _ pieces.component[OF that]] slots that by auto
  have mapped: "(227,context_relation_argument p
      (data_list_term (map (\<lambda>s. Pair_Term (Payload_Term s) (artifact_data_term (A s) (E s) (B s) (F s))) ss)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      (\<forall>s\<in>set ss.
        (\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
        (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)) \<and>
      t=data_list_term (map (\<lambda>s. assembly_contribution_term q s (A s) (E s) (B s) (F s)) ss)"
    by (rule assembly_piece_list.encoded_partial_input[OF formed each])
  show ?thesis using mapped by (simp add: map_map comp_def)
qed

lemma assembly_piece_coverage_suffices:
  assumes enumeration: "piece_family_enumeration P ss A E B F"
    and coverage: "set (tagged_atom_list ss A)\<subseteq>rel_dom q"
  shows "\<forall>s\<in>set ss.
    (\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
    (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)"
proof -
  interpret pieces: enumerated_piece_family P ss A E B F
    by (rule enumerated_piece_family.intro[OF enumeration])
  have atom: "(s,a)\<in>rel_dom q" if "s\<in>set ss" "a\<in>set (A s)" for s a
    using coverage that by auto
  show ?thesis
  proof (rule ballI)
    fix s assume member: "s\<in>set ss"
    have support: "\<forall>z\<in>set (E s). fst z\<in>set (A s) \<and> fst (snd z)\<in>set (A s) \<and> snd (snd z)\<in>set (A s)"
      "fst ` set (B s)\<subseteq>set (A s)" "fst ` set (F s)\<subseteq>set (A s)"
      using artifact_enumeration_support[OF pieces.component[OF member]] by auto
    show "(\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
        (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)"
      using support atom[OF member] by blast
  qed
qed

text \<open>
  The source premise admits the complete origin table, including its
  functionality and payload boundaries. Every lookup is then exactly the
  existing relation's value on its domain. Incidence uses three lookups with
  one occurrence key; an attachment changes only its atom coordinate.

  The general partial-map contract propagates the domain conditions across
  each complete input list. The result preserves its order and every repeated
  occurrence. These traversals check only the coordinates they use. Complete
  copied-carrier coverage remains an independent report premise.
\<close>

end
