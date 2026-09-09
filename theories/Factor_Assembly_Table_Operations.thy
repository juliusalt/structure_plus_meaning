theory Factor_Assembly_Table_Operations
  imports Factor_Assembly_Enumerations Factor_Data_Table_Operations Factor_Structural_Table_Admission
begin

section \<open>The supplied piece table determines its actual field enumerations\<close>

theorem piece_table_enumerations:
  "piece_family_presents payload_value_presents P t \<longleftrightarrow>
    (\<exists>ss A E B F. piece_family_enumeration P ss A E B F \<and>
      (\<forall>s\<in>set ss. octets_formed s) \<and>
      t=pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss))"
proof
  assume table: "piece_family_presents payload_value_presents P t"
  have formed: "piece_family_formed P"
    using native_piece_families.subject_boundary[OF table] by blast
  obtain ss stored where source: "distinct ss" "set ss=piece_slots P"
    "\<forall>s\<in>set ss. octets_formed s \<and> artifact_value_presents (piece_at P s) (stored s)"
    "t=pair_list_term (map (\<lambda>s. (Payload_Term s,stored s)) ss)"
    using table by (simp only: piece_family_presents_def data_table_encoded_keys
      piece_slots_def piece_at_def; blast)
  have witnesses: "\<forall>s\<in>set ss. \<exists>z.
      artifact_enumeration (piece_at P s) (fst z) (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z))) \<and>
      stored s=artifact_data_term (fst z) (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z)))"
    using source(3) by (auto simp: artifact_value_presents_def)
  obtain Z where chosen: "\<forall>s\<in>set ss.
      artifact_enumeration (piece_at P s) (fst (Z s)) (fst (snd (Z s)))
        (fst (snd (snd (Z s)))) (snd (snd (snd (Z s)))) \<and>
      stored s=artifact_data_term (fst (Z s)) (fst (snd (Z s)))
        (fst (snd (snd (Z s)))) (snd (snd (snd (Z s))))"
    using bchoice[OF witnesses] by blast
  let ?A="\<lambda>s. fst (Z s)"
  let ?E="\<lambda>s. fst (snd (Z s))"
  let ?B="\<lambda>s. fst (snd (snd (Z s)))"
  let ?F="\<lambda>s. snd (snd (snd (Z s)))"
  have enumeration: "piece_family_enumeration P ss ?A ?E ?B ?F"
    using formed source(1,2) chosen by (simp add: piece_family_enumeration_def)
  have actual: "map (\<lambda>s. (Payload_Term s,stored s)) ss=
      map (\<lambda>s. (Payload_Term s,artifact_data_term (?A s) (?E s) (?B s) (?F s))) ss"
    by (rule map_cong) (use chosen in auto)
  show "\<exists>ss A E B F. piece_family_enumeration P ss A E B F \<and>
      (\<forall>s\<in>set ss. octets_formed s) \<and>
      t=pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)"
    by (rule exI[of _ ss], rule exI[of _ ?A], rule exI[of _ ?E], rule exI[of _ ?B], rule exI[of _ ?F])
      (use enumeration source(3,4) actual in \<open>auto simp: actual\<close>)
next
  assume "\<exists>ss A E B F. piece_family_enumeration P ss A E B F \<and>
      (\<forall>s\<in>set ss. octets_formed s) \<and>
      t=pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)"
  then obtain ss A E B F where enumeration: "piece_family_enumeration P ss A E B F"
    and keys: "\<forall>s\<in>set ss. octets_formed s"
    and actual: "t=pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)"
    by blast
  interpret pieces: enumerated_piece_family P ss A E B F by (rule enumerated_piece_family.intro[OF enumeration])
  have functionality: "single_valued (piece_graph P)"
    using pieces.pieces by (simp add: piece_family_formed_def)
  have field_values: "\<forall>s\<in>set ss. artifact_value_presents (piece_at P s) (artifact_data_term (A s) (E s) (B s) (F s))"
  proof (intro ballI)
    fix s assume member: "s\<in>set ss"
    show "artifact_value_presents (piece_at P s) (artifact_data_term (A s) (E s) (B s) (F s))"
      unfolding artifact_value_presents_def
      by (rule exI[of _ "A s"], rule exI[of _ "E s"], rule exI[of _ "B s"], rule exI[of _ "F s"])
        (use pieces.component[OF member] in simp)
  qed
  show "piece_family_presents payload_value_presents P t"
    unfolding piece_family_presents_def data_table_encoded_keys
    by (intro exI[of _ ss] exI[of _ "\<lambda>s. artifact_data_term (A s) (E s) (B s) (F s)"])
      (use pieces.slots functionality field_values keys actual in \<open>simp add: piece_slots_def piece_at_def\<close>)
qed

section \<open>Origins have one exact payload form at each complete key\<close>

lemma origin_entry_encoding:
  "origin_entry_presents z t \<longleftrightarrow>
    octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z)) \<and> octets_formed (snd z) \<and>
    t=Pair_Term (address_pair_data (fst z)) (Payload_Term (snd z))"
  by (auto simp: factor_pair_presents_def address_pair_data_def)

theorem origin_table_enumerations:
  "origin_table_presents payload_value_presents q t \<longleftrightarrow>
    (\<exists>ks. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
      (\<forall>k\<in>set ks. octets_formed (fst k) \<and> octets_formed (snd k) \<and> octets_formed (rel_value q k)) \<and>
      t=pair_list_term (map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks))"
proof -
  have key_reading: "factor_pair_presents payload_value_presents payload_value_presents=
      (\<lambda>k p. (octets_formed (fst k) \<and> octets_formed (snd k)) \<and> p=address_pair_data k)"
    by (intro ext) (auto simp: factor_pair_presents_def address_pair_data_def)
  have indexed: "origin_table_presents payload_value_presents q t \<longleftrightarrow>
      (\<exists>ks stored. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
        (\<forall>k\<in>set ks. (octets_formed (fst k) \<and> octets_formed (snd k)) \<and>
          octets_formed (rel_value q k) \<and> stored k=Payload_Term (rel_value q k)) \<and>
        t=pair_list_term (map (\<lambda>k. (address_pair_data k,stored k)) ks))"
    by (simp only: key_reading data_table_encoded_keys)
  show ?thesis
  proof (simp only: indexed, rule iffI)
    assume "\<exists>ks stored. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
        (\<forall>k\<in>set ks. (octets_formed (fst k) \<and> octets_formed (snd k)) \<and>
          octets_formed (rel_value q k) \<and> stored k=Payload_Term (rel_value q k)) \<and>
        t=pair_list_term (map (\<lambda>k. (address_pair_data k,stored k)) ks)"
    then obtain ks stored where source: "distinct ks" "set ks=rel_dom q" "single_valued q"
      "\<forall>k\<in>set ks. (octets_formed (fst k) \<and> octets_formed (snd k)) \<and>
        octets_formed (rel_value q k) \<and> stored k=Payload_Term (rel_value q k)"
      "t=pair_list_term (map (\<lambda>k. (address_pair_data k,stored k)) ks)" by blast
    have same: "map (\<lambda>k. (address_pair_data k,stored k)) ks=
        map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks"
      by (rule map_cong) (use source(4) in auto)
    show "\<exists>ks. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
        (\<forall>k\<in>set ks. octets_formed (fst k) \<and> octets_formed (snd k) \<and> octets_formed (rel_value q k)) \<and>
        t=pair_list_term (map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks)"
      by (rule exI[of _ ks]) (use source same in \<open>auto simp: same\<close>)
  next
    assume "\<exists>ks. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
        (\<forall>k\<in>set ks. octets_formed (fst k) \<and> octets_formed (snd k) \<and> octets_formed (rel_value q k)) \<and>
        t=pair_list_term (map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks)"
    then obtain ks where source: "distinct ks" "set ks=rel_dom q" "single_valued q"
      "\<forall>k\<in>set ks. octets_formed (fst k) \<and> octets_formed (snd k) \<and> octets_formed (rel_value q k)"
      "t=pair_list_term (map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks)" by blast
    show "\<exists>ks stored. distinct ks \<and> set ks=rel_dom q \<and> single_valued q \<and>
        (\<forall>k\<in>set ks. (octets_formed (fst k) \<and> octets_formed (snd k)) \<and>
          octets_formed (rel_value q k) \<and> stored k=Payload_Term (rel_value q k)) \<and>
        t=pair_list_term (map (\<lambda>k. (address_pair_data k,stored k)) ks)"
      by (rule exI[of _ ks], rule exI[of _ "\<lambda>k. Payload_Term (rel_value q k)"])
        (use source in simp)
  qed
qed

theorem origin_table_selection:
  assumes source: "origin_table_presents payload_value_presents q p"
  shows "selected_data_member t p \<longleftrightarrow> (\<exists>z\<in>q. origin_entry_presents z t)"
proof (rule data_collection_selection_unique)
  show "data_collection_presents origin_entry_presents q p"
    using source by (simp add: data_table_presents_def)
  show "\<And>z t. z\<in>q \<Longrightarrow> origin_entry_presents z t \<Longrightarrow>
      term_formed t \<and> self_contained_term t" using origin_entry_data by blast
  show "\<And>z t u. z\<in>q \<Longrightarrow> origin_entry_presents z t \<Longrightarrow>
      origin_entry_presents z u \<Longrightarrow> t=u" by (simp only: origin_entry_encoding; blast)
qed

corollary origin_table_selection_at_key:
  assumes source: "origin_table_presents payload_value_presents q p"
  shows "selected_data_member (Pair_Term (address_pair_data k) t) p \<longleftrightarrow>
    (\<exists>v. (k,v)\<in>q \<and> payload_value_presents v t)"
proof
  assume selected: "selected_data_member (Pair_Term (address_pair_data k) t) p"
  obtain z where member: "z\<in>q" and reading: "origin_entry_presents z (Pair_Term (address_pair_data k) t)"
    using selected by (simp only: origin_table_selection[OF source]; blast)
  obtain a v where shape: "z=(a,v)" by (cases z)
  have equality: "address_pair_data k=address_pair_data a"
    using reading by (simp only: origin_entry_encoding shape fst_conv snd_conv factor_term.inject; blast)
  have same: "a=k" using injD[OF address_pair_data_injective equality] by simp
  have datum: "payload_value_presents v t" using reading
    by (simp only: origin_entry_encoding shape fst_conv snd_conv factor_term.inject; blast)
  show "\<exists>v. (k,v)\<in>q \<and> payload_value_presents v t"
    using member shape same datum by blast
next
  assume "\<exists>v. (k,v)\<in>q \<and> payload_value_presents v t"
  then obtain v where row: "(k,v)\<in>q" and datum: "payload_value_presents v t" by blast
  have boundary: "octets_formed (fst k) \<and> octets_formed (snd k)"
    using native_origin_tables.subject_boundary[OF source] row by auto
  have entry: "origin_entry_presents (k,v) (Pair_Term (address_pair_data k) t)"
    using boundary datum by (simp only: origin_entry_encoding fst_conv snd_conv factor_term.inject; blast)
  show "selected_data_member (Pair_Term (address_pair_data k) t) p"
    using row entry by (simp only: origin_table_selection[OF source]; blast)
qed

corollary origin_table_value_selection:
  assumes source: "origin_table_presents payload_value_presents q p" and key: "k\<in>rel_dom q"
  shows "selected_data_member (Pair_Term (address_pair_data k) t) p \<longleftrightarrow>
    t=Payload_Term (rel_value q k)"
proof -
  have functional: "single_valued q" and data: "\<forall>z\<in>q. octets_formed (snd z)"
    using native_origin_tables.subject_boundary[OF source] by auto
  obtain v where row: "(k,v)\<in>q" using key by (auto simp: rel_dom_def)
  have stored: "rel_value q k=v" by (rule rel_value_eq[OF functional row])
  have formed: "octets_formed v" using data row by auto
  have selected: "selected_data_member (Pair_Term (address_pair_data k) t) p \<longleftrightarrow>
      (\<exists>w. (k,w)\<in>q \<and> payload_value_presents w t)"
    by (rule origin_table_selection_at_key[OF source])
  show ?thesis
  proof
    assume checked: "selected_data_member (Pair_Term (address_pair_data k) t) p"
    obtain w where member: "(k,w)\<in>q" and datum: "payload_value_presents w t"
      using selected checked by blast
    have same: "w=v" by (rule single_valued_outputs[OF functional member row])
    show "t=Payload_Term (rel_value q k)" using datum same stored by simp
  next
    assume equality: "t=Payload_Term (rel_value q k)"
    have datum: "payload_value_presents v t" using equality formed stored by simp
    show "selected_data_member (Pair_Term (address_pair_data k) t) p"
      using selected row datum by blast
  qed
qed

text \<open>
  The piece theorem extracts the enumerations actually stored at each slot.
  The earlier copied-field and gluing laws can therefore be applied to those
  same lists, including every counted attachment occurrence. No arbitrary
  replacement presentation is substituted for an input piece.

  Origin lookup is a specialization of complete collection selection. Its
  key and destination have unique payload forms, so no value comparison is
  needed. The table remains an explicit premise: lookup does not claim to
  admit the complete table or to establish coverage of a piece family.
  Repeated destination values at different keys remain valid, and the row
  projections retain every such occurrence in the supplied key order.
\<close>

end
