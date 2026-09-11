theory Factor_Construction_Claims
  imports Factor_Construction Factor_Finite_Terms
    "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

section \<open>Exact coordinates of a complete construction account\<close>

type_synonym addressed_construction = "(local_address,local_address) source_construction"

fun construction_source_term :: "nat + local_address \<Rightarrow> factor_term" where
  "construction_source_term (Inl n) = natural_term n"
| "construction_source_term (Inr b) = Payload_Term b"

lemma construction_source_term_exact:
  "construction_source_term j = construction_source_term k \<longleftrightarrow> j=k"
  by (cases j; cases k) (auto simp: eq_commute)

definition construction_selection_term ::
  "((nat + local_address) \<times> local_address set) \<Rightarrow> factor_term" where
  "construction_selection_term z =
    Pair_Term (construction_source_term (fst z)) (finite_set_term Payload_Term (snd z))"

definition construction_atom_term :: "local_address \<times> local_address \<Rightarrow> factor_term" where
  "construction_atom_term z = Pair_Term (Payload_Term (fst z)) (Payload_Term (snd z))"

definition construction_coordinates_formed ::
  "(local_address \<times> exact_artifact) set \<Rightarrow> addressed_construction \<Rightarrow> bool" where
  "construction_coordinates_formed B W \<longleftrightarrow>
    (\<forall>b R. (b,R) \<in> B \<longrightarrow> octets_formed b) \<and>
    (\<forall>s j A. (s,j,A) \<in> construction_selections W \<longrightarrow> octets_formed s)"

lemma payload_term_injective: "inj Payload_Term"
  by (rule injI) simp

lemma whole_artifact_term_injective: "inj (Target_Term \<circ> Whole_Artifact)"
  by (rule injI) simp

lemma construction_atom_term_injective: "inj construction_atom_term"
  by (rule injI) (auto simp: construction_atom_term_def)

lemma construction_selection_term_exact:
  assumes "finite A" "finite C"
  shows "construction_selection_term (j,A) = construction_selection_term (k,C) \<longleftrightarrow>
    j=k \<and> A=C"
  using finite_set_term_exact[OF assms payload_term_injective]
  by (simp add: construction_selection_term_def construction_source_term_exact)

lemma construction_selection_term_formed:
  assumes sf: "construction_sources_formed xs B"
    and valid: "source_selection_valid xs B j A"
    and addresses: "\<forall>b R. (b,R) \<in> B \<longrightarrow> octets_formed b"
  shows "term_formed (construction_selection_term (j,A))"
proof -
  obtain R where source: "construction_source_at xs B j R"
    using valid by (auto simp: source_selection_valid_def)
  have resolved: "construction_source_value xs B j = R" and rf: "exact_formed R"
    using construction_source_value_at[OF sf source] by auto
  have finite: "finite A" and subset: "A \<subseteq> rra_carrier (object_structure R)"
    using valid resolved by (auto simp: source_selection_valid_def)
  have atoms: "\<forall>a\<in>A. octets_formed a" using subset rf by (auto simp: exact_formed_def)
  have src: "term_formed (construction_source_term j)"
    using source addresses by (cases j) auto
  show ?thesis using src atoms finite_set_term_formed[OF finite, of Payload_Term]
    by (simp add: construction_selection_term_def)
qed

lemma construction_origin_coordinates:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and origin: "((s,a),b) \<in> construction_origins W"
  shows "octets_formed s \<and> octets_formed a \<and> octets_formed b"
proof -
  have mapping: "exact_map (copied_carrier (construction_pieces xs B W))
    (rra_carrier (object_structure R)) (construction_origins W)"
    and pf: "piece_family_formed (construction_pieces xs B W)"
    and rf: "exact_formed R"
    using built by (auto simp: source_constructs_def assembly_relation_def)
  have copied: "(s,a) \<in> copied_carrier (construction_pieces xs B W)"
    and out: "b \<in> rra_carrier (object_structure R)"
    using origin mapping by (auto simp: exact_map_def rel_dom_def rel_ran_def)
  have slot: "s \<in> piece_slots (construction_pieces xs B W)"
    and atom: "a \<in> rra_carrier (object_structure (piece_at (construction_pieces xs B W) s))"
    using copied by (auto simp: copied_carrier_def)
  have key: "s \<in> rel_dom (construction_selections W)"
    using slot by (simp add: construction_piece_slots)
  have sa: "octets_formed s" using key coords
    by (auto simp: construction_coordinates_formed_def rel_dom_def)
  have aa: "octets_formed a" using piece_at_formed[OF pf slot] atom
    by (auto simp: exact_formed_def)
  have ba: "octets_formed b" using rf out by (auto simp: exact_formed_def)
  show ?thesis using sa aa ba by blast
qed

section \<open>One complete ordinary argument\<close>

definition construction_claim_term ::
  "exact_artifact list \<Rightarrow> (local_address \<times> exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> factor_term" where
  "construction_claim_term xs B W R = enumeration_term
    [artifact_list_term xs,
     finite_table_term Payload_Term (Target_Term \<circ> Whole_Artifact) B,
     finite_table_term Payload_Term construction_selection_term (construction_selections W),
     finite_table_term construction_atom_term Payload_Term (construction_origins W),
     Target_Term (Whole_Artifact R)]"

lemma construction_claim_formed:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
  shows "term_formed (construction_claim_term xs B W R)"
proof -
  have sf: "construction_sources_formed xs B"
    and selections: "\<And>s j A. (s,j,A) \<in> construction_selections W \<Longrightarrow>
      source_selection_valid xs B j A"
    using built by (auto simp: source_constructs_def construction_selection_formed_def)
  have ba: "\<forall>b T. (b,T) \<in> B \<longrightarrow> octets_formed b"
    and sa: "\<forall>s j A. (s,j,A) \<in> construction_selections W \<longrightarrow> octets_formed s"
    using coords by (auto simp: construction_coordinates_formed_def)
  have inputs: "term_formed (artifact_list_term xs)"
    using sf by (simp add: artifact_list_term_formed construction_sources_formed_def)
  have bases: "term_formed (finite_table_term Payload_Term (Target_Term \<circ> Whole_Artifact) B)"
    using ba sf finite_table_term_formed[OF source_construction_finite(1,2)[OF built],
      of Payload_Term "Target_Term \<circ> Whole_Artifact"]
    by (auto simp: construction_sources_formed_def)
  have each_selection: "\<forall>s z. (s,z) \<in> construction_selections W \<longrightarrow>
    term_formed (Payload_Term s) \<and> term_formed (construction_selection_term z)"
  proof (intro allI impI)
    fix s z assume member: "(s,z) \<in> construction_selections W"
    obtain j A where shape: "z=(j,A)" by (cases z) auto
    have chosen: "(s,j,A) \<in> construction_selections W" using member shape by simp
    have formed: "term_formed (construction_selection_term (j,A))"
      by (rule construction_selection_term_formed[OF sf selections[OF chosen] ba])
    show "term_formed (Payload_Term s) \<and> term_formed (construction_selection_term z)"
      using formed sa chosen shape by auto
  qed
  have pieces: "term_formed (finite_table_term Payload_Term construction_selection_term
    (construction_selections W))"
    using finite_table_term_formed[OF source_construction_finite(3,4)[OF built],
      of Payload_Term construction_selection_term] each_selection by blast
  have each_origin: "\<forall>k b. (k,b) \<in> construction_origins W \<longrightarrow>
    term_formed (construction_atom_term k) \<and> term_formed (Payload_Term b)"
    using construction_origin_coordinates[OF built coords]
    by (auto simp: construction_atom_term_def)
  have origins: "term_formed (finite_table_term construction_atom_term Payload_Term
    (construction_origins W))"
    using finite_table_term_formed[OF source_construction_finite(5,6)[OF built],
      of construction_atom_term Payload_Term] each_origin by blast
  show ?thesis using inputs bases pieces origins source_construction_finite(7)[OF built]
    by (simp add: construction_claim_term_def enumeration_term_formed)
qed

text \<open>
  This function supplies one finite presentation witness. Its ordering has no
  semantic authority. Factor_Construction_Presentations defines the complete
  presentation relation and the separate permission admissibility obligation.
\<close>

end
