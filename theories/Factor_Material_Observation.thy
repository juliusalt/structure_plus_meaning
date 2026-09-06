theory Factor_Material_Observation
  imports Factor_Term_Encoding "HOL-Library.Multiset"
begin

section \<open>Complete finite enumerations of the existing object basis\<close>

definition enumerated_artifact ::
  "local_address list \<Rightarrow> (local_address \<times> local_address \<times> local_address) list \<Rightarrow>
    (local_address \<times> octets) list \<Rightarrow> (local_address \<times> octets) list \<Rightarrow> exact_artifact" where
  "enumerated_artifact A E B F =
    \<lparr>object_structure = \<lparr>rra_carrier=set A, rra_incidence=set E\<rparr>,
     object_data = \<lparr>bag_count=count_list B, functional_bindings=set F\<rparr>\<rparr>"

definition artifact_enumeration ::
  "exact_artifact \<Rightarrow> local_address list \<Rightarrow>
    (local_address \<times> local_address \<times> local_address) list \<Rightarrow>
    (local_address \<times> octets) list \<Rightarrow> (local_address \<times> octets) list \<Rightarrow> bool" where
  "artifact_enumeration R A E B F \<longleftrightarrow>
    exact_formed R \<and> distinct A \<and> distinct E \<and> distinct F \<and> R = enumerated_artifact A E B F"

lemma artifact_enumeration_material:
  assumes "artifact_enumeration R A E B F"
  shows "exact_formed R" "set A = rra_carrier (object_structure R)"
    "set E = rra_incidence (object_structure R)"
    "count_list B = bag_count (object_data R)"
    "set F = functional_bindings (object_data R)"
    "set B = bag_support (object_data R)"
  using assms by (auto simp: artifact_enumeration_def enumerated_artifact_def bag_support_def count_list_0_iff)

lemma artifact_enumeration_no_repeated_set_entry:
  assumes "artifact_enumeration R A E B F"
  shows "distinct A \<and> distinct E \<and> distinct F"
  using assms by (simp add: artifact_enumeration_def)

lemma finite_counts_have_enumeration:
  assumes finite: "finite {x. 0 < n x}"
  shows "\<exists>xs. count_list xs = n"
proof -
  obtain xs where list: "mset xs = Abs_multiset n"
    using surjD[OF surj_mset, of "Abs_multiset n"] by auto
  have counts: "count (Abs_multiset n) = n" by (rule count_Abs_multiset[OF finite])
  have "count_list xs = n"
    by (rule ext) (use list counts in \<open>simp add: count_mset[symmetric]\<close>)
  then show ?thesis by blast
qed

theorem artifact_enumeration_exists:
  assumes formed: "exact_formed R"
  shows "\<exists>A E B F. artifact_enumeration R A E B F"
proof -
  have finiteA: "finite (rra_carrier (object_structure R))"
    and finiteE: "finite (rra_incidence (object_structure R))"
    and finiteF: "finite (functional_bindings (object_data R))"
    and finiteB: "finite {x. 0 < bag_count (object_data R) x}"
    using formed by (auto simp: exact_formed_def object_formed_def rra_formed_def
        basis_formed_def bag_support_def)
  obtain A where atoms: "set A = rra_carrier (object_structure R)" "distinct A"
    using finite_distinct_list[OF finiteA] by blast
  obtain E where edges: "set E = rra_incidence (object_structure R)" "distinct E"
    using finite_distinct_list[OF finiteE] by blast
  obtain F where functional: "set F = functional_bindings (object_data R)" "distinct F"
    using finite_distinct_list[OF finiteF] by blast
  obtain B where counts: "count_list B = bag_count (object_data R)"
    using finite_counts_have_enumeration[OF finiteB] by blast
  have recovered: "R = enumerated_artifact A E B F"
    using atoms(1) edges(1) functional(1) counts
    by (simp add: exact_identity_iff rra_identity basis_identity enumerated_artifact_def)
  have "artifact_enumeration R A E B F"
    using formed atoms(2) edges(2) functional(2) recovered by (simp add: artifact_enumeration_def)
  then show ?thesis by blast
qed

theorem artifact_enumeration_determines_source:
  assumes "artifact_enumeration R A E B F" "artifact_enumeration S A E B F"
  shows "R = S"
  using assms by (simp add: artifact_enumeration_def)

theorem artifact_enumeration_order:
  assumes "distinct A" "distinct A'" "distinct E" "distinct E'" "distinct F" "distinct F'"
    "set A = set A'" "set E = set E'" "count_list B = count_list B'" "set F = set F'"
  shows "artifact_enumeration R A E B F \<longleftrightarrow> artifact_enumeration R A' E' B' F'"
  using assms by (simp add: artifact_enumeration_def enumerated_artifact_def)

section \<open>Ordinary terms expose the complete enumeration\<close>

fun enumeration_term :: "factor_term list \<Rightarrow> factor_term" where
  "enumeration_term [] = Target_Term (Whole_Artifact empty_artifact)"
| "enumeration_term (t#ts) = Pair_Term t (enumeration_term ts)"

lemma enumeration_term_injective:
  "enumeration_term xs = enumeration_term ys \<longleftrightarrow> xs = ys"
  by (induction xs arbitrary: ys) (case_tac ys; auto)+

lemma enumeration_term_formed:
  "term_formed (enumeration_term xs) \<longleftrightarrow> (\<forall>t\<in>set xs. term_formed t)"
  by (induction xs) auto

definition occurrence_term :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term" where
  "occurrence_term R a = Target_Term (Occurrence_Anchor (R,a))"

definition atom_term :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term" where
  "atom_term R a = Pair_Term (Payload_Term a) (occurrence_term R a)"

lemma atom_term_injective:
  "inj (atom_term R)"
  by (rule injI) (simp add: atom_term_def)

definition incidence_term ::
  "exact_artifact \<Rightarrow> (local_address \<times> local_address \<times> local_address) \<Rightarrow> factor_term" where
  "incidence_term R e = (case e of (a,b,c) \<Rightarrow>
    Pair_Term (occurrence_term R a) (Pair_Term (occurrence_term R b) (occurrence_term R c)))"

definition attachment_term :: "exact_artifact \<Rightarrow> (local_address \<times> octets) \<Rightarrow> factor_term" where
  "attachment_term R av = (case av of (a,v) \<Rightarrow> Pair_Term (occurrence_term R a) (Payload_Term v))"

lemma occurrence_term_injective [simp]:
  "occurrence_term R a = occurrence_term R b \<longleftrightarrow> a = b"
  by (simp add: occurrence_term_def)

lemma incidence_term_injective:
  "inj (incidence_term R)"
  by (rule injI) (auto simp: incidence_term_def split: prod.splits)

lemma attachment_term_injective:
  "inj (attachment_term R)"
  by (rule injI) (auto simp: attachment_term_def split: prod.splits)

lemma occurrence_term_formed:
  "term_formed (occurrence_term R a) \<longleftrightarrow>
    exact_formed R \<and> a \<in> rra_carrier (object_structure R)"
  by (simp add: occurrence_term_def anchor_formed_def)

lemma atom_term_formed:
  "term_formed (atom_term R a) \<longleftrightarrow>
    exact_formed R \<and> a \<in> rra_carrier (object_structure R)"
  by (auto simp: atom_term_def occurrence_term_formed exact_formed_def)

lemma artifact_enumeration_terms_formed:
  assumes enumeration: "artifact_enumeration R A E B F"
  shows "term_formed (enumeration_term (map (atom_term R) A))"
    "term_formed (enumeration_term (map (incidence_term R) E))"
    "term_formed (enumeration_term (map (attachment_term R) B))"
    "term_formed (enumeration_term (map (attachment_term R) F))"
proof -
  have formed: "exact_formed R" and atoms: "set A = rra_carrier (object_structure R)"
    and edges: "set E = rra_incidence (object_structure R)"
    and bags: "set B = bag_support (object_data R)"
    and funcs: "set F = functional_bindings (object_data R)"
    using artifact_enumeration_material[OF enumeration] by auto
  have edge_members: "\<And>a b c. (a,b,c) \<in> set E \<Longrightarrow>
    a \<in> rra_carrier (object_structure R) \<and> b \<in> rra_carrier (object_structure R) \<and>
    c \<in> rra_carrier (object_structure R)"
    using formed edges by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have data_members: "\<And>a v. (a,v) \<in> set B \<union> set F \<Longrightarrow>
    a \<in> rra_carrier (object_structure R) \<and> octets_formed v"
  proof -
    fix a v assume member: "(a,v) \<in> set B \<union> set F"
    have actual: "(a,v) \<in> bag_support (object_data R) \<union> functional_bindings (object_data R)"
      using member bags funcs by simp
    have basis: "basis_formed (rra_carrier (object_structure R)) (object_data R)"
      using formed by (simp add: exact_formed_def object_formed_def)
    have carrier: "a \<in> rra_carrier (object_structure R)"
      using basis actual by (auto simp: basis_formed_def)
    have payload_value: "v \<in> basis_values (object_data R)"
      using actual by (auto simp: basis_values_def intro: rev_image_eqI)
    have vf: "octets_formed v" using formed payload_value by (auto simp: exact_formed_def)
    show "a \<in> rra_carrier (object_structure R) \<and> octets_formed v" using carrier vf by blast
  qed
  show "term_formed (enumeration_term (map (atom_term R) A))"
    using formed atoms by (simp add: enumeration_term_formed atom_term_formed)
  show "term_formed (enumeration_term (map (incidence_term R) E))"
    using formed edge_members
    by (auto simp: enumeration_term_formed incidence_term_def occurrence_term_formed split: prod.splits)
  show "term_formed (enumeration_term (map (attachment_term R) B))"
    "term_formed (enumeration_term (map (attachment_term R) F))"
    using formed data_members
    by (auto simp: enumeration_term_formed attachment_term_def occurrence_term_formed split: prod.splits)
qed

definition material_observation ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "material_observation source atoms edges counts functions \<longleftrightarrow>
    (\<exists>R A E B F. artifact_enumeration R A E B F \<and> source = Target_Term (Whole_Artifact R) \<and>
      atoms = enumeration_term (map (atom_term R) A) \<and>
      edges = enumeration_term (map (incidence_term R) E) \<and>
      counts = enumeration_term (map (attachment_term R) B) \<and>
      functions = enumeration_term (map (attachment_term R) F))"

lemma material_observation_formed:
  assumes "material_observation source atoms edges counts functions"
  shows "term_formed source \<and> term_formed atoms \<and> term_formed edges \<and>
    term_formed counts \<and> term_formed functions"
  using assms artifact_enumeration_material(1) artifact_enumeration_terms_formed
  by (auto simp: material_observation_def)

theorem material_observation_incidence_empty:
  assumes "material_observation (Target_Term (Whole_Artifact R)) atoms edges counts functions"
  shows "edges = enumeration_term [] \<longleftrightarrow> rra_incidence (object_structure R) = {}"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F"
    and encoding: "edges = enumeration_term (map (incidence_term R) E)"
    using assms by (auto simp: material_observation_def)
  have actual: "set E = rra_incidence (object_structure R)"
    by (rule artifact_enumeration_material(3)[OF enumeration])
  show ?thesis by (simp only: encoding enumeration_term_injective) (simp add: actual[symmetric])
qed

theorem material_observation_total:
  assumes "exact_formed R"
  shows "\<exists>atoms edges counts functions.
    material_observation (Target_Term (Whole_Artifact R)) atoms edges counts functions"
  using artifact_enumeration_exists[OF assms] by (auto simp: material_observation_def)

theorem material_observation_exact:
  "material_observation (Target_Term (Whole_Artifact R))
    (enumeration_term (map (atom_term R) A))
    (enumeration_term (map (incidence_term R) E))
    (enumeration_term (map (attachment_term R) B))
    (enumeration_term (map (attachment_term R) F)) \<longleftrightarrow> artifact_enumeration R A E B F"
proof -
  have atom_inj: "inj (atom_term R)" by (rule atom_term_injective)
  show ?thesis
    by (auto simp: material_observation_def enumeration_term_injective
        inj_map_eq_map[OF atom_inj] inj_map_eq_map[OF incidence_term_injective]
        inj_map_eq_map[OF attachment_term_injective])
qed

theorem material_observation_rejects_omitted_incidence:
  assumes "artifact_enumeration R A E B F" "e \<in> set E"
  shows "\<not> material_observation (Target_Term (Whole_Artifact R))
    (enumeration_term (map (atom_term R) A))
    (enumeration_term (map (incidence_term R) (remove1 e E)))
    (enumeration_term (map (attachment_term R) B))
    (enumeration_term (map (attachment_term R) F))"
proof -
  have distinct: "distinct E" using assms(1) by (simp add: artifact_enumeration_def)
  have source: "set E = rra_incidence (object_structure R)"
    by (rule artifact_enumeration_material(3)[OF assms(1)])
  have missing: "e \<notin> set (remove1 e E)" using distinct by simp
  show ?thesis using source missing assms(2)
    by (auto simp: material_observation_exact dest: artifact_enumeration_material(3))
qed

definition material_tuple ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "material_tuple source atoms edges counts functions =
    Pair_Term source (Pair_Term atoms (Pair_Term edges (Pair_Term counts functions)))"

theorem material_observation_has_native_quotation:
  assumes observed: "material_observation source atoms edges counts functions"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>R I K.
    environment_formed E \<and> artifact_at E None R \<and>
    term_quoted_at E None [] (material_tuple source atoms edges counts functions) I K \<and>
    rra_carrier (object_structure R) = I \<union> K"
proof -
  have formed: "term_formed (material_tuple source atoms edges counts functions)"
    using material_observation_formed[OF observed] by (simp add: material_tuple_def)
  show ?thesis by (rule term_quotation_total[OF formed])
qed

text \<open>
  A material observation checks one complete equation over the existing RRA
  object basis. It invokes no semantic judgment or externally supplied reader.
  Each carrier entry links its actual address, as an opaque payload, to its
  exact occurrence anchor. Incidences and attachments use those anchors. This
  exposes the identity boundary required by occurrence citations without
  interpreting address bytes as operation selectors. Other payload bytes remain
  opaque values. Set-valued tables have no repeated entry. Anonymous attachments
  use exactly their original multiplicities.

  An enumeration is an explicitly ordered ordinary argument. Different orders
  with the same complete tables satisfy this particular observation relation;
  no order is assigned to the source artifact, and no rule about reordering
  arbitrary semantic premises follows. The empty enumeration uses the unique
  empty formed artifact. No coordinate or attached name selects an observation.

  This theory establishes the material relation and native quotations of its
  arguments. Integrating the relation into recovered semantic schemas requires
  its own complete native premise reader and meaning construction.
\<close>

end
