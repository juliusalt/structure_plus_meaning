theory Factor_Construction_Presentations
  imports Factor_Construction_Claims Factor_Finite_Presentations Factor_Derivation
begin

section \<open>Complete accounts without a privileged enumeration\<close>

definition construction_selection_presents ::
  "((nat + local_address) \<times> local_address set) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "construction_selection_presents z t \<longleftrightarrow>
    (\<exists>a. finite_set_presents Payload_Term (snd z) a \<and>
      t=Pair_Term (construction_source_term (fst z)) a)"

lemma construction_selection_term_presents:
  assumes "finite (snd z)"
  shows "construction_selection_presents z (construction_selection_term z)"
  using finite_set_term_presents[OF assms, of Payload_Term]
  by (auto simp: construction_selection_presents_def construction_selection_term_def)

lemma construction_selection_presents_unique:
  assumes first: "construction_selection_presents z t"
    and second: "construction_selection_presents w t"
  shows "z=w"
proof -
  obtain a where sets: "finite_set_presents Payload_Term (snd z) a"
    "finite_set_presents Payload_Term (snd w) a"
    and sources: "construction_source_term (fst z)=construction_source_term (fst w)"
    using first second by (auto simp: construction_selection_presents_def)
  have fst: "fst z=fst w" using sources by (simp add: construction_source_term_exact)
  have snd: "snd z=snd w" by (rule finite_set_presents_unique[OF sets payload_term_injective])
  show ?thesis using fst snd by (rule prod_eqI)
qed

lemma construction_selection_presents_formed:
  assumes present: "construction_selection_presents z t"
    and canonical: "term_formed (construction_selection_term z)"
  shows "term_formed t"
proof -
  obtain a where read: "finite_set_presents Payload_Term (snd z) a"
    and shape: "t=Pair_Term (construction_source_term (fst z)) a"
    using present by (auto simp: construction_selection_presents_def)
  have fin: "finite (snd z)"
    using finite_collection_presents_finite[OF read[unfolded finite_set_presents_def]] .
  have source: "term_formed (construction_source_term (fst z))"
    and atoms: "\<forall>b\<in>snd z. term_formed (Payload_Term b)"
    using canonical finite_set_term_formed[OF fin, of Payload_Term]
    by (auto simp: construction_selection_term_def)
  have af: "term_formed a"
    by (rule finite_set_presents_formed[OF read]) (use atoms in blast)
  show ?thesis using shape source af by simp
qed

definition construction_claim_presents ::
  "exact_artifact list \<Rightarrow> (local_address \<times> exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> factor_term \<Rightarrow> bool" where
  "construction_claim_presents xs B W R t \<longleftrightarrow>
    (\<exists>b s orig.
      finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) B b \<and>
      finite_table_presents Payload_Term construction_selection_presents (construction_selections W) s \<and>
      finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins W) orig \<and>
      t=enumeration_term [artifact_list_term xs,b,s,orig,Target_Term (Whole_Artifact R)])"

lemma construction_claim_term_presents:
  assumes built: "source_constructs xs B W R"
  shows "construction_claim_presents xs B W R (construction_claim_term xs B W R)"
proof -
  have bases: "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T))
    B (finite_table_term Payload_Term (Target_Term \<circ> Whole_Artifact) B)"
    by (rule finite_table_term_presents[OF source_construction_finite(1,2)[OF built]]) simp
  have each_value: "\<And>z. z\<in>rel_ran (construction_selections W) \<Longrightarrow>
    construction_selection_presents z (construction_selection_term z)"
    by (rule construction_selection_term_presents)
       (use built in \<open>auto simp: source_constructs_def construction_selection_formed_def
          rel_ran_def source_selection_valid_def\<close>)
  have selections: "finite_table_presents Payload_Term construction_selection_presents
    (construction_selections W)
    (finite_table_term Payload_Term construction_selection_term (construction_selections W))"
    by (rule finite_table_term_presents[OF source_construction_finite(3,4)[OF built]])
       (rule each_value; assumption)
  have origins: "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a)
    (construction_origins W)
    (finite_table_term construction_atom_term Payload_Term (construction_origins W))"
    by (rule finite_table_term_presents[OF source_construction_finite(5,6)[OF built]]) simp
  show ?thesis using bases selections origins
    by (auto simp: construction_claim_presents_def construction_claim_term_def)
qed

lemma construction_claim_presents_formed:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and present: "construction_claim_presents xs B W R t"
  shows "term_formed t"
proof -
  obtain b s orig where reads:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) B b"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections W) s"
    "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins W) orig"
    and shape: "t=enumeration_term [artifact_list_term xs,b,s,orig,Target_Term (Whole_Artifact R)]"
    using present by (auto simp: construction_claim_presents_def)
  have canonical: "term_formed (construction_claim_term xs B W R)"
    by (rule construction_claim_formed[OF built coords])
  have inputs: "term_formed (artifact_list_term xs)" and result_value: "exact_formed R"
    and bases: "\<And>k v. (k,v)\<in>B \<Longrightarrow> term_formed (Payload_Term k) \<and> exact_formed v"
    and selections: "\<And>k v. (k,v)\<in>construction_selections W \<Longrightarrow>
      term_formed (Payload_Term k) \<and> term_formed (construction_selection_term v)"
    and origins: "\<And>k v. (k,v)\<in>construction_origins W \<Longrightarrow>
      term_formed (construction_atom_term k) \<and> term_formed (Payload_Term v)"
    using canonical
      finite_table_term_formed[OF source_construction_finite(1,2)[OF built],
        of Payload_Term "Target_Term \<circ> Whole_Artifact"]
      finite_table_term_formed[OF source_construction_finite(3,4)[OF built],
        of Payload_Term construction_selection_term]
      finite_table_term_formed[OF source_construction_finite(5,6)[OF built],
        of construction_atom_term Payload_Term]
    by (auto simp: construction_claim_term_def enumeration_term_formed)
  have bf: "term_formed b"
    by (rule finite_table_presents_formed[OF reads(1)]) (use bases in auto)
  have sf: "term_formed s"
    by (rule finite_table_presents_formed[OF reads(2)])
       (use selections construction_selection_presents_formed in blast)
  have oform: "term_formed orig"
    by (rule finite_table_presents_formed[OF reads(3)]) (use origins in auto)
  show ?thesis using shape inputs result_value bf sf oform by (simp add: enumeration_term_formed)
qed

theorem construction_claim_presents_unique:
  assumes first: "construction_claim_presents xs B W R t"
    and second: "construction_claim_presents ys C X S t"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof -
  obtain b s orig where bases:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) B b"
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) C b"
    and selections:
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections W) s"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections X) s"
    and origins:
    "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins W) orig"
    "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins X) orig"
    and inputs: "artifact_list_term xs=artifact_list_term ys" and result_value: "R=S"
    using first second by (auto simp: construction_claim_presents_def enumeration_term_injective)
  have bc: "B=C" by (rule finite_table_presents_unique[OF bases payload_term_injective]) simp
  have sel: "construction_selections W=construction_selections X"
    by (rule finite_table_presents_unique[OF selections payload_term_injective])
       (use construction_selection_presents_unique in blast)
  have org: "construction_origins W=construction_origins X"
    by (rule finite_table_presents_unique[OF origins construction_atom_term_injective]) simp
  have wx: "W=X" using sel org by (cases W; cases X) auto
  show ?thesis using inputs bc wx result_value by (simp add: artifact_list_term_exact)
qed

section \<open>Native reading includes every complete presentation\<close>

definition native_construction_claim_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address \<times> exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow>
    local_address set \<Rightarrow> local_address set \<Rightarrow> bool" where
  "native_construction_claim_at E u r xs B W R I K \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    (\<exists>t. construction_claim_presents xs B W R t \<and> term_quoted_at E u r t I K)"

theorem native_construction_presentation_total:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and present: "construction_claim_presents xs B W R t"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>S I K.
    environment_formed E \<and> artifact_at E None S \<and> term_quoted_at E None [] t I K \<and>
    native_construction_claim_at E None [] xs B W R I K \<and>
    rra_carrier (object_structure S)=I\<union>K"
proof -
  obtain E :: "local_address option artifact_environment" and S I K where layout:
    "environment_formed E" "artifact_at E None S" "term_quoted_at E None [] t I K"
    "rra_carrier (object_structure S)=I\<union>K"
    using term_quotation_total[OF construction_claim_presents_formed[OF built coords present]] by blast
  have native: "native_construction_claim_at E None [] xs B W R I K"
    using built coords present layout(3) by (auto simp: native_construction_claim_at_def)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ S], rule exI[of _ I], rule exI[of _ K])
       (use layout native in blast)
qed

theorem native_construction_claim_total:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>S I K.
    environment_formed E \<and> artifact_at E None S \<and>
    native_construction_claim_at E None [] xs B W R I K \<and>
    rra_carrier (object_structure S)=I\<union>K"
  using native_construction_presentation_total[
    OF built coords construction_claim_term_presents[OF built]] by blast

section \<open>Permission descends to the complete unordered account\<close>

definition construction_permission_invariant ::
  "('a,'p,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "construction_permission_invariant P d \<longleftrightarrow>
    (\<forall>xs B W R t u. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W R t \<longrightarrow>
      construction_claim_presents xs B W R u \<longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> schema_call_formed P d u) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> (d,u)\<in>positive_meaning P))"

lemma construction_permission_invariantD:
  assumes invariant: "construction_permission_invariant P d"
    and built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and first: "construction_claim_presents xs B W R t"
    and second: "construction_claim_presents xs B W R u"
  shows "schema_call_formed P d t \<longleftrightarrow> schema_call_formed P d u"
    "(d,t)\<in>positive_meaning P \<longleftrightarrow> (d,u)\<in>positive_meaning P"
  using invariant[unfolded construction_permission_invariant_def, rule_format,
    OF built coords first second] by auto

lemma construction_permission_invariant_transport:
  assumes boundary: "\<And>t. schema_call_formed Q e t \<longleftrightarrow> schema_call_formed P d t"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  shows "construction_permission_invariant Q e \<longleftrightarrow> construction_permission_invariant P d"
  by (simp add: construction_permission_invariant_def boundary meaning)

theorem construction_permission_factors_through_account:
  "construction_permission_invariant P d \<longleftrightarrow>
    (\<exists>A M. \<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W R t \<longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> A xs B W R) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> M xs B W R))"
proof
  assume invariant: "construction_permission_invariant P d"
  let ?A = "\<lambda>xs B W R. schema_call_formed P d (construction_claim_term xs B W R)"
  let ?M = "\<lambda>xs B W R. (d,construction_claim_term xs B W R)\<in>positive_meaning P"
  show "\<exists>A M. \<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W R t \<longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> A xs B W R) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> M xs B W R)"
  proof (rule exI[of _ ?A], rule exI[of _ ?M], intro allI impI)
    fix xs B W R t assume built: "source_constructs xs B W R"
      and coords: "construction_coordinates_formed B W"
      and present: "construction_claim_presents xs B W R t"
    show "(schema_call_formed P d t \<longleftrightarrow> ?A xs B W R) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> ?M xs B W R)"
      using construction_permission_invariantD[
        OF invariant built coords present construction_claim_term_presents[OF built]] by blast
  qed
next
  assume "\<exists>A M. \<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W R t \<longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> A xs B W R) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> M xs B W R)"
  then obtain A M where factors: "\<And>xs B W R t. source_constructs xs B W R \<Longrightarrow>
      construction_coordinates_formed B W \<Longrightarrow>
      construction_claim_presents xs B W R t \<Longrightarrow>
      (schema_call_formed P d t \<longleftrightarrow> A xs B W R) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> M xs B W R)" by blast
  show "construction_permission_invariant P d"
    unfolding construction_permission_invariant_def
  proof (intro allI impI)
    fix xs B W R t u assume built: "source_constructs xs B W R"
      and coords: "construction_coordinates_formed B W"
      and first: "construction_claim_presents xs B W R t"
      and second: "construction_claim_presents xs B W R u"
    show "(schema_call_formed P d t \<longleftrightarrow> schema_call_formed P d u) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> (d,u)\<in>positive_meaning P)"
      using factors[OF built coords first] factors[OF built coords second] by blast
  qed
qed

definition factor_constructs ::
  "('a,'p,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> exact_artifact list \<Rightarrow>
    (local_address \<times> exact_artifact) set \<Rightarrow> addressed_construction \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "factor_constructs P d xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<exists>t. construction_claim_presents xs B W R t \<and> (d,t)\<in>positive_meaning P)"

theorem factor_construction_at_presentation:
  assumes built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    and present: "construction_claim_presents xs B W R t"
  shows "factor_constructs P d xs B W R \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof
  assume "factor_constructs P d xs B W R"
  then obtain u where other: "construction_claim_presents xs B W R u" "(d,u)\<in>positive_meaning P"
    by (auto simp: factor_constructs_def)
  show "(d,t)\<in>positive_meaning P"
    using construction_permission_invariantD(2)[OF invariant built coords other(1) present] other(2) by blast
next
  assume "(d,t)\<in>positive_meaning P"
  then show "factor_constructs P d xs B W R"
    using built coords invariant present by (auto simp: factor_constructs_def)
qed

theorem factor_construction_every_presentation:
  "factor_constructs P d xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<forall>t. construction_claim_presents xs B W R t \<longrightarrow> (d,t)\<in>positive_meaning P)"
proof
  assume allowed: "factor_constructs P d xs B W R"
  have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using allowed by (auto simp: factor_constructs_def)
  have every: "\<forall>t. construction_claim_presents xs B W R t \<longrightarrow> (d,t)\<in>positive_meaning P"
  proof (intro allI impI)
    fix t assume present: "construction_claim_presents xs B W R t"
    show "(d,t)\<in>positive_meaning P"
      using factor_construction_at_presentation[OF built coords invariant present] allowed by blast
  qed
  show "source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<forall>t. construction_claim_presents xs B W R t \<longrightarrow> (d,t)\<in>positive_meaning P)"
    using built coords invariant every by blast
next
  assume all: "source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<forall>t. construction_claim_presents xs B W R t \<longrightarrow> (d,t)\<in>positive_meaning P)"
  have built: "source_constructs xs B W R" using all by blast
  have present: "construction_claim_presents xs B W R (construction_claim_term xs B W R)"
    by (rule construction_claim_term_presents[OF built])
  show "factor_constructs P d xs B W R"
    using all present by (auto simp: factor_constructs_def)
qed

theorem factor_construction_assembly:
  assumes "factor_constructs P d xs B W R"
  shows "K2 (construction_assembly xs B W) \<and> R=assembly_output (construction_assembly xs B W)"
  using assms by (simp add: factor_constructs_def source_constructs_iff_K2)

theorem factor_construction_derivation:
  "factor_constructs P d xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and>
    construction_permission_invariant P d \<and>
    (\<exists>t tree. construction_claim_presents xs B W R t \<and> checks_schema_proof P tree d t)"
  by (simp add: factor_constructs_def schema_proof_adequate)

text \<open>
  Invariance is an explicit admissibility obligation for interpreting a chosen
  definition as permission on unordered accounts. It is a derived property of
  its existing interface and positive meaning, not a new consequence rule.
  A positive proof about one serialization alone does not discharge it.
  Under this obligation, existential, universal, and any supplied complete
  presentation give the same permission. The definition selects no sorting.

  Ordinary ordered arguments keep their order. Input occurrences, exact source
  coordinates, and the five distinct account fields are preserved here.
  A native mechanism for checking admission evidence remains a separate task.
\<close>

end
