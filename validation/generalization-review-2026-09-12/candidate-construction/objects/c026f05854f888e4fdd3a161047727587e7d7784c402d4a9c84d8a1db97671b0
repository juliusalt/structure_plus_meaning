theory Factor_Derivation_Presentations
  imports Factor_Judgment_Presentations Factor_Derivation_Admission Factor_Program_Scopes
begin

section \<open>Complete identified claim collections use the general collection class\<close>

type_synonym native_claims =
  "(local_address option definition_site \<times> (local_address option definition_site \<times> factor_term)) set"
type_synonym derivation_record =
  "site_context \<times> (local_address option definition_site \<times>
    ((local_address option definition_site \<times> factor_term) \<times> native_claims))"
type_synonym derivation_details =
  "local_address option native_system \<times> (local_address option native_derivation_graph \<times> native_claims)"

abbreviation positioned_claim_value ::
  "(local_address option definition_site \<times> (local_address option definition_site \<times> factor_term)) \<Rightarrow> factor_term" where
  "positioned_claim_value q \<equiv> Pair_Term (definition_site_value (fst q))
    (call_instance_value (fst (snd q)) (snd (snd q)))"

lemma positioned_claim_value_injective: "inj positioned_claim_value"
  by (rule injI) (auto simp: call_instance_value_injective prod_eq_iff)

lemma positioned_claim_rows:
  "data_list_term (map positioned_claim_value xs)=positioned_call_rows_term xs"
  by (simp add: map_map comp_def case_prod_unfold)

definition claim_collection_presents :: "native_claims \<Rightarrow> factor_term \<Rightarrow> bool" where
  "claim_collection_presents=data_collection_presents (\<lambda>q t. t=positioned_claim_value q)"

lemma claim_collection_fields:
  "claim_collection_presents H t \<longleftrightarrow>
    (\<exists>hs. distinct hs \<and> set hs=H \<and> t=positioned_call_rows_term hs)"
  by (simp only: claim_collection_presents_def data_collection_presents_function positioned_claim_rows)

theorem claim_collection_presentation_class:
  "presentation_class claim_collection_presents finite
    (\<lambda>t. \<exists>hs. distinct hs \<and> t=positioned_call_rows_term hs)"
  using injective_data_collection_class[OF positioned_claim_value_injective]
  by (simp only: claim_collection_presents_def positioned_claim_rows)

interpretation claim_collections: presentation_class claim_collection_presents finite
  "\<lambda>t. \<exists>hs. distinct hs \<and> t=positioned_call_rows_term hs"
  by (rule claim_collection_presentation_class)

abbreviation call_value_presents ::
  "(local_address option definition_site \<times> factor_term) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "call_value_presents q t \<equiv> t=call_instance_value (fst q) (snd q)"

lemma call_value_presentation_class:
  "presentation_class call_value_presents (\<lambda>_. True) (\<lambda>t. \<exists>q. call_value_presents q t)"
proof -
  have injective: "inj (\<lambda>q. call_instance_value (fst q) (snd q))"
    using call_instance_pair_injective by (simp only: case_prod_unfold)
  show ?thesis using injective_presentation_class[
      where f="\<lambda>q. call_instance_value (fst q) (snd q)" and D="\<lambda>_. True"] injective by simp
qed

section \<open>One actual source supplies the program, proof graph, and reading\<close>

definition derivation_record_presents :: "derivation_record \<Rightarrow> factor_term \<Rightarrow> bool" where
  "derivation_record_presents =
    factor_pair_presents source_root_presents
      (factor_pair_presents site_coordinate_presents (factor_pair_presents call_value_presents claim_collection_presents))"

definition derivation_record_valid :: "derivation_record \<Rightarrow> bool" where
  "derivation_record_valid z \<longleftrightarrow>
    (case z of ((E,p),(root,(q,H))) \<Rightarrow> (\<exists>P G. native_package_at E (fst p) (snd p) P \<and>
      native_schema_graph_at E root G \<and> schema_graph_derives (positioned_program P) G root (fst q) (snd q) H))"

definition derivation_record_reading :: "derivation_record \<Rightarrow> derivation_details \<Rightarrow> bool" where
  "derivation_record_reading z b \<longleftrightarrow>
    (case (z,b) of (((E,p),(root,(q,H))),(P,(G,J))) \<Rightarrow>
      native_package_at E (fst p) (snd p) P \<and> native_schema_graph_at E root G \<and>
      schema_graph_reading (positioned_program P) G root (fst q) (snd q) J \<and>
      H=schema_graph_assumptions G J)"

definition derivation_presents :: "derivation_record \<Rightarrow> factor_term \<Rightarrow> bool" where
  "derivation_presents z t \<longleftrightarrow> derivation_record_valid z \<and> derivation_record_presents z t"

lemma derivation_record_cases:
  fixes z :: derivation_record
  obtains E p root q H where "z=((E,p),(root,(q,H)))"
  by (rule that[of "fst (fst z)" "snd (fst z)" "fst (snd z)"
    "fst (snd (snd z))" "snd (snd (snd z))"]) simp

lemma derivation_record_fields:
  "derivation_record_presents ((E,p),(root,(q,H))) z \<longleftrightarrow>
    p\<in>environment_positions E \<and>
    (\<exists>e hs. environment_value_presents E e \<and> distinct hs \<and> set hs=H \<and>
      z=derivation_argument e (use_data_term (fst p)) (Payload_Term (snd p)) (definition_site_value root)
        (definition_site_value (fst q)) (snd q) (positioned_call_rows_term hs))"
  by (simp only: derivation_record_presents_def factor_pair_presents_def source_root_presents_def
    claim_collection_fields call_instance_value_def fst_conv snd_conv; blast)

lemma derivation_record_valid_fields:
  "derivation_record_valid ((E,p),(root,(q,H))) \<longleftrightarrow>
    (\<exists>P G. native_package_at E (fst p) (snd p) P \<and> native_schema_graph_at E root G \<and>
      schema_graph_derives (positioned_program P) G root (fst q) (snd q) H)"
  by (simp only: derivation_record_valid_def case_prod_conv)

theorem derivation_record_class:
  "presentation_class derivation_record_presents
    (\<lambda>z. site_context_formed (fst z) \<and> finite (snd (snd (snd z))))
    (\<lambda>t. \<exists>z. derivation_record_presents z t)"
proof -
  let ?S="\<lambda>t. \<exists>z. source_root_presents z t"
  let ?N="\<lambda>t. \<exists>d. site_coordinate_presents d t"
  let ?C="\<lambda>t. \<exists>q. call_value_presents q t"
  let ?H="\<lambda>t. \<exists>hs. distinct hs \<and> t=positioned_call_rows_term hs"
  let ?body="\<lambda>t. \<exists>c h. ?C c \<and> ?H h \<and> t=Pair_Term c h"
  let ?node="\<lambda>t. \<exists>n b. ?N n \<and> ?body b \<and> t=Pair_Term n b"
  let ?A="\<lambda>t. \<exists>s n. ?S s \<and> ?node n \<and> t=Pair_Term s n"
  have result: "presentation_class derivation_record_presents
      (\<lambda>z. site_context_formed (fst z) \<and> finite (snd (snd (snd z)))) ?A"
    using factor_pair_class[OF source_root_presentation_class
      factor_pair_class[OF site_coordinate_presentation
        factor_pair_class[OF call_value_presentation_class claim_collection_presentation_class]]]
    by (simp add: derivation_record_presents_def)
  interpret records: presentation_class derivation_record_presents
    "\<lambda>z. site_context_formed (fst z) \<and> finite (snd (snd (snd z)))" ?A by (rule result)
  have admission: "?A=(\<lambda>t. \<exists>z. derivation_record_presents z t)"
    by (rule ext) (rule records.admissible_iff)
  show ?thesis using result by (simp only: admission)
qed

lemma derivation_record_bound:
  assumes valid: "derivation_record_valid z"
  shows "site_context_formed (fst z) \<and> finite (snd (snd (snd z)))"
proof -
  obtain E p root q H where shape: "z=((E,p),(root,(q,H)))"
    by (rule derivation_record_cases[of z]) (rule that; assumption)
  obtain P G where parts: "native_package_at E (fst p) (snd p) P" "native_schema_graph_at E root G"
    "schema_graph_derives (positioned_program P) G root (fst q) (snd q) H"
    using valid by (simp only: shape derivation_record_valid_fields) blast
  have environment: "environment_formed E" by (rule native_schema_graph_environment[OF parts(2)])
  have position: "p\<in>environment_positions E" using native_package_root_position[OF parts(1)] by simp
  have finite: "finite H" by (rule schema_graph_exact_assertions(2)[OF parts(3)])
  show ?thesis using environment position finite by (simp only: shape fst_conv snd_conv)
qed

theorem derivation_class_admission:
  "(102,t)\<in>positive_meaning derivation_admission_system \<longleftrightarrow> (\<exists>z. derivation_presents z t)"
proof
  assume holds: "(102,t)\<in>positive_meaning derivation_admission_system"
  obtain E e pu pr root d x hs P G where parts:
    "t=derivation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) x (positioned_call_rows_term hs)"
    "environment_value_presents E e" "native_package_at E pu pr P" "native_schema_graph_at E root G"
    "distinct hs" "schema_graph_derives (positioned_program P) G root d x (set hs)"
    using derivation_admission_sound[OF holds] by (elim exE conjE) (rule that; assumption)
  let ?z="((E,(pu,pr)),(root,((d,x),set hs)))"
  have valid: "derivation_record_valid ?z"
    by (simp only: derivation_record_valid_fields fst_conv snd_conv)
      (use parts(3,4,6) in blast)
  have position: "(pu,pr)\<in>environment_positions E" by (rule native_package_root_position[OF parts(3)])
  have read: "derivation_record_presents ?z t"
    apply (simp only: derivation_record_fields fst_conv snd_conv)
    apply (rule conjI[OF position])
    apply (rule exI[of _ e], rule exI[of _ hs])
    using parts(1,2,5) apply simp
    done
  show "\<exists>z. derivation_presents z t"
    by (rule exI[of _ ?z]) (use valid read in \<open>simp add: derivation_presents_def\<close>)
next
  assume "\<exists>z. derivation_presents z t"
  then obtain z where valid: "derivation_record_valid z" and read: "derivation_record_presents z t"
    by (auto simp: derivation_presents_def)
  obtain E p root q H where shape: "z=((E,p),(root,(q,H)))"
    by (rule derivation_record_cases[of z]) (rule that; assumption)
  have actual: "derivation_record_presents ((E,p),(root,(q,H))) t" using read shape by simp
  obtain e hs where fields: "environment_value_presents E e" "distinct hs" "set hs=H"
    "t=derivation_argument e (use_data_term (fst p)) (Payload_Term (snd p)) (definition_site_value root)
      (definition_site_value (fst q)) (snd q) (positioned_call_rows_term hs)"
    using derivation_record_fields[THEN iffD1, OF actual]
    by (elim conjE exE) (rule that; assumption)
  have actual_valid: "derivation_record_valid ((E,p),(root,(q,H)))" using valid shape by simp
  obtain P G where parts: "native_package_at E (fst p) (snd p) P" "native_schema_graph_at E root G"
    "schema_graph_derives (positioned_program P) G root (fst q) (snd q) H"
    using derivation_record_valid_fields[THEN iffD1, OF actual_valid]
    by (elim exE conjE) (rule that; assumption)
  have derived: "schema_graph_derives (positioned_program P) G root (fst q) (snd q) (set hs)"
    using parts(3) by (simp only: fields(3))
  show "(102,t)\<in>positive_meaning derivation_admission_system"
    using derivation_admission_complete[OF fields(1) parts(1,2) fields(2) derived]
    by (simp only: fields(4))
qed

theorem derivation_presentation_class:
  "presentation_class derivation_presents derivation_record_valid
    (\<lambda>t. (102,t)\<in>positive_meaning derivation_admission_system)"
proof -
  have constrained: "presentation_class (\<lambda>z t. derivation_record_valid z \<and> derivation_record_presents z t)
      derivation_record_valid (\<lambda>t. \<exists>z. derivation_record_valid z \<and> derivation_record_presents z t)"
    by (rule presentation_class_subdomain[OF derivation_record_class derivation_record_bound])
  have reading: "derivation_presents=(\<lambda>z t. derivation_record_valid z \<and> derivation_record_presents z t)"
    by (intro ext) (simp only: derivation_presents_def)
  show ?thesis using constrained by (simp only: derivation_class_admission reading)
qed

interpretation derivations: presentation_class derivation_presents derivation_record_valid
  "\<lambda>t. (102,t)\<in>positive_meaning derivation_admission_system"
  by (rule derivation_presentation_class)

lemma derivation_record_reading_fields:
  "derivation_record_reading ((E,p),(root,(q,H))) (P,(G,J)) \<longleftrightarrow>
    native_package_at E (fst p) (snd p) P \<and> native_schema_graph_at E root G \<and>
    schema_graph_reading (positioned_program P) G root (fst q) (snd q) J \<and>
    H=schema_graph_assumptions G J"
  by (simp only: derivation_record_reading_def case_prod_conv)

lemma derivation_reading_valid:
  assumes "derivation_record_reading z b"
  shows "derivation_record_valid z"
  using assms by (auto simp: derivation_record_reading_def derivation_record_valid_def
    schema_graph_derives_def split: prod.splits; blast)

lemma derivation_reading_total:
  assumes "derivation_record_valid z"
  shows "\<exists>b. derivation_record_reading z b"
  using assms by (auto simp: derivation_record_reading_def derivation_record_valid_def
    schema_graph_derives_def split: prod.splits; blast)

lemma derivation_reading_unique:
  assumes first: "derivation_record_reading z b" and second: "derivation_record_reading z c"
  shows "b=c"
proof -
  obtain E p root q H where shape: "z=((E,p),(root,(q,H)))"
    by (rule derivation_record_cases[of z]) (rule that; assumption)
  obtain P G J where b: "b=(P,(G,J))"
    by (rule that[of "fst b" "fst (snd b)" "snd (snd b)"]) simp
  obtain Q F L where c: "c=(Q,(F,L))"
    by (rule that[of "fst c" "fst (snd c)" "snd (snd c)"]) simp
  have left: "native_package_at E (fst p) (snd p) P" "native_schema_graph_at E root G"
    "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    using first by (auto simp: shape b derivation_record_reading_fields)
  have right: "native_package_at E (fst p) (snd p) Q" "native_schema_graph_at E root F"
    "schema_graph_reading (positioned_program Q) F root (fst q) (snd q) L"
    using second by (auto simp: shape c derivation_record_reading_fields)
  have programs: "P=Q" by (rule native_package_unique[OF left(1) right(1)])
  have graphs: "G=F" by (rule native_schema_graph_unique[OF left(2) right(2)])
  have other: "schema_graph_reading (positioned_program P) G root (fst q) (snd q) L"
    using right(3) programs graphs by simp
  have claims: "J=L" by (rule schema_graph_reading_unique[OF left(3) other])
  show ?thesis using programs graphs claims b c by simp
qed

abbreviation derivation_with_reading_presents ::
  "(derivation_record\<times>derivation_details) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "derivation_with_reading_presents z t \<equiv>
    derivation_presents (fst z) t \<and> derivation_record_reading (fst z) (snd z)"

theorem derivation_reading_presentation_class:
  "presentation_class derivation_with_reading_presents
    (\<lambda>z. derivation_record_reading (fst z) (snd z))
    (\<lambda>t. (102,t)\<in>positive_meaning derivation_admission_system)"
proof -
  have result: "presentation_class derivation_with_reading_presents
      (\<lambda>z. derivation_record_valid (fst z) \<and> derivation_record_reading (fst z) (snd z))
      (\<lambda>t. \<exists>z b. derivation_presents z t \<and> derivation_record_reading z b)"
    by (rule presentation_class_determined[OF derivation_presentation_class derivation_reading_unique])
  have domain: "(\<lambda>z. derivation_record_valid (fst z) \<and> derivation_record_reading (fst z) (snd z)) =
      (\<lambda>z. derivation_record_reading (fst z) (snd z))"
    by (rule ext) (use derivation_reading_valid in blast)
  have admission: "(\<lambda>t. \<exists>z b. derivation_presents z t \<and> derivation_record_reading z b) =
      (\<lambda>t. (102,t)\<in>positive_meaning derivation_admission_system)"
    by (rule ext) (simp only: derivation_class_admission;
      use derivations.subject_boundary derivation_reading_total in blast)
  show ?thesis using result by (simp only: domain admission)
qed

interpretation derivation_readings: presentation_class derivation_with_reading_presents
  "\<lambda>z. derivation_record_reading (fst z) (snd z)"
  "\<lambda>t. (102,t)\<in>positive_meaning derivation_admission_system"
  by (rule derivation_reading_presentation_class)

theorem derivation_presented_reading:
  assumes presented: "derivation_with_reading_presents (((E,p),(root,(q,H))),(P,(G,J))) v"
  shows "native_package_at E (fst p) (snd p) P"
    and "native_schema_graph_at E root G"
    and "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    and "H=schema_graph_assumptions G J"
    and "rel_dom J=schema_graph_nodes G"
    and "finite J \<and> single_valued J"
proof -
  have parts: "native_package_at E (fst p) (snd p) P" "native_schema_graph_at E root G"
    "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    "H=schema_graph_assumptions G J"
    using presented by (auto simp: fst_conv snd_conv derivation_record_reading_fields)
  show "native_package_at E (fst p) (snd p) P" by (rule parts(1))
  show "native_schema_graph_at E root G" by (rule parts(2))
  show "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J" by (rule parts(3))
  show "H=schema_graph_assumptions G J" by (rule parts(4))
  show "rel_dom J=schema_graph_nodes G" using parts(3) by (simp add: schema_graph_reading_def)
  show "finite J \<and> single_valued J"
    using schema_graph_reading_finite[OF parts(3)] parts(3) by (simp add: schema_graph_reading_def)
qed

lemma derivation_presents_formed:
  assumes "derivation_presents z t"
  shows "term_formed t"
  using schema_call_formed_target[OF positive_meaning_formed[
    OF derivations.presentation_boundary[OF assms]]] by blast

theorem derivation_presented_conditional_sound:
  assumes presented: "derivation_with_reading_presents (((E,p),(root,(q,H))),(P,(G,J))) v"
    and support: "\<forall>n e x. (n,e,x)\<in>H \<longrightarrow> (e,x)\<in>positive_meaning P"
  shows "q\<in>positive_meaning P"
proof -
  have package: "native_package_at E (fst p) (snd p) P"
    and read: "schema_graph_reading (positioned_program P) G root (fst q) (snd q) J"
    and boundary: "H=schema_graph_assumptions G J"
    using derivation_presented_reading[OF presented] by blast+
  have formed: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have truth: "(fst q,snd q)\<in>positive_meaning (positioned_program P)"
  proof (rule schema_graph_reading_sound[OF read])
    fix n a assume member: "(n,a)\<in>schema_graph_assumptions G J"
    have row: "(n,fst a,snd a)\<in>H" using member boundary by simp
    have actual: "(fst a,snd a)\<in>positive_meaning P" using support row by blast
    show "a\<in>positive_meaning (positioned_program P)"
      using actual by (simp only: positioned_program_meaning[OF formed] prod.collapse)
  qed
  show ?thesis using truth by (simp only: positioned_program_meaning[OF formed] prod.collapse)
qed

corollary derivation_presented_closed_sound:
  assumes "derivation_with_reading_presents (((E,p),(root,(q,{}))),(P,(G,J))) v"
  shows "q\<in>positive_meaning P"
  by (rule derivation_presented_conditional_sound[OF assms]) simp

theorem native_derivation_presentation_total:
  assumes package: "native_package_at E pu pr P" and graph: "native_schema_graph_at E root G"
    and derived: "schema_graph_derives (positioned_program P) G root d t H"
  shows "\<exists>v J. derivation_with_reading_presents
      (((E,(pu,pr)),(root,((d,t),H))),(P,(G,J))) v \<and>
    (102,v)\<in>positive_meaning derivation_admission_system \<and> term_formed v"
proof -
  obtain J where read: "schema_graph_reading (positioned_program P) G root d t J"
    and boundary: "H=schema_graph_assumptions G J"
    using derived by (auto simp: schema_graph_derives_def)
  have subject: "derivation_record_reading ((E,(pu,pr)),(root,((d,t),H))) (P,(G,J))"
    using package graph read boundary by (simp only: derivation_record_reading_fields fst_conv snd_conv)
  obtain v where presented: "derivation_with_reading_presents
      (((E,(pu,pr)),(root,((d,t),H))),(P,(G,J))) v"
    using derivation_readings.total[of "(((E,(pu,pr)),(root,((d,t),H))),(P,(G,J)))"] subject
    by (simp only: fst_conv snd_conv; blast)
  have admitted: "(102,v)\<in>positive_meaning derivation_admission_system"
    by (rule derivation_readings.presentation_boundary[OF presented])
  have formed: "term_formed v" using schema_call_formed_target[OF positive_meaning_formed[OF admitted]] by blast
  show ?thesis by (rule exI[of _ v], rule exI[of _ J]) (use presented admitted formed in simp)
qed

text \<open>
  The complete source, its program site, the proof root, the supplied root call,
  and every identified assertion row form the record. Products and complete
  collection classes build its presentations. Native derivation admission
  restricts that record to the independently defined derivation relation.

  The actual program, graph, and complete claim assignment are then recovered
  components. Every claim uses the same native source and every actual premise
  link. They add no stored field or independently supplied claim cache.
  Conditional soundness requires the exact assertions to hold; an empty
  assertion boundary supplies the closed case. Every valid native derivation
  has an admitted presentation over this complete domain.
\<close>

end
