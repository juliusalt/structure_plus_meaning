theory Factor_Executable_Environment_Values
  imports Factor_Executable_Artifact_Values Factor_Environment_Values "HOL-Library.Option_ord"
begin

section \<open>Every use carries its complete artifact rows\<close>

definition environment_artifact_rows_object ::
  "(local_address option\<times>artifact_value_rows) \<Rightarrow> local_address option\<times>exact_artifact" where
  "environment_artifact_rows_object q=(fst q,artifact_rows_object (snd q))"

definition environment_artifact_rows_term ::
  "(local_address option\<times>artifact_value_rows) \<Rightarrow> factor_term" where
  "environment_artifact_rows_term q=Pair_Term (use_data_term (fst q)) (artifact_rows_term (snd q))"

definition finite_environment_artifact_rows ::
  "local_address option finite_artifact_environment \<Rightarrow>
    (local_address option\<times>artifact_value_rows) list" where
  "finite_environment_artifact_rows C=sorted_list_of_fset
    (fimage (\<lambda>(u,R). (u,finite_artifact_rows R)) (finite_environment_artifacts C))"

lemma environment_artifact_rows_finite [simp]:
  "environment_artifact_rows_object (u,finite_artifact_rows R)=(u,decode_finite_object R)"
  by (simp add: environment_artifact_rows_object_def)

lemma environment_artifact_rows_recovers:
  assumes "environment_artifact_entry_presents z (environment_artifact_rows_term q)"
  shows "z=environment_artifact_rows_object q"
proof -
  have coordinates: "use_data_term (fst z)=use_data_term (fst q)"
    and artifact: "artifact_value_presents (snd z) (artifact_rows_term (snd q))"
    using assms by (auto simp: environment_artifact_entry_presents_def environment_artifact_rows_term_def)
  have use: "fst z=fst q" by (rule injD[OF use_data_term_injective coordinates])
  have material: "snd z=artifact_rows_object (snd q)" by (rule artifact_rows_term_recovers[OF artifact])
  show ?thesis using use material by (simp add: environment_artifact_rows_object_def prod_eq_iff)
qed

lemma finite_environment_artifact_rows_sources:
  "set (map environment_artifact_rows_object (finite_environment_artifact_rows C))=
    environment_artifacts (decode_finite_environment C)"
  by (auto simp: finite_environment_artifact_rows_def fimage.rep_eq map_relation_values_def
    image_image split_def)

lemma finite_environment_artifact_rows_distinct:
  "distinct (map environment_artifact_rows_object (finite_environment_artifact_rows C))"
proof -
  have injective: "inj_on environment_artifact_rows_object (set (finite_environment_artifact_rows C))"
    by (auto simp: inj_on_def finite_environment_artifact_rows_def fimage.rep_eq
      environment_artifact_rows_object_def split_def)
  show ?thesis using injective
    by (simp add: distinct_map finite_environment_artifact_rows_def)
qed

lemma finite_environment_artifact_rows_present:
  assumes formed: "finite_environment_formed C"
  shows "data_collection_presents environment_artifact_entry_presents
    (environment_artifacts (decode_finite_environment C))
    (data_list_term (map environment_artifact_rows_term (finite_environment_artifact_rows C)))"
proof -
  let ?xs="finite_environment_artifact_rows C"
  let ?ys="map environment_artifact_rows_object ?xs"
  let ?encode="\<lambda>z. Pair_Term (use_data_term (fst z))
    (artifact_rows_term (finite_artifact_rows (finite_object_of (snd z))))"
  have decoded: "?encode (environment_artifact_rows_object q)=environment_artifact_rows_term q"
    if "q\<in>set ?xs" for q
    using that by (auto simp: finite_environment_artifact_rows_def fimage.rep_eq
      environment_artifact_rows_term_def split_def)
  have each: "environment_artifact_entry_presents (environment_artifact_rows_object q)
    (environment_artifact_rows_term q)" if "q\<in>set ?xs" for q
    using that formed
    by (auto simp: finite_environment_artifact_rows_def fimage.rep_eq
      finite_environment_formed_components environment_artifact_rows_term_def
      environment_artifact_entry_presents_def finite_artifact_rows_value_exact split_def
      split: prod.splits)
  have material: "data_collection_presents environment_artifact_entry_presents
    (environment_artifacts (decode_finite_environment C)) (data_list_term (map ?encode ?ys))"
  proof (rule data_collection_presents_map[OF finite_environment_artifact_rows_distinct
      finite_environment_artifact_rows_sources])
    fix z assume member: "z\<in>environment_artifacts (decode_finite_environment C)"
    have "z\<in>set ?ys"
      using member by (simp only: finite_environment_artifact_rows_sources)
    then have "z\<in>image environment_artifact_rows_object (set ?xs)"
      by (simp only: set_map)
    then obtain q where row: "q\<in>set ?xs" "z=environment_artifact_rows_object q"
      by blast
    show "environment_artifact_entry_presents z (?encode z)"
      using each[OF row(1)] decoded[OF row(1)] row(2) by simp
  qed
  have same: "map ?encode ?ys=map environment_artifact_rows_term ?xs"
    by (simp only: map_map; rule map_cong) (use decoded in auto)
  show ?thesis using material by (simp only: same)
qed

section \<open>The complete value preserves the environment and its formation gate\<close>

definition finite_environment_term ::
  "local_address option finite_artifact_environment \<Rightarrow> factor_term" where
  "finite_environment_term C=Pair_Term
    (data_list_term (map environment_artifact_rows_term (finite_environment_artifact_rows C)))
    (data_list_term (map binding_data (sorted_list_of_fset (finite_environment_bindings C))))"

lemma finite_environment_term_self_contained [simp]:
  "self_contained_term (finite_environment_term C)"
  by (simp add: finite_environment_term_def data_list_term_self_contained environment_artifact_rows_term_def)

definition finite_environment_value ::
  "local_address option finite_artifact_environment \<Rightarrow> finite_factor_term" where
  "finite_environment_value C=the (finite_self_contained_term (finite_environment_term C))"

lemma decode_finite_environment_value [simp]:
  "decode_finite_term (finite_environment_value C)=finite_environment_term C"
  unfolding finite_environment_value_def
  by (rule decode_finite_self_contained_term) simp

theorem finite_environment_value_exact:
  "environment_value_presents E (decode_finite_term (finite_environment_value C)) \<longleftrightarrow>
    finite_environment_formed C \<and> E=decode_finite_environment C"
proof
  assume present: "environment_value_presents E (decode_finite_term (finite_environment_value C))"
  have formed: "environment_formed E"
    and artifacts: "data_collection_presents environment_artifact_entry_presents
      (environment_artifacts E)
      (data_list_term (map environment_artifact_rows_term (finite_environment_artifact_rows C)))"
    and bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E)
      (data_list_term (map binding_data (sorted_list_of_fset (finite_environment_bindings C))))"
    using present by (auto simp: environment_value_presents_def finite_environment_term_def)
  have art: "environment_artifacts E=environment_artifacts (decode_finite_environment C)"
    using data_collection_presents_recover_map[OF artifacts environment_artifact_rows_recovers]
      finite_environment_artifact_rows_sources[of C] by simp
  have bind: "environment_bindings E=environment_bindings (decode_finite_environment C)"
  proof -
    have "environment_bindings E=set (map id (sorted_list_of_fset (finite_environment_bindings C)))"
      by (rule data_collection_presents_recover_map[OF bindings]) (auto dest: injD[OF binding_data_injective])
    then show ?thesis by simp
  qed
  have same: "E=decode_finite_environment C" using art bind
    by (cases E; cases "decode_finite_environment C") simp
  show "finite_environment_formed C \<and> E=decode_finite_environment C"
    using formed same by (simp add: finite_environment_formed_correct)
next
  assume actual: "finite_environment_formed C \<and> E=decode_finite_environment C"
  have formed: "environment_formed E" using actual by (simp add: finite_environment_formed_correct)
  have artifacts: "data_collection_presents environment_artifact_entry_presents
    (environment_artifacts E)
    (data_list_term (map environment_artifact_rows_term (finite_environment_artifact_rows C)))"
    using finite_environment_artifact_rows_present actual by simp
  have bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E)
    (data_list_term (map binding_data (sorted_list_of_fset (finite_environment_bindings C))))"
    by (rule data_collection_presents_map) (use actual in auto)
  show "environment_value_presents E (decode_finite_term (finite_environment_value C))"
    using formed artifacts bindings
    by (auto simp: environment_value_presents_def finite_environment_term_def)
qed

lemma finite_environment_value_formed:
  assumes "finite_environment_formed C"
  shows "finite_term_formed (finite_environment_value C)"
  using finite_environment_value_exact environment_value_presents_formed assms
  by (auto simp: finite_term_formed_correct)

definition finite_presented_environment_formed ::
  "local_address option finite_artifact_environment \<Rightarrow> bool" where
  "finite_presented_environment_formed C=finite_environment_formed C"

lemma finite_presented_environment_formed_correct:
  "finite_presented_environment_formed C \<longleftrightarrow> environment_formed (decode_finite_environment C)"
  by (simp add: finite_presented_environment_formed_def finite_environment_formed_correct)

export_code finite_data_projection finite_artifact_value finite_environment_value
  finite_exact_formed finite_presented_environment_formed finite_term_formed
  nat_of_integer integer_of_nat finite_empty_artifact
  finite_enumerated_artifact finite_enumerated_environment
  Finite_Payload Finite_Pair Finite_Target Finite_Whole
  in SML module_name Finite_Presented_Data file_prefix finite_presented_data

text \<open>
  The implementation consumes complete finite tables. Equal artifacts at
  different uses stay distinct placements; every binding endpoint remains
  explicit. The mathematical inverse in the proof identifies existing finite
  rows and is not part of the executable construction.

  Use words retain their existing natural-number encoding. They do not gain
  the byte restriction of artifact addresses. The exact theorem rejects every
  malformed source environment even when its data term has the required outer
  shape. It does not itself establish a native package or inference reading.
\<close>

end
