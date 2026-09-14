theory RRA_Finite_Generation_Construction
  imports RRA_Finite_Generation_Encoding RRA_Finite_Generation_Checking
    RRA_Finite_Anchor_Selection RRA_Finite_Environment_Preservation
begin

definition finite_generation_record_ready where
  "finite_generation_record_ready E l p c rows=(finite_environment_formed E \<and>
    finite_target_formed l \<and> finite_target_formed p \<and> finite_target_formed c \<and>
    distinct (map snd rows) \<and> list_all (\<lambda>(d,G).
      finite_check_generation G E (fst d) (snd d)) rows)"

definition finite_generation_record_core where
  "finite_generation_record_core l p c rows=Generation l (fset_of_list (map snd rows)) p c"

definition finite_generation_record_body where
  "finite_generation_record_body E l p c rows anchors=(
    finite_generation_record_environment E l p c (map (\<lambda>(d,R). (R,snd d)) anchors)
      (\<lambda>i. fst (fst (anchors!i))),
    finite_generation_record_use E,finite_generation_record_core l p c rows)"

definition finite_construct_generation_record where
  "finite_construct_generation_record E l p c rows=(if finite_generation_record_ready E l p c rows then
    map_option (finite_generation_record_body E l p c rows)
      (keyed_option_map (finite_anchor_artifact E) (map fst rows)) else None)"

lemma finite_generation_record_anchors_available:
  assumes ready: "finite_generation_record_ready E l p c rows"
  shows "keyed_option_map (finite_anchor_artifact E) (map fst rows)\<noteq>None"
proof -
  have formed: "finite_environment_formed E" using ready by (simp only: finite_generation_record_ready_def; blast)
  have available: "finite_anchor_artifact E d\<noteq>None" if requested: "d\<in>set (map fst rows)" for d
  proof -
    have choice: "\<exists>q\<in>set rows. d=fst q" using requested by (simp only: set_map image_iff)
    obtain q where in_rows: "q\<in>set rows" and key: "d=fst q"
      using choice by blast
    obtain e G where pair: "q=(e,G)" by (cases q) auto
    have member: "(d,G)\<in>set rows" using in_rows key pair by simp
    have checked: "finite_check_generation G E (fst d) (snd d)"
      using ready member by (auto simp: finite_generation_record_ready_def list_all_iff)
    have position: "d |\<in>| finite_environment_positions E"
      using finite_check_generation_position[OF checked] by simp
    have selected: "\<exists>R. finite_anchor_artifact E d=Some R"
      using position by (simp only: finite_anchor_artifact_domain[OF formed])
    show ?thesis using selected by (cases "finite_anchor_artifact E d") auto
  qed
  show ?thesis using available by (simp only: keyed_option_map_domain; blast)
qed

theorem finite_construct_generation_record_domain:
  "(\<exists>F u G. finite_construct_generation_record E l p c rows=Some (F,u,G)) \<longleftrightarrow>
    finite_generation_record_ready E l p c rows"
proof
  assume "\<exists>F u G. finite_construct_generation_record E l p c rows=Some (F,u,G)"
  then show "finite_generation_record_ready E l p c rows"
    by (auto simp: finite_construct_generation_record_def split: if_splits)
next
  assume ready: "finite_generation_record_ready E l p c rows"
  have available: "keyed_option_map (finite_anchor_artifact E) (map fst rows)\<noteq>None"
    by (rule finite_generation_record_anchors_available[OF ready])
  obtain anchors where selected: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
    using available by (cases "keyed_option_map (finite_anchor_artifact E) (map fst rows)") auto
  obtain F z where first: "finite_generation_record_body E l p c rows anchors=(F,z)"
    by (cases "finite_generation_record_body E l p c rows anchors") auto
  obtain u G where second: "z=(u,G)" by (cases z) auto
  have constructed: "finite_construct_generation_record E l p c rows=Some (F,u,G)"
    by (simp only: finite_construct_generation_record_def ready if_True selected option.simps first second)
  show "\<exists>F u G. finite_construct_generation_record E l p c rows=Some (F,u,G)"
    using constructed by blast
qed

locale finite_generation_record_construction =
  fixes E :: "local_address option finite_artifact_environment"
    and l p c :: finite_exact_target
    and rows :: "(local_address option definition_site\<times>finite_generation) list"
    and anchors :: "(local_address option definition_site\<times>finite_exact_artifact) list"
  assumes ready: "finite_generation_record_ready E l p c rows"
    and queried: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
begin

abbreviation as where "as\<equiv>map (\<lambda>(d,R). (R,snd d)) anchors"
abbreviation v where "v\<equiv>\<lambda>i. fst (fst (anchors!i))"
abbreviation F where "F\<equiv>finite_generation_record_environment E l p c as v"
abbreviation u where "u\<equiv>finite_generation_record_use E"
abbreviation G where "G\<equiv>finite_generation_record_core l p c rows"

lemma lengths: "length anchors=length rows"
  using keyed_option_map_result(1)[OF queried] by (metis length_map)

lemma at:
  assumes "i<length anchors"
  shows "fst (anchors!i)=fst (rows!i) \<and>
    finite_anchor_artifact E (fst (anchors!i))=Some (snd (anchors!i))"
  using keyed_option_map_at[OF queried, of i] assms lengths by auto

lemma selected_anchors:
  "\<forall>i\<in>{..<length (map (map_prod decode_finite_object id) as)}.
    artifact_at (decode_finite_environment E) (v i)
      (fst ((map (map_prod decode_finite_object id) as)!i)) \<and>
    anchor_formed (fst ((map (map_prod decode_finite_object id) as)!i),
      snd ((map (map_prod decode_finite_object id) as)!i))"
proof (intro ballI)
  fix i assume index: "i\<in>{..<length (map (map_prod decode_finite_object id) as)}"
  have bound: "i<length anchors" using index by simp
  have formed: "finite_environment_formed E" using ready by (simp only: finite_generation_record_ready_def; blast)
  have selected: "finite_anchor_artifact E (fst (anchors!i))=Some (snd (anchors!i))"
    using at[OF bound] by blast
  show "artifact_at (decode_finite_environment E) (v i)
      (fst ((map (map_prod decode_finite_object id) as)!i)) \<and>
    anchor_formed (fst ((map (map_prod decode_finite_object id) as)!i),
      snd ((map (map_prod decode_finite_object id) as)!i))"
    using finite_anchor_artifact_properties[OF formed selected] bound
    by (simp add: map_map comp_def map_prod_def split_def)
qed

sublocale native: generation_record_construction "decode_finite_environment E"
    "decode_finite_target l" "decode_finite_target p" "decode_finite_target c"
    "map (map_prod decode_finite_object id) as" v
  by (rule generation_record_construction.intro[OF _ _ _ _ selected_anchors])
    (use ready in \<open>auto simp: finite_generation_record_ready_def
      finite_environment_formed_correct finite_target_formed_correct\<close>)

lemma environment: "decode_finite_environment F=native.installed"
  by (rule finite_generation_record_environment_exact)

lemma record_use: "u=native.record_use"
  by (rule finite_generation_record_use_exact)

lemma recovered:
  "generation_at (decode_finite_environment F) u [] (decode_finite_generation G)"
proof -
  let ?g="\<lambda>i. decode_finite_generation (snd (rows!i))"
  have different: "distinct (map snd rows)" using ready by (simp only: finite_generation_record_ready_def; blast)
  have decoded: "distinct (map decode_finite_generation (map snd rows))"
    using different by (auto simp: distinct_map inj_on_def)
  have indexed: "inj_on (\<lambda>i. (map decode_finite_generation (map snd rows))!i) {..<length rows}"
    by (rule inj_on_nth[OF decoded]) simp
  have injective: "inj_on ?g {..<length (map (map_prod decode_finite_object id) as)}"
    using indexed by (auto simp: inj_on_def lengths)
  have predecessors: "\<forall>i<length (map (map_prod decode_finite_object id) as).
    generation_at (decode_finite_environment E) (v i)
      (snd ((map (map_prod decode_finite_object id) as)!i)) (?g i)"
  proof (intro allI impI)
    fix i assume index: "i<length (map (map_prod decode_finite_object id) as)"
    have bound: "i<length anchors" and original: "i<length rows" using index lengths by simp_all
    have checked: "finite_check_generation (snd (rows!i)) E (fst (fst (rows!i))) (snd (fst (rows!i)))"
      using ready nth_mem[OF original]
      by (cases "rows!i") (auto simp: finite_generation_record_ready_def list_all_iff)
    show "generation_at (decode_finite_environment E) (v i)
      (snd ((map (map_prod decode_finite_object id) as)!i)) (?g i)"
      using checked at[OF bound] bound original
      by (simp add: finite_check_generation_exact map_map comp_def map_prod_def split_def)
  qed
  have image: "?g ` {..<length (map (map_prod decode_finite_object id) as)}=
    fset (fimage decode_finite_generation (fset_of_list (map snd rows)))"
    by (auto simp: lengths fimage.rep_eq fset_of_list.rep_eq set_conv_nth)
  show ?thesis using native.recovers[OF injective predecessors]
    by (simp only: environment record_use image fset_inverse finite_generation_record_core_def
      decode_finite_generation_node)
qed

theorem properties:
  "finite_environment_formed F"
  "environment_included (decode_finite_environment E) (decode_finite_environment F)"
  "finite_environment_agrees_on E F (finite_environment_uses E)"
  "finite_check_generation G F u []"
  "u\<notin>fset (finite_environment_uses E)"
proof -
  show "finite_environment_formed F" by (simp only: finite_environment_formed_correct environment; rule native.properties(1))
  show "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: environment; rule native.properties(2))
  show "finite_environment_agrees_on E F (finite_environment_uses E)"
    using native.old_artifacts native.old_bindings
    by (simp only: finite_environment_agrees_on_correct finite_environment_uses_correct environment; blast)
  show "finite_check_generation G F u []" using recovered by (simp only: finite_check_generation_exact)
  show "u\<notin>fset (finite_environment_uses E)"
    by (simp only: finite_environment_uses_correct record_use;
      rule generation_record_use_fresh[OF native.ef])
qed

end

theorem finite_construct_generation_record_correct:
  assumes result: "finite_construct_generation_record E l p c rows=Some (F,u,G)"
  shows "finite_generation_record_ready E l p c rows"
    "G=finite_generation_record_core l p c rows"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "finite_check_generation G F u []"
    "u\<notin>fset (finite_environment_uses E)"
proof -
  have ready: "finite_generation_record_ready E l p c rows"
    using result finite_construct_generation_record_domain[of E l p c rows] by blast
  obtain anchors where queried: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
    and body: "finite_generation_record_body E l p c rows anchors=(F,u,G)"
    using result ready by (auto simp: finite_construct_generation_record_def split: option.splits)
  interpret construction: finite_generation_record_construction E l p c rows anchors
    by (rule finite_generation_record_construction.intro[OF ready queried])
  have result_fields: "F=construction.F" "u=construction.u" "G=construction.G"
    using body by (simp_all add: finite_generation_record_body_def)
  show "finite_generation_record_ready E l p c rows" by (rule ready)
  show "G=finite_generation_record_core l p c rows" by (rule result_fields(3))
  show "finite_environment_formed F" by (simp only: result_fields; rule construction.properties(1))
  show "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: result_fields; rule construction.properties(2))
  show "finite_environment_agrees_on E F (finite_environment_uses E)"
    by (simp only: result_fields; rule construction.properties(3))
  show "finite_check_generation G F u []" by (simp only: result_fields; rule construction.properties(4))
  show "u\<notin>fset (finite_environment_uses E)" by (simp only: result_fields; rule construction.properties(5))
qed

export_code finite_construct_generation_record checking SML

text \<open>
  Every original predecessor is checked at its actual cited site before its
  anchor is selected. The same guard applies to an empty predecessor list.
  The result preserves every original artifact and outgoing binding and
  recovers exactly the requested generation core. Cause truth and historical
  permission remain separate from this record construction.
\<close>

end
