theory RRA_Bounded_Generation_Construction
  imports RRA_Finite_Embedded_Generation_Construction RRA_Finite_Graft_Bounds
begin

lemma bounded_generation_use_fresh:
  "finite_environment_head_bound n E \<Longrightarrow> Some [n]\<notin>fset (finite_environment_uses E)"
  by (auto simp: finite_environment_head_bound_uses)

lemma bounded_generation_predecessor_head:
  "finite_environment_head_bound n E \<Longrightarrow>
    finite_environment_head_bound (Suc n) (finite_fresh_generation_predecessor_environment E (Some [n]) l p c as v)"
  by (auto simp: finite_environment_head_bound_def finite_fresh_generation_predecessor_environment_def
    finite_add_source_bindings_def finite_add_artifact_use_def Ball_def)

lemma bounded_generation_embedding:
  assumes bound: "finite_environment_head_bound n E"
  shows "boundary_use_embedding (environment_uses (decode_finite_environment
    (finite_fresh_generation_predecessor_environment E (Some [n]) l p c as v)))
      (Some [n]) (prefix_use_map [Suc n] (Some [n]))"
proof -
  let ?F="finite_fresh_generation_predecessor_environment E (Some [n]) l p c as v"
  let ?L="finite_literal_environment (finite_generation_record_frame l p c as) (finite_generation_record_literals l p c)"
  have head: "finite_environment_head_bound (Suc n) ?F"
    by (rule bounded_generation_predecessor_head[OF bound])
  have shared: "finite_shared_graft_artifact ?F (Some [n]) ?L"
    by (auto simp: finite_shared_graft_artifact_def finite_fresh_generation_predecessor_environment_def
      finite_add_source_bindings_def finite_add_artifact_use_def finite_literal_environment_def Bex_def)
  show ?thesis by (rule bounded_graft_prefix_embedding[OF head shared])
qed

definition finite_bounded_generation_environment where
  "finite_bounded_generation_environment n E l p c as v=
    finite_embedded_generation_record_environment (prefix_use_map [Suc n] (Some [n])) E (Some [n]) l p c as v"

lemma finite_bounded_generation_head:
  assumes bound: "finite_environment_head_bound n E"
  shows "finite_environment_head_bound (Suc (Suc n)) (finite_bounded_generation_environment n E l p c as v)"
  unfolding finite_bounded_generation_environment_def finite_embedded_generation_record_environment_def
  by (rule finite_graft_head_bound[OF bounded_generation_predecessor_head[OF bound]]) simp

locale finite_bounded_generation_construction = finite_generation_record_construction E l p c rows anchors
  for E :: "local_address option finite_artifact_environment"
    and l p c :: finite_exact_target
    and rows :: "(local_address option definition_site\<times>finite_generation) list"
    and anchors :: "(local_address option definition_site\<times>finite_exact_artifact) list" +
  fixes n :: nat
  assumes bound: "finite_environment_head_bound n E"
begin

sublocale bounded: finite_embedded_generation_construction E l p c rows anchors
    "Some [n]" "prefix_use_map [Suc n] (Some [n])"
  by (unfold_locales)
    (rule bounded_generation_use_fresh[OF bound], rule bounded_generation_embedding[OF bound])

lemma result_environment:
  "finite_bounded_generation_environment n E l p c as v=bounded.result_environment"
  by (simp only: finite_bounded_generation_environment_def)

end

definition finite_bounded_generation_body where
  "finite_bounded_generation_body n E l p c rows anchors=(
    (Suc (Suc n),finite_bounded_generation_environment n E l p c
      (map (\<lambda>(d,R). (R,snd d)) anchors) (\<lambda>i. fst (fst (anchors!i)))),
    Some [n],finite_generation_record_core l p c rows)"

definition finite_construct_bounded_generation where
  "finite_construct_bounded_generation q l p c rows=(let n=fst q;E=snd q in
    if finite_environment_head_bound n E \<and> finite_generation_record_ready E l p c rows then
      map_option (finite_bounded_generation_body n E l p c rows)
        (keyed_option_map (finite_anchor_artifact E) (map fst rows)) else None)"

theorem finite_construct_bounded_generation_domain:
  "finite_construct_bounded_generation (n,E) l p c rows\<noteq>None \<longleftrightarrow>
    finite_environment_head_bound n E \<and> finite_generation_record_ready E l p c rows"
  using finite_generation_record_anchors_available[of E l p c rows]
  by (auto simp: finite_construct_bounded_generation_def finite_bounded_generation_body_def split: option.splits)

theorem finite_construct_bounded_generation_correct:
  assumes result: "finite_construct_bounded_generation (n,E) l p c rows=Some ((n',F),u,G)"
  shows "n'=Suc (Suc n)" "u=Some [n]" "G=finite_generation_record_core l p c rows"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "finite_check_generation G F u []"
    "finite_generation_predecessor_references F u [] l p c=fset_of_list (map fst rows)"
    "finite_environment_head_bound n' F"
proof -
  have ready: "finite_generation_record_ready E l p c rows" and bound: "finite_environment_head_bound n E"
    using result finite_construct_bounded_generation_domain[of n E l p c rows] by auto
  obtain anchors where queried: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
    and body: "finite_bounded_generation_body n E l p c rows anchors=((n',F),u,G)"
    using result by (auto simp: finite_construct_bounded_generation_def split: option.splits if_splits)
  interpret construction: finite_bounded_generation_construction E l p c rows anchors n
    by (unfold_locales) (rule ready, rule queried, rule bound)
  have head_eq: "Suc (Suc n)=n'"
    using arg_cong[OF body, where f="\<lambda>r. fst (fst r)"]
    by (simp add: finite_bounded_generation_body_def)
  have environment_eq: "construction.bounded.result_environment=F"
    using arg_cong[OF body, where f="\<lambda>r. snd (fst r)"]
    by (simp add: finite_bounded_generation_body_def construction.result_environment)
  have use_eq: "Some [n]=u"
    using arg_cong[OF body, where f="\<lambda>r. fst (snd r)"]
    by (simp add: finite_bounded_generation_body_def)
  have core_eq: "construction.G=G"
    using arg_cong[OF body, where f="\<lambda>r. snd (snd r)"]
    by (simp add: finite_bounded_generation_body_def)
  have result_fields: "n'=Suc (Suc n)" "u=Some [n]" "G=construction.G" "F=construction.bounded.result_environment"
    using head_eq environment_eq use_eq core_eq by blast+
  show "n'=Suc (Suc n)" "u=Some [n]" "G=finite_generation_record_core l p c rows" by (rule result_fields)+
  show "finite_environment_formed F"
    by (simp only: result_fields; rule construction.bounded.properties(1))
  show "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: result_fields; rule construction.bounded.properties(2))
  show "finite_environment_agrees_on E F (finite_environment_uses E)"
    by (simp only: result_fields; rule construction.bounded.properties(3))
  show "finite_check_generation G F u []"
    by (simp only: result_fields; rule construction.bounded.properties(4))
  show "finite_generation_predecessor_references F u [] l p c=fset_of_list (map fst rows)"
    by (simp only: result_fields; rule construction.bounded.properties(5))
  show "finite_environment_head_bound n' F"
    by (simp only: result_fields construction.result_environment[symmetric]; rule finite_bounded_generation_head[OF bound])
qed

text \<open>
  The explicit stored head supplies the record use and its successor supplies
  the literal embedding. Complete original readiness still checks each cited
  predecessor. The result advances the bound twice and preserves the whole
  generation, exact references and original material through the general
  installation contract. This finite reference scans the old environment;
  a local indexed implementation requires its own complete projection proof.
\<close>

end
