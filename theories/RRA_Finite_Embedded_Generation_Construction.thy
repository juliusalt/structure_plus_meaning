theory RRA_Finite_Embedded_Generation_Construction
  imports RRA_Finite_Embedded_Generation_Records RRA_Selected_Generation_Predecessors
    RRA_Finite_Generation_References
begin

locale finite_embedded_generation_construction = finite_generation_record_construction E l p c rows anchors
  for E :: "local_address option finite_artifact_environment"
    and l p c :: finite_exact_target
    and rows :: "(local_address option definition_site\<times>finite_generation) list"
    and anchors :: "(local_address option definition_site\<times>finite_exact_artifact) list" +
  fixes chosen_use :: "local_address option" and h :: "local_address option\<Rightarrow>local_address option"
  assumes fresh: "chosen_use\<notin>fset (finite_environment_uses E)"
    and embedding: "boundary_use_embedding
      (environment_uses (decode_finite_environment
        (finite_fresh_generation_predecessor_environment E chosen_use l p c
          (map (\<lambda>(d,R). (R,snd d)) anchors) (\<lambda>i. fst (fst (anchors!i)))))) chosen_use h"
begin

abbreviation result_environment where
  "result_environment\<equiv>finite_embedded_generation_record_environment h E chosen_use l p c as v"

sublocale installed: embedded_generation_record "decode_finite_environment E" chosen_use
    "decode_finite_target l" "decode_finite_target p" "decode_finite_target c" decoded_anchors v h
proof (unfold_locales)
  show "environment_formed (decode_finite_environment E)" by (rule native.ef)
  show "target_formed (decode_finite_target l)" by (rule native.lf)
  show "target_formed (decode_finite_target p)" by (rule native.pf)
  show "target_formed (decode_finite_target c)" by (rule native.cf)
  show "\<forall>i\<in>{..<length decoded_anchors}.
    artifact_at (decode_finite_environment E) (v i) (fst (decoded_anchors!i)) \<and>
      anchor_formed (fst (decoded_anchors!i),snd (decoded_anchors!i))"
    by (rule selected_anchors)
  show "chosen_use\<notin>environment_uses (decode_finite_environment E)"
    using fresh by (simp add: finite_environment_uses_correct)
  show "boundary_use_embedding
    (environment_uses (fresh_generation_predecessor_environment (decode_finite_environment E) chosen_use
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c) decoded_anchors v)) chosen_use h"
    using embedding by (simp only: finite_fresh_generation_predecessor_exact)
qed

lemma result_exact: "decode_finite_environment result_environment=installed.H"
  by (rule finite_embedded_generation_record_exact)

theorem properties:
  "finite_environment_formed result_environment"
  "environment_included (decode_finite_environment E) (decode_finite_environment result_environment)"
  "finite_environment_agrees_on E result_environment (finite_environment_uses E)"
  "finite_check_generation G result_environment chosen_use []"
  "finite_generation_predecessor_references result_environment chosen_use [] l p c=fset_of_list (map fst rows)"
proof -
  show "finite_environment_formed result_environment"
    by (simp only: finite_environment_formed_correct result_exact; rule installed.formed)
  show "environment_included (decode_finite_environment E) (decode_finite_environment result_environment)"
    by (simp only: result_exact; rule installed.included)
  show "finite_environment_agrees_on E result_environment (finite_environment_uses E)"
    using installed.old_artifacts installed.old_bindings
    by (simp only: finite_environment_agrees_on_correct finite_environment_uses_correct result_exact; blast)
  have recovered: "generation_at installed.H chosen_use [] (decode_finite_generation G)"
    using installed.recovery.recovers[OF selected_generation_injective selected_generation_readings]
    by (simp only: selected_generation_values fset_inverse finite_generation_record_core_def decode_finite_generation_node)
  show "finite_check_generation G result_environment chosen_use []"
    using recovered by (simp only: finite_check_generation_exact result_exact)
  show "finite_generation_predecessor_references result_environment chosen_use [] l p c=fset_of_list (map fst rows)"
    by (simp only: fset_inject[symmetric] finite_generation_predecessor_references_correct result_exact
      installed.recovery.predecessor_references selected_generation_sites fset_of_list.rep_eq)
qed

end

text \<open>
  Complete original readiness and selected anchors suffice for every fresh use
  and admitted embedding. The original finite generation core and every cited
  predecessor site are recovered, while all old material is preserved.
  The arbitrary mapping is a stated proof premise, not a native checked guard.
\<close>

end
