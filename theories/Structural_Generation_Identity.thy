theory Structural_Generation_Identity
  imports Structural_Artifact_Identity RRA_Finite_Generation_Checking
begin

function (sequential) structural_generation_code :: "finite_generation\<Rightarrow>nat list" where
  "structural_generation_code (Generation l P p c)=structural_words_code [
    structural_target_code l,structural_words_code (sorted_list_of_fset (fimage structural_generation_code P)),
    structural_target_code p,structural_target_code c]"
  by pat_completeness auto

termination
  apply (relation "measure size")
   apply (rule wf_measure)
  apply (simp only: in_measure)
  apply (rule predecessor_size_decreases)
  apply (simp add: predecessor_edges_def)
  done

lemma structural_generation_code_recovers:
  "structural_generation_code G=structural_generation_code H \<Longrightarrow> G=H"
proof (induction G arbitrary: H)
  case (Generation l P p c)
  obtain l' Q p' c' where H: "H=Generation l' Q p' c'" by (cases H) auto
  have fields: "l=l'" "p=p'" "c=c'"
    and codes: "sorted_list_of_fset (fimage structural_generation_code P)=
      sorted_list_of_fset (fimage structural_generation_code Q)"
    using Generation.prems by (auto simp: H structural_words_code_injective structural_target_code_injective)
  have sets: "set (sorted_list_of_fset (fimage structural_generation_code P))=
    set (sorted_list_of_fset (fimage structural_generation_code Q))" by (rule arg_cong[OF codes])
  have image: "fimage structural_generation_code P=fimage structural_generation_code Q"
    by (rule fset_inject[THEN iffD1]) (use sets in simp)
  have predecessors: "P=Q"
    by (rule finite_image_equality_from_source[OF image]) (use Generation.IH in blast)
  show ?case by (simp only: H fields predecessors)
qed

theorem structural_generation_code_injective:
  "structural_generation_code G=structural_generation_code H \<longleftrightarrow> G=H"
  using structural_generation_code_recovers by blast

export_code structural_generation_code structural_target_code structural_artifact_code checking SML

text \<open>
  Recursive codes retain every original target and the complete unordered
  predecessor family. Sorting only its complete child codes chooses a value
  presentation. The recovery proof establishes original generation identity
  for every input and supplies no formation, cause truth or history permission.
\<close>

end
