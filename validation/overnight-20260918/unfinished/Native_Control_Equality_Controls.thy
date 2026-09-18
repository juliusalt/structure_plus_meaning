theory Native_Control_Equality_Controls
  imports Native_Control_Seed_Subject
begin

declare development_seed_context_def [code] development_seed_roots_def [code]

text \<open>Generate a control for each equality name the actual equation reader
  recognizes. The entity list, root terms and every other table entry are fixed.
  Each output coordinate refers to the complete entity list in the checked prefix.\<close>

value [code] "Parallel.map (\<lambda>name.
  let C=development_seed_context;
      D=(map (\<lambda>s. if s=name then STR ''HOL.eq.moved'' else s) (fst C),snd C);
      malformed=isabelle_malformed_entities D;
      unreached=isabelle_unreached_entities development_seed_roots D
  in (name,C=D,snd C=snd D,isabelle_unknown_positions D,
    isabelle_undeclared_constants development_seed_roots D,
    map (\<lambda>i. (i,isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) (snd C!i),
      isabelle_entity_subjects (fst D) (isabelle_development_constants (snd D)) (snd D!i),
      snd D!i\<in>set malformed,snd D!i\<in>set unreached)) [0..<length (snd C)]))
  isabelle_equality_names"

end
