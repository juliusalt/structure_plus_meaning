theory Factor_Invariant_Evaluation_Sharing
  imports Finite_Inference_Histories Factor_Finite_Program_Histories
    Factor_Executable_Instances
    Factor_Executable_Systems
    Factor_Finite_Program_Applications
    Finite_Observation_Repairs
    Factor_Schema_Generation
    Listed_Set_Unions
begin

section \<open>Loop-invariant subcomputations are computed once\<close>

lemma ffilter_member_cong:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> P x=Q x"
  shows "ffilter P A=ffilter Q A"
  using assms by (auto simp: fset_eq_iff)

declare finite_inference_witnesses_def[code del]

lemma finite_inference_witnesses_direct_code [code]:
  "finite_inference_witnesses project F X=ffilter (\<lambda>w. case project w of (a,H) \<Rightarrow>
    finite_premise_functional H \<and> fset (fimage snd H)\<subseteq>fset X) F"
  unfolding finite_inference_witnesses_def
  by (rule ffilter_member_cong) (auto simp: finite_inference_enabled_def split: prod.splits)

declare finite_material_satisfied_def[code del]

lemma finite_material_satisfied_shared_code [code]:
  "finite_material_satisfied V M=(let
      S=finite_pattern_instances V (finite_material_source M);
      A=finite_pattern_instances V (finite_material_atoms M);
      E=finite_pattern_instances V (finite_material_edges M);
      B=finite_pattern_instances V (finite_material_counts M);
      F=finite_pattern_instances V (finite_material_functions M)
    in fBex S (\<lambda>s. fBex A (\<lambda>a. fBex E (\<lambda>e. fBex B (\<lambda>b. fBex F (\<lambda>f.
      finite_material_observation s a e b f))))))"
  by (simp only: finite_material_satisfied_def Let_def)

declare finite_system_formed_def[code del]

lemma finite_system_formed_shared_code [code]:
  "finite_system_formed P=(let D=finite_system_definitions P in
    finite_relation_functional (finite_system_interfaces P) \<and>
    fBall (finite_system_interfaces P) (\<lambda>(d,p). finite_pattern_formed p) \<and>
    finite_relation_functional (finite_system_clauses P) \<and>
    fBall (finite_system_clauses P) (\<lambda>((d,c),S).
      d |\<in>| D \<and> finite_schema_formed S \<and> finite_schema_dependencies S |\<subseteq>| D))"
  by (simp only: finite_system_formed_def Let_def)

declare finite_program_head_covered_def[code del]

lemma finite_program_head_covered_shared_code [code]:
  "finite_program_head_covered P D=(let H=fimage fst D in
    fBall (finite_system_clauses P) (\<lambda>((d,c),S). d |\<in>| H \<longrightarrow> finite_schema_head_missing S={||}))"
  by (simp only: finite_program_head_covered_def Let_def)

declare finite_candidate_losses_def[code del]

lemma finite_candidate_losses_shared_code [code]:
  "finite_candidate_losses F table c d=(let P=finite_candidate_profile F table d in
    ffilter (\<lambda>q. q\<notin>fset P) (finite_candidate_profile F table c))"
  by (simp only: finite_candidate_losses_def Let_def)

declare finite_basis_residual_def[code del]

lemma finite_basis_residual_listed_code [code abstract]:
  "fset (finite_basis_residual C F table relation)=listed_image_union (\<lambda>c.
    let P=fset (finite_candidate_profile F table c) in
    Pair c ` Set.filter (\<lambda>d. relation c d\<noteq>(P\<subseteq>fset (finite_candidate_profile F table d))) (fset C)) (fset C)"
  by (auto simp: finite_basis_residual_def listed_image_union_def Let_def ffUnion.rep_eq fimage.rep_eq
    ffilter.rep_eq Set.filter_eq)

declare finite_sound_observation_facets_def[code del]

lemma finite_sound_observation_facets_shared_code [code]:
  "finite_sound_observation_facets C relation U table=ffilter (\<lambda>f.
    fBall C (\<lambda>c. let P=fset (finite_candidate_profile {|f|} table c) in fBall C (\<lambda>d. relation c d \<longrightarrow>
      P\<subseteq>fset (finite_candidate_profile {|f|} table d)))) U"
  by (simp only: finite_sound_observation_facets_def Let_def)

text \<open>
  The residual comparisons and the conflicts and repairs derived from them are sets of candidate
  pairs, each computed once and then only read. United member by member they cost the square of
  their size, which grows with the square of the candidates; listed, each is built in one pass.
\<close>

lemma finite_observation_conflicts_listed_code [code abstract]:
  "fset (finite_observation_conflicts C relation F table)=listed_image_union (\<lambda>c.
    listed_image_union (\<lambda>d. if relation c d then
      (\<lambda>(f,w). (c,d,f,w)) ` fset (finite_candidate_losses F table c d) else {}) (fset C)) (fset C)"
  by (auto simp: finite_observation_conflicts_def listed_image_union_def ffUnion.rep_eq fimage.rep_eq
    split: if_splits)

lemma finite_available_observation_repairs_listed_code [code abstract]:
  "fset (finite_available_observation_repairs C relation U F table)=(let
     A=ffilter (\<lambda>f. f\<notin>fset F) (finite_sound_observation_facets C relation U table) in
     listed_image_union (\<lambda>(c,d). if relation c d then {} else
       (\<lambda>(f,w). (c,d,f,w)) ` fset (finite_candidate_losses A table c d))
       (fset (finite_basis_residual C F table relation)))"
  by (auto simp: finite_available_observation_repairs_def listed_image_union_def Let_def ffUnion.rep_eq
    fimage.rep_eq split: if_splits)

lemma filter_map_single_pass:
  "map g (filter P xs)=concat (map (\<lambda>x. if P x then [g x] else []) xs)"
  by (induction xs) auto

lemma finite_premise_joins_single_match [code]:
  "finite_premise_joins ((s,d,p)#ps) K=concat (map (\<lambda>(V,H).
    concat (map (\<lambda>(e,t). let B=V |\<union>| finite_matching_bindings p t in
      if e=d \<and> finite_pattern_accepts p t \<and> finite_relation_functional B
      then [(B,finsert (s,e,t) H)] else []) K))
    (finite_premise_joins ps K))"
  by (simp only: finite_premise_joins.simps filter_map_single_pass Let_def split_def)

lemmas [code] = finite_premise_joins.simps(1)

text \<open>
  Each equation evaluates a set or binding that does not depend on the element
  under inspection once for the enclosing traversal. A witness is kept exactly
  when its projected rule satisfies the original enabling condition, which is the
  membership test on members of the original rule family. Filter order, repeated
  occurrences, list order and every Boolean result are unchanged.
\<close>

section \<open>The applications of a demand are computed once per evaluation\<close>

text \<open>
  Readiness reads the rule table of the requested applications to check demand closure, and
  the history and the closure then read the same applications again. Computing them once and
  reading both from that one value leaves every result unchanged; on the scope review of a
  native question over sixteen candidates the program proofs fell from 3.1 to 2.0 seconds.
\<close>

declare finite_program_history_def [code del]

lemma finite_program_history_shared_code [code]:
  "finite_program_history P D=(let W=finite_program_applications P D in
    if finite_system_formed P \<and> finite_program_head_covered P D \<and>
      fBall (fimage finite_program_application_rule W) (\<lambda>(q,H). fimage snd H |\<subseteq>| D)
    then finite_inference_labelled_history finite_program_application_rule W {||} else None)"
  by (simp add: finite_program_history_def finite_program_evaluation_ready_def
    finite_program_demand_closed_def finite_program_rule_table_def Let_def)

declare finite_program_evaluation_def [code del]

lemma finite_program_evaluation_shared_code [code]:
  "finite_program_evaluation P D=(let F=finite_program_rule_table P D in
    if finite_system_formed P \<and> finite_program_head_covered P D \<and> fBall F (\<lambda>(q,H). fimage snd H |\<subseteq>| D)
    then Some (let settled=finite_inference_result F {||} in ffilter (\<lambda>q. q\<in>settled) D) else None)"
  by (simp add: finite_program_evaluation_def finite_program_evaluation_ready_def
    finite_program_demand_closed_def Let_def)

end
