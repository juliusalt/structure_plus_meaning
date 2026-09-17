theory Factor_Certified_Cause_Variants
  imports Factor_Certified_Cause_Cases
begin

definition certified_cause_rebuild where
  "certified_cause_rebuild X R C=(case X of (H,pu,pr,au,ar,root,S) \<Rightarrow>
    map_option (\<lambda>(E,gu,G). (E,gu,[],G,H,root,R))
      (finite_construct_generation_record (finite_enumerated_environment [] [])
        (Finite_Whole (finite_payload_syntax [60])) (Finite_Whole R) (Finite_Whole C) []))"

definition reversed_environment_term where
  "reversed_environment_term E=Pair_Term
    (data_list_term (map environment_artifact_rows_term (rev (finite_environment_artifact_rows E))))
    (data_list_term (map binding_data (rev (sorted_list_of_fset (finite_environment_bindings E)))))"

definition reversed_judgment_term where
  "reversed_judgment_term E pu pr au ar=Pair_Term (reversed_environment_term E)
    (Pair_Term (site_data_term pu pr) (site_data_term au ar))"

definition certified_cause_changed_replay where
  "certified_cause_changed_replay H pu=H\<lparr>finite_environment_artifacts :=
    fimage (\<lambda>(v,D). (v,if v=pu then finite_attach_structure D
      \<lparr>finite_carrier={|[255]|},finite_incidence={||}\<rparr> else D))
      (finite_environment_artifacts H)\<rparr>"

definition certified_cause_variant ::
  "nat \<Rightarrow> literal_replay_subject \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation\<times>
      local_address option finite_artifact_environment\<times>finite_exact_artifact) \<Rightarrow>
    certified_cause_subject option" where
  "certified_cause_variant w X built=(case X of (H,pu,pr,au,ar,root,R) \<Rightarrow>
    case built of (E,gu,G,J,C) \<Rightarrow>
      if w=1 then Some (E,gu,[],G,J,root,R)
      else if w=2 then Some (E,gu,[],G,H,(fst root,[255]),R)
      else if w=3 then Some (E,gu,[],G,H,root,finite_payload_syntax [62])
      else if w=4 then (case finite_data_syntax (finite_judgment_term H pu pr au ar) of
        None \<Rightarrow> None | Some D \<Rightarrow> certified_cause_rebuild X R D)
      else if w=5 then certified_cause_rebuild X (finite_payload_syntax [62]) C
      else if w=6 then certified_cause_rebuild X R (finite_syntax_union C finite_empty_artifact)
      else if w=7 then (case finite_data_syntax (reversed_judgment_term J pu pr au ar) of
        None \<Rightarrow> None | Some D \<Rightarrow> certified_cause_rebuild X R D)
      else if w=8 then certified_cause_rebuild X R (finite_payload_syntax [63])
      else if w=9 then Some (E,gu,[],Generation (Finite_Whole (finite_payload_syntax [99]))
        (generation_predecessors G) (generation_payload G) (generation_cause G),H,root,R)
      else if w=10 then Some (E,gu,[255],G,H,root,R)
      else if w=11 then Some (E,gu,[],G,finite_enumerated_environment [] [],root,R)
      else if w=12 then Some (finite_add_artifact_use E (Some [255]) (finite_payload_syntax [256]),gu,[],G,H,root,R)
      else if w=14 then Some (E,gu,[],G,certified_cause_changed_replay H pu,root,R)
      else Some (E,gu,[],G,H,root,R))"

definition certified_cause_family where
  "certified_cause_family seed w=fimage (\<lambda>(c,result). (c,case result of None \<Rightarrow> None
    | Some (X,built) \<Rightarrow> case built of None \<Rightarrow> None
      | Some b \<Rightarrow> certified_cause_variant w X b))
      (certified_cause_seed_family seed (if w=13 then 6 else 0))"

definition certified_cause_covered where
  "certified_cause_covered seed=fBex (certified_cause_family seed 0)
    (\<lambda>(c,X). case X of None \<Rightarrow> False | Some x \<Rightarrow> certified_cause_direct x)"

lemma certified_cause_covered_exact:
  "certified_cause_covered seed \<longleftrightarrow>
    (\<exists>c X. (c,Some X) |\<in>| certified_cause_family seed 0 \<and> certified_cause_holds X)"
  by (simp only: certified_cause_covered_def certified_cause_direct_exact finite_optional_relation_exists)

text \<open>
  The native constructors retain failed positions. Variants change the actual
  proof material, proof root, requested payload, recorded environment, cause
  quotation layout, value enumeration, generation core and generation site.
  One valid-source variant uses words containing 300. Another adds a disconnected
  formed node to the retained program artifact, preserving all bindings and
  other artifacts while changing the whole recorded scope inclusion. The original checker
  determines every outcome; these cases contain no supplied satisfaction flags.
\<close>

end
