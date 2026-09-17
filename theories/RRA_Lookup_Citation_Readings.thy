theory RRA_Lookup_Citation_Readings
  imports RRA_Environment_Lookup_Contracts RRA_Finite_Generation_Readings RRA_Finite_Anchor_Selection
begin

definition lookup_bound_artifacts where
  "lookup_bound_artifacts artifacts bindings u k=ffUnion (fimage artifacts (bindings u k))"

fun lookup_citation_targets where
  "lookup_citation_targets artifacts bindings u (Local a)=
    fimage (\<lambda>C. Finite_Anchor C a)
      (ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (artifacts u))"
| "lookup_citation_targets artifacts bindings u (External k a)=
    fimage (\<lambda>C. Finite_Anchor C a)
      (ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (lookup_bound_artifacts artifacts bindings u k))"
| "lookup_citation_targets artifacts bindings u Local_Whole=
    fimage Finite_Whole (ffilter finite_exact_formed (artifacts u))"
| "lookup_citation_targets artifacts bindings u (External_Whole k)=
    fimage Finite_Whole (ffilter finite_exact_formed (lookup_bound_artifacts artifacts bindings u k))"

fun lookup_citation_locations where
  "lookup_citation_locations artifacts bindings u (Local a)=
    (if fBex (artifacts u) (\<lambda>C. finite_target_formed (Finite_Anchor C a)) then {|(u,a)|} else {||})"
| "lookup_citation_locations artifacts bindings u (External k a)=
    fimage (\<lambda>v. (v,a)) (ffilter (\<lambda>v.
      fBex (artifacts v) (\<lambda>C. finite_target_formed (Finite_Anchor C a))) (bindings u k))"
| "lookup_citation_locations artifacts bindings u Local_Whole={||}"
| "lookup_citation_locations artifacts bindings u (External_Whole k)={||}"

definition lookup_anchored_targets where
  "lookup_anchored_targets artifacts bindings u r=ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (\<lambda>(c,I). lookup_citation_targets artifacts bindings u c)
      (finite_citation_candidates C r))) (artifacts u))"

definition lookup_located_values where
  "lookup_located_values artifacts bindings u r=ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (\<lambda>(c,I). lookup_citation_locations artifacts bindings u c)
      (finite_citation_candidates C r))) (artifacts u))"

definition lookup_anchor_artifact where
  "lookup_anchor_artifact artifacts d=finite_singleton_option
    (ffilter (\<lambda>R. snd d |\<in>| finite_carrier (finite_structure R)) (artifacts (fst d)))"

lemma finite_citation_location_member:
  "d |\<in>| finite_citation_locations E u c \<longleftrightarrow>
    citation_location (decode_finite_environment E) u c (fst d) (snd d)"
  by (cases d) (simp only: finite_citation_locations_correct fst_conv snd_conv)

locale environment_lookup_reading =
  fixes artifacts :: "local_address option\<Rightarrow>finite_exact_artifact fset"
    and bindings :: "local_address option\<Rightarrow>local_address\<Rightarrow>local_address option fset"
    and E :: "local_address option finite_artifact_environment"
  assumes represented: "environment_lookup_represents artifacts bindings E"
begin

lemma artifacts_exact: "artifacts u=finite_artifacts_at E u"
  using represented by (auto simp: environment_lookup_represents_def finite_artifacts_at_member
    intro!: fset_inject[THEN iffD1] set_eqI)

lemma binding_member:
  "v |\<in>| bindings u k \<longleftrightarrow> ((u,k),v) |\<in>| finite_environment_bindings E"
  using represented by (simp add: environment_lookup_represents_def)

lemma bound_artifacts_exact: "lookup_bound_artifacts artifacts bindings u k=finite_bound_artifacts E u k"
  by (auto simp: lookup_bound_artifacts_def finite_union_image_member
    finite_bound_artifacts_member artifacts_exact binding_member intro!: fset_inject[THEN iffD1] set_eqI)

lemma citation_targets_exact:
  "lookup_citation_targets artifacts bindings u c=finite_citation_targets E u c"
  by (cases c) (simp_all only: lookup_citation_targets.simps finite_citation_targets.simps
    artifacts_exact bound_artifacts_exact)

lemma citation_locations_exact:
  "lookup_citation_locations artifacts bindings u c=finite_citation_locations E u c"
  by (cases c; auto simp: artifacts_exact binding_member finite_image_member
    intro!: fset_inject[THEN iffD1] set_eqI intro: rev_image_eqI split: prod.splits; force)

lemma anchored_targets_exact:
  "lookup_anchored_targets artifacts bindings u r=finite_anchored_targets E u r"
  by (simp only: lookup_anchored_targets_def finite_anchored_targets_def artifacts_exact citation_targets_exact)

lemma located_values_member:
  "d |\<in>| lookup_located_values artifacts bindings u r \<longleftrightarrow>
    (\<exists>C c I. C |\<in>| finite_artifacts_at E u \<and> (c,I) |\<in>| finite_citation_candidates C r \<and>
      d |\<in>| finite_citation_locations E u c)"
  by (auto simp: lookup_located_values_def finite_union_image_member
    artifacts_exact citation_locations_exact split_paired_Ex)

lemma located_values_exact: "lookup_located_values artifacts bindings u r=finite_located_values E u r"
proof (rule fset_inject[THEN iffD1], rule set_eqI)
  fix d
  have equivalent: "d |\<in>| lookup_located_values artifacts bindings u r \<longleftrightarrow>
    located_at (decode_finite_environment E) u r (fst d) (snd d)"
  proof
    assume read: "d |\<in>| lookup_located_values artifacts bindings u r"
    show "located_at (decode_finite_environment E) u r (fst d) (snd d)"
      using read by (auto simp: located_values_member finite_citation_candidates_correct
        finite_citation_location_member finite_artifacts_at_member located_at_def)
  next
    assume read: "located_at (decode_finite_environment E) u r (fst d) (snd d)"
    obtain C c I where source: "C |\<in>| finite_artifacts_at E u"
      and citation: "citation_at (decode_finite_object C) r c I"
      and target: "citation_location (decode_finite_environment E) u c (fst d) (snd d)"
      using read by (auto simp: located_at_def finite_artifacts_at_complete finite_artifacts_at_member)
    obtain J where chosen: "(c,J) |\<in>| finite_citation_candidates C r"
      using finite_citation_candidates_complete[OF citation] by blast
    show "d |\<in>| lookup_located_values artifacts bindings u r"
      using source chosen target by (simp only: located_values_member finite_citation_location_member; blast)
  qed
  show "d\<in>fset (lookup_located_values artifacts bindings u r) \<longleftrightarrow>d\<in>fset (finite_located_values E u r)"
    by (simp only: equivalent finite_located_values_correct)
qed

lemma anchor_artifact_exact: "lookup_anchor_artifact artifacts d=finite_anchor_artifact E d"
  by (simp only: lookup_anchor_artifact_def finite_anchor_artifact_def artifacts_exact)

end

text \<open>
  Complete artifact and binding lookups preserve all four citation forms, whole
  target values and distinct locations. No original environment view is built
  by these operations. The exactness premise covers every original relation
  entry and is independent of the particular lookup implementation.
\<close>

end
