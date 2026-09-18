theory Finite_Investigation_Basis_Sharing
  imports Ordered_Finite_Rows
begin

section \<open>Each candidate profile is computed once for the whole basis\<close>

lemma map_of_computed_rows:
  "c\<in>set cs \<Longrightarrow> map_of (map (\<lambda>c. (c,g c)) cs) c=Some (g c)"
  by (induction cs) auto

lemma investigation_profile_rows:
  "investigation_profile selected observations c=
    filter (\<lambda>x. x\<in>fset (finite_candidate_profile (fset_of_list selected) (fset_of_list observations) c))
      (remdups (map (\<lambda>(f,d,w). (f,w)) observations))"
  by (simp only: investigation_profile_def investigation_select_def)

lemma investigation_profile_losses:
  "investigation_select (investigation_profile selected observations c)
      (finite_candidate_losses (fset_of_list selected) (fset_of_list observations) c d)=
    filter (\<lambda>x. x\<notin>fset (finite_candidate_profile (fset_of_list selected) (fset_of_list observations) d))
      (investigation_profile selected observations c)"
proof -
  let ?P="\<lambda>c. finite_candidate_profile (fset_of_list selected) (fset_of_list observations) c"
  have distinct: "distinct (investigation_profile selected observations c)"
    by (simp add: investigation_profile_rows)
  have within: "x\<in>fset (?P c)" if "x\<in>set (investigation_profile selected observations c)" for x
    using that by (simp add: investigation_profile_rows)
  show ?thesis
    unfolding investigation_select_def distinct_remdups_id[OF distinct]
    by (rule filter_cong[OF refl]) (use within in \<open>auto simp: finite_candidate_losses_def\<close>)
qed

lemma investigation_basis_shared_profiles:
  "investigation_basis candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; compare=(\<lambda>c d. (c,d)\<in>set relation);
         residual=finite_basis_residual C F table compare;
         rows=remdups (map (\<lambda>(f,d,w). (f,w)) observations);
         profiles=map (\<lambda>c. let P=finite_candidate_profile F table c in (c,P)) candidates;
         listed=map (\<lambda>(c,P). (c,filter (\<lambda>x. x\<in>fset P) rows)) profiles
     in (finite_basis_evaluation C U F table compare residual,
       investigation_select (investigation_pairs candidates) residual,
       listed,
       map (\<lambda>(c,d). let P=the (map_of profiles d) in
         (c,d,filter (\<lambda>x. x\<notin>fset P) (the (map_of listed c)))) (investigation_pairs candidates)))"
proof -
  let ?F="fset_of_list selected" and ?T="fset_of_list observations"
  let ?rows="remdups (map (\<lambda>(f,d,w). (f,w)) observations)"
  let ?profiles="map (\<lambda>c. (c,finite_candidate_profile ?F ?T c)) candidates"
  let ?listed="map (\<lambda>c. (c,investigation_profile selected observations c)) candidates"
  have listed: "map (\<lambda>(c,P). (c,filter (\<lambda>x. x\<in>fset P) ?rows)) ?profiles=?listed"
    by (simp add: investigation_profile_rows)
  have profile_lookup: "the (map_of ?profiles d)=finite_candidate_profile ?F ?T d" if "d\<in>set candidates" for d
    using map_of_computed_rows[OF that, of "finite_candidate_profile ?F ?T"] by simp
  have listed_lookup: "the (map_of ?listed c)=investigation_profile selected observations c" if "c\<in>set candidates" for c
    using map_of_computed_rows[OF that, of "investigation_profile selected observations"] by simp
  have pairs: "(c,d)\<in>set (investigation_pairs candidates) \<Longrightarrow> c\<in>set candidates \<and> d\<in>set candidates" for c d
    by (auto simp: investigation_pairs_def)
  have losses: "map (\<lambda>(c,d). (c,d,filter (\<lambda>x. x\<notin>fset (the (map_of ?profiles d))) (the (map_of ?listed c))))
      (investigation_pairs candidates)=
    map (\<lambda>(c,d). (c,d,investigation_select (investigation_profile selected observations c)
      (finite_candidate_losses ?F ?T c d))) (investigation_pairs candidates)"
    by (rule map_cong[OF refl]) (auto simp: investigation_profile_losses profile_lookup listed_lookup dest!: pairs)
  have shape: "investigation_basis candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=?F; table=?T; compare=(\<lambda>c d. (c,d)\<in>set relation);
         residual=finite_basis_residual C F table compare
     in (finite_basis_evaluation C U F table compare residual,
       investigation_select (investigation_pairs candidates) residual,
       ?listed,
       map (\<lambda>(c,d). (c,d,filter (\<lambda>x. x\<notin>fset (the (map_of ?profiles d))) (the (map_of ?listed c))))
         (investigation_pairs candidates)))"
    by (simp only: investigation_basis_def Let_def losses)
  show ?thesis
    by (simp only: shape Let_def listed)
qed

declare investigation_basis_def[code del]

lemma investigation_basis_ordered_code [code]:
  "investigation_basis candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; compare=(\<lambda>c d. (c,d)\<in>set relation);
         residual=finite_basis_residual C F table compare;
         rows=ordered_remdups (map (\<lambda>(f,d,w). (f,w)) observations);
         profiles=map (\<lambda>c. let P=finite_candidate_profile F table c in (c,P)) candidates;
         listed=map (\<lambda>(c,P). let T=ordered_member_tree P in (c,filter (\<lambda>x. RBT.lookup T x\<noteq>None) rows)) profiles
     in (finite_basis_evaluation C U F table compare residual,
       ordered_investigation_select (investigation_pairs candidates) residual,
       listed,
       map (\<lambda>(c,d). let T=ordered_member_tree (the (map_of profiles d)) in
         (c,d,filter (\<lambda>x. RBT.lookup T x=None) (the (map_of listed c)))) (investigation_pairs candidates)))"
  by (simp only: investigation_basis_shared_profiles Let_def ordered_remdups_exact
    ordered_investigation_select_exact ordered_member_tree_none not_not)

declare investigation_repairs_def[code del]

lemma investigation_repairs_ordered_code [code]:
  "investigation_repairs candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; compare=(\<lambda>c d. (c,d)\<in>set relation);
         loss_rows=investigation_loss_rows candidates observations
     in (ordered_investigation_select facets (finite_sound_observation_facets C compare U table),
       ordered_investigation_select loss_rows (finite_observation_conflicts C compare F table),
       ordered_investigation_select loss_rows (finite_available_observation_repairs C compare U F table),
       ordered_investigation_select (investigation_pairs candidates) (finite_unrepairable_comparisons C compare U table)))"
  by (simp only: investigation_repairs_def ordered_investigation_select_exact)

declare investigation_retain_def[code del]

lemma investigation_retain_ordered_code [code]:
  "investigation_retain candidates facets selected observations relation=
    ordered_investigation_select selected (finite_sound_observation_facets (fset_of_list candidates)
      (\<lambda>c d. (c,d)\<in>set relation) (fset_of_list facets) (fset_of_list observations))"
  by (simp only: investigation_retain_def ordered_investigation_select_exact)

text \<open>
  The deduplicated observation rows, every candidate profile and every loss
  are those of the original basis; ordered indexes deduplicate rows and read
  profile membership without repeated whole-list scans. Each profile relation is formed once and
  consumed by all candidate pairs; a loss keeps the original ordered profile
  rows that are absent from the compared candidate's profile. Repeated
  candidates, empty profiles and the residual evaluation are unchanged.
\<close>

end
