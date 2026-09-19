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
         table=fset_of_list observations; R=ordered_member_tree (fset_of_list relation);
         compare=(\<lambda>c d. RBT.lookup R (c,d)\<noteq>None);
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
    ordered_investigation_select_exact ordered_member_tree_none not_not fset_of_list.rep_eq)

section \<open>Loss rows are ordered against each observation pair once\<close>

text \<open>
  The repairs present their rows in the order of every candidate pair joined with every observation
  row, a list of the number of pairs times the number of rows, in which a pair and an observation
  pair repeat once for every candidate that shares it. Selecting from a list reads only the last
  occurrence of each member, so the order in which each observation pair occurs once selects the
  same rows (`investigation_select_loss_order`) from a list of the number of pairs times
  the number of distinct observation pairs.
\<close>

definition investigation_loss_order :: "nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow> (nat\<times>nat\<times>nat\<times>nat) list" where
  "investigation_loss_order candidates observations=concat (map (\<lambda>(c,d).
    map (\<lambda>(f,w). (c,d,f,w)) (remdups (map (\<lambda>(f,a,w). (f,w)) observations))) (investigation_pairs candidates))"

lemma remdups_append_remdups_left: "remdups (remdups xs @ ys)=remdups (xs @ ys)"
  by (induction xs) auto

lemma remdups_concat_remdups:
  "remdups (concat (map (\<lambda>p. remdups (f p)) ps))=remdups (concat (map f ps))"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  have "remdups (concat (map (\<lambda>p. remdups (f p)) (p#ps)))=
      remdups (remdups (f p) @ remdups (concat (map (\<lambda>p. remdups (f p)) ps)))"
    by (simp only: list.map concat.simps remdups_append2)
  also have "\<dots>=remdups (remdups (f p) @ remdups (concat (map f ps)))"
    by (simp only: Cons.IH)
  also have "\<dots>=remdups (concat (map f (p#ps)))"
    by (simp only: list.map concat.simps remdups_append2 remdups_append_remdups_left)
  finally show ?case .
qed

lemma investigation_loss_order_remdups:
  "remdups (investigation_loss_order candidates observations)=
    remdups (investigation_loss_rows candidates observations)"
proof -
  let ?F="\<lambda>p. case p of (c,d) \<Rightarrow> map (\<lambda>(f,w). (c,d,f,w)) (remdups (map (\<lambda>(f,a,w). (f,w)) observations))"
  let ?G="\<lambda>p. case p of (c,d) \<Rightarrow> map (\<lambda>(f,a,w). (c,d,f,w)) observations"
  have block: "remdups (?F p)=remdups (?G p)" for p
  proof (cases p)
    case (Pair c d)
    have "map (\<lambda>(f,a,w). (c,d,f,w)) observations=map (\<lambda>(f,w). (c,d,f,w)) (map (\<lambda>(f,a,w). (f,w)) observations)"
      by (induction observations) auto
    then show ?thesis by (simp only: Pair prod.case remdups_map_remdups)
  qed
  have "remdups (investigation_loss_order candidates observations)=
      remdups (concat (map (\<lambda>p. remdups (?F p)) (investigation_pairs candidates)))"
    by (simp only: investigation_loss_order_def remdups_concat_remdups)
  also have "\<dots>=remdups (concat (map (\<lambda>p. remdups (?G p)) (investigation_pairs candidates)))"
    by (simp only: block)
  also have "\<dots>=remdups (investigation_loss_rows candidates observations)"
    by (simp only: investigation_loss_rows_def remdups_concat_remdups)
  finally show ?thesis .
qed

lemma investigation_select_loss_order:
  "investigation_select (investigation_loss_rows candidates observations) X=
    investigation_select (investigation_loss_order candidates observations) X"
  by (simp only: investigation_select_def investigation_loss_order_remdups)

declare investigation_repairs_def[code del]

lemma investigation_repairs_ordered_code [code]:
  "investigation_repairs candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; R=ordered_member_tree (fset_of_list relation);
         compare=(\<lambda>c d. RBT.lookup R (c,d)\<noteq>None);
         loss_rows=investigation_loss_order candidates observations
     in (ordered_investigation_select facets (finite_sound_observation_facets C compare U table),
       ordered_investigation_select loss_rows (finite_observation_conflicts C compare F table),
       ordered_investigation_select loss_rows (finite_available_observation_repairs C compare U F table),
       ordered_investigation_select (investigation_pairs candidates) (finite_unrepairable_comparisons C compare U table)))"
  by (simp only: investigation_repairs_def Let_def ordered_member_tree_listed
    ordered_investigation_select_exact investigation_select_loss_order)

declare investigation_retain_def[code del]

lemma investigation_retain_ordered_code [code]:
  "investigation_retain candidates facets selected observations relation=(let
    R=ordered_member_tree (fset_of_list relation) in
    ordered_investigation_select selected (finite_sound_observation_facets (fset_of_list candidates)
      (\<lambda>c d. RBT.lookup R (c,d)\<noteq>None) (fset_of_list facets) (fset_of_list observations)))"
  by (simp only: investigation_retain_def Let_def ordered_member_tree_listed ordered_investigation_select_exact)

text \<open>
  The deduplicated observation rows, every candidate profile and every loss
  are those of the original basis; ordered indexes deduplicate rows and read
  profile membership without repeated whole-list scans. Each profile relation is formed once and
  consumed by all candidate pairs; a loss keeps the original ordered profile
  rows that are absent from the compared candidate's profile. The comparison relation is indexed
  once, so every comparison is one lookup. Repeated
  candidates, empty profiles and the residual evaluation are unchanged.
\<close>

end
