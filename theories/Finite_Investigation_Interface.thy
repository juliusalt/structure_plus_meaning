theory Finite_Investigation_Interface
  imports Finite_Observation_Repairs Observation_Revisions "HOL-Library.Code_Target_Nat"
begin

section \<open>List arguments retain the finite relations they present\<close>

definition investigation_select :: "'a list \<Rightarrow> 'a fset \<Rightarrow> 'a list" where
  "investigation_select xs A=filter (\<lambda>x. x\<in>fset A) (remdups xs)"

lemma investigation_select_exact:
  "fset A\<subseteq>set xs \<Longrightarrow> set (investigation_select xs A)=fset A"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_select_def)

definition investigation_rules ::
  "(nat\<times>(nat\<times>nat) list) list \<Rightarrow> (nat\<times>(nat\<times>nat) fset) fset" where
  "investigation_rules rules=fset_of_list (map (\<lambda>(a,H). (a,fset_of_list H)) rules)"

definition investigation_atoms ::
  "(nat\<times>(nat\<times>nat) list) list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat) list \<Rightarrow> nat list" where
  "investigation_atoms rules known goals=
    map snd goals @ known @ map fst rules @ concat (map (\<lambda>(a,H). map snd H) rules)"

lemma investigation_demand_in_atoms:
  "fset (finite_inference_demand (investigation_rules rules) (fset_of_list known)
      (fimage snd (fset_of_list goals)))\<subseteq>set (investigation_atoms rules known goals)"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' finite_inference_demand_def finite_reachable_outputs_member
    finite_inference_demand_edges_def investigation_rules_def investigation_atoms_def
    ffUnion.rep_eq fimage.rep_eq split: prod.splits if_splits; force)

definition investigation_reasons ::
  "(nat\<times>(nat\<times>nat) list) list \<Rightarrow> nat list \<Rightarrow> nat fset \<Rightarrow>
    (nat\<times>(nat\<times>nat) list\<times>nat\<times>nat) list" where
  "investigation_reasons rules known demanded=concat (map (\<lambda>(a,H).
    if a\<in>fset demanded \<and> a\<notin>set known \<and> finite_premise_functional (fset_of_list H)
    then map (\<lambda>(i,b). (a,H,i,b)) H else []) rules)"

lemma investigation_reasons_exact:
  "(\<lambda>(a,H,i,b). (a,fset_of_list H,i,b)) `
      set (investigation_reasons rules known
        (finite_inference_demand (investigation_rules rules) (fset_of_list known) A))=
    fset (finite_inference_demand_reasons (investigation_rules rules) (fset_of_list known) A)"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_reasons_def investigation_rules_def
    finite_inference_demand_reasons_def ffUnion.rep_eq fimage.rep_eq
    split: prod.splits if_splits; force)

definition investigation_inference ::
  "(nat\<times>(nat\<times>nat) list) list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat) list \<Rightarrow>
    (bool\<times>(nat\<times>nat) list\<times>nat list\<times>(nat\<times>(nat\<times>nat) list\<times>nat\<times>nat) list)" where
  "investigation_inference rules known goals=
    (let F=investigation_rules rules; K=fset_of_list known; H=fset_of_list goals;
         G=finite_inference_residual F K H; D=finite_inference_demand F K (fimage snd H)
     in (finite_guided_inference_evaluation F K H G,
       investigation_select goals G,
       investigation_select (investigation_atoms rules known goals) D,
       investigation_reasons rules known D))"

lemma investigation_inference_shared_code [code]:
  "investigation_inference rules known goals=
    (let F=investigation_rules rules; K=fset_of_list known; H=fset_of_list goals;
         G=finite_inference_residual F K H; D=finite_inference_demand F K (fimage snd H)
     in (finite_inference_formed F \<and> finite_premise_functional H,
       investigation_select goals G,
       investigation_select (investigation_atoms rules known goals) D,
       investigation_reasons rules known D))"
  by (simp only: investigation_inference_def Let_def finite_guided_inference_evaluation_exact
    finite_inference_evaluation_def; simp)

theorem investigation_inference_formation:
  "fst (investigation_inference rules known goals) \<longleftrightarrow>
    finite_inference_formed (investigation_rules rules) \<and>
    finite_premise_functional (fset_of_list goals)"
  by (simp add: investigation_inference_def Let_def
    finite_guided_inference_evaluation_exact finite_inference_evaluation_def)

theorem investigation_inference_residual:
  "set (fst (snd (investigation_inference rules known goals)))=
    fset (finite_inference_residual (investigation_rules rules) (fset_of_list known) (fset_of_list goals))"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_inference_def Let_def investigation_select_def finite_inference_residual_def)

theorem investigation_inference_demand:
  "set (fst (snd (snd (investigation_inference rules known goals))))=
    fset (finite_inference_demand (investigation_rules rules) (fset_of_list known)
      (fimage snd (fset_of_list goals)))"
  by (simp add: investigation_inference_def Let_def
    investigation_select_exact[OF investigation_demand_in_atoms])

theorem investigation_inference_reasons:
  "(\<lambda>(a,H,i,b). (a,fset_of_list H,i,b)) `
      set (snd (snd (snd (investigation_inference rules known goals))))=
    fset (finite_inference_demand_reasons (investigation_rules rules) (fset_of_list known)
      (fimage snd (fset_of_list goals)))"
  by (simp add: investigation_inference_def Let_def investigation_reasons_exact)

section \<open>Observation reports retain every mismatch and loss\<close>

definition investigation_profile ::
  "nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow> nat \<Rightarrow> (nat\<times>nat) list" where
  "investigation_profile selected observations c=investigation_select
    (map (\<lambda>(f,d,w). (f,w)) observations)
    (finite_candidate_profile (fset_of_list selected) (fset_of_list observations) c)"

lemma investigation_profile_exact:
  "set (investigation_profile selected observations c)=
    fset (finite_candidate_profile (fset_of_list selected) (fset_of_list observations) c)"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_profile_def investigation_select_def
    finite_candidate_profile_def fimage.rep_eq split: prod.splits)

definition investigation_pairs :: "nat list \<Rightarrow> (nat\<times>nat) list" where
  "investigation_pairs candidates=concat (map (\<lambda>c. map (\<lambda>d. (c,d)) candidates) candidates)"

lemma investigation_pairs_exact:
  "set (investigation_pairs candidates)=set candidates\<times>set candidates"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_pairs_def)

definition investigation_basis ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    (nat\<times>nat) list \<Rightarrow>
    (bool\<times>(nat\<times>nat) list\<times>(nat\<times>(nat\<times>nat) list) list\<times>
      (nat\<times>nat\<times>(nat\<times>nat) list) list)" where
  "investigation_basis candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; compare=(\<lambda>c d. (c,d)\<in>set relation);
         residual=finite_basis_residual C F table compare
     in (finite_basis_evaluation C U F table compare residual,
       investigation_select (investigation_pairs candidates) residual,
       map (\<lambda>c. (c,investigation_profile selected observations c)) candidates,
       map (\<lambda>(c,d). (c,d,investigation_select (investigation_profile selected observations c)
         (finite_candidate_losses F table c d))) (investigation_pairs candidates)))"

theorem investigation_basis_formation:
  "fst (investigation_basis candidates facets selected observations relation) \<longleftrightarrow>
    finite_observation_table_formed (fset_of_list candidates) (fset_of_list facets) (fset_of_list observations) \<and>
    set selected\<subseteq>set facets"
  by (simp add: investigation_basis_def Let_def finite_basis_evaluation_def fset_of_list.rep_eq)

theorem investigation_basis_residual:
  "set (fst (snd (investigation_basis candidates facets selected observations relation)))=
    fset (finite_basis_residual (fset_of_list candidates) (fset_of_list selected)
      (fset_of_list observations) (\<lambda>c d. (c,d)\<in>set relation))"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_basis_def Let_def investigation_select_def investigation_pairs_exact
    finite_basis_residual_def ffUnion.rep_eq fimage.rep_eq split: prod.splits)

theorem investigation_basis_profiles:
  "(\<lambda>(c,P). (c,set P)) `
      set (fst (snd (snd (investigation_basis candidates facets selected observations relation))))=
    {(c,fset (finite_candidate_profile (fset_of_list selected) (fset_of_list observations) c)) |c. c\<in>set candidates}"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_basis_def Let_def investigation_profile_exact)

theorem investigation_basis_losses:
  "(\<lambda>(c,d,L). (c,d,set L)) `
      set (snd (snd (snd (investigation_basis candidates facets selected observations relation))))=
    {(c,d,fset (finite_candidate_losses (fset_of_list selected) (fset_of_list observations) c d))
      |c d. c\<in>set candidates \<and> d\<in>set candidates}"
  by (auto simp: fset_of_list.rep_eq image_image image_iff case_prod_beta' investigation_basis_def Let_def investigation_pairs_exact
    investigation_select_def investigation_profile_exact finite_candidate_losses_def)


section \<open>Repair guidance retains all available witnesses and both obstructions\<close>

definition investigation_loss_rows ::
  "nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow> (nat\<times>nat\<times>nat\<times>nat) list" where
  "investigation_loss_rows candidates observations=concat (map (\<lambda>(c,d).
    map (\<lambda>(f,a,w). (c,d,f,w)) observations) (investigation_pairs candidates))"

lemma investigation_loss_rows_exact:
  "set (investigation_loss_rows candidates observations)=
    {(c,d,f,w). c\<in>set candidates \<and> d\<in>set candidates \<and> (\<exists>a. (f,a,w)\<in>set observations)}"
  by (auto simp: investigation_loss_rows_def investigation_pairs_exact image_iff
    case_prod_beta' split: prod.splits; force)

definition investigation_repairs ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    (nat\<times>nat) list \<Rightarrow>
    (nat list\<times>(nat\<times>nat\<times>nat\<times>nat) list\<times>
      (nat\<times>nat\<times>nat\<times>nat) list\<times>(nat\<times>nat) list)" where
  "investigation_repairs candidates facets selected observations relation=
    (let C=fset_of_list candidates; U=fset_of_list facets; F=fset_of_list selected;
         table=fset_of_list observations; compare=(\<lambda>c d. (c,d)\<in>set relation);
         loss_rows=investigation_loss_rows candidates observations
     in (investigation_select facets (finite_sound_observation_facets C compare U table),
       investigation_select loss_rows (finite_observation_conflicts C compare F table),
       investigation_select loss_rows (finite_available_observation_repairs C compare U F table),
       investigation_select (investigation_pairs candidates) (finite_unrepairable_comparisons C compare U table)))"

theorem investigation_sound_facets:
  "set (fst (investigation_repairs candidates facets selected observations relation))=
    sound_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_repairs_def Let_def investigation_select_def
    finite_sound_observation_facets_exact fset_of_list.rep_eq; blast)

theorem investigation_conflicts:
  "set (fst (snd (investigation_repairs candidates facets selected observations relation)))=
    observation_conflicts (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set selected) (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_repairs_def Let_def investigation_select_def investigation_loss_rows_exact
    finite_observation_conflicts_exact observation_conflicts_def finite_table_observations_def
    fset_of_list.rep_eq)

theorem investigation_available_repairs:
  "set (fst (snd (snd (investigation_repairs candidates facets selected observations relation))))=
    available_observation_repairs (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (set selected) (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_repairs_def Let_def investigation_select_def investigation_loss_rows_exact
    finite_available_observation_repairs_exact available_observation_repairs_def comparison_failures_def
    finite_table_observations_def fset_of_list.rep_eq)

theorem investigation_unrepairable_comparisons:
  "set (snd (snd (snd (investigation_repairs candidates facets selected observations relation))))=
    comparison_failures (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (sound_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
        (set facets) (finite_table_observations (fset_of_list observations)))
      (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_repairs_def Let_def investigation_select_def investigation_pairs_exact
    finite_unrepairable_comparisons_exact comparison_failures_def fset_of_list.rep_eq)

definition investigation_extend ::
  "nat list \<Rightarrow> (nat\<times>nat\<times>nat\<times>nat) list \<Rightarrow> nat list" where
  "investigation_extend selected repairs=remdups (selected @ map (\<lambda>(c,d,f,w). f) repairs)"

lemma investigation_extend_exact:
  "set (investigation_extend selected repairs)=reported_observation_extension (set selected) (set repairs)"
  by (auto simp: investigation_extend_def reported_observation_extension_def image_iff
    case_prod_beta' split: prod.splits; force)

theorem investigation_extension_adequate:
  fixes candidates facets selected :: "nat list"
    and observations :: "(nat\<times>nat\<times>nat) list"
    and relation :: "(nat\<times>nat) list"
  assumes selected: "set selected\<subseteq>set facets"
  defines "report \<equiv> investigation_repairs candidates facets selected observations relation"
  shows "comparison_basis (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set (investigation_extend selected (fst (snd (snd report)))))
      (finite_table_observations (fset_of_list observations)) \<longleftrightarrow>
    fst (snd report)=[] \<and> snd (snd (snd report))=[]"
proof -
  have conflicts: "fst (snd report)=[] \<longleftrightarrow>
      observation_conflicts (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
        (set selected) (finite_table_observations (fset_of_list observations))={}"
    using investigation_conflicts[of candidates facets selected observations relation]
    by (auto simp: report_def)
  have blocked: "snd (snd (snd report))=[] \<longleftrightarrow>
      comparison_failures (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
        (sound_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
          (set facets) (finite_table_observations (fset_of_list observations)))
        (finite_table_observations (fset_of_list observations))={}"
    using investigation_unrepairable_comparisons[of candidates facets selected observations relation]
    by (auto simp: report_def)
  show ?thesis
    by (simp only: report_def investigation_extend_exact investigation_available_repairs
      reported_extension_is_adequate_exactly_when_an_extension_exists[OF selected];
      simp only: conflicts[unfolded report_def] blocked[unfolded report_def])
qed

section \<open>Revision reports preserve the selected sound part and recompute its needs\<close>

definition investigation_retain ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    (nat\<times>nat) list \<Rightarrow> nat list" where
  "investigation_retain candidates facets selected observations relation=
    investigation_select selected (finite_sound_observation_facets (fset_of_list candidates)
      (\<lambda>c d. (c,d)\<in>set relation) (fset_of_list facets) (fset_of_list observations))"

lemma investigation_retain_exact:
  "set (investigation_retain candidates facets selected observations relation)=
    retained_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (set selected) (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_retain_def investigation_select_def
    finite_sound_observation_facets_exact fset_of_list.rep_eq retained_observation_facets_def; blast)

definition investigation_revision ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    (nat\<times>nat) list \<Rightarrow>
    (nat list\<times>nat list\<times>(nat\<times>nat\<times>nat\<times>nat) list\<times>nat list\<times>(nat\<times>nat) list)" where
  "investigation_revision candidates facets selected observations relation=
    (let retained=investigation_retain candidates facets selected observations relation;
         withdrawn=filter (\<lambda>f. f\<notin>set retained) (remdups selected);
         repairs=fst (snd (snd (investigation_repairs candidates facets retained observations relation)));
         revised=investigation_extend retained repairs;
         residual=fst (snd (investigation_basis candidates facets revised observations relation))
     in (retained,withdrawn,repairs,revised,residual))"

theorem investigation_revision_retained:
  "set (fst (investigation_revision candidates facets selected observations relation))=
    retained_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (set selected) (finite_table_observations (fset_of_list observations))"
  by (simp only: investigation_revision_def Let_def fst_conv investigation_retain_exact)

theorem investigation_revision_withdrawn:
  "set (fst (snd (investigation_revision candidates facets selected observations relation)))=
    withdrawn_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (set selected) (finite_table_observations (fset_of_list observations))"
  by (auto simp: investigation_revision_def Let_def investigation_retain_exact
    retained_observation_facets_def withdrawn_observation_facets_def; blast)

theorem investigation_revision_repairs:
  "set (fst (snd (snd (investigation_revision candidates facets selected observations relation))))=
    available_observation_repairs (set candidates) (\<lambda>c d. (c,d)\<in>set relation) (set facets)
      (retained_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
        (set facets) (set selected) (finite_table_observations (fset_of_list observations)))
      (finite_table_observations (fset_of_list observations))"
  by (simp only: investigation_revision_def Let_def fst_conv snd_conv
    investigation_available_repairs investigation_retain_exact)

theorem investigation_revision_selection:
  "set (fst (snd (snd (snd (investigation_revision candidates facets selected observations relation)))))=
    revised_observation_selection (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (set facets) (set selected) (finite_table_observations (fset_of_list observations))"
  by (simp only: investigation_revision_def Let_def fst_conv snd_conv investigation_extend_exact
    investigation_available_repairs investigation_retain_exact revised_observation_selection_def)

theorem investigation_revision_residual:
  "set (snd (snd (snd (snd (investigation_revision candidates facets selected observations relation)))))=
    comparison_failures (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
      (sound_observation_facets (set candidates) (\<lambda>c d. (c,d)\<in>set relation)
        (set facets) (finite_table_observations (fset_of_list observations)))
      (finite_table_observations (fset_of_list observations))"
proof -
  let ?K="investigation_retain candidates facets selected observations relation"
  let ?P="fst (snd (snd (investigation_repairs candidates facets ?K observations relation)))"
  let ?G="investigation_extend ?K ?P"
  let ?O="finite_table_observations (fset_of_list observations)"
  let ?R="\<lambda>c d. (c,d)\<in>set relation"
  have selected: "set ?G=revised_observation_selection (set candidates) ?R (set facets) (set selected) ?O"
    by (simp only: investigation_extend_exact investigation_available_repairs
      investigation_retain_exact revised_observation_selection_def)
  have sound: "comparison_observations_sound (set candidates) ?R (set ?G) ?O"
    by (simp only: selected revised_observation_selection_sound)
  have residual: "fset (finite_basis_residual (fset_of_list candidates) (fset_of_list ?G)
      (fset_of_list observations) ?R)=comparison_failures (set candidates) ?R (set ?G) ?O"
    using sound by (auto simp: finite_basis_residual_member comparison_failures_def
      comparison_observations_sound_def fset_of_list.rep_eq candidate_profile_comparison; blast)
  show ?thesis
    by (simp only: investigation_revision_def Let_def fst_conv snd_conv investigation_basis_residual
      residual selected revision_has_exactly_the_full_sound_language_failures)
qed

export_code investigation_inference investigation_basis investigation_repairs investigation_extend
  investigation_revision nat_of_integer integer_of_nat checking SML

text \<open>
  Natural numbers are private input identifiers, with equality as their only
  semantic use. Lists present finite relations. Reports retain complete rules,
  premise occurrences, profiles, losses, and unresolved comparison pairs.
  Reordering a list or repeating an identical row changes no represented set.
  Distinct premise occurrences carrying the same condition remain distinct.

  These projection contracts connect the executed lists to the existing finite
  evaluator. Input formation, rule soundness, established seeds, observation
  completeness, and coverage of an independently specified subject remain
  separate conditions. A successful process does not establish those meanings.
\<close>

end
