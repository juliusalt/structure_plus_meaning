theory Finite_Investigation_Interface
  imports Finite_Investigation "HOL-Library.Code_Target_Nat"
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

export_code investigation_inference investigation_basis nat_of_integer integer_of_nat checking SML

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
