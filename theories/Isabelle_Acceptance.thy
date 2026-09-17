theory Isabelle_Acceptance
  imports Isabelle_Renaming Factor_Finite_Ground_Source Factor_Finite_Native_Evaluation
begin

section \<open>Accepted entities are the positive meaning of one ground program\<close>

text \<open>
  Acceptance is proved once for the notion: the entities presented by a checked context
  are installed as the ground clauses of one native program, and its entry holds exactly
  of their presentations. Receiving notions consume this contract; known calls of that
  program are exactly the accepted entities.
\<close>

definition isabelle_acceptance_source where
  "isabelle_acceptance_source es=finite_ground_source (map isabelle_entity_data es)"

theorem isabelle_acceptance_source_total:
  "\<exists>d F u. isabelle_acceptance_source es=Some (d,F,u)"
proof -
  have formed: "list_all finite_term_formed (map isabelle_entity_data es)"
    by (simp add: list_all_iff)
  show ?thesis
    unfolding isabelle_acceptance_source_def
    using finite_ground_source_total[of "map isabelle_entity_data es"] formed by blast
qed

theorem isabelle_acceptance_meaning:
  assumes source: "isabelle_acceptance_source es=Some (d,F,u)"
  obtains P where "native_package_at (decode_finite_environment F) u [] P"
    "\<And>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
    "\<And>e. (d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning P \<longleftrightarrow> e\<in>set es"
proof -
  obtain P where package: "native_package_at (decode_finite_environment F) u [] P"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> t\<in>decode_finite_term ` set (map isabelle_entity_data es)"
    using finite_ground_source_meaning[OF source[unfolded isabelle_acceptance_source_def]] by blast
  have members: "(d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))" for t
    using spec[OF meaning, of t] by (simp add: image_iff)
  have entities: "(d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning P \<longleftrightarrow> e\<in>set es" for e
    by (simp add: members inj_eq[OF isabelle_entity_data_injective])
  show thesis by (rule that[OF package members entities])
qed

corollary isabelle_acceptance_membership:
  assumes source: "isabelle_acceptance_source es=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] Q"
  shows "(d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning Q \<longleftrightarrow> e\<in>set es"
proof (rule isabelle_acceptance_meaning[OF source])
  fix P
  assume installed: "native_package_at (decode_finite_environment F) u [] P"
    and members: "\<And>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
    and entities: "\<And>e. (d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning P \<longleftrightarrow> e\<in>set es"
  have same: "Q=P" by (rule native_package_unique[OF package installed])
  show "(d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning Q \<longleftrightarrow> e\<in>set es"
    by (simp only: same entities)
qed

text \<open>
  This membership equation is what a receiving notion consumes. The package is fixed by
  the entry of the state, so any program installed at that entry decides exactly the
  supplied entities; no use re-establishes the connection.
\<close>

corollary isabelle_acceptance_members:
  assumes source: "isabelle_acceptance_source es=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] Q"
  shows "(d,t)\<in>positive_meaning Q \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
proof (rule isabelle_acceptance_meaning[OF source])
  fix P
  assume installed: "native_package_at (decode_finite_environment F) u [] P"
    and members: "\<And>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
    and entities: "\<And>e. (d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning P \<longleftrightarrow> e\<in>set es"
  have same: "Q=P" by (rule native_package_unique[OF package installed])
  show "(d,t)\<in>positive_meaning Q \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
    by (simp only: same members)
qed

text \<open>
  The same entry read at an arbitrary term is the other half of that contract: nothing
  outside the supplied entities lies in it, so a notion admitting under that entry never
  re-derives which terms it may hold of.
\<close>

corollary isabelle_acceptance_known_calls:
  assumes source: "isabelle_acceptance_source es=Some (d,F,u)"
  obtains P where "native_package_at (decode_finite_environment F) u [] P"
    "(\<lambda>e. (d,decode_finite_term (isabelle_entity_data e))) ` set es\<subseteq>positive_meaning P"
proof (rule isabelle_acceptance_meaning[OF source])
  fix P
  assume package: "native_package_at (decode_finite_environment F) u [] P"
    and members: "\<And>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e))"
    and entities: "\<And>e. (d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning P \<longleftrightarrow> e\<in>set es"
  have known: "(\<lambda>e. (d,decode_finite_term (isabelle_entity_data e))) ` set es\<subseteq>positive_meaning P"
  proof
    fix c assume "c\<in>(\<lambda>e. (d,decode_finite_term (isabelle_entity_data e))) ` set es"
    then obtain e where member: "e\<in>set es"
      and call: "c=(d,decode_finite_term (isabelle_entity_data e))" by blast
    show "c\<in>positive_meaning P" using member by (simp only: call entities)
  qed
  show thesis by (rule that[OF package known])
qed

section \<open>Native evaluation decides acceptance of demanded entities exactly\<close>

definition isabelle_demand_acceptance :: "isabelle_entity list \<Rightarrow> isabelle_entity list \<Rightarrow>
    (isabelle_entity fset\<times>isabelle_entity fset) option" where
  "isabelle_demand_acceptance es demands=(case isabelle_acceptance_source es of
     None \<Rightarrow> None
   | Some (d,F,u) \<Rightarrow>
       (case finite_native_program_evaluation F u [] (fset_of_list (map (\<lambda>e. (d,isabelle_entity_data e)) demands)) of
         None \<Rightarrow> None
       | Some (P,A) \<Rightarrow> Some (fset_of_list (filter (\<lambda>e. (d,isabelle_entity_data e) |\<in>| A) demands),
           fset_of_list (filter (\<lambda>e. (d,isabelle_entity_data e) |\<notin>| A) demands))))"

theorem isabelle_demand_acceptance_exact:
  assumes result: "isabelle_demand_acceptance es demands=Some (accepted,refused)"
  shows "fset accepted=set demands\<inter>set es" "fset refused=set demands-set es"
proof -
  obtain d F u where source: "isabelle_acceptance_source es=Some (d,F,u)"
    using isabelle_acceptance_source_total by blast
  let ?D="fset_of_list (map (\<lambda>e. (d,isabelle_entity_data e)) demands)"
  let ?accepted="\<lambda>A. fset_of_list (filter (\<lambda>e. (d,isabelle_entity_data e) |\<in>| A) demands)"
  let ?refused="\<lambda>A. fset_of_list (filter (\<lambda>e. (d,isabelle_entity_data e) |\<notin>| A) demands)"
  have unfolded: "isabelle_demand_acceptance es demands=
      (case finite_native_program_evaluation F u [] ?D of None \<Rightarrow> None
        | Some (P,A) \<Rightarrow> Some (?accepted A,?refused A))"
    by (simp only: isabelle_demand_acceptance_def source option.case prod.case)
  obtain P A where evaluation: "finite_native_program_evaluation F u [] ?D=Some (P,A)"
    and readings: "accepted=?accepted A" "refused=?refused A"
  proof (cases "finite_native_program_evaluation F u [] ?D")
    case None
    have "isabelle_demand_acceptance es demands=None" by (simp only: unfolded None option.case)
    then show ?thesis using result by simp
  next
    case (Some PA)
    obtain Q B where pair: "PA=(Q,B)" by (cases PA) simp
    have reading: "isabelle_demand_acceptance es demands=Some (?accepted B,?refused B)"
      by (simp only: unfolded Some pair option.case prod.case)
    show ?thesis
    proof (rule that[of Q B])
      show "finite_native_program_evaluation F u [] ?D=Some (Q,B)" by (simp only: Some pair)
      show "accepted=?accepted B" using result reading by simp
      show "refused=?refused B" using result reading by simp
    qed
  qed
  have meaning: "(d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning (decode_finite_system P)
      \<longleftrightarrow> e\<in>set es" for e
    by (rule isabelle_acceptance_membership[OF source finite_native_program_evaluation_exact(1)[OF evaluation]])
  have decided: "(d,isabelle_entity_data e) |\<in>| A \<longleftrightarrow> e\<in>set es" if demanded: "e\<in>set demands" for e
  proof -
    have "(d,isabelle_entity_data e) |\<in>| ?D" using demanded by (simp add: fset_of_list_elem)
    then have "(d,isabelle_entity_data e) |\<in>| A \<longleftrightarrow>
        (d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning (decode_finite_system P)"
      by (rule finite_native_program_evaluation_call[OF evaluation])
    then show ?thesis by (simp only: meaning)
  qed
  show "fset accepted=set demands\<inter>set es"
    using decided by (auto simp: readings(1) fset_of_list.rep_eq)
  show "fset refused=set demands-set es"
    using decided by (auto simp: readings(2) fset_of_list.rep_eq)
qed

type_synonym isabelle_acceptance_assessment = "(isabelle_entity fset\<times>isabelle_entity fset) option"

definition isabelle_acceptance_assessment_data :: "isabelle_acceptance_assessment \<Rightarrow> finite_factor_term" where
  "isabelle_acceptance_assessment_data=finite_option_presentation
    (finite_pair_presentation isabelle_entities_data isabelle_entities_data)"

lemma isabelle_acceptance_assessment_data_injective [intro]: "inj isabelle_acceptance_assessment_data"
  unfolding isabelle_acceptance_assessment_data_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective isabelle_collections_injective)

text \<open>
  An accepted build supplies the entities; the native program decides only membership of
  their presentations. Provenance of the entity list is the physical boundary of the build
  that defined it. It establishes no native claim beyond this contract.
\<close>

section \<open>Acceptance follows a renaming of the entities it decides\<close>

theorem isabelle_renamed_acceptance:
  assumes injective: "inj f"
    and original: "isabelle_demand_acceptance es demands=Some (accepted,refused)"
    and renamed: "isabelle_demand_acceptance (map (isabelle_entity_rename f) es)
      (map (isabelle_entity_rename f) demands)=Some (accepted',refused')"
  shows "accepted'=fimage (isabelle_entity_rename f) accepted"
    "refused'=fimage (isabelle_entity_rename f) refused"
proof -
  let ?g="isabelle_entity_rename f"
  have entities: "inj ?g" by (rule isabelle_entity_rename_injective[OF injective])
  have accepted_set: "fset accepted'=?g ` fset accepted"
    using isabelle_demand_acceptance_exact(1)[OF original] isabelle_demand_acceptance_exact(1)[OF renamed]
    by (simp only: set_map image_Int[OF entities])
  have refused_set: "fset refused'=?g ` fset refused"
    using isabelle_demand_acceptance_exact(2)[OF original] isabelle_demand_acceptance_exact(2)[OF renamed]
    by (simp only: set_map image_set_diff[OF entities])
  show "accepted'=fimage ?g accepted"
    by (simp only: fset_inject[symmetric] fimage.rep_eq accepted_set)
  show "refused'=fimage ?g refused"
    by (simp only: fset_inject[symmetric] fimage.rep_eq refused_set)
qed

end
