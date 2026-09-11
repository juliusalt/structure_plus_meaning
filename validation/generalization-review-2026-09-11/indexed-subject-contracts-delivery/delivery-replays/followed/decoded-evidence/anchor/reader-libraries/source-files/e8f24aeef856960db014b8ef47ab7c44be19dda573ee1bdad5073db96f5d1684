theory Finite_Investigation
  imports Method_Investigation Finite_Inference_Development
begin

section \<open>Complete finite observations return the actual comparison failures\<close>

definition finite_table_observations where
  "finite_table_observations table f c={w. (f,c,w)\<in>fset table}"

definition finite_observation_table_formed where
  "finite_observation_table_formed C U table \<longleftrightarrow>
    fBall table (\<lambda>(f,c,w). f\<in>fset U \<and> c\<in>fset C)"

definition finite_candidate_profile where
  "finite_candidate_profile F table c=
    fimage (\<lambda>(f,d,w). (f,w)) (ffilter (\<lambda>(f,d,w). f\<in>fset F \<and> d=c) table)"

theorem finite_candidate_profile_exact:
  "fset (finite_candidate_profile F table c)=candidate_profile (fset F) (finite_table_observations table) c"
proof -
  have member: "(f,w)\<in>fset (finite_candidate_profile F table c) \<longleftrightarrow>
      f\<in>fset F \<and> (f,c,w)\<in>fset table" for f w
  proof
    assume "(f,w)\<in>fset (finite_candidate_profile F table c)"
    then show "f\<in>fset F \<and> (f,c,w)\<in>fset table"
      by (auto simp: finite_candidate_profile_def fimage.rep_eq case_prod_beta' image_iff)
  next
    assume row: "f\<in>fset F \<and> (f,c,w)\<in>fset table"
    have selected: "(f,c,w)\<in>fset (ffilter (\<lambda>(f,d,w). f\<in>fset F \<and> d=c) table)"
      using row by simp
    show "(f,w)\<in>fset (finite_candidate_profile F table c)"
      unfolding finite_candidate_profile_def fimage.rep_eq
      by (rule image_eqI[where x="(f,c,w)", OF _ selected]) simp
  qed
  show ?thesis by (auto simp: member candidate_profile_def finite_table_observations_def)
qed

definition finite_candidate_losses where
  "finite_candidate_losses F table c d=
    ffilter (\<lambda>q. q\<notin>fset (finite_candidate_profile F table d)) (finite_candidate_profile F table c)"

theorem finite_candidate_losses_exact:
  "fset (finite_candidate_losses F table c d)=candidate_losses (fset F) (finite_table_observations table) c d"
  by (auto simp: finite_candidate_losses_def finite_candidate_profile_exact candidate_losses_def)

definition finite_basis_residual where
  "finite_basis_residual C F table relation=ffUnion (fimage (\<lambda>c.
    fimage (\<lambda>d. (c,d)) (ffilter (\<lambda>d.
      relation c d \<noteq> (fset (finite_candidate_profile F table c)\<subseteq>
        fset (finite_candidate_profile F table d))) C)) C)"

theorem finite_basis_residual_exact:
  "fset (finite_basis_residual C F table relation)=
    rel_dom (remaining_obligations {z. basis_condition relation (finite_table_observations table) z}
      (basis_obligations (fset C) (fset F)))"
  by (auto simp: finite_basis_residual_def ffUnion.rep_eq fimage.rep_eq
    finite_candidate_profile_exact remaining_obligations_def basis_obligations_def
    basis_condition_def graph_map_def rel_dom_def split: prod.splits)

theorem finite_basis_residual_empty:
  "finite_basis_residual C F table relation={||} \<longleftrightarrow>
    comparison_basis (fset C) relation (fset F) (finite_table_observations table)"
proof -
  have domain: "rel_dom (remaining_obligations K (graph_map I g))={i\<in>I. g i\<notin>K}" for K I g
    by (auto simp: rel_dom_def remaining_obligations_def graph_map_def)
  have represented: "fset (finite_basis_residual C F table relation)={} \<longleftrightarrow>
      comparison_basis (fset C) relation (fset F) (finite_table_observations table)"
    by (simp only: finite_basis_residual_exact basis_obligations_def domain;
      auto simp: basis_condition_def comparison_basis_def)
  have transfer: "(fset (finite_basis_residual C F table relation)=fset {||}) \<longleftrightarrow>
      finite_basis_residual C F table relation={||}"
    by (rule fset_inject)
  show ?thesis using represented transfer by simp
qed

definition finite_basis_evaluation where
  "finite_basis_evaluation C U F table relation residual \<longleftrightarrow>
    finite_observation_table_formed C U table \<and> fset F\<subseteq>fset U \<and>
    residual=finite_basis_residual C F table relation"

theorem finite_basis_evaluation_at_complete_observations:
  assumes complete: "\<And>f c. f\<in>fset U \<Longrightarrow> c\<in>fset C \<Longrightarrow>
    observe f c=finite_table_observations table f c"
    and evaluated: "finite_basis_evaluation C U F table relation {||}"
  shows "comparison_basis (fset C) relation (fset F) observe"
proof -
  have selected: "fset F\<subseteq>fset U"
    and basis: "comparison_basis (fset C) relation (fset F) (finite_table_observations table)"
    using evaluated by (auto simp: finite_basis_evaluation_def finite_basis_residual_empty[symmetric])
  have actual: "observe f c=finite_table_observations table f c"
    if "f\<in>fset F" "c\<in>fset C" for f c
    by (rule complete[OF subsetD[OF selected that(1)] that(2)])
  have profiles: "candidate_profile (fset F) observe c=
      candidate_profile (fset F) (finite_table_observations table) c"
    if "c\<in>fset C" for c
    using actual[OF _ that] by (auto simp: candidate_profile_def)
  show ?thesis
    unfolding comparison_basis_def
  proof (intro ballI)
    fix c d assume first: "c\<in>fset C" and second: "d\<in>fset C"
    show "relation c d \<longleftrightarrow>
      candidate_profile (fset F) observe c\<subseteq>candidate_profile (fset F) observe d"
      by (simp only: profiles[OF first] profiles[OF second]
        comparison_basis_at[OF basis first second, symmetric]; simp)
  qed
qed

section \<open>Finite demand retains whole rules and exposes qualified reasons\<close>

definition finite_inference_demand_edges where
  "finite_inference_demand_edges F K=ffUnion (fimage (\<lambda>(a,H).
    if a\<in>fset K \<or> \<not>finite_premise_functional H then {||}
    else fimage (\<lambda>(i,b). (a,b)) H) F)"

theorem finite_inference_demand_edges_exact:
  "fset (finite_inference_demand_edges F K)=inference_demand_edges (finite_inference_rules F) (fset K)"
proof -
  have union_member: "x\<in>fset (ffUnion (fimage g T)) \<longleftrightarrow>
      (\<exists>t\<in>fset T. x\<in>fset (g t))" for x g T
    by (auto simp: ffUnion.rep_eq fimage.rep_eq)
  have row_member: "(a,b)\<in>fset (if c\<in>fset K \<or> \<not>finite_premise_functional G then {||}
      else fimage (\<lambda>(i,b). (c,b)) G) \<longleftrightarrow>
      c\<notin>fset K \<and> finite_premise_functional G \<and> a=c \<and> (\<exists>i. (i,b)\<in>fset G)"
    for a b c G
    by (auto simp: fimage.rep_eq image_iff split: if_splits prod.splits)
  have represented: "(a,b)\<in>fset (finite_inference_demand_edges F K) \<longleftrightarrow>
      a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)" for a b
  proof
    assume member: "(a,b)\<in>fset (finite_inference_demand_edges F K)"
    let ?contribution="\<lambda>(c,G). if c\<in>fset K \<or> \<not>finite_premise_functional G then {||}
      else fimage (\<lambda>(i,b). (c,b)) G"
    have expanded: "\<exists>t\<in>fset F. (a,b)\<in>fset (?contribution t)"
      using member by (simp only: finite_inference_demand_edges_def union_member)
    obtain t where row: "t\<in>fset F" and contribution: "(a,b)\<in>fset (?contribution t)"
      using expanded by blast
    obtain c G where tuple: "t=(c,G)" by (cases t) auto
    have local: "(a,b)\<in>fset (if c\<in>fset K \<or> \<not>finite_premise_functional G then {||}
        else fimage (\<lambda>(i,b). (c,b)) G)"
      using contribution by (simp only: tuple prod.case)
    have details: "c\<notin>fset K \<and> finite_premise_functional G \<and>
        a=c \<and> (\<exists>i. (i,b)\<in>fset G)"
      using local by (simp only: row_member; simp)
    show "a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)"
      using row details by (auto simp: tuple finite_premise_functional_exact)
  next
    assume "a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)"
    then obtain G i where unknown: "a\<notin>fset K" and row: "(a,G)\<in>fset F"
      and formed: "single_valued (fset G)" and premise: "(i,b)\<in>fset G" by blast
    show "(a,b)\<in>fset (finite_inference_demand_edges F K)"
      unfolding finite_inference_demand_edges_def union_member
      by (rule bexI[of _ "(a,G)"])
        (use unknown formed premise row in \<open>auto simp: row_member finite_premise_functional_exact\<close>)
  qed
  have meaning: "(a,b)\<in>inference_demand_edges (finite_inference_rules F) (fset K) \<longleftrightarrow>
      a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)" for a b
  proof
    assume "(a,b)\<in>inference_demand_edges (finite_inference_rules F) (fset K)"
    then obtain H i where unknown: "a\<notin>fset K" and formed: "single_valued H"
      and rule: "finite_inference_rules F a H" and premise: "(i,b)\<in>H"
      by (auto simp: inference_demand_edges_def inference_premise_use_def)
    obtain G where row: "(a,G)\<in>fset F" and equation: "H=fset G"
      using rule by (auto simp: finite_inference_rules_def)
    show "a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)"
      using unknown formed row premise by (auto simp: equation)
  next
    assume "a\<notin>fset K \<and> (\<exists>G i. (a,G)\<in>fset F \<and>
        single_valued (fset G) \<and> (i,b)\<in>fset G)"
    then obtain G i where unknown: "a\<notin>fset K" and row: "(a,G)\<in>fset F"
      and formed: "single_valued (fset G)" and member: "(i,b)\<in>fset G" by blast
    have rule: "finite_inference_rules F a (fset G)"
      unfolding finite_inference_rules_def by (rule exI[of _ G]) (use row in simp)
    have premise: "inference_premise_use (finite_inference_rules F) a (fset G) i b"
      using formed member rule by (simp add: inference_premise_use_def)
    show "(a,b)\<in>inference_demand_edges (finite_inference_rules F) (fset K)"
      using unknown premise by (auto simp: inference_demand_edges_def)
  qed
  show ?thesis by (auto simp: represented meaning)
qed

definition finite_inference_demand where
  "finite_inference_demand F K A=ffUnion (fimage
    (\<lambda>a. finite_reachable_outputs id (finite_inference_demand_edges F K) a) A)"


lemma finite_inference_demand_code [code]:
  "finite_inference_demand F K A=finite_reachable_outputs_from id (finite_inference_demand_edges F K) A"
  by (simp only: finite_inference_demand_def finite_reachable_outputs_from_def)

theorem finite_inference_demand_exact:
  "fset (finite_inference_demand F K A)=inference_demand (finite_inference_rules F) (fset K) (fset A)"
  by (auto simp: finite_inference_demand_def ffUnion.rep_eq fimage.rep_eq
    finite_development_scope[symmetric] development_scope_def
    finite_inference_demand_edges_exact inference_demand_def)

definition finite_inference_demand_reasons where
  "finite_inference_demand_reasons F K A=ffUnion (fimage (\<lambda>(a,H).
    if a\<in>fset (finite_inference_demand F K A) \<and> a\<notin>fset K \<and> finite_premise_functional H
    then fimage (\<lambda>(i,b). (a,H,i,b)) H else {||}) F)"


lemma finite_inference_demand_reasons_code [code]:
  "finite_inference_demand_reasons F K A =
    (let demanded=finite_inference_demand F K A
     in ffUnion (fimage (\<lambda>(a,H).
       if a\<in>fset demanded \<and> a\<notin>fset K \<and> finite_premise_functional H
       then fimage (\<lambda>(i,b). (a,H,i,b)) H else {||}) F))"
  by (simp only: Let_def finite_inference_demand_reasons_def)

theorem finite_inference_demand_reasons_exact:
  "(a,H,i,b)\<in>fset (finite_inference_demand_reasons F K A) \<longleftrightarrow>
    a\<in>inference_demand (finite_inference_rules F) (fset K) (fset A) \<and>
    a\<notin>fset K \<and> (a,H)\<in>fset F \<and> single_valued (fset H) \<and> (i,b)\<in>fset H"
  by (auto simp: finite_inference_demand_reasons_def ffUnion.rep_eq fimage.rep_eq
    finite_inference_demand_exact finite_premise_functional_exact split: prod.splits if_splits)

definition finite_guided_inference_table where
  "finite_guided_inference_table F K A=
    ffilter (\<lambda>(a,H). a\<in>fset (finite_inference_demand F K A)) F"


lemma finite_guided_inference_table_code [code]:
  "finite_guided_inference_table F K A =
    (let demanded=finite_inference_demand F K A in ffilter (\<lambda>(a,H). a\<in>fset demanded) F)"
  by (simp only: Let_def finite_guided_inference_table_def)

theorem finite_guided_inference_rules_exact:
  "finite_inference_rules (finite_guided_inference_table F K A)=
    guided_inferences (finite_inference_rules F) (fset K) (fset A)"
  by (intro ext)
    (auto simp: finite_inference_rules_def finite_guided_inference_table_def
      finite_inference_demand_exact guided_inferences_def)

lemma finite_guided_inference_table_formed:
  "finite_inference_formed F \<Longrightarrow> finite_inference_formed (finite_guided_inference_table F K A)"
  by (auto simp: finite_inference_formed_def finite_guided_inference_table_def)

theorem finite_guided_goal_residual_exact:
  "finite_inference_residual (finite_guided_inference_table F K (fimage snd H)) K H=
    finite_inference_residual F K H"
proof -
  have boundary: "rel_ran (fset H)\<subseteq>fset (fimage snd H)"
    by (simp add: rel_ran_image fimage.rep_eq)
  have equal: "fset (finite_inference_residual (finite_guided_inference_table F K (fimage snd H)) K H)=
      fset (finite_inference_residual F K H)"
    by (simp only: finite_inference_residual_exact finite_guided_inference_rules_exact
      guided_goal_residual_exact[OF boundary])
  show ?thesis using equal by (simp only: fset_inject)
qed

definition finite_guided_inference_evaluation where
  "finite_guided_inference_evaluation F K H G \<longleftrightarrow>
    finite_inference_formed F \<and>
    finite_inference_evaluation (finite_guided_inference_table F K (fimage snd H)) K H G"

theorem finite_guided_inference_evaluation_exact:
  "finite_guided_inference_evaluation F K H G \<longleftrightarrow> finite_inference_evaluation F K H G"
  using finite_guided_inference_table_formed
  by (auto simp: finite_guided_inference_evaluation_def finite_inference_evaluation_def
    finite_guided_goal_residual_exact)

theorem finite_guided_inference_evaluation_sound:
  assumes "finite_guided_inference_evaluation F K H {||}"
    "inference_sound T (finite_inference_rules F)" "fset K\<subseteq>{a. T a}"
  shows "\<forall>i a. (i,a)\<in>fset H \<longrightarrow> T a"
  by (rule finite_inference_evaluation_sound[OF _ assms(2,3)])
    (use assms(1) in \<open>simp only: finite_guided_inference_evaluation_exact\<close>)

theorem an_unused_malformed_rule_is_still_rejected:
  "\<not>finite_guided_inference_evaluation
    (fset_of_list [(False,fset_of_list [(0::nat,False),(0,True)])]) {||} {||} {||}"
  by (simp add: finite_guided_inference_evaluation_def finite_inference_formed_def finite_premise_functional_def)

theorem finite_basis_report_exposes_the_omitted_facet:
  defines "C \<equiv> fset_of_list [False,True]"
    and "table \<equiv> fset_of_list [(False,False,()),(False,True,()),(True,True,())]"
  shows "finite_basis_residual C (fset_of_list [False]) table (\<lambda>c d. c\<longrightarrow>d)=
      fset_of_list [(True,False)]"
    and "finite_basis_residual C (fset_of_list [True]) table (\<lambda>c d. c\<longrightarrow>d)={||}"
  by (auto simp: finite_basis_residual_def finite_candidate_profile_def C_def table_def)

export_code finite_observation_table_formed finite_candidate_profile finite_candidate_losses
  finite_basis_residual finite_basis_evaluation finite_inference_demand_edges
  finite_inference_demand finite_inference_demand_reasons finite_guided_inference_table
  finite_guided_inference_evaluation checking SML

text \<open>
  The proved code equations share one demand computation across all goals,
  complete rule reports, and the selected table. The whole original rule
  table still supplies the formation check; no unused malformed rule is
  hidden by the optimization.

  The finite specialization returns candidate losses, every observation-basis
  mismatch, demanded conditions, and the complete rule and premise occurrence
  behind each reason. Its exactness contracts use the same profiles, basis
  conditions, demands, and residuals as the general account.

  Guidance preserves the original goal evaluator exactly. Formation checks
  still cover the whole supplied rule table, including unused malformed rules.
  The original goal family retains every occurrence. A complete finite
  observation table must separately be related to the actual observations;
  finite enumeration does not validate the submitted comparison meaning.

  The SML export checks operative finite code. It neither enumerates an
  arbitrary infinite method nor supplies native Factor checking of the
  mathematical soundness, adequacy, or scope-coverage proofs.
\<close>

end
