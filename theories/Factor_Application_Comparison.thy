theory Factor_Application_Comparison
  imports Factor_Observed_Applications Factor_Guided_Investigation
    Finite_Derived_Observations "HOL-Library.Product_Lexorder"
begin

section \<open>Concrete construction subjects and independent application conditions\<close>

type_synonym finite_natural_application =
  "finite_factor_term \<times> (nat\<times>finite_factor_term) fset \<times>
    (nat\<times>nat\<times>finite_factor_term) fset"

record finite_application_problem =
  application_entry :: nat
  application_schema :: "(nat,nat,nat) finite_factor_schema"
  application_enumeration :: "(nat\<times>nat\<times>nat finite_term_pattern) list"
  application_frontier :: "(nat\<times>finite_factor_term) fset"
  application_requests :: "(nat\<times>finite_factor_term) fset"
  application_required :: "finite_natural_application fset"

datatype application_construction = Separate_Application_Sources | Joined_Application_Observations

fun application_construction_result where
  "application_construction_result Separate_Application_Sources P=
    fimage (\<lambda>(d,S,t,V,H). (t,V,H))
      (finite_generated_applications_on_set
         [(application_entry P,application_schema P,application_enumeration P)] (application_frontier P)
       |\<union>| finite_requested_applications
         [(application_entry P,application_schema P,application_enumeration P)] (application_requests P))"
| "application_construction_result Joined_Application_Observations P=
    fimage (\<lambda>(d,S,t,V,H). (t,V,H))
      (finite_guided_applications [(application_entry P,application_schema P,application_enumeration P)]
        (application_frontier P) (application_requests P))"

datatype application_condition =
    Complete_Instance_Condition
  | Existing_Application_Condition
  | Required_Application_Condition

definition application_instances_valid where
  "application_instances_valid S A \<longleftrightarrow>
    fBall A (\<lambda>(t,V,H). finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V)"

fun application_condition_holds where
  "application_condition_holds Complete_Instance_Condition m P=
    application_instances_valid (application_schema P) (application_construction_result m P)"
| "application_condition_holds Existing_Application_Condition m P=
    (application_construction_result Separate_Application_Sources P |\<subseteq>|
      application_construction_result m P)"
| "application_condition_holds Required_Application_Condition m P=
    (application_required P |\<subseteq>| application_construction_result m P)"

definition application_candidate_subjects where
  "application_candidate_subjects=fset_of_list
    [(0::nat,Separate_Application_Sources),(1,Joined_Application_Observations)]"

definition application_condition_subjects where
  "application_condition_subjects=fset_of_list
    [(0::nat,Complete_Instance_Condition),(1,Existing_Application_Condition),(2,Required_Application_Condition)]"

definition application_observations where
  "application_observations W=finite_derived_observations application_candidate_subjects
    application_condition_subjects W application_condition_holds"

theorem application_observation_subject:
  assumes workloads: "single_valued (fset W)"
    and candidate: "(c,m) |\<in>| application_candidate_subjects"
    and condition: "(f,r) |\<in>| application_condition_subjects"
    and problem: "(w,P) |\<in>| W"
  shows "(f,c,w) |\<in>| application_observations W \<longleftrightarrow> application_condition_holds r m P"
  unfolding application_observations_def
  apply (rule finite_derived_observation_at_subject[OF _ candidate condition problem])
  using workloads by (auto simp: finite_observation_subjects_formed_def
    application_candidate_subjects_def application_condition_subjects_def
    single_valued_def fset_of_list.rep_eq)

theorem application_observation_required:
  assumes workloads: "single_valued (fset W)" and problem: "(w,P) |\<in>| W"
  shows "(2,1,w) |\<in>| application_observations W \<longleftrightarrow>
    application_required P |\<subseteq>| application_construction_result Joined_Application_Observations P"
  using application_observation_subject[OF workloads, of 1 Joined_Application_Observations
    2 Required_Application_Condition w P] problem
  by (simp add: application_candidate_subjects_def application_condition_subjects_def fset_of_list.rep_eq)

definition application_comparison where
  "application_comparison W=ffilter (\<lambda>(c,d).
    finite_candidate_profile (fimage fst application_condition_subjects) (application_observations W) c
      |\<subseteq>| finite_candidate_profile (fimage fst application_condition_subjects) (application_observations W) d)
    (ffUnion (fimage (\<lambda>(c,m). fimage (\<lambda>(d,n). (c,d)) application_candidate_subjects)
      application_candidate_subjects))"

definition application_investigation_observations where
  "application_investigation_observations (Ws::(nat\<times>finite_application_problem) list)=
    sorted_list_of_fset (application_observations (fset_of_list Ws))"

definition application_investigation_relation where
  "application_investigation_relation (Ws::(nat\<times>finite_application_problem) list)=
    sorted_list_of_fset (application_comparison (fset_of_list Ws))"

definition application_investigation where
  "application_investigation Ws selected=investigation_basis [0,1] [0,1,2] selected
    (application_investigation_observations Ws) (application_investigation_relation Ws)"

text \<open>
  A candidate is one of the two actual construction operations on the complete
  problem record. Conditions are defined independently on returned complete
  applications: valid instances, inclusion of the existing applications, and
  inclusion of the explicitly requested application relation.

  The observation equation connects every execution index to its actual
  construction, condition and complete problem. Candidate and facet prose is
  unnecessary to that equation. Future problem records enter the same operation;
  their requirement relation is data whose membership is checked against the
  returned applications. A finite comparison cannot establish coverage of every
  possible construction operation or the truth of conditional premise calls.
\<close>

end
