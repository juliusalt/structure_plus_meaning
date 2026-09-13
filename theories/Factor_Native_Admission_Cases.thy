theory Factor_Native_Admission_Cases
  imports Factor_Finite_Native_Admission_Construction Factor_Finite_Admission_Goal_Evaluation
    Factor_Finite_Source_Extension_Cases Factor_Program_Evaluation_Investigation Factor_Finite_Term_Demands
begin

type_synonym native_admission_problem =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    local_address option definition_site admission_goal\<times>finite_factor_term fset"

fun admission_goal_variant :: "nat\<Rightarrow>'d admission_goal\<Rightarrow>'d admission_goal" where
  "admission_goal_variant m (Existing_Admission d)=Existing_Admission d"
| "admission_goal_variant m (Paired_Admission g h)=(if m=1 then admission_goal_variant m g
    else Paired_Admission (admission_goal_variant m g)
      (if m=2 then admission_goal_variant m g else admission_goal_variant m h))"
| "admission_goal_variant m (Collected_Admission g)=(if m=3 then admission_goal_variant m g
    else Collected_Admission (admission_goal_variant m g))"

lemma admission_goal_variant_original [simp]: "admission_goal_variant 0 g=g"
  by (induction g) simp_all

fun admission_goal_samples :: "finite_factor_term fset\<Rightarrow>'d admission_goal\<Rightarrow>finite_factor_term fset" where
  "admission_goal_samples B (Existing_Admission d)=B"
| "admission_goal_samples B (Paired_Admission g h)=ffUnion (fimage (\<lambda>x.
    fimage (Finite_Pair x) (admission_goal_samples B h)) (admission_goal_samples B g))"
| "admission_goal_samples B (Collected_Admission g)=finsert (Finite_Payload [])
    (ffUnion (fimage (\<lambda>x. {|finite_data_sequence [x],finite_data_sequence [x,x],
      finite_data_sequence [x,Finite_Payload [1]]|}) (admission_goal_samples B g)))"

definition native_admission_shapes :: "(nat\<times>nat) list" where
  "native_admission_shapes=concat (map (\<lambda>s. map (Pair s) [0,1,2,3,4,5,7]) [0,1,4,5,8,9,10,11,12])"

definition native_admission_goal :: "nat\<Rightarrow>'d\<Rightarrow>'d\<Rightarrow>'d\<Rightarrow>'d admission_goal" where
  "native_admission_goal k a b absent=(let x=Existing_Admission a; y=Existing_Admission b in
    if k=0 then x else if k=1 then Paired_Admission x y else if k=2 then Collected_Admission x
    else if k=3 then Paired_Admission (Collected_Admission x) y
    else if k=4 then Collected_Admission (Paired_Admission x y)
    else if k=5 then Collected_Admission (Collected_Admission x)
    else Paired_Admission x (Existing_Admission absent))"

definition native_admission_seed where
  "native_admission_seed i=(if i=12 then Some
    ((finite_guard_source False)\<lparr>finite_environment_artifacts:=finsert
      (Some [255],finite_payload_syntax [47]) (finite_environment_artifacts (finite_guard_source False))\<rparr>,None,[0])
    else finite_source_extension_seed i)"

definition native_source_goal_problem where
  "native_source_goal_problem goal samples k E u r B=(let
    P=(case finite_native_source E u r of None \<Rightarrow>
      \<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr> | Some Q \<Rightarrow> Q);
    absent=finite_native_admission_fresh P; ds=sorted_list_of_fset (finite_system_definitions P);
    a=(case ds of [] \<Rightarrow> absent | d#rest \<Rightarrow> d);
    b=(case ds of [] \<Rightarrow> absent | d#rest \<Rightarrow> (case rest of [] \<Rightarrow> d | e#remaining \<Rightarrow> e));
    g=goal k a b absent
    in (E,u,r,g,B |\<union>| samples B g))"

definition native_admission_problem :: "nat\<Rightarrow>native_admission_problem option" where
  "native_admission_problem w=(if w<length native_admission_shapes then
    (case native_admission_shapes!w of (s,k) \<Rightarrow> map_option (\<lambda>(E,u,r).
      native_source_goal_problem native_admission_goal admission_goal_samples k E u r
        (finsert (Finite_Payload [256]) program_evaluation_terms)) (native_admission_seed s)) else None)"

definition native_admission_method :: "nat\<Rightarrow>native_admission_problem\<Rightarrow>
    (local_address option definition_site\<times>local_address option finite_artifact_environment\<times>local_address option) option" where
  "native_admission_method m X=(case X of (E,u,r,g,T) \<Rightarrow>
    if m=5 then None else map_option (\<lambda>(d,F,v). (d,
      (if m=4 then F\<lparr>finite_environment_artifacts:=
        ffilter (\<lambda>(a,A). a\<noteq>Some [255]) (finite_environment_artifacts F)\<rparr> else F),v))
      (finite_construct_source_admission E u r (admission_goal_variant (if m=4 then 0 else m) g)))"

lemma native_admission_method_original:
  "native_admission_method 0 (E,u,r,g,T)=finite_construct_source_admission E u r g"
  by (cases "finite_construct_source_admission E u r g")
    (simp_all add: native_admission_method_def split: prod.splits)

definition native_admission_source_report where
  "native_admission_source_report X=(case X of (E,u,r,g,T) \<Rightarrow>
    let source=finite_native_source E u r;
      supported=(case source of None \<Rightarrow> False | Some P \<Rightarrow>
        finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P);
      D=(case source of None \<Rightarrow> {||} | Some P \<Rightarrow> finite_program_term_demand P T);
      evaluated=finite_native_program_evaluation E u r D
    in (source,supported,D,evaluated,map_option (\<lambda>(P,A). ffilter (finite_admission_goal_test A g) T) evaluated))"

definition native_entry_target_report where
  "native_entry_target_report u r T result=map_option (\<lambda>(d,F,v).
    let source=finite_native_source F v [];
      D=(case source of None \<Rightarrow> {||} | Some P \<Rightarrow> finite_program_term_demand P T);
      evaluated=finite_native_program_evaluation F v [] D
    in (d,F,v,source,D,evaluated,map_option (\<lambda>(P,A). ffilter (\<lambda>t. (d,t) |\<in>| A) T) evaluated,
      finite_native_source F u r)) result"

definition native_admission_target_report where
  "native_admission_target_report X result=(case X of (E,u,r,g,T) \<Rightarrow>
    native_entry_target_report u r T result)"

definition native_admission_report where
  "native_admission_report w=map_option (\<lambda>X. (X,native_admission_source_report X,
    map (\<lambda>m. (m,native_admission_target_report X (native_admission_method m X))) [0,1,2,3,4,5]))
    (native_admission_problem w)"

export_code native_admission_report checking SML

text \<open>
  The source environments are actual previously constructed packages. They
  include distinct component meanings, empty families, recursion, literal
  targets, an empty package, a missing package and an unused malformed artifact.
  A further source retains one valid unused artifact so that deleting it can be
  observed independently of the requested entry's positive meaning.

  Goals name definitions recovered from each source. The six operations retain
  the goal, project the left field, duplicate the left requirement, remove list
  structure, remove the unused artifact after construction, or return no result.
  Samples are generated from the goal's shape and a fixed term family, without
  reading any candidate's truth values. All demanded calls include their term
  components. The reports retain complete inputs, outputs and computed source
  and target evaluations; they do not by themselves select an operation.
\<close>

end
